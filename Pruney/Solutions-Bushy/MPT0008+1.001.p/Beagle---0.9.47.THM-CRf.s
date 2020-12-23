%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0008+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:33 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   24 (  29 expanded)
%              Number of leaves         :   11 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :   33 (  48 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(B,C) )
       => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_8,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [C_10,B_11,A_12] :
      ( r2_hidden(C_10,B_11)
      | ~ r2_hidden(C_10,A_12)
      | ~ r1_tarski(A_12,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_25,plain,(
    ! [A_14,B_15,B_16] :
      ( r2_hidden('#skF_1'(A_14,B_15),B_16)
      | ~ r1_tarski(A_14,B_16)
      | r1_tarski(A_14,B_15) ) ),
    inference(resolution,[status(thm)],[c_6,c_20])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    ! [A_17,B_18,B_19,B_20] :
      ( r2_hidden('#skF_1'(A_17,B_18),B_19)
      | ~ r1_tarski(B_20,B_19)
      | ~ r1_tarski(A_17,B_20)
      | r1_tarski(A_17,B_18) ) ),
    inference(resolution,[status(thm)],[c_25,c_2])).

tff(c_44,plain,(
    ! [A_21,B_22] :
      ( r2_hidden('#skF_1'(A_21,B_22),'#skF_4')
      | ~ r1_tarski(A_21,'#skF_3')
      | r1_tarski(A_21,B_22) ) ),
    inference(resolution,[status(thm)],[c_10,c_34])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53,plain,(
    ! [A_23] :
      ( ~ r1_tarski(A_23,'#skF_3')
      | r1_tarski(A_23,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_4])).

tff(c_60,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_53])).

tff(c_66,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_60])).

%------------------------------------------------------------------------------
