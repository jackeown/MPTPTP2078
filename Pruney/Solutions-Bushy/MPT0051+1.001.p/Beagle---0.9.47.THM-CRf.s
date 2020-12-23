%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0051+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:38 EST 2020

% Result     : Theorem 7.65s
% Output     : CNFRefutation 7.65s
% Verified   : 
% Statistics : Number of formulae       :   35 (  43 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   47 (  67 expanded)
%              Number of equality atoms :    2 (   3 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_55,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k4_xboole_0(A,B),C)
       => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_44,plain,(
    ~ r1_tarski('#skF_6',k2_xboole_0('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    r1_tarski(k4_xboole_0('#skF_6','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_103,plain,(
    ! [D_41,A_42,B_43] :
      ( r2_hidden(D_41,k4_xboole_0(A_42,B_43))
      | r2_hidden(D_41,B_43)
      | ~ r2_hidden(D_41,A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2221,plain,(
    ! [D_257,B_258,A_259,B_260] :
      ( r2_hidden(D_257,B_258)
      | ~ r1_tarski(k4_xboole_0(A_259,B_260),B_258)
      | r2_hidden(D_257,B_260)
      | ~ r2_hidden(D_257,A_259) ) ),
    inference(resolution,[status(thm)],[c_103,c_2])).

tff(c_2263,plain,(
    ! [D_261] :
      ( r2_hidden(D_261,'#skF_8')
      | r2_hidden(D_261,'#skF_7')
      | ~ r2_hidden(D_261,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_46,c_2221])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( ~ r2_hidden(D_11,A_6)
      | r2_hidden(D_11,k2_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_51,plain,(
    ! [A_30,B_31] :
      ( ~ r2_hidden('#skF_1'(A_30,B_31),B_31)
      | r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_61,plain,(
    ! [A_30,A_6,B_7] :
      ( r1_tarski(A_30,k2_xboole_0(A_6,B_7))
      | ~ r2_hidden('#skF_1'(A_30,k2_xboole_0(A_6,B_7)),A_6) ) ),
    inference(resolution,[status(thm)],[c_12,c_51])).

tff(c_5202,plain,(
    ! [A_506,B_507] :
      ( r1_tarski(A_506,k2_xboole_0('#skF_7',B_507))
      | r2_hidden('#skF_1'(A_506,k2_xboole_0('#skF_7',B_507)),'#skF_8')
      | ~ r2_hidden('#skF_1'(A_506,k2_xboole_0('#skF_7',B_507)),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2263,c_61])).

tff(c_5223,plain,(
    ! [B_508] :
      ( r2_hidden('#skF_1'('#skF_6',k2_xboole_0('#skF_7',B_508)),'#skF_8')
      | r1_tarski('#skF_6',k2_xboole_0('#skF_7',B_508)) ) ),
    inference(resolution,[status(thm)],[c_6,c_5202])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | r2_hidden(D_11,k2_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_60,plain,(
    ! [A_30,A_6,B_7] :
      ( r1_tarski(A_30,k2_xboole_0(A_6,B_7))
      | ~ r2_hidden('#skF_1'(A_30,k2_xboole_0(A_6,B_7)),B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_51])).

tff(c_5237,plain,(
    r1_tarski('#skF_6',k2_xboole_0('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_5223,c_60])).

tff(c_5252,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_44,c_5237])).

%------------------------------------------------------------------------------
