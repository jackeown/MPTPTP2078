%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0287+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:03 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   29 (  35 expanded)
%              Number of leaves         :   16 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   35 (  52 expanded)
%              Number of equality atoms :    1 (   2 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > #nlpp > k3_tarski > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_49,negated_conjecture,(
    ~ ! [A,B] :
        ( ! [C] :
            ( r2_hidden(C,A)
           => r1_tarski(C,B) )
       => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(c_26,plain,(
    ~ r1_tarski(k3_tarski('#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ! [A_42,C_43] :
      ( r2_hidden('#skF_5'(A_42,k3_tarski(A_42),C_43),A_42)
      | ~ r2_hidden(C_43,k3_tarski(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28,plain,(
    ! [C_26] :
      ( r1_tarski(C_26,'#skF_7')
      | ~ r2_hidden(C_26,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_70,plain,(
    ! [C_43] :
      ( r1_tarski('#skF_5'('#skF_6',k3_tarski('#skF_6'),C_43),'#skF_7')
      | ~ r2_hidden(C_43,k3_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_59,c_28])).

tff(c_52,plain,(
    ! [C_40,A_41] :
      ( r2_hidden(C_40,'#skF_5'(A_41,k3_tarski(A_41),C_40))
      | ~ r2_hidden(C_40,k3_tarski(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_252,plain,(
    ! [C_68,B_69,A_70] :
      ( r2_hidden(C_68,B_69)
      | ~ r1_tarski('#skF_5'(A_70,k3_tarski(A_70),C_68),B_69)
      | ~ r2_hidden(C_68,k3_tarski(A_70)) ) ),
    inference(resolution,[status(thm)],[c_52,c_2])).

tff(c_262,plain,(
    ! [C_71] :
      ( r2_hidden(C_71,'#skF_7')
      | ~ r2_hidden(C_71,k3_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_70,c_252])).

tff(c_294,plain,(
    ! [B_72] :
      ( r2_hidden('#skF_1'(k3_tarski('#skF_6'),B_72),'#skF_7')
      | r1_tarski(k3_tarski('#skF_6'),B_72) ) ),
    inference(resolution,[status(thm)],[c_6,c_262])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_302,plain,(
    r1_tarski(k3_tarski('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_294,c_4])).

tff(c_308,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_26,c_302])).

%------------------------------------------------------------------------------
