%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0245+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:58 EST 2020

% Result     : Theorem 1.54s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   19 (  21 expanded)
%              Number of leaves         :   12 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   16 (  22 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_37,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => ( r2_hidden(C,A)
          | r1_tarski(A,k4_xboole_0(B,k1_tarski(C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_zfmisc_1)).

tff(f_30,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r2_hidden(C,A)
        | r1_tarski(A,k4_xboole_0(B,k1_tarski(C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l2_zfmisc_1)).

tff(c_6,plain,(
    ~ r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_9,plain,(
    ! [A_4,B_5,C_6] :
      ( r1_tarski(A_4,k4_xboole_0(B_5,k1_tarski(C_6)))
      | r2_hidden(C_6,A_4)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_4,plain,(
    ~ r1_tarski('#skF_1',k4_xboole_0('#skF_2',k1_tarski('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,
    ( r2_hidden('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_9,c_4])).

tff(c_15,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_12])).

tff(c_17,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_15])).

%------------------------------------------------------------------------------
