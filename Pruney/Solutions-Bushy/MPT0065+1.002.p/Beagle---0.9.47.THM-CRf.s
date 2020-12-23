%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0065+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:39 EST 2020

% Result     : Theorem 1.45s
% Output     : CNFRefutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   33 (  50 expanded)
%              Number of leaves         :   12 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  83 expanded)
%              Number of equality atoms :    6 (  13 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_49,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_xboole_0(A,B)
          & r1_tarski(B,C) )
       => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
     => ~ r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

tff(c_6,plain,(
    ! [B_4] : ~ r2_xboole_0(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_27,plain,(
    ! [A_13,B_14] :
      ( r2_xboole_0(A_13,B_14)
      | B_14 = A_13
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12,plain,(
    ~ r2_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_48,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_27,c_12])).

tff(c_49,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_16,plain,(
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ r2_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_18])).

tff(c_14,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_67,plain,(
    ! [A_19,C_20,B_21] :
      ( r1_tarski(A_19,C_20)
      | ~ r1_tarski(B_21,C_20)
      | ~ r1_tarski(A_19,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_75,plain,(
    ! [A_22] :
      ( r1_tarski(A_22,'#skF_3')
      | ~ r1_tarski(A_22,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_14,c_67])).

tff(c_78,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_75])).

tff(c_82,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_78])).

tff(c_83,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_86,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_14])).

tff(c_23,plain,(
    ! [B_11,A_12] :
      ( ~ r2_xboole_0(B_11,A_12)
      | ~ r2_xboole_0(A_12,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_26,plain,(
    ~ r2_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_23])).

tff(c_43,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_27,c_26])).

tff(c_93,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_43])).

tff(c_97,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_16])).

tff(c_101,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_97])).

%------------------------------------------------------------------------------
