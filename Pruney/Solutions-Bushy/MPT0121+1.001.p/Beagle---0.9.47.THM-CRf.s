%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0121+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:45 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   28 (  37 expanded)
%              Number of leaves         :   12 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   38 (  66 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_53,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_xboole_0(A,D)
          & r1_xboole_0(B,D)
          & r1_xboole_0(C,D) )
       => r1_xboole_0(k2_xboole_0(k2_xboole_0(A,B),C),D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_xboole_1)).

tff(f_28,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_16,plain,(
    r1_xboole_0('#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_17,plain,(
    ! [B_6,A_7] :
      ( r1_xboole_0(B_6,A_7)
      | ~ r1_xboole_0(A_7,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_26,plain,(
    r1_xboole_0('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_17])).

tff(c_14,plain,(
    r1_xboole_0('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_25,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_17])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( ~ r1_xboole_0(A_3,C_5)
      | ~ r1_xboole_0(A_3,B_4)
      | r1_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_17])).

tff(c_41,plain,(
    ! [A_14,C_15,B_16] :
      ( ~ r1_xboole_0(A_14,C_15)
      | ~ r1_xboole_0(A_14,B_16)
      | r1_xboole_0(A_14,k2_xboole_0(B_16,C_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_53,plain,(
    ! [B_17,C_18,A_19] :
      ( r1_xboole_0(k2_xboole_0(B_17,C_18),A_19)
      | ~ r1_xboole_0(A_19,C_18)
      | ~ r1_xboole_0(A_19,B_17) ) ),
    inference(resolution,[status(thm)],[c_41,c_2])).

tff(c_10,plain,(
    ~ r1_xboole_0(k2_xboole_0(k2_xboole_0('#skF_1','#skF_2'),'#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_64,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_3')
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_53,c_10])).

tff(c_71,plain,(
    ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_64])).

tff(c_75,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_2')
    | ~ r1_xboole_0('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_71])).

tff(c_79,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_25,c_75])).

%------------------------------------------------------------------------------
