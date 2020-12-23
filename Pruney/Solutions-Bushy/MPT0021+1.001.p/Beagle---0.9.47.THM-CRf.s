%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0021+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:35 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 131 expanded)
%              Number of leaves         :   13 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :   66 ( 250 expanded)
%              Number of equality atoms :   17 (  71 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,B)
          & ! [D] :
              ( ( r1_tarski(A,D)
                & r1_tarski(C,D) )
             => r1_tarski(B,D) ) )
       => B = k2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_26,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(k2_xboole_0(A_7,C_9),B_8)
      | ~ r1_tarski(C_9,B_8)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_14,plain,(
    k2_xboole_0('#skF_1','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(A_5,k2_xboole_0(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_24,plain,(
    ! [B_15,A_16] : k2_xboole_0(B_15,A_16) = k2_xboole_0(A_16,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_39,plain,(
    ! [A_16,B_15] : r1_tarski(A_16,k2_xboole_0(B_15,A_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_10])).

tff(c_16,plain,(
    ! [D_11] :
      ( r1_tarski('#skF_2',D_11)
      | ~ r1_tarski('#skF_3',D_11)
      | ~ r1_tarski('#skF_1',D_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_110,plain,(
    ! [A_22,C_23,B_24] :
      ( r1_tarski(k2_xboole_0(A_22,C_23),B_24)
      | ~ r1_tarski(C_23,B_24)
      | ~ r1_tarski(A_22,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_425,plain,(
    ! [A_34,C_35,B_36] :
      ( k2_xboole_0(A_34,C_35) = B_36
      | ~ r1_tarski(B_36,k2_xboole_0(A_34,C_35))
      | ~ r1_tarski(C_35,B_36)
      | ~ r1_tarski(A_34,B_36) ) ),
    inference(resolution,[status(thm)],[c_110,c_4])).

tff(c_454,plain,(
    ! [B_15,A_16] :
      ( k2_xboole_0(B_15,A_16) = A_16
      | ~ r1_tarski(A_16,A_16)
      | ~ r1_tarski(B_15,A_16) ) ),
    inference(resolution,[status(thm)],[c_39,c_425])).

tff(c_486,plain,(
    ! [B_37,A_38] :
      ( k2_xboole_0(B_37,A_38) = A_38
      | ~ r1_tarski(B_37,A_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_454])).

tff(c_691,plain,(
    ! [D_43] :
      ( k2_xboole_0('#skF_2',D_43) = D_43
      | ~ r1_tarski('#skF_3',D_43)
      | ~ r1_tarski('#skF_1',D_43) ) ),
    inference(resolution,[status(thm)],[c_16,c_486])).

tff(c_1727,plain,(
    ! [B_62] :
      ( k2_xboole_0('#skF_2',k2_xboole_0('#skF_3',B_62)) = k2_xboole_0('#skF_3',B_62)
      | ~ r1_tarski('#skF_1',k2_xboole_0('#skF_3',B_62)) ) ),
    inference(resolution,[status(thm)],[c_10,c_691])).

tff(c_1754,plain,(
    k2_xboole_0('#skF_2',k2_xboole_0('#skF_3','#skF_1')) = k2_xboole_0('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_39,c_1727])).

tff(c_1771,plain,(
    k2_xboole_0('#skF_2',k2_xboole_0('#skF_1','#skF_3')) = k2_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_1754])).

tff(c_475,plain,(
    ! [A_34,C_35] :
      ( k2_xboole_0(A_34,C_35) = '#skF_2'
      | ~ r1_tarski(C_35,'#skF_2')
      | ~ r1_tarski(A_34,'#skF_2')
      | ~ r1_tarski('#skF_3',k2_xboole_0(A_34,C_35))
      | ~ r1_tarski('#skF_1',k2_xboole_0(A_34,C_35)) ) ),
    inference(resolution,[status(thm)],[c_16,c_425])).

tff(c_1839,plain,
    ( k2_xboole_0('#skF_2',k2_xboole_0('#skF_1','#skF_3')) = '#skF_2'
    | ~ r1_tarski(k2_xboole_0('#skF_1','#skF_3'),'#skF_2')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ r1_tarski('#skF_3',k2_xboole_0('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_1',k2_xboole_0('#skF_2',k2_xboole_0('#skF_1','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1771,c_475])).

tff(c_1887,plain,
    ( k2_xboole_0('#skF_1','#skF_3') = '#skF_2'
    | ~ r1_tarski(k2_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1771,c_39,c_8,c_1771,c_1839])).

tff(c_1888,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_1887])).

tff(c_1905,plain,
    ( ~ r1_tarski('#skF_3','#skF_2')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_1888])).

tff(c_1909,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_1905])).

%------------------------------------------------------------------------------
