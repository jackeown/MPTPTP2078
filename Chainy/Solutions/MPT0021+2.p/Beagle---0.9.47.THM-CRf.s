%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0021+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:10 EST 2020

% Result     : Theorem 7.29s
% Output     : CNFRefutation 7.32s
% Verified   : 
% Statistics : Number of formulae       :   61 (  69 expanded)
%              Number of leaves         :   41 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :   48 (  71 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_20 > #skF_18 > #skF_6 > #skF_1 > #skF_17 > #skF_19 > #skF_4 > #skF_10 > #skF_12 > #skF_5 > #skF_21 > #skF_9 > #skF_7 > #skF_14 > #skF_3 > #skF_2 > #skF_8 > #skF_16 > #skF_15

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_20',type,(
    '#skF_20': $i )).

tff('#skF_18',type,(
    '#skF_18': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * ( $i * $i ) ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_17',type,(
    '#skF_17': ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_19',type,(
    '#skF_19': $i )).

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

tff('#skF_21',type,(
    '#skF_21': $i )).

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

tff(f_286,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,B)
          & ! [D] :
              ( ( r1_tarski(A,D)
                & r1_tarski(C,D) )
             => r1_tarski(B,D) ) )
       => B = k2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

tff(f_331,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

tff(f_317,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_266,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_242,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_214,plain,(
    r1_tarski('#skF_21','#skF_20') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_216,plain,(
    r1_tarski('#skF_19','#skF_20') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_9424,plain,(
    ! [A_468,C_469,B_470] :
      ( r1_tarski(k2_xboole_0(A_468,C_469),B_470)
      | ~ r1_tarski(C_469,B_470)
      | ~ r1_tarski(A_468,B_470) ) ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_xboole_0(B_6,A_5) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_210,plain,(
    k2_xboole_0('#skF_19','#skF_21') != '#skF_20' ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_247,plain,(
    k2_xboole_0('#skF_21','#skF_19') != '#skF_20' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_210])).

tff(c_236,plain,(
    ! [A_118,B_119] : r1_tarski(A_118,k2_xboole_0(A_118,B_119)) ),
    inference(cnfTransformation,[status(thm)],[f_317])).

tff(c_477,plain,(
    ! [B_158,A_159] : k2_xboole_0(B_158,A_159) = k2_xboole_0(A_159,B_158) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_501,plain,(
    ! [B_158,A_159] : r1_tarski(B_158,k2_xboole_0(A_159,B_158)) ),
    inference(superposition,[status(thm),theory(equality)],[c_477,c_236])).

tff(c_212,plain,(
    ! [D_100] :
      ( r1_tarski('#skF_20',D_100)
      | ~ r1_tarski('#skF_21',D_100)
      | ~ r1_tarski('#skF_19',D_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_650,plain,(
    ! [A_174,B_175] :
      ( k2_xboole_0(A_174,B_175) = B_175
      | ~ r1_tarski(A_174,B_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_766,plain,(
    ! [D_186] :
      ( k2_xboole_0('#skF_20',D_186) = D_186
      | ~ r1_tarski('#skF_21',D_186)
      | ~ r1_tarski('#skF_19',D_186) ) ),
    inference(resolution,[status(thm)],[c_212,c_650])).

tff(c_871,plain,(
    ! [A_196] :
      ( k2_xboole_0('#skF_20',k2_xboole_0(A_196,'#skF_19')) = k2_xboole_0(A_196,'#skF_19')
      | ~ r1_tarski('#skF_21',k2_xboole_0(A_196,'#skF_19')) ) ),
    inference(resolution,[status(thm)],[c_501,c_766])).

tff(c_893,plain,(
    k2_xboole_0('#skF_20',k2_xboole_0('#skF_21','#skF_19')) = k2_xboole_0('#skF_21','#skF_19') ),
    inference(resolution,[status(thm)],[c_236,c_871])).

tff(c_1161,plain,(
    r1_tarski('#skF_20',k2_xboole_0('#skF_21','#skF_19')) ),
    inference(superposition,[status(thm),theory(equality)],[c_893,c_236])).

tff(c_1798,plain,(
    ! [B_264,A_265] :
      ( B_264 = A_265
      | ~ r1_tarski(B_264,A_265)
      | ~ r1_tarski(A_265,B_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_1810,plain,
    ( k2_xboole_0('#skF_21','#skF_19') = '#skF_20'
    | ~ r1_tarski(k2_xboole_0('#skF_21','#skF_19'),'#skF_20') ),
    inference(resolution,[status(thm)],[c_1161,c_1798])).

tff(c_1832,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_21','#skF_19'),'#skF_20') ),
    inference(negUnitSimplification,[status(thm)],[c_247,c_1810])).

tff(c_9466,plain,
    ( ~ r1_tarski('#skF_19','#skF_20')
    | ~ r1_tarski('#skF_21','#skF_20') ),
    inference(resolution,[status(thm)],[c_9424,c_1832])).

tff(c_9551,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_216,c_9466])).
%------------------------------------------------------------------------------
