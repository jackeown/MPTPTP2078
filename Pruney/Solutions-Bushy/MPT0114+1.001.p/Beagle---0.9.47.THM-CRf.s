%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0114+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:45 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 136 expanded)
%              Number of leaves         :   19 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 ( 230 expanded)
%              Number of equality atoms :    3 (  18 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_45,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k5_xboole_0(B,C))
      <=> ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).

tff(f_26,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_20,plain,
    ( r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_23,plain,(
    r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_25,plain,(
    ! [A_15,B_16] : k4_xboole_0(k2_xboole_0(A_15,B_16),k3_xboole_0(A_15,B_16)) = k5_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,C_5)
      | ~ r1_tarski(A_3,k4_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_49,plain,(
    ! [A_20,A_21,B_22] :
      ( r1_xboole_0(A_20,k3_xboole_0(A_21,B_22))
      | ~ r1_tarski(A_20,k5_xboole_0(A_21,B_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25,c_4])).

tff(c_6,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_tarski(A_3,B_4)
      | ~ r1_tarski(A_3,k4_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_41,plain,(
    ! [A_17,A_18,B_19] :
      ( r1_tarski(A_17,k2_xboole_0(A_18,B_19))
      | ~ r1_tarski(A_17,k5_xboole_0(A_18,B_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25,c_6])).

tff(c_45,plain,(
    r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_23,c_41])).

tff(c_10,plain,
    ( ~ r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6'))
    | ~ r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_47,plain,
    ( ~ r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_10])).

tff(c_48,plain,(
    ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_47])).

tff(c_52,plain,(
    ~ r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_49,c_48])).

tff(c_56,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_23,c_52])).

tff(c_57,plain,(
    ~ r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_47])).

tff(c_58,plain,(
    r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_47])).

tff(c_14,plain,
    ( r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6'))
    | ~ r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_75,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_58,c_14])).

tff(c_12,plain,
    ( r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6'))
    | ~ r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_73,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_58,c_12])).

tff(c_2,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),k3_xboole_0(A_1,B_2)) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_60,plain,(
    ! [A_26,B_27,C_28] :
      ( r1_tarski(A_26,k4_xboole_0(B_27,C_28))
      | ~ r1_xboole_0(A_26,C_28)
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_76,plain,(
    ! [A_29,A_30,B_31] :
      ( r1_tarski(A_29,k5_xboole_0(A_30,B_31))
      | ~ r1_xboole_0(A_29,k3_xboole_0(A_30,B_31))
      | ~ r1_tarski(A_29,k2_xboole_0(A_30,B_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_60])).

tff(c_79,plain,
    ( r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3'))
    | ~ r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_73,c_76])).

tff(c_88,plain,(
    r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_79])).

tff(c_90,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_88])).

tff(c_92,plain,(
    ~ r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_16,plain,
    ( ~ r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3'))
    | r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_112,plain,(
    ~ r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_16])).

tff(c_91,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_18,plain,
    ( r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3'))
    | r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_93,plain,(
    r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_94,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_93])).

tff(c_95,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_116,plain,(
    ! [A_40,B_41,C_42] :
      ( r1_tarski(A_40,k4_xboole_0(B_41,C_42))
      | ~ r1_xboole_0(A_40,C_42)
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_129,plain,(
    ! [A_43,A_44,B_45] :
      ( r1_tarski(A_43,k5_xboole_0(A_44,B_45))
      | ~ r1_xboole_0(A_43,k3_xboole_0(A_44,B_45))
      | ~ r1_tarski(A_43,k2_xboole_0(A_44,B_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_116])).

tff(c_135,plain,
    ( r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3'))
    | ~ r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_95,c_129])).

tff(c_139,plain,(
    r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_135])).

tff(c_141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_139])).

%------------------------------------------------------------------------------
