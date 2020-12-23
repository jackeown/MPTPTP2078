%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0336+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:07 EST 2020

% Result     : Theorem 7.27s
% Output     : CNFRefutation 7.27s
% Verified   : 
% Statistics : Number of formulae       :   55 (  87 expanded)
%              Number of leaves         :   24 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :   60 ( 112 expanded)
%              Number of equality atoms :   29 (  54 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_28,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_46,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_54,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_20,plain,(
    ! [A_16] : k2_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_28,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_192,plain,(
    ! [A_38,B_39] :
      ( k3_xboole_0(A_38,B_39) = k1_xboole_0
      | ~ r1_xboole_0(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_200,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_192])).

tff(c_424,plain,(
    ! [A_54,B_55,C_56] : k2_xboole_0(k3_xboole_0(A_54,B_55),k3_xboole_0(A_54,C_56)) = k3_xboole_0(A_54,k2_xboole_0(B_55,C_56)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8232,plain,(
    ! [A_126,B_127,B_128] : k2_xboole_0(k3_xboole_0(A_126,B_127),k3_xboole_0(B_128,A_126)) = k3_xboole_0(A_126,k2_xboole_0(B_127,B_128)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_424])).

tff(c_8592,plain,(
    ! [B_127] : k3_xboole_0('#skF_2',k2_xboole_0(B_127,'#skF_3')) = k2_xboole_0(k3_xboole_0('#skF_2',B_127),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_8232])).

tff(c_8700,plain,(
    ! [B_127] : k3_xboole_0('#skF_2',k2_xboole_0(B_127,'#skF_3')) = k3_xboole_0('#skF_2',B_127) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_8592])).

tff(c_172,plain,(
    ! [A_32,B_33] :
      ( r1_xboole_0(A_32,B_33)
      | k3_xboole_0(A_32,B_33) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_175,plain,(
    k3_xboole_0(k2_xboole_0('#skF_1','#skF_3'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_172,c_26])).

tff(c_177,plain,(
    k3_xboole_0('#skF_2',k2_xboole_0('#skF_1','#skF_3')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_175])).

tff(c_8704,plain,(
    k3_xboole_0('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8700,c_177])).

tff(c_8705,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_8704])).

tff(c_30,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_324,plain,(
    ! [A_49,B_50,C_51] : k3_xboole_0(k3_xboole_0(A_49,B_50),C_51) = k3_xboole_0(A_49,k3_xboole_0(B_50,C_51)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_375,plain,(
    ! [A_52,C_53] : k3_xboole_0(A_52,k3_xboole_0(A_52,C_53)) = k3_xboole_0(A_52,C_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_324])).

tff(c_410,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,k3_xboole_0(A_3,B_4)) = k3_xboole_0(B_4,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_375])).

tff(c_32,plain,(
    r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(k1_tarski(A_9),B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_308,plain,(
    ! [A_45,C_46,B_47] :
      ( r1_tarski(A_45,C_46)
      | ~ r1_tarski(B_47,C_46)
      | ~ r1_tarski(A_45,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_7053,plain,(
    ! [A_111,B_112,A_113] :
      ( r1_tarski(A_111,B_112)
      | ~ r1_tarski(A_111,k1_tarski(A_113))
      | ~ r2_hidden(A_113,B_112) ) ),
    inference(resolution,[status(thm)],[c_14,c_308])).

tff(c_7064,plain,(
    ! [B_114] :
      ( r1_tarski(k3_xboole_0('#skF_1','#skF_2'),B_114)
      | ~ r2_hidden('#skF_4',B_114) ) ),
    inference(resolution,[status(thm)],[c_32,c_7053])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( k2_xboole_0(A_11,B_12) = B_12
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_7081,plain,(
    ! [B_114] :
      ( k2_xboole_0(k3_xboole_0('#skF_1','#skF_2'),B_114) = B_114
      | ~ r2_hidden('#skF_4',B_114) ) ),
    inference(resolution,[status(thm)],[c_7064,c_16])).

tff(c_8706,plain,(
    ! [B_129] : k3_xboole_0('#skF_2',k2_xboole_0(B_129,'#skF_3')) = k3_xboole_0('#skF_2',B_129) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_8592])).

tff(c_8774,plain,
    ( k3_xboole_0('#skF_2',k3_xboole_0('#skF_1','#skF_2')) = k3_xboole_0('#skF_2','#skF_3')
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7081,c_8706])).

tff(c_8814,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_4,c_410,c_200,c_4,c_8774])).

tff(c_8818,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8705,c_8814])).

%------------------------------------------------------------------------------
