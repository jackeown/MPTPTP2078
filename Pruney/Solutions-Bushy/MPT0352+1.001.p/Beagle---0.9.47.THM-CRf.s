%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0352+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:09 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 102 expanded)
%              Number of leaves         :   21 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :   57 ( 158 expanded)
%              Number of equality atoms :   18 (  38 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_xboole_0 > k6_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,C)
            <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_28,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_37,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_30,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

tff(c_28,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_56,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_22,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_129,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_22])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_139,plain,(
    ! [A_26,B_27] :
      ( k3_subset_1(A_26,k3_subset_1(A_26,B_27)) = B_27
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_157,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_18,c_139])).

tff(c_66,plain,(
    ! [A_21,B_22] :
      ( k4_xboole_0(A_21,B_22) = k3_subset_1(A_21,B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_82,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_66])).

tff(c_10,plain,(
    ! [A_7,B_8] : k6_subset_1(A_7,B_8) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_3,B_4] : m1_subset_1(k6_subset_1(A_3,B_4),k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_29,plain,(
    ! [A_3,B_4] : m1_subset_1(k4_xboole_0(A_3,B_4),k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_4])).

tff(c_188,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k4_xboole_0(A_30,B_31)) = k3_subset_1(A_30,k4_xboole_0(A_30,B_31)) ),
    inference(resolution,[status(thm)],[c_29,c_66])).

tff(c_219,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_subset_1('#skF_1',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_188])).

tff(c_236,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_82,c_219])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_158,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_20,c_139])).

tff(c_83,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_66])).

tff(c_222,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k4_xboole_0('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_188])).

tff(c_237,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_83,c_222])).

tff(c_12,plain,(
    ! [C_11,B_10,A_9] :
      ( r1_tarski(k4_xboole_0(C_11,B_10),k4_xboole_0(C_11,A_9))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_562,plain,(
    ! [A_45] :
      ( r1_tarski('#skF_2',k4_xboole_0('#skF_1',A_45))
      | ~ r1_tarski(A_45,k3_subset_1('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_12])).

tff(c_566,plain,(
    r1_tarski('#skF_2',k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_56,c_562])).

tff(c_570,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_566])).

tff(c_572,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_570])).

tff(c_574,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_573,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_586,plain,(
    ! [A_48,B_49] :
      ( k4_xboole_0(A_48,B_49) = k3_subset_1(A_48,B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_602,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_586])).

tff(c_603,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_586])).

tff(c_654,plain,(
    ! [C_52,B_53,A_54] :
      ( r1_tarski(k4_xboole_0(C_52,B_53),k4_xboole_0(C_52,A_54))
      | ~ r1_tarski(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_853,plain,(
    ! [B_62] :
      ( r1_tarski(k4_xboole_0('#skF_1',B_62),k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_tarski('#skF_2',B_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_603,c_654])).

tff(c_869,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_602,c_853])).

tff(c_871,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_869])).

tff(c_873,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_574,c_871])).

%------------------------------------------------------------------------------
