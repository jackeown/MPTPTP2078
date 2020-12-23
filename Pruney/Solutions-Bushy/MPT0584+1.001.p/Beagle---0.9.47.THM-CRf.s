%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0584+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:32 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   33 (  46 expanded)
%              Number of leaves         :   15 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   33 (  69 expanded)
%              Number of equality atoms :   19 (  36 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_47,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C,D] :
                ( ( r1_tarski(C,D)
                  & k7_relat_1(A,D) = k7_relat_1(B,D) )
               => k7_relat_1(A,C) = k7_relat_1(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t188_relat_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_26,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_30,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_8,plain,(
    k7_relat_1('#skF_2','#skF_3') != k7_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_54,plain,(
    ! [A_17,B_18] :
      ( k3_xboole_0(A_17,B_18) = A_17
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_58,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_12,c_54])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_62,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_2])).

tff(c_16,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    k7_relat_1('#skF_2','#skF_4') = k7_relat_1('#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_82,plain,(
    ! [C_19,A_20,B_21] :
      ( k7_relat_1(k7_relat_1(C_19,A_20),B_21) = k7_relat_1(C_19,k3_xboole_0(A_20,B_21))
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_97,plain,(
    ! [B_21] :
      ( k7_relat_1(k7_relat_1('#skF_1','#skF_4'),B_21) = k7_relat_1('#skF_2',k3_xboole_0('#skF_4',B_21))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_82])).

tff(c_102,plain,(
    ! [B_22] : k7_relat_1(k7_relat_1('#skF_1','#skF_4'),B_22) = k7_relat_1('#skF_2',k3_xboole_0('#skF_4',B_22)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_97])).

tff(c_4,plain,(
    ! [C_5,A_3,B_4] :
      ( k7_relat_1(k7_relat_1(C_5,A_3),B_4) = k7_relat_1(C_5,k3_xboole_0(A_3,B_4))
      | ~ v1_relat_1(C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_111,plain,(
    ! [B_22] :
      ( k7_relat_1('#skF_2',k3_xboole_0('#skF_4',B_22)) = k7_relat_1('#skF_1',k3_xboole_0('#skF_4',B_22))
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_4])).

tff(c_127,plain,(
    ! [B_23] : k7_relat_1('#skF_2',k3_xboole_0('#skF_4',B_23)) = k7_relat_1('#skF_1',k3_xboole_0('#skF_4',B_23)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_111])).

tff(c_139,plain,(
    k7_relat_1('#skF_1',k3_xboole_0('#skF_4','#skF_3')) = k7_relat_1('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_127])).

tff(c_152,plain,(
    k7_relat_1('#skF_2','#skF_3') = k7_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_139])).

tff(c_154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_152])).

%------------------------------------------------------------------------------
