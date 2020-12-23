%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0232+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:57 EST 2020

% Result     : Theorem 1.22s
% Output     : CNFRefutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   25 (  35 expanded)
%              Number of leaves         :   13 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   20 (  37 expanded)
%              Number of equality atoms :   13 (  21 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_32,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => k2_tarski(A,B) = k1_tarski(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_zfmisc_1)).

tff(f_30,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
     => A = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_26,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(c_6,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_53,plain,(
    ! [C_10,A_11,B_12] :
      ( C_10 = A_11
      | ~ r1_tarski(k2_tarski(A_11,B_12),k1_tarski(C_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_66,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_10,c_53])).

tff(c_67,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_79,plain,(
    ! [C_15,B_16,A_17] :
      ( C_15 = B_16
      | ~ r1_tarski(k2_tarski(A_17,B_16),k1_tarski(C_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_53])).

tff(c_92,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_67,c_79])).

tff(c_8,plain,(
    k2_tarski('#skF_1','#skF_2') != k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_68,plain,(
    k2_tarski('#skF_1','#skF_2') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_8])).

tff(c_94,plain,(
    k2_tarski('#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_68])).

tff(c_98,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_94])).

%------------------------------------------------------------------------------
