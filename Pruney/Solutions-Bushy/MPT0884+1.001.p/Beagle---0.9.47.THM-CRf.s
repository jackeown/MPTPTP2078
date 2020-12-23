%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0884+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:01 EST 2020

% Result     : Theorem 44.38s
% Output     : CNFRefutation 44.38s
% Verified   : 
% Statistics : Number of formulae       :   35 (  41 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   21 (  27 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_28,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_26,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_32,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k2_tarski(A,B),k2_tarski(C,D)) = k2_enumset1(k4_tarski(A,C),k4_tarski(A,D),k4_tarski(B,C),k4_tarski(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_mcart_1)).

tff(f_30,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).

tff(f_39,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k3_zfmisc_1(k2_tarski(A,B),k1_tarski(C),k2_tarski(D,E)) = k2_enumset1(k3_mcart_1(A,C,D),k3_mcart_1(B,C,D),k3_mcart_1(A,C,E),k3_mcart_1(B,C,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_mcart_1)).

tff(c_105,plain,(
    ! [A_36,B_37,C_38] : k2_zfmisc_1(k2_tarski(A_36,B_37),k1_tarski(C_38)) = k2_tarski(k4_tarski(A_36,C_38),k4_tarski(B_37,C_38)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6] : k2_zfmisc_1(k2_zfmisc_1(A_4,B_5),C_6) = k3_zfmisc_1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_120,plain,(
    ! [A_36,C_38,B_37,C_6] : k2_zfmisc_1(k2_tarski(k4_tarski(A_36,C_38),k4_tarski(B_37,C_38)),C_6) = k3_zfmisc_1(k2_tarski(A_36,B_37),k1_tarski(C_38),C_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_4])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k4_tarski(k4_tarski(A_1,B_2),C_3) = k3_mcart_1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_353,plain,(
    ! [A_50,C_51,D_52,B_53] : k2_enumset1(k4_tarski(A_50,C_51),k4_tarski(A_50,D_52),k4_tarski(B_53,C_51),k4_tarski(B_53,D_52)) = k2_zfmisc_1(k2_tarski(A_50,B_53),k2_tarski(C_51,D_52)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_380,plain,(
    ! [A_50,D_52,B_2,C_3,A_1] : k2_enumset1(k4_tarski(A_50,C_3),k4_tarski(A_50,D_52),k3_mcart_1(A_1,B_2,C_3),k4_tarski(k4_tarski(A_1,B_2),D_52)) = k2_zfmisc_1(k2_tarski(A_50,k4_tarski(A_1,B_2)),k2_tarski(C_3,D_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_353])).

tff(c_5650,plain,(
    ! [B_183,A_182,C_184,A_186,D_185] : k2_enumset1(k4_tarski(A_182,C_184),k4_tarski(A_182,D_185),k3_mcart_1(A_186,B_183,C_184),k3_mcart_1(A_186,B_183,D_185)) = k2_zfmisc_1(k2_tarski(A_182,k4_tarski(A_186,B_183)),k2_tarski(C_184,D_185)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_380])).

tff(c_5677,plain,(
    ! [B_183,B_2,C_3,A_1,A_186,D_185] : k2_enumset1(k3_mcart_1(A_1,B_2,C_3),k4_tarski(k4_tarski(A_1,B_2),D_185),k3_mcart_1(A_186,B_183,C_3),k3_mcart_1(A_186,B_183,D_185)) = k2_zfmisc_1(k2_tarski(k4_tarski(A_1,B_2),k4_tarski(A_186,B_183)),k2_tarski(C_3,D_185)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5650])).

tff(c_5685,plain,(
    ! [B_183,B_2,C_3,A_1,A_186,D_185] : k2_enumset1(k3_mcart_1(A_1,B_2,C_3),k3_mcart_1(A_1,B_2,D_185),k3_mcart_1(A_186,B_183,C_3),k3_mcart_1(A_186,B_183,D_185)) = k2_zfmisc_1(k2_tarski(k4_tarski(A_1,B_2),k4_tarski(A_186,B_183)),k2_tarski(C_3,D_185)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_5677])).

tff(c_6,plain,(
    ! [A_7,C_9,B_8,D_10] : k2_enumset1(A_7,C_9,B_8,D_10) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_14,plain,(
    k2_enumset1(k3_mcart_1('#skF_1','#skF_3','#skF_4'),k3_mcart_1('#skF_2','#skF_3','#skF_4'),k3_mcart_1('#skF_1','#skF_3','#skF_5'),k3_mcart_1('#skF_2','#skF_3','#skF_5')) != k3_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_15,plain,(
    k2_enumset1(k3_mcart_1('#skF_1','#skF_3','#skF_4'),k3_mcart_1('#skF_1','#skF_3','#skF_5'),k3_mcart_1('#skF_2','#skF_3','#skF_4'),k3_mcart_1('#skF_2','#skF_3','#skF_5')) != k3_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14])).

tff(c_71289,plain,(
    k2_zfmisc_1(k2_tarski(k4_tarski('#skF_1','#skF_3'),k4_tarski('#skF_2','#skF_3')),k2_tarski('#skF_4','#skF_5')) != k3_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5685,c_15])).

tff(c_71292,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_71289])).

%------------------------------------------------------------------------------
