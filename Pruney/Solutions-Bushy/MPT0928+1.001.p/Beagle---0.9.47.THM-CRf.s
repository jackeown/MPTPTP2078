%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0928+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:05 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   33 (  39 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   39 (  61 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_51,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D)
          & r1_tarski(E,F)
          & r1_tarski(G,H) )
       => r1_tarski(k4_zfmisc_1(A,C,E,G),k4_zfmisc_1(B,D,F,H)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_mcart_1)).

tff(f_40,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D)
        & r1_tarski(E,F) )
     => r1_tarski(k3_zfmisc_1(A,C,E),k3_zfmisc_1(B,D,F)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_mcart_1)).

tff(f_26,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_zfmisc_1)).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [C_11,E_13,B_10,F_14,D_12,A_9] :
      ( r1_tarski(k3_zfmisc_1(A_9,C_11,E_13),k3_zfmisc_1(B_10,D_12,F_14))
      | ~ r1_tarski(E_13,F_14)
      | ~ r1_tarski(C_11,D_12)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_10,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] : k2_zfmisc_1(k3_zfmisc_1(A_1,B_2,C_3),D_4) = k4_zfmisc_1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_26,plain,(
    ! [A_19,C_20,B_21,D_22] :
      ( r1_tarski(k2_zfmisc_1(A_19,C_20),k2_zfmisc_1(B_21,D_22))
      | ~ r1_tarski(C_20,D_22)
      | ~ r1_tarski(A_19,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_34,plain,(
    ! [C_29,C_33,B_32,A_34,A_30,D_31] :
      ( r1_tarski(k2_zfmisc_1(A_30,C_29),k4_zfmisc_1(A_34,B_32,C_33,D_31))
      | ~ r1_tarski(C_29,D_31)
      | ~ r1_tarski(A_30,k3_zfmisc_1(A_34,B_32,C_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_26])).

tff(c_42,plain,(
    ! [A_42,C_47,A_48,D_46,C_44,B_45,D_43,B_41] :
      ( r1_tarski(k4_zfmisc_1(A_48,B_45,C_47,D_43),k4_zfmisc_1(A_42,B_41,C_44,D_46))
      | ~ r1_tarski(D_43,D_46)
      | ~ r1_tarski(k3_zfmisc_1(A_48,B_45,C_47),k3_zfmisc_1(A_42,B_41,C_44)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_34])).

tff(c_8,plain,(
    ~ r1_tarski(k4_zfmisc_1('#skF_1','#skF_3','#skF_5','#skF_7'),k4_zfmisc_1('#skF_2','#skF_4','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_45,plain,
    ( ~ r1_tarski('#skF_7','#skF_8')
    | ~ r1_tarski(k3_zfmisc_1('#skF_1','#skF_3','#skF_5'),k3_zfmisc_1('#skF_2','#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_42,c_8])).

tff(c_48,plain,(
    ~ r1_tarski(k3_zfmisc_1('#skF_1','#skF_3','#skF_5'),k3_zfmisc_1('#skF_2','#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_45])).

tff(c_51,plain,
    ( ~ r1_tarski('#skF_5','#skF_6')
    | ~ r1_tarski('#skF_3','#skF_4')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_48])).

tff(c_55,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_12,c_51])).

%------------------------------------------------------------------------------
