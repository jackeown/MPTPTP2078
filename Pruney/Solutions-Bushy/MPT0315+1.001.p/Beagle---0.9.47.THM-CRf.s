%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0315+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:05 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   34 (  45 expanded)
%              Number of leaves         :   18 (  25 expanded)
%              Depth                    :    5
%              Number of atoms          :   36 (  68 expanded)
%              Number of equality atoms :    1 (   2 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_xboole_0(A,B)
          | r1_xboole_0(C,D) )
       => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] :
      ~ ( r2_hidden(A,k3_xboole_0(k2_zfmisc_1(B,C),k2_zfmisc_1(D,E)))
        & ! [F,G] :
            ~ ( A = k4_tarski(F,G)
              & r2_hidden(F,k3_xboole_0(B,D))
              & r2_hidden(G,k3_xboole_0(C,E)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_zfmisc_1)).

tff(c_14,plain,
    ( r1_xboole_0('#skF_6','#skF_7')
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_15,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_3'(A_8,B_9),k3_xboole_0(A_8,B_9))
      | r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_27,plain,(
    ! [D_24,B_25,C_26,A_27,E_23] :
      ( r2_hidden('#skF_1'(E_23,D_24,B_25,C_26,A_27),k3_xboole_0(B_25,D_24))
      | ~ r2_hidden(A_27,k3_xboole_0(k2_zfmisc_1(B_25,C_26),k2_zfmisc_1(D_24,E_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_37,plain,(
    ! [E_33,D_34,B_35,C_36] :
      ( r2_hidden('#skF_1'(E_33,D_34,B_35,C_36,'#skF_3'(k2_zfmisc_1(B_35,C_36),k2_zfmisc_1(D_34,E_33))),k3_xboole_0(B_35,D_34))
      | r1_xboole_0(k2_zfmisc_1(B_35,C_36),k2_zfmisc_1(D_34,E_33)) ) ),
    inference(resolution,[status(thm)],[c_8,c_27])).

tff(c_10,plain,(
    ! [A_8,B_9,C_12] :
      ( ~ r1_xboole_0(A_8,B_9)
      | ~ r2_hidden(C_12,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_54,plain,(
    ! [B_37,D_38,C_39,E_40] :
      ( ~ r1_xboole_0(B_37,D_38)
      | r1_xboole_0(k2_zfmisc_1(B_37,C_39),k2_zfmisc_1(D_38,E_40)) ) ),
    inference(resolution,[status(thm)],[c_37,c_10])).

tff(c_12,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_4','#skF_6'),k2_zfmisc_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_57,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_12])).

tff(c_61,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15,c_57])).

tff(c_62,plain,(
    r1_xboole_0('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_70,plain,(
    ! [A_50,E_46,C_49,D_47,B_48] :
      ( r2_hidden('#skF_2'(E_46,D_47,B_48,C_49,A_50),k3_xboole_0(C_49,E_46))
      | ~ r2_hidden(A_50,k3_xboole_0(k2_zfmisc_1(B_48,C_49),k2_zfmisc_1(D_47,E_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_107,plain,(
    ! [E_69,D_70,B_71,C_72] :
      ( r2_hidden('#skF_2'(E_69,D_70,B_71,C_72,'#skF_3'(k2_zfmisc_1(B_71,C_72),k2_zfmisc_1(D_70,E_69))),k3_xboole_0(C_72,E_69))
      | r1_xboole_0(k2_zfmisc_1(B_71,C_72),k2_zfmisc_1(D_70,E_69)) ) ),
    inference(resolution,[status(thm)],[c_8,c_70])).

tff(c_124,plain,(
    ! [C_73,E_74,B_75,D_76] :
      ( ~ r1_xboole_0(C_73,E_74)
      | r1_xboole_0(k2_zfmisc_1(B_75,C_73),k2_zfmisc_1(D_76,E_74)) ) ),
    inference(resolution,[status(thm)],[c_107,c_10])).

tff(c_127,plain,(
    ~ r1_xboole_0('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_124,c_12])).

tff(c_131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_127])).

%------------------------------------------------------------------------------
