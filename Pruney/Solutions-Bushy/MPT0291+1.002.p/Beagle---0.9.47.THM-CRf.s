%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0291+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:03 EST 2020

% Result     : Theorem 11.86s
% Output     : CNFRefutation 11.86s
% Verified   : 
% Statistics : Number of formulae       :   38 (  47 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 (  80 expanded)
%              Number of equality atoms :    2 (   5 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_xboole_0 > #nlpp > k3_tarski > #skF_6 > #skF_4 > #skF_3 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_7 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( ! [C] :
            ( r2_hidden(C,A)
           => r1_xboole_0(C,B) )
       => r1_xboole_0(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(c_44,plain,(
    ~ r1_xboole_0(k3_tarski('#skF_8'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_110,plain,(
    ! [A_53,B_54] :
      ( r2_hidden('#skF_7'(A_53,B_54),k3_xboole_0(A_53,B_54))
      | r1_xboole_0(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_24,plain,(
    ! [D_27,B_23,A_22] :
      ( r2_hidden(D_27,B_23)
      | ~ r2_hidden(D_27,k3_xboole_0(A_22,B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_133,plain,(
    ! [A_53,B_54] :
      ( r2_hidden('#skF_7'(A_53,B_54),B_54)
      | r1_xboole_0(A_53,B_54) ) ),
    inference(resolution,[status(thm)],[c_110,c_24])).

tff(c_26,plain,(
    ! [D_27,A_22,B_23] :
      ( r2_hidden(D_27,A_22)
      | ~ r2_hidden(D_27,k3_xboole_0(A_22,B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_135,plain,(
    ! [A_53,B_54] :
      ( r2_hidden('#skF_7'(A_53,B_54),A_53)
      | r1_xboole_0(A_53,B_54) ) ),
    inference(resolution,[status(thm)],[c_110,c_26])).

tff(c_8,plain,(
    ! [C_18,A_3] :
      ( r2_hidden(C_18,'#skF_4'(A_3,k3_tarski(A_3),C_18))
      | ~ r2_hidden(C_18,k3_tarski(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_195,plain,(
    ! [A_61,C_62] :
      ( r2_hidden('#skF_4'(A_61,k3_tarski(A_61),C_62),A_61)
      | ~ r2_hidden(C_62,k3_tarski(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_46,plain,(
    ! [C_34] :
      ( r1_xboole_0(C_34,'#skF_9')
      | ~ r2_hidden(C_34,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_223,plain,(
    ! [C_62] :
      ( r1_xboole_0('#skF_4'('#skF_8',k3_tarski('#skF_8'),C_62),'#skF_9')
      | ~ r2_hidden(C_62,k3_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_195,c_46])).

tff(c_332,plain,(
    ! [D_88,A_89,B_90] :
      ( r2_hidden(D_88,k3_xboole_0(A_89,B_90))
      | ~ r2_hidden(D_88,B_90)
      | ~ r2_hidden(D_88,A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_42,plain,(
    ! [A_28,B_29,C_32] :
      ( ~ r1_xboole_0(A_28,B_29)
      | ~ r2_hidden(C_32,k3_xboole_0(A_28,B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_358,plain,(
    ! [A_91,B_92,D_93] :
      ( ~ r1_xboole_0(A_91,B_92)
      | ~ r2_hidden(D_93,B_92)
      | ~ r2_hidden(D_93,A_91) ) ),
    inference(resolution,[status(thm)],[c_332,c_42])).

tff(c_18554,plain,(
    ! [D_685,C_686] :
      ( ~ r2_hidden(D_685,'#skF_9')
      | ~ r2_hidden(D_685,'#skF_4'('#skF_8',k3_tarski('#skF_8'),C_686))
      | ~ r2_hidden(C_686,k3_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_223,c_358])).

tff(c_18780,plain,(
    ! [C_687] :
      ( ~ r2_hidden(C_687,'#skF_9')
      | ~ r2_hidden(C_687,k3_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_8,c_18554])).

tff(c_19001,plain,(
    ! [B_688] :
      ( ~ r2_hidden('#skF_7'(k3_tarski('#skF_8'),B_688),'#skF_9')
      | r1_xboole_0(k3_tarski('#skF_8'),B_688) ) ),
    inference(resolution,[status(thm)],[c_135,c_18780])).

tff(c_19021,plain,(
    r1_xboole_0(k3_tarski('#skF_8'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_133,c_19001])).

tff(c_19029,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_44,c_19021])).

%------------------------------------------------------------------------------
