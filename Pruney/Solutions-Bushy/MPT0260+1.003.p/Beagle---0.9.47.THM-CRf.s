%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0260+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:00 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   40 (  43 expanded)
%              Number of leaves         :   24 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  45 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_49,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_xboole_0(k2_tarski(A,B),C)
          & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(c_44,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_53,plain,(
    ! [A_20] :
      ( k1_xboole_0 = A_20
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_57,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_53])).

tff(c_58,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_44])).

tff(c_50,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [D_8,B_4] : r2_hidden(D_8,k2_tarski(D_8,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_52,plain,(
    r1_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_118,plain,(
    ! [A_33,B_34] :
      ( k3_xboole_0(A_33,B_34) = k1_xboole_0
      | ~ r1_xboole_0(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_126,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_118])).

tff(c_198,plain,(
    ! [D_47,A_48,B_49] :
      ( r2_hidden(D_47,k3_xboole_0(A_48,B_49))
      | ~ r2_hidden(D_47,B_49)
      | ~ r2_hidden(D_47,A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_223,plain,(
    ! [D_50] :
      ( r2_hidden(D_50,k1_xboole_0)
      | ~ r2_hidden(D_50,'#skF_7')
      | ~ r2_hidden(D_50,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_198])).

tff(c_230,plain,
    ( r2_hidden('#skF_5',k1_xboole_0)
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_8,c_223])).

tff(c_238,plain,(
    r2_hidden('#skF_5',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_230])).

tff(c_48,plain,(
    ! [B_19,A_18] :
      ( ~ v1_xboole_0(B_19)
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_248,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_238,c_48])).

tff(c_256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_248])).

%------------------------------------------------------------------------------
