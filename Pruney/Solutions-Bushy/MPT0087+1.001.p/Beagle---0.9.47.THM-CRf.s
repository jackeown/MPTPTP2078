%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0087+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:42 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   26 (  29 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   31 (  45 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_56,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_xboole_1)).

tff(c_26,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),A_9)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_40,plain,(
    ! [A_19,B_20] :
      ( r2_hidden('#skF_3'(A_19,B_20),B_20)
      | r1_xboole_0(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_201,plain,(
    ! [A_54,A_55,B_56] :
      ( r2_hidden('#skF_3'(A_54,k4_xboole_0(A_55,B_56)),A_55)
      | r1_xboole_0(A_54,k4_xboole_0(A_55,B_56)) ) ),
    inference(resolution,[status(thm)],[c_40,c_6])).

tff(c_30,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_63,plain,(
    ! [A_26,B_27,C_28] :
      ( ~ r1_xboole_0(A_26,B_27)
      | ~ r2_hidden(C_28,B_27)
      | ~ r2_hidden(C_28,A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_69,plain,(
    ! [C_28] :
      ( ~ r2_hidden(C_28,'#skF_5')
      | ~ r2_hidden(C_28,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_63])).

tff(c_302,plain,(
    ! [A_70,B_71] :
      ( ~ r2_hidden('#skF_3'(A_70,k4_xboole_0('#skF_5',B_71)),'#skF_4')
      | r1_xboole_0(A_70,k4_xboole_0('#skF_5',B_71)) ) ),
    inference(resolution,[status(thm)],[c_201,c_69])).

tff(c_307,plain,(
    ! [B_71] : r1_xboole_0('#skF_4',k4_xboole_0('#skF_5',B_71)) ),
    inference(resolution,[status(thm)],[c_26,c_302])).

tff(c_28,plain,(
    ~ r1_xboole_0('#skF_4',k4_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_310,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_28])).

%------------------------------------------------------------------------------
