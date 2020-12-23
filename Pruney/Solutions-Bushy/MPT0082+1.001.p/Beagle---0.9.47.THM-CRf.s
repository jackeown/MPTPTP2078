%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0082+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:41 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   25 (  30 expanded)
%              Number of leaves         :   14 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  49 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_51,axiom,(
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

tff(f_33,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_28,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_68,plain,(
    ! [D_26,A_27,B_28] :
      ( r2_hidden(D_26,k3_xboole_0(A_27,B_28))
      | ~ r2_hidden(D_26,B_28)
      | ~ r2_hidden(D_26,A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    r1_xboole_0(k3_xboole_0('#skF_4','#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_53,plain,(
    ! [A_22,B_23,C_24] :
      ( ~ r1_xboole_0(A_22,B_23)
      | ~ r2_hidden(C_24,B_23)
      | ~ r2_hidden(C_24,A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_56,plain,(
    ! [C_24] :
      ( ~ r2_hidden(C_24,'#skF_5')
      | ~ r2_hidden(C_24,k3_xboole_0('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_26,c_53])).

tff(c_82,plain,(
    ! [D_29] :
      ( ~ r2_hidden(D_29,'#skF_5')
      | ~ r2_hidden(D_29,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_56])).

tff(c_102,plain,(
    ! [A_31] :
      ( ~ r2_hidden('#skF_3'(A_31,'#skF_5'),'#skF_4')
      | r1_xboole_0(A_31,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_82])).

tff(c_106,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_102])).

tff(c_110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_28,c_106])).

%------------------------------------------------------------------------------
