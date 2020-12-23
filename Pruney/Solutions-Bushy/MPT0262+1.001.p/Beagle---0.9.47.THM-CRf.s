%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0262+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:00 EST 2020

% Result     : Theorem 39.18s
% Output     : CNFRefutation 39.18s
% Verified   : 
% Statistics : Number of formulae       :   36 (  61 expanded)
%              Number of leaves         :   19 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   44 ( 112 expanded)
%              Number of equality atoms :   12 (  24 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,B)
          & ~ r2_hidden(C,B)
          & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_42,plain,(
    ~ r1_xboole_0(k2_tarski('#skF_6','#skF_8'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_44,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_46,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_63,plain,(
    ! [A_34,B_35] :
      ( r2_hidden('#skF_5'(A_34,B_35),k3_xboole_0(A_34,B_35))
      | r1_xboole_0(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_24,plain,(
    ! [D_12,A_7,B_8] :
      ( r2_hidden(D_12,A_7)
      | ~ r2_hidden(D_12,k3_xboole_0(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_76,plain,(
    ! [A_36,B_37] :
      ( r2_hidden('#skF_5'(A_36,B_37),A_36)
      | r1_xboole_0(A_36,B_37) ) ),
    inference(resolution,[status(thm)],[c_63,c_24])).

tff(c_2,plain,(
    ! [D_6,B_2,A_1] :
      ( D_6 = B_2
      | D_6 = A_1
      | ~ r2_hidden(D_6,k2_tarski(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_129632,plain,(
    ! [A_26934,B_26935,B_26936] :
      ( '#skF_5'(k2_tarski(A_26934,B_26935),B_26936) = B_26935
      | '#skF_5'(k2_tarski(A_26934,B_26935),B_26936) = A_26934
      | r1_xboole_0(k2_tarski(A_26934,B_26935),B_26936) ) ),
    inference(resolution,[status(thm)],[c_76,c_2])).

tff(c_130268,plain,
    ( '#skF_5'(k2_tarski('#skF_6','#skF_8'),'#skF_7') = '#skF_8'
    | '#skF_5'(k2_tarski('#skF_6','#skF_8'),'#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_129632,c_42])).

tff(c_130269,plain,(
    '#skF_5'(k2_tarski('#skF_6','#skF_8'),'#skF_7') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_130268])).

tff(c_22,plain,(
    ! [D_12,B_8,A_7] :
      ( r2_hidden(D_12,B_8)
      | ~ r2_hidden(D_12,k3_xboole_0(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_74,plain,(
    ! [A_34,B_35] :
      ( r2_hidden('#skF_5'(A_34,B_35),B_35)
      | r1_xboole_0(A_34,B_35) ) ),
    inference(resolution,[status(thm)],[c_63,c_22])).

tff(c_130273,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | r1_xboole_0(k2_tarski('#skF_6','#skF_8'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_130269,c_74])).

tff(c_130355,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_46,c_130273])).

tff(c_130356,plain,(
    '#skF_5'(k2_tarski('#skF_6','#skF_8'),'#skF_7') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_130268])).

tff(c_130361,plain,
    ( r2_hidden('#skF_8','#skF_7')
    | r1_xboole_0(k2_tarski('#skF_6','#skF_8'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_130356,c_74])).

tff(c_130443,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_44,c_130361])).

%------------------------------------------------------------------------------
