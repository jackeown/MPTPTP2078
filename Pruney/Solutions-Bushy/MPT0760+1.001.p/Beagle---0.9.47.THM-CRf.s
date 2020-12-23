%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0760+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:49 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :   36 (  38 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   46 (  52 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k3_relat_1(B))
          | k1_wellord1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_wellord1)).

tff(f_38,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

tff(f_39,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(c_30,plain,(
    k1_wellord1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_34,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_22,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_35,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_537,plain,(
    ! [A_122,B_123,C_124] :
      ( r2_hidden(k4_tarski('#skF_1'(A_122,B_123,C_124),B_123),A_122)
      | r2_hidden('#skF_2'(A_122,B_123,C_124),C_124)
      | k1_wellord1(A_122,B_123) = C_124
      | ~ v1_relat_1(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    ! [B_14,C_15,A_13] :
      ( r2_hidden(B_14,k3_relat_1(C_15))
      | ~ r2_hidden(k4_tarski(A_13,B_14),C_15)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_667,plain,(
    ! [B_143,A_144,C_145] :
      ( r2_hidden(B_143,k3_relat_1(A_144))
      | r2_hidden('#skF_2'(A_144,B_143,C_145),C_145)
      | k1_wellord1(A_144,B_143) = C_145
      | ~ v1_relat_1(A_144) ) ),
    inference(resolution,[status(thm)],[c_537,c_24])).

tff(c_28,plain,(
    ! [B_17,A_16] :
      ( ~ v1_xboole_0(B_17)
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_700,plain,(
    ! [C_146,B_147,A_148] :
      ( ~ v1_xboole_0(C_146)
      | r2_hidden(B_147,k3_relat_1(A_148))
      | k1_wellord1(A_148,B_147) = C_146
      | ~ v1_relat_1(A_148) ) ),
    inference(resolution,[status(thm)],[c_667,c_28])).

tff(c_704,plain,(
    ! [B_149,A_150] :
      ( r2_hidden(B_149,k3_relat_1(A_150))
      | k1_wellord1(A_150,B_149) = k1_xboole_0
      | ~ v1_relat_1(A_150) ) ),
    inference(resolution,[status(thm)],[c_35,c_700])).

tff(c_32,plain,(
    ~ r2_hidden('#skF_3',k3_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_733,plain,
    ( k1_wellord1('#skF_4','#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_704,c_32])).

tff(c_743,plain,(
    k1_wellord1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_733])).

tff(c_745,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_743])).

%------------------------------------------------------------------------------
