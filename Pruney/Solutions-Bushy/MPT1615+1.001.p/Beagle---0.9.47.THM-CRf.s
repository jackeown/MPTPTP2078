%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1615+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:07 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   32 (  44 expanded)
%              Number of leaves         :   17 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   39 (  73 expanded)
%              Number of equality atoms :    4 (  12 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_pre_topc > k3_yellow_0 > k2_yellow_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_52,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k3_yellow_0(k2_yellow_1(u1_pre_topc(A))) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow_1)).

tff(f_37,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k1_xboole_0,A)
       => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(c_12,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_2] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(A_2))
      | ~ l1_pre_topc(A_2)
      | ~ v2_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [A_9] :
      ( k3_yellow_0(k2_yellow_1(A_9)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    k3_yellow_0(k2_yellow_1(u1_pre_topc('#skF_1'))) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_33,plain,
    ( ~ r2_hidden(k1_xboole_0,u1_pre_topc('#skF_1'))
    | v1_xboole_0(u1_pre_topc('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_8])).

tff(c_35,plain,(
    ~ r2_hidden(k1_xboole_0,u1_pre_topc('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_33])).

tff(c_38,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_35])).

tff(c_42,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_38])).

tff(c_43,plain,(
    v1_xboole_0(u1_pre_topc('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_33])).

tff(c_16,plain,(
    ! [A_7] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(A_7))
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( ~ v1_xboole_0(B_4)
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_20,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(u1_pre_topc(A_7))
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7) ) ),
    inference(resolution,[status(thm)],[c_16,c_6])).

tff(c_47,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_43,c_20])).

tff(c_51,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_47])).

%------------------------------------------------------------------------------
