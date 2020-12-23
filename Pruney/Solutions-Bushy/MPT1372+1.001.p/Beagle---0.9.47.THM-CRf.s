%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1372+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:52 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   30 (  40 expanded)
%              Number of leaves         :   15 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   38 (  68 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v8_struct_0 > v2_pre_topc > v1_finset_1 > v1_compts_1 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v8_struct_0,type,(
    v8_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_compts_1,type,(
    v1_compts_1: $i > $o )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(f_55,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ( v1_finset_1(u1_struct_0(A))
         => v1_compts_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_compts_1)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_46,axiom,(
    ! [A] :
      ( ( ~ v8_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_finset_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_struct_0)).

tff(f_34,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( ( v8_struct_0(A)
          & v2_pre_topc(A) )
       => ( v2_pre_topc(A)
          & v1_compts_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_compts_1)).

tff(c_10,plain,(
    ~ v1_compts_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [A_2] :
      ( l1_struct_0(A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12,plain,(
    v1_finset_1(u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    ! [A_5] :
      ( ~ v1_finset_1(u1_struct_0(A_5))
      | ~ l1_struct_0(A_5)
      | v8_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_22,plain,
    ( ~ l1_struct_0('#skF_1')
    | v8_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_18])).

tff(c_23,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_26,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_23])).

tff(c_30,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_26])).

tff(c_31,plain,(
    v8_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_33,plain,(
    ! [A_6] :
      ( v1_compts_1(A_6)
      | ~ v2_pre_topc(A_6)
      | ~ v8_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_36,plain,
    ( v1_compts_1('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_31,c_33])).

tff(c_39,plain,(
    v1_compts_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16,c_36])).

tff(c_41,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_39])).

%------------------------------------------------------------------------------
