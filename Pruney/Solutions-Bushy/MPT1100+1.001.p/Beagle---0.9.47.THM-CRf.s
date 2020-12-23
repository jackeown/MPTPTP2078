%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1100+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:24 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   42 (  50 expanded)
%              Number of leaves         :   25 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :   57 (  71 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_67,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => r2_hidden(k1_xboole_0,u1_pre_topc(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_pre_topc)).

tff(f_55,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_56,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_pre_topc(A)
      <=> ( r2_hidden(u1_struct_0(A),u1_pre_topc(A))
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( r1_tarski(B,u1_pre_topc(A))
               => r2_hidden(k5_setfam_1(u1_struct_0(A),B),u1_pre_topc(A)) ) )
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r2_hidden(B,u1_pre_topc(A))
                      & r2_hidden(C,u1_pre_topc(A)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(A),B,C),u1_pre_topc(A)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

tff(c_50,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_52,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_40,plain,(
    ! [A_17] : r1_tarski(k1_xboole_0,A_17) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_46,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_42,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_65,plain,(
    ! [A_26,B_27] :
      ( k5_setfam_1(A_26,B_27) = k3_tarski(B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(k1_zfmisc_1(A_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_76,plain,(
    ! [A_29,A_30] :
      ( k5_setfam_1(A_29,A_30) = k3_tarski(A_30)
      | ~ r1_tarski(A_30,k1_zfmisc_1(A_29)) ) ),
    inference(resolution,[status(thm)],[c_46,c_65])).

tff(c_80,plain,(
    ! [A_29] : k5_setfam_1(A_29,k1_xboole_0) = k3_tarski(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_40,c_76])).

tff(c_82,plain,(
    ! [A_29] : k5_setfam_1(A_29,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_80])).

tff(c_129,plain,(
    ! [A_39,B_40] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(A_39),B_40),u1_pre_topc(A_39))
      | ~ r1_tarski(B_40,u1_pre_topc(A_39))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_39))))
      | ~ v2_pre_topc(A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_133,plain,(
    ! [A_39] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(A_39))
      | ~ r1_tarski(k1_xboole_0,u1_pre_topc(A_39))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_39))))
      | ~ v2_pre_topc(A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_129])).

tff(c_136,plain,(
    ! [A_41] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(A_41))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_41))))
      | ~ v2_pre_topc(A_41)
      | ~ l1_pre_topc(A_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_133])).

tff(c_139,plain,(
    ! [A_41] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(A_41))
      | ~ v2_pre_topc(A_41)
      | ~ l1_pre_topc(A_41)
      | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_41))) ) ),
    inference(resolution,[status(thm)],[c_46,c_136])).

tff(c_143,plain,(
    ! [A_42] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(A_42))
      | ~ v2_pre_topc(A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_139])).

tff(c_48,plain,(
    ~ r2_hidden(k1_xboole_0,u1_pre_topc('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_146,plain,
    ( ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_143,c_48])).

tff(c_150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_146])).

%------------------------------------------------------------------------------
