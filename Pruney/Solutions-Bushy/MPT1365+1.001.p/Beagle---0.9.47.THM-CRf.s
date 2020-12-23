%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1365+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:51 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 103 expanded)
%              Number of leaves         :   25 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :  119 ( 321 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v8_pre_topc,type,(
    v8_pre_topc: $i > $o )).

tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v8_pre_topc(A)
                    & v2_compts_1(B,A)
                    & v2_compts_1(C,A) )
                 => v2_compts_1(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_compts_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v4_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v4_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k3_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tops_1)).

tff(f_30,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v2_compts_1(B,A)
                  & r1_tarski(C,B)
                  & v4_pre_topc(C,A) )
               => v2_compts_1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_compts_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_82,plain,(
    ! [A_37,B_38,C_39] :
      ( k9_subset_1(A_37,B_38,C_39) = k3_xboole_0(B_38,C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_91,plain,(
    ! [B_38] : k9_subset_1(u1_struct_0('#skF_1'),B_38,'#skF_3') = k3_xboole_0(B_38,'#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_82])).

tff(c_16,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_142,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_16])).

tff(c_143,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_142])).

tff(c_30,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_22,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_20,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_106,plain,(
    ! [B_41,A_42] :
      ( v4_pre_topc(B_41,A_42)
      | ~ v2_compts_1(B_41,A_42)
      | ~ v8_pre_topc(A_42)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42)
      | ~ v2_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_113,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_106])).

tff(c_120,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_22,c_20,c_113])).

tff(c_18,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_116,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_106])).

tff(c_123,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_22,c_18,c_116])).

tff(c_217,plain,(
    ! [B_48,C_49,A_50] :
      ( v4_pre_topc(k3_xboole_0(B_48,C_49),A_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ v4_pre_topc(C_49,A_50)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ v4_pre_topc(B_48,A_50)
      | ~ l1_pre_topc(A_50)
      | ~ v2_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_232,plain,(
    ! [B_48] :
      ( v4_pre_topc(k3_xboole_0(B_48,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc('#skF_3','#skF_1')
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v4_pre_topc(B_48,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_217])).

tff(c_271,plain,(
    ! [B_53] :
      ( v4_pre_topc(k3_xboole_0(B_53,'#skF_3'),'#skF_1')
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v4_pre_topc(B_53,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_123,c_232])).

tff(c_290,plain,
    ( v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_271])).

tff(c_306,plain,(
    v4_pre_topc(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_2,c_290])).

tff(c_144,plain,(
    ! [B_44] : k9_subset_1(u1_struct_0('#skF_1'),B_44,'#skF_3') = k3_xboole_0(B_44,'#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_82])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] :
      ( m1_subset_1(k9_subset_1(A_3,B_4,C_5),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(C_5,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_150,plain,(
    ! [B_44] :
      ( m1_subset_1(k3_xboole_0(B_44,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_4])).

tff(c_158,plain,(
    ! [B_45] : m1_subset_1(k3_xboole_0(B_45,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_150])).

tff(c_167,plain,(
    ! [A_1] : m1_subset_1(k3_xboole_0('#skF_3',A_1),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_158])).

tff(c_12,plain,(
    ! [A_15,B_16] : r1_tarski(k3_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_337,plain,(
    ! [C_57,A_58,B_59] :
      ( v2_compts_1(C_57,A_58)
      | ~ v4_pre_topc(C_57,A_58)
      | ~ r1_tarski(C_57,B_59)
      | ~ v2_compts_1(B_59,A_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_923,plain,(
    ! [A_93,B_94,A_95] :
      ( v2_compts_1(k3_xboole_0(A_93,B_94),A_95)
      | ~ v4_pre_topc(k3_xboole_0(A_93,B_94),A_95)
      | ~ v2_compts_1(A_93,A_95)
      | ~ m1_subset_1(k3_xboole_0(A_93,B_94),k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ m1_subset_1(A_93,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95) ) ),
    inference(resolution,[status(thm)],[c_12,c_337])).

tff(c_950,plain,(
    ! [A_1] :
      ( v2_compts_1(k3_xboole_0('#skF_3',A_1),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0('#skF_3',A_1),'#skF_1')
      | ~ v2_compts_1('#skF_3','#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_167,c_923])).

tff(c_1054,plain,(
    ! [A_98] :
      ( v2_compts_1(k3_xboole_0('#skF_3',A_98),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0('#skF_3',A_98),'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_24,c_18,c_950])).

tff(c_1074,plain,(
    v2_compts_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_306,c_1054])).

tff(c_1101,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_1074])).

%------------------------------------------------------------------------------
