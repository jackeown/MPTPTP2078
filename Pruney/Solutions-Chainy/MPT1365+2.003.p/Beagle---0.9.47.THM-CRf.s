%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:54 EST 2020

% Result     : Theorem 26.04s
% Output     : CNFRefutation 26.17s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 143 expanded)
%              Number of leaves         :   36 (  68 expanded)
%              Depth                    :   10
%              Number of atoms          :  183 ( 425 expanded)
%              Number of equality atoms :   18 (  26 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v8_pre_topc > v2_pre_topc > v1_pre_topc > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff(v8_pre_topc,type,(
    v8_pre_topc: $i > $o )).

tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_136,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_compts_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_99,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_compts_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v4_pre_topc(B,A)
                  & v4_pre_topc(C,A) )
               => v4_pre_topc(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_117,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_compts_1)).

tff(c_8,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_81,plain,(
    ! [A_53,B_54] : k1_setfam_1(k2_tarski(A_53,B_54)) = k3_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_131,plain,(
    ! [B_61,A_62] : k1_setfam_1(k2_tarski(B_61,A_62)) = k3_xboole_0(A_62,B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_81])).

tff(c_12,plain,(
    ! [A_12,B_13] : k1_setfam_1(k2_tarski(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_137,plain,(
    ! [B_61,A_62] : k3_xboole_0(B_61,A_62) = k3_xboole_0(A_62,B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_12])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_264,plain,(
    ! [A_71,B_72,C_73] :
      ( k9_subset_1(A_71,B_72,C_73) = k3_xboole_0(B_72,C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_273,plain,(
    ! [B_72] : k9_subset_1(u1_struct_0('#skF_1'),B_72,'#skF_3') = k3_xboole_0(B_72,'#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_264])).

tff(c_32,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_352,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_32])).

tff(c_353,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_352])).

tff(c_154,plain,(
    ! [A_63,B_64] : k4_xboole_0(A_63,k4_xboole_0(A_63,B_64)) = k3_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_163,plain,(
    ! [A_63,B_64] : r1_tarski(k3_xboole_0(A_63,B_64),A_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_4])).

tff(c_34,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_38,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1136,plain,(
    ! [B_104,A_105] :
      ( v4_pre_topc(B_104,A_105)
      | ~ v2_compts_1(B_104,A_105)
      | ~ v8_pre_topc(A_105)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105)
      | ~ v2_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1155,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1136])).

tff(c_1163,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_38,c_34,c_1155])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_36,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1152,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1136])).

tff(c_1160,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_38,c_36,c_1152])).

tff(c_272,plain,(
    ! [B_72] : k9_subset_1(u1_struct_0('#skF_1'),B_72,'#skF_2') = k3_xboole_0(B_72,'#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_264])).

tff(c_1690,plain,(
    ! [A_117,B_118,C_119] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(A_117),B_118,C_119),A_117)
      | ~ v4_pre_topc(C_119,A_117)
      | ~ v4_pre_topc(B_118,A_117)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117)
      | ~ v2_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1702,plain,(
    ! [B_72] :
      ( v4_pre_topc(k3_xboole_0(B_72,'#skF_2'),'#skF_1')
      | ~ v4_pre_topc('#skF_2','#skF_1')
      | ~ v4_pre_topc(B_72,'#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_1690])).

tff(c_6479,plain,(
    ! [B_217] :
      ( v4_pre_topc(k3_xboole_0(B_217,'#skF_2'),'#skF_1')
      | ~ v4_pre_topc(B_217,'#skF_1')
      | ~ m1_subset_1(B_217,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_1160,c_1702])).

tff(c_6507,plain,
    ( v4_pre_topc(k3_xboole_0('#skF_3','#skF_2'),'#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_6479])).

tff(c_6525,plain,(
    v4_pre_topc(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1163,c_6507])).

tff(c_314,plain,(
    ! [A_77,B_78] :
      ( u1_struct_0(k1_pre_topc(A_77,B_78)) = B_78
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_324,plain,
    ( u1_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_314])).

tff(c_331,plain,(
    u1_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_324])).

tff(c_528,plain,(
    ! [A_88,B_89] :
      ( m1_pre_topc(k1_pre_topc(A_88,B_89),A_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_539,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_528])).

tff(c_546,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_539])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_711,plain,(
    ! [C_94,A_95,B_96] :
      ( m1_subset_1(C_94,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ m1_subset_1(C_94,k1_zfmisc_1(u1_struct_0(B_96)))
      | ~ m1_pre_topc(B_96,A_95)
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3617,plain,(
    ! [A_166,A_167,B_168] :
      ( m1_subset_1(A_166,k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ m1_pre_topc(B_168,A_167)
      | ~ l1_pre_topc(A_167)
      | ~ r1_tarski(A_166,u1_struct_0(B_168)) ) ),
    inference(resolution,[status(thm)],[c_16,c_711])).

tff(c_3629,plain,(
    ! [A_166] :
      ( m1_subset_1(A_166,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_166,u1_struct_0(k1_pre_topc('#skF_1','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_546,c_3617])).

tff(c_3639,plain,(
    ! [A_166] :
      ( m1_subset_1(A_166,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_166,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_44,c_3629])).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1340,plain,(
    ! [C_109,A_110,B_111] :
      ( v2_compts_1(C_109,A_110)
      | ~ v4_pre_topc(C_109,A_110)
      | ~ r1_tarski(C_109,B_111)
      | ~ v2_compts_1(B_111,A_110)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110)
      | ~ v2_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_4596,plain,(
    ! [A_187,B_188,A_189] :
      ( v2_compts_1(k4_xboole_0(A_187,B_188),A_189)
      | ~ v4_pre_topc(k4_xboole_0(A_187,B_188),A_189)
      | ~ v2_compts_1(A_187,A_189)
      | ~ m1_subset_1(k4_xboole_0(A_187,B_188),k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ m1_subset_1(A_187,k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ l1_pre_topc(A_189)
      | ~ v2_pre_topc(A_189) ) ),
    inference(resolution,[status(thm)],[c_4,c_1340])).

tff(c_4637,plain,(
    ! [A_5,B_6,A_189] :
      ( v2_compts_1(k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)),A_189)
      | ~ v4_pre_topc(k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)),A_189)
      | ~ v2_compts_1(A_5,A_189)
      | ~ m1_subset_1(k3_xboole_0(A_5,B_6),k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ m1_subset_1(A_5,k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ l1_pre_topc(A_189)
      | ~ v2_pre_topc(A_189) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_4596])).

tff(c_10595,plain,(
    ! [A_270,B_271,A_272] :
      ( v2_compts_1(k3_xboole_0(A_270,B_271),A_272)
      | ~ v4_pre_topc(k3_xboole_0(A_270,B_271),A_272)
      | ~ v2_compts_1(A_270,A_272)
      | ~ m1_subset_1(k3_xboole_0(A_270,B_271),k1_zfmisc_1(u1_struct_0(A_272)))
      | ~ m1_subset_1(A_270,k1_zfmisc_1(u1_struct_0(A_272)))
      | ~ l1_pre_topc(A_272)
      | ~ v2_pre_topc(A_272) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_4637])).

tff(c_10665,plain,(
    ! [A_270,B_271] :
      ( v2_compts_1(k3_xboole_0(A_270,B_271),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(A_270,B_271),'#skF_1')
      | ~ v2_compts_1(A_270,'#skF_1')
      | ~ m1_subset_1(A_270,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(k3_xboole_0(A_270,B_271),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3639,c_10595])).

tff(c_82709,plain,(
    ! [A_771,B_772] :
      ( v2_compts_1(k3_xboole_0(A_771,B_772),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(A_771,B_772),'#skF_1')
      | ~ v2_compts_1(A_771,'#skF_1')
      | ~ m1_subset_1(A_771,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(k3_xboole_0(A_771,B_772),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_10665])).

tff(c_82847,plain,
    ( v2_compts_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_6525,c_82709])).

tff(c_83006,plain,(
    v2_compts_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_40,c_34,c_82847])).

tff(c_83008,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_353,c_83006])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:22:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 26.04/16.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 26.04/16.62  
% 26.04/16.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 26.04/16.63  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v8_pre_topc > v2_pre_topc > v1_pre_topc > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 26.04/16.63  
% 26.04/16.63  %Foreground sorts:
% 26.04/16.63  
% 26.04/16.63  
% 26.04/16.63  %Background operators:
% 26.04/16.63  
% 26.04/16.63  
% 26.04/16.63  %Foreground operators:
% 26.04/16.63  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 26.04/16.63  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 26.04/16.63  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 26.04/16.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 26.04/16.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 26.04/16.63  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 26.04/16.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 26.04/16.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 26.04/16.63  tff('#skF_2', type, '#skF_2': $i).
% 26.04/16.63  tff('#skF_3', type, '#skF_3': $i).
% 26.04/16.63  tff('#skF_1', type, '#skF_1': $i).
% 26.04/16.63  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 26.04/16.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 26.04/16.63  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 26.04/16.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 26.04/16.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 26.04/16.63  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 26.04/16.63  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 26.04/16.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 26.04/16.63  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 26.04/16.63  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 26.04/16.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 26.04/16.63  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 26.04/16.63  
% 26.17/16.64  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 26.17/16.64  tff(f_41, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 26.17/16.64  tff(f_136, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v8_pre_topc(A) & v2_compts_1(B, A)) & v2_compts_1(C, A)) => v2_compts_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_compts_1)).
% 26.17/16.64  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 26.17/16.64  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 26.17/16.64  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 26.17/16.64  tff(f_99, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_compts_1)).
% 26.17/16.64  tff(f_86, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => v4_pre_topc(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tops_1)).
% 26.17/16.64  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_pre_topc)).
% 26.17/16.64  tff(f_53, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 26.17/16.64  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 26.17/16.64  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 26.17/16.64  tff(f_117, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_compts_1)).
% 26.17/16.64  tff(c_8, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 26.17/16.64  tff(c_81, plain, (![A_53, B_54]: (k1_setfam_1(k2_tarski(A_53, B_54))=k3_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_41])).
% 26.17/16.64  tff(c_131, plain, (![B_61, A_62]: (k1_setfam_1(k2_tarski(B_61, A_62))=k3_xboole_0(A_62, B_61))), inference(superposition, [status(thm), theory('equality')], [c_8, c_81])).
% 26.17/16.64  tff(c_12, plain, (![A_12, B_13]: (k1_setfam_1(k2_tarski(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 26.17/16.64  tff(c_137, plain, (![B_61, A_62]: (k3_xboole_0(B_61, A_62)=k3_xboole_0(A_62, B_61))), inference(superposition, [status(thm), theory('equality')], [c_131, c_12])).
% 26.17/16.64  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 26.17/16.64  tff(c_264, plain, (![A_71, B_72, C_73]: (k9_subset_1(A_71, B_72, C_73)=k3_xboole_0(B_72, C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 26.17/16.64  tff(c_273, plain, (![B_72]: (k9_subset_1(u1_struct_0('#skF_1'), B_72, '#skF_3')=k3_xboole_0(B_72, '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_264])).
% 26.17/16.64  tff(c_32, plain, (~v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_136])).
% 26.17/16.64  tff(c_352, plain, (~v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_273, c_32])).
% 26.17/16.64  tff(c_353, plain, (~v2_compts_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_352])).
% 26.17/16.64  tff(c_154, plain, (![A_63, B_64]: (k4_xboole_0(A_63, k4_xboole_0(A_63, B_64))=k3_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_33])).
% 26.17/16.64  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 26.17/16.64  tff(c_163, plain, (![A_63, B_64]: (r1_tarski(k3_xboole_0(A_63, B_64), A_63))), inference(superposition, [status(thm), theory('equality')], [c_154, c_4])).
% 26.17/16.64  tff(c_34, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_136])).
% 26.17/16.64  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_136])).
% 26.17/16.64  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_136])).
% 26.17/16.64  tff(c_38, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_136])).
% 26.17/16.64  tff(c_1136, plain, (![B_104, A_105]: (v4_pre_topc(B_104, A_105) | ~v2_compts_1(B_104, A_105) | ~v8_pre_topc(A_105) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105) | ~v2_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_99])).
% 26.17/16.64  tff(c_1155, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1136])).
% 26.17/16.64  tff(c_1163, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_38, c_34, c_1155])).
% 26.17/16.64  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 26.17/16.64  tff(c_36, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_136])).
% 26.17/16.64  tff(c_1152, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1136])).
% 26.17/16.64  tff(c_1160, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_38, c_36, c_1152])).
% 26.17/16.64  tff(c_272, plain, (![B_72]: (k9_subset_1(u1_struct_0('#skF_1'), B_72, '#skF_2')=k3_xboole_0(B_72, '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_264])).
% 26.17/16.64  tff(c_1690, plain, (![A_117, B_118, C_119]: (v4_pre_topc(k9_subset_1(u1_struct_0(A_117), B_118, C_119), A_117) | ~v4_pre_topc(C_119, A_117) | ~v4_pre_topc(B_118, A_117) | ~m1_subset_1(C_119, k1_zfmisc_1(u1_struct_0(A_117))) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117) | ~v2_pre_topc(A_117))), inference(cnfTransformation, [status(thm)], [f_86])).
% 26.17/16.64  tff(c_1702, plain, (![B_72]: (v4_pre_topc(k3_xboole_0(B_72, '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~v4_pre_topc(B_72, '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_272, c_1690])).
% 26.17/16.64  tff(c_6479, plain, (![B_217]: (v4_pre_topc(k3_xboole_0(B_217, '#skF_2'), '#skF_1') | ~v4_pre_topc(B_217, '#skF_1') | ~m1_subset_1(B_217, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_1160, c_1702])).
% 26.17/16.64  tff(c_6507, plain, (v4_pre_topc(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_6479])).
% 26.17/16.64  tff(c_6525, plain, (v4_pre_topc(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1163, c_6507])).
% 26.17/16.64  tff(c_314, plain, (![A_77, B_78]: (u1_struct_0(k1_pre_topc(A_77, B_78))=B_78 | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_60])).
% 26.17/16.64  tff(c_324, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_314])).
% 26.17/16.64  tff(c_331, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_324])).
% 26.17/16.64  tff(c_528, plain, (![A_88, B_89]: (m1_pre_topc(k1_pre_topc(A_88, B_89), A_88) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_53])).
% 26.17/16.64  tff(c_539, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_528])).
% 26.17/16.64  tff(c_546, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_539])).
% 26.17/16.64  tff(c_16, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 26.17/16.64  tff(c_711, plain, (![C_94, A_95, B_96]: (m1_subset_1(C_94, k1_zfmisc_1(u1_struct_0(A_95))) | ~m1_subset_1(C_94, k1_zfmisc_1(u1_struct_0(B_96))) | ~m1_pre_topc(B_96, A_95) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_70])).
% 26.17/16.64  tff(c_3617, plain, (![A_166, A_167, B_168]: (m1_subset_1(A_166, k1_zfmisc_1(u1_struct_0(A_167))) | ~m1_pre_topc(B_168, A_167) | ~l1_pre_topc(A_167) | ~r1_tarski(A_166, u1_struct_0(B_168)))), inference(resolution, [status(thm)], [c_16, c_711])).
% 26.17/16.64  tff(c_3629, plain, (![A_166]: (m1_subset_1(A_166, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_166, u1_struct_0(k1_pre_topc('#skF_1', '#skF_3'))))), inference(resolution, [status(thm)], [c_546, c_3617])).
% 26.17/16.64  tff(c_3639, plain, (![A_166]: (m1_subset_1(A_166, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_166, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_331, c_44, c_3629])).
% 26.17/16.64  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 26.17/16.64  tff(c_1340, plain, (![C_109, A_110, B_111]: (v2_compts_1(C_109, A_110) | ~v4_pre_topc(C_109, A_110) | ~r1_tarski(C_109, B_111) | ~v2_compts_1(B_111, A_110) | ~m1_subset_1(C_109, k1_zfmisc_1(u1_struct_0(A_110))) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110) | ~v2_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_117])).
% 26.17/16.64  tff(c_4596, plain, (![A_187, B_188, A_189]: (v2_compts_1(k4_xboole_0(A_187, B_188), A_189) | ~v4_pre_topc(k4_xboole_0(A_187, B_188), A_189) | ~v2_compts_1(A_187, A_189) | ~m1_subset_1(k4_xboole_0(A_187, B_188), k1_zfmisc_1(u1_struct_0(A_189))) | ~m1_subset_1(A_187, k1_zfmisc_1(u1_struct_0(A_189))) | ~l1_pre_topc(A_189) | ~v2_pre_topc(A_189))), inference(resolution, [status(thm)], [c_4, c_1340])).
% 26.17/16.64  tff(c_4637, plain, (![A_5, B_6, A_189]: (v2_compts_1(k4_xboole_0(A_5, k4_xboole_0(A_5, B_6)), A_189) | ~v4_pre_topc(k4_xboole_0(A_5, k4_xboole_0(A_5, B_6)), A_189) | ~v2_compts_1(A_5, A_189) | ~m1_subset_1(k3_xboole_0(A_5, B_6), k1_zfmisc_1(u1_struct_0(A_189))) | ~m1_subset_1(A_5, k1_zfmisc_1(u1_struct_0(A_189))) | ~l1_pre_topc(A_189) | ~v2_pre_topc(A_189))), inference(superposition, [status(thm), theory('equality')], [c_6, c_4596])).
% 26.17/16.64  tff(c_10595, plain, (![A_270, B_271, A_272]: (v2_compts_1(k3_xboole_0(A_270, B_271), A_272) | ~v4_pre_topc(k3_xboole_0(A_270, B_271), A_272) | ~v2_compts_1(A_270, A_272) | ~m1_subset_1(k3_xboole_0(A_270, B_271), k1_zfmisc_1(u1_struct_0(A_272))) | ~m1_subset_1(A_270, k1_zfmisc_1(u1_struct_0(A_272))) | ~l1_pre_topc(A_272) | ~v2_pre_topc(A_272))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_4637])).
% 26.17/16.64  tff(c_10665, plain, (![A_270, B_271]: (v2_compts_1(k3_xboole_0(A_270, B_271), '#skF_1') | ~v4_pre_topc(k3_xboole_0(A_270, B_271), '#skF_1') | ~v2_compts_1(A_270, '#skF_1') | ~m1_subset_1(A_270, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(k3_xboole_0(A_270, B_271), '#skF_3'))), inference(resolution, [status(thm)], [c_3639, c_10595])).
% 26.17/16.64  tff(c_82709, plain, (![A_771, B_772]: (v2_compts_1(k3_xboole_0(A_771, B_772), '#skF_1') | ~v4_pre_topc(k3_xboole_0(A_771, B_772), '#skF_1') | ~v2_compts_1(A_771, '#skF_1') | ~m1_subset_1(A_771, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(k3_xboole_0(A_771, B_772), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_10665])).
% 26.17/16.64  tff(c_82847, plain, (v2_compts_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_6525, c_82709])).
% 26.17/16.64  tff(c_83006, plain, (v2_compts_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_163, c_40, c_34, c_82847])).
% 26.17/16.64  tff(c_83008, plain, $false, inference(negUnitSimplification, [status(thm)], [c_353, c_83006])).
% 26.17/16.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 26.17/16.64  
% 26.17/16.64  Inference rules
% 26.17/16.64  ----------------------
% 26.17/16.64  #Ref     : 0
% 26.17/16.64  #Sup     : 21131
% 26.17/16.64  #Fact    : 0
% 26.17/16.64  #Define  : 0
% 26.17/16.64  #Split   : 11
% 26.17/16.64  #Chain   : 0
% 26.17/16.64  #Close   : 0
% 26.17/16.64  
% 26.17/16.64  Ordering : KBO
% 26.17/16.64  
% 26.17/16.64  Simplification rules
% 26.17/16.64  ----------------------
% 26.17/16.64  #Subsume      : 4658
% 26.17/16.64  #Demod        : 19663
% 26.17/16.64  #Tautology    : 5764
% 26.17/16.64  #SimpNegUnit  : 2
% 26.17/16.64  #BackRed      : 1
% 26.17/16.64  
% 26.17/16.64  #Partial instantiations: 0
% 26.17/16.64  #Strategies tried      : 1
% 26.17/16.64  
% 26.17/16.64  Timing (in seconds)
% 26.17/16.64  ----------------------
% 26.17/16.65  Preprocessing        : 0.34
% 26.17/16.65  Parsing              : 0.19
% 26.17/16.65  CNF conversion       : 0.02
% 26.17/16.65  Main loop            : 15.54
% 26.17/16.65  Inferencing          : 1.95
% 26.17/16.65  Reduction            : 8.69
% 26.17/16.65  Demodulation         : 7.83
% 26.17/16.65  BG Simplification    : 0.27
% 26.17/16.65  Subsumption          : 4.05
% 26.17/16.65  Abstraction          : 0.43
% 26.17/16.65  MUC search           : 0.00
% 26.17/16.65  Cooper               : 0.00
% 26.17/16.65  Total                : 15.91
% 26.17/16.65  Index Insertion      : 0.00
% 26.17/16.65  Index Deletion       : 0.00
% 26.17/16.65  Index Matching       : 0.00
% 26.17/16.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
