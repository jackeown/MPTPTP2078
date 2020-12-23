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

% Result     : Theorem 8.24s
% Output     : CNFRefutation 8.24s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 660 expanded)
%              Number of leaves         :   31 ( 239 expanded)
%              Depth                    :   16
%              Number of atoms          :  206 (1170 expanded)
%              Number of equality atoms :   38 ( 374 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_117,negated_conjecture,(
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

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_compts_1)).

tff(f_67,axiom,(
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

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_98,axiom,(
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
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_75,plain,(
    ! [A_45,B_46] : k1_setfam_1(k2_tarski(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_172,plain,(
    ! [A_56,B_57] : k1_setfam_1(k2_tarski(A_56,B_57)) = k3_xboole_0(B_57,A_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_75])).

tff(c_14,plain,(
    ! [A_16,B_17] : k1_setfam_1(k2_tarski(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_178,plain,(
    ! [B_57,A_56] : k3_xboole_0(B_57,A_56) = k3_xboole_0(A_56,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_14])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_240,plain,(
    ! [A_60,B_61,C_62] :
      ( k9_subset_1(A_60,B_61,C_62) = k3_xboole_0(B_61,C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_249,plain,(
    ! [B_61] : k9_subset_1(u1_struct_0('#skF_1'),B_61,'#skF_3') = k3_xboole_0(B_61,'#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_240])).

tff(c_26,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_280,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_26])).

tff(c_281,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_280])).

tff(c_96,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(A_51,B_52)
      | ~ m1_subset_1(A_51,k1_zfmisc_1(B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_108,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_34,c_96])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_121,plain,(
    k3_xboole_0('#skF_3',u1_struct_0('#skF_1')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_108,c_6])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(k3_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_90,plain,(
    ! [A_47,B_48] :
      ( k3_xboole_0(A_47,B_48) = A_47
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_301,plain,(
    ! [A_67,B_68] : k3_xboole_0(k3_xboole_0(A_67,B_68),A_67) = k3_xboole_0(A_67,B_68) ),
    inference(resolution,[status(thm)],[c_4,c_90])).

tff(c_364,plain,(
    ! [A_69,B_70] : r1_tarski(k3_xboole_0(A_69,B_70),k3_xboole_0(A_69,B_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_4])).

tff(c_376,plain,(
    ! [B_57,A_56] : r1_tarski(k3_xboole_0(B_57,A_56),k3_xboole_0(A_56,B_57)) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_364])).

tff(c_113,plain,(
    ! [A_53,C_54,B_55] :
      ( r1_tarski(k3_xboole_0(A_53,C_54),B_55)
      | ~ r1_tarski(A_53,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1853,plain,(
    ! [A_119,C_120,B_121] :
      ( k3_xboole_0(k3_xboole_0(A_119,C_120),B_121) = k3_xboole_0(A_119,C_120)
      | ~ r1_tarski(A_119,B_121) ) ),
    inference(resolution,[status(thm)],[c_113,c_6])).

tff(c_195,plain,(
    ! [B_58,A_59] : k3_xboole_0(B_58,A_59) = k3_xboole_0(A_59,B_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_14])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(k3_xboole_0(A_1,C_3),B_2)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_213,plain,(
    ! [A_59,B_58,B_2] :
      ( r1_tarski(k3_xboole_0(A_59,B_58),B_2)
      | ~ r1_tarski(B_58,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_2])).

tff(c_6434,plain,(
    ! [A_187,C_188,B_189,B_190] :
      ( r1_tarski(k3_xboole_0(A_187,C_188),B_189)
      | ~ r1_tarski(B_190,B_189)
      | ~ r1_tarski(A_187,B_190) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1853,c_213])).

tff(c_8657,plain,(
    ! [A_216,C_217,A_218,B_219] :
      ( r1_tarski(k3_xboole_0(A_216,C_217),A_218)
      | ~ r1_tarski(A_216,k3_xboole_0(A_218,B_219)) ) ),
    inference(resolution,[status(thm)],[c_4,c_6434])).

tff(c_8748,plain,(
    ! [B_220,A_221,C_222] : r1_tarski(k3_xboole_0(k3_xboole_0(B_220,A_221),C_222),A_221) ),
    inference(resolution,[status(thm)],[c_376,c_8657])).

tff(c_8928,plain,(
    ! [C_222] : r1_tarski(k3_xboole_0('#skF_3',C_222),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_8748])).

tff(c_40,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_32,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_30,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_630,plain,(
    ! [B_80,A_81] :
      ( v4_pre_topc(B_80,A_81)
      | ~ v2_compts_1(B_80,A_81)
      | ~ v8_pre_topc(A_81)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_637,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_630])).

tff(c_644,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_30,c_637])).

tff(c_28,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_640,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_630])).

tff(c_647,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_28,c_640])).

tff(c_1200,plain,(
    ! [A_97,B_98,C_99] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(A_97),B_98,C_99),A_97)
      | ~ v4_pre_topc(C_99,A_97)
      | ~ v4_pre_topc(B_98,A_97)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97)
      | ~ v2_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1212,plain,(
    ! [B_61] :
      ( v4_pre_topc(k3_xboole_0(B_61,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc('#skF_3','#skF_1')
      | ~ v4_pre_topc(B_61,'#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_1200])).

tff(c_1578,plain,(
    ! [B_110] :
      ( v4_pre_topc(k3_xboole_0(B_110,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(B_110,'#skF_1')
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_34,c_647,c_1212])).

tff(c_1585,plain,
    ( v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_1578])).

tff(c_1592,plain,(
    v4_pre_topc(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_644,c_178,c_1585])).

tff(c_410,plain,(
    ! [A_69,B_70] : k3_xboole_0(k3_xboole_0(A_69,B_70),k3_xboole_0(A_69,B_70)) = k3_xboole_0(A_69,B_70) ),
    inference(resolution,[status(thm)],[c_364,c_6])).

tff(c_680,plain,(
    ! [B_87,A_88] : k3_xboole_0(k3_xboole_0(B_87,A_88),A_88) = k3_xboole_0(A_88,B_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_301])).

tff(c_765,plain,(
    k3_xboole_0(u1_struct_0('#skF_1'),'#skF_3') = k3_xboole_0('#skF_3',u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_680])).

tff(c_785,plain,(
    k3_xboole_0(u1_struct_0('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_765])).

tff(c_107,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_36,c_96])).

tff(c_112,plain,(
    k3_xboole_0('#skF_2',u1_struct_0('#skF_1')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_107,c_6])).

tff(c_128,plain,(
    r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_4])).

tff(c_18,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1526,plain,(
    ! [B_105,B_106,A_107] :
      ( k9_subset_1(B_105,B_106,A_107) = k3_xboole_0(B_106,A_107)
      | ~ r1_tarski(A_107,B_105) ) ),
    inference(resolution,[status(thm)],[c_18,c_240])).

tff(c_1558,plain,(
    ! [A_4,B_106,B_5] : k9_subset_1(A_4,B_106,k3_xboole_0(A_4,B_5)) = k3_xboole_0(B_106,k3_xboole_0(A_4,B_5)) ),
    inference(resolution,[status(thm)],[c_4,c_1526])).

tff(c_421,plain,(
    ! [A_71,C_72,B_73] :
      ( k9_subset_1(A_71,C_72,B_73) = k9_subset_1(A_71,B_73,C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1756,plain,(
    ! [B_113,B_114,A_115] :
      ( k9_subset_1(B_113,B_114,A_115) = k9_subset_1(B_113,A_115,B_114)
      | ~ r1_tarski(A_115,B_113) ) ),
    inference(resolution,[status(thm)],[c_18,c_421])).

tff(c_1790,plain,(
    ! [A_4,B_5,B_114] : k9_subset_1(A_4,k3_xboole_0(A_4,B_5),B_114) = k9_subset_1(A_4,B_114,k3_xboole_0(A_4,B_5)) ),
    inference(resolution,[status(thm)],[c_4,c_1756])).

tff(c_3724,plain,(
    ! [A_152,B_153,B_154] : k9_subset_1(A_152,k3_xboole_0(A_152,B_153),B_154) = k3_xboole_0(B_154,k3_xboole_0(A_152,B_153)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1558,c_1790])).

tff(c_3907,plain,(
    ! [A_156,B_157,B_158] : k9_subset_1(A_156,k3_xboole_0(B_157,A_156),B_158) = k3_xboole_0(B_158,k3_xboole_0(A_156,B_157)) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_3724])).

tff(c_248,plain,(
    ! [B_61] : k9_subset_1(u1_struct_0('#skF_1'),B_61,'#skF_2') = k3_xboole_0(B_61,'#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_240])).

tff(c_3934,plain,(
    ! [B_157] : k3_xboole_0(k3_xboole_0(B_157,u1_struct_0('#skF_1')),'#skF_2') = k3_xboole_0('#skF_2',k3_xboole_0(u1_struct_0('#skF_1'),B_157)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3907,c_248])).

tff(c_6578,plain,(
    ! [A_193,C_194] :
      ( r1_tarski(k3_xboole_0(A_193,C_194),u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_193,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_107,c_6434])).

tff(c_723,plain,(
    ! [A_88,B_87,B_2] :
      ( r1_tarski(k3_xboole_0(A_88,B_87),B_2)
      | ~ r1_tarski(k3_xboole_0(B_87,A_88),B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_680,c_2])).

tff(c_6804,plain,(
    ! [C_197,A_198] :
      ( r1_tarski(k3_xboole_0(C_197,A_198),u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_198,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6578,c_723])).

tff(c_6832,plain,(
    ! [B_157] :
      ( r1_tarski(k3_xboole_0('#skF_2',k3_xboole_0(u1_struct_0('#skF_1'),B_157)),u1_struct_0('#skF_1'))
      | ~ r1_tarski('#skF_2','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3934,c_6804])).

tff(c_7304,plain,(
    ! [B_204] : r1_tarski(k3_xboole_0('#skF_2',k3_xboole_0(u1_struct_0('#skF_1'),B_204)),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_6832])).

tff(c_7362,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_785,c_7304])).

tff(c_7393,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_7362])).

tff(c_7424,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),u1_struct_0('#skF_1')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_7393,c_6])).

tff(c_250,plain,(
    ! [B_63,A_64] : r1_tarski(k3_xboole_0(B_63,A_64),A_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_4])).

tff(c_1059,plain,(
    ! [B_95,A_96] : k3_xboole_0(k3_xboole_0(B_95,A_96),A_96) = k3_xboole_0(B_95,A_96) ),
    inference(resolution,[status(thm)],[c_250,c_6])).

tff(c_1229,plain,(
    ! [A_101,B_102] : k3_xboole_0(k3_xboole_0(A_101,B_102),A_101) = k3_xboole_0(B_102,A_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_1059])).

tff(c_1343,plain,(
    ! [A_56,B_102] : k3_xboole_0(A_56,k3_xboole_0(A_56,B_102)) = k3_xboole_0(B_102,A_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_1229])).

tff(c_7871,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),k3_xboole_0('#skF_3','#skF_2')) = k3_xboole_0(u1_struct_0('#skF_1'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7424,c_1343])).

tff(c_7977,plain,(
    k3_xboole_0(u1_struct_0('#skF_1'),k3_xboole_0('#skF_3','#skF_2')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_7871])).

tff(c_911,plain,(
    ! [C_89,A_90,B_91] :
      ( v2_compts_1(C_89,A_90)
      | ~ v4_pre_topc(C_89,A_90)
      | ~ r1_tarski(C_89,B_91)
      | ~ v2_compts_1(B_91,A_90)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90)
      | ~ v2_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3422,plain,(
    ! [A_143,C_144,A_145,B_146] :
      ( v2_compts_1(k3_xboole_0(A_143,C_144),A_145)
      | ~ v4_pre_topc(k3_xboole_0(A_143,C_144),A_145)
      | ~ v2_compts_1(B_146,A_145)
      | ~ m1_subset_1(k3_xboole_0(A_143,C_144),k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(A_145)
      | ~ v2_pre_topc(A_145)
      | ~ r1_tarski(A_143,B_146) ) ),
    inference(resolution,[status(thm)],[c_2,c_911])).

tff(c_9647,plain,(
    ! [A_232,C_233,A_234,B_235] :
      ( v2_compts_1(k3_xboole_0(A_232,C_233),A_234)
      | ~ v4_pre_topc(k3_xboole_0(A_232,C_233),A_234)
      | ~ v2_compts_1(B_235,A_234)
      | ~ m1_subset_1(B_235,k1_zfmisc_1(u1_struct_0(A_234)))
      | ~ l1_pre_topc(A_234)
      | ~ v2_pre_topc(A_234)
      | ~ r1_tarski(A_232,B_235)
      | ~ r1_tarski(k3_xboole_0(A_232,C_233),u1_struct_0(A_234)) ) ),
    inference(resolution,[status(thm)],[c_18,c_3422])).

tff(c_9654,plain,(
    ! [A_232,C_233] :
      ( v2_compts_1(k3_xboole_0(A_232,C_233),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(A_232,C_233),'#skF_1')
      | ~ v2_compts_1('#skF_3','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_232,'#skF_3')
      | ~ r1_tarski(k3_xboole_0(A_232,C_233),u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_34,c_9647])).

tff(c_10122,plain,(
    ! [A_242,C_243] :
      ( v2_compts_1(k3_xboole_0(A_242,C_243),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(A_242,C_243),'#skF_1')
      | ~ r1_tarski(A_242,'#skF_3')
      | ~ r1_tarski(k3_xboole_0(A_242,C_243),u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_28,c_9654])).

tff(c_10156,plain,
    ( v2_compts_1(k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),u1_struct_0('#skF_1')),'#skF_1')
    | ~ v4_pre_topc(k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),u1_struct_0('#skF_1')),'#skF_1')
    | ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_3')
    | ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7424,c_10122])).

tff(c_10283,plain,(
    v2_compts_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8928,c_4,c_1592,c_7977,c_178,c_7977,c_178,c_10156])).

tff(c_10285,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_281,c_10283])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:33:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.24/2.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.24/2.78  
% 8.24/2.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.24/2.78  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 8.24/2.78  
% 8.24/2.78  %Foreground sorts:
% 8.24/2.78  
% 8.24/2.78  
% 8.24/2.78  %Background operators:
% 8.24/2.78  
% 8.24/2.78  
% 8.24/2.78  %Foreground operators:
% 8.24/2.78  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 8.24/2.78  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 8.24/2.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.24/2.78  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.24/2.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.24/2.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.24/2.78  tff('#skF_2', type, '#skF_2': $i).
% 8.24/2.78  tff('#skF_3', type, '#skF_3': $i).
% 8.24/2.78  tff('#skF_1', type, '#skF_1': $i).
% 8.24/2.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.24/2.78  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 8.24/2.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.24/2.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.24/2.78  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.24/2.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.24/2.78  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.24/2.78  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 8.24/2.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.24/2.78  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.24/2.78  
% 8.24/2.80  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.24/2.80  tff(f_47, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 8.24/2.80  tff(f_117, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v8_pre_topc(A) & v2_compts_1(B, A)) & v2_compts_1(C, A)) => v2_compts_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_compts_1)).
% 8.24/2.80  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 8.24/2.80  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.24/2.80  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.24/2.80  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 8.24/2.80  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 8.24/2.80  tff(f_80, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_compts_1)).
% 8.24/2.80  tff(f_67, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => v4_pre_topc(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tops_1)).
% 8.24/2.80  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 8.24/2.80  tff(f_98, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_compts_1)).
% 8.24/2.80  tff(c_8, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.24/2.80  tff(c_75, plain, (![A_45, B_46]: (k1_setfam_1(k2_tarski(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.24/2.80  tff(c_172, plain, (![A_56, B_57]: (k1_setfam_1(k2_tarski(A_56, B_57))=k3_xboole_0(B_57, A_56))), inference(superposition, [status(thm), theory('equality')], [c_8, c_75])).
% 8.24/2.80  tff(c_14, plain, (![A_16, B_17]: (k1_setfam_1(k2_tarski(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.24/2.80  tff(c_178, plain, (![B_57, A_56]: (k3_xboole_0(B_57, A_56)=k3_xboole_0(A_56, B_57))), inference(superposition, [status(thm), theory('equality')], [c_172, c_14])).
% 8.24/2.80  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.24/2.80  tff(c_240, plain, (![A_60, B_61, C_62]: (k9_subset_1(A_60, B_61, C_62)=k3_xboole_0(B_61, C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.24/2.80  tff(c_249, plain, (![B_61]: (k9_subset_1(u1_struct_0('#skF_1'), B_61, '#skF_3')=k3_xboole_0(B_61, '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_240])).
% 8.24/2.80  tff(c_26, plain, (~v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.24/2.80  tff(c_280, plain, (~v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_249, c_26])).
% 8.24/2.80  tff(c_281, plain, (~v2_compts_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_178, c_280])).
% 8.24/2.80  tff(c_96, plain, (![A_51, B_52]: (r1_tarski(A_51, B_52) | ~m1_subset_1(A_51, k1_zfmisc_1(B_52)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.24/2.80  tff(c_108, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_96])).
% 8.24/2.80  tff(c_6, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.24/2.80  tff(c_121, plain, (k3_xboole_0('#skF_3', u1_struct_0('#skF_1'))='#skF_3'), inference(resolution, [status(thm)], [c_108, c_6])).
% 8.24/2.80  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(k3_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.24/2.80  tff(c_90, plain, (![A_47, B_48]: (k3_xboole_0(A_47, B_48)=A_47 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.24/2.80  tff(c_301, plain, (![A_67, B_68]: (k3_xboole_0(k3_xboole_0(A_67, B_68), A_67)=k3_xboole_0(A_67, B_68))), inference(resolution, [status(thm)], [c_4, c_90])).
% 8.24/2.80  tff(c_364, plain, (![A_69, B_70]: (r1_tarski(k3_xboole_0(A_69, B_70), k3_xboole_0(A_69, B_70)))), inference(superposition, [status(thm), theory('equality')], [c_301, c_4])).
% 8.24/2.80  tff(c_376, plain, (![B_57, A_56]: (r1_tarski(k3_xboole_0(B_57, A_56), k3_xboole_0(A_56, B_57)))), inference(superposition, [status(thm), theory('equality')], [c_178, c_364])).
% 8.24/2.80  tff(c_113, plain, (![A_53, C_54, B_55]: (r1_tarski(k3_xboole_0(A_53, C_54), B_55) | ~r1_tarski(A_53, B_55))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.24/2.80  tff(c_1853, plain, (![A_119, C_120, B_121]: (k3_xboole_0(k3_xboole_0(A_119, C_120), B_121)=k3_xboole_0(A_119, C_120) | ~r1_tarski(A_119, B_121))), inference(resolution, [status(thm)], [c_113, c_6])).
% 8.24/2.80  tff(c_195, plain, (![B_58, A_59]: (k3_xboole_0(B_58, A_59)=k3_xboole_0(A_59, B_58))), inference(superposition, [status(thm), theory('equality')], [c_172, c_14])).
% 8.24/2.80  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(k3_xboole_0(A_1, C_3), B_2) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.24/2.80  tff(c_213, plain, (![A_59, B_58, B_2]: (r1_tarski(k3_xboole_0(A_59, B_58), B_2) | ~r1_tarski(B_58, B_2))), inference(superposition, [status(thm), theory('equality')], [c_195, c_2])).
% 8.24/2.80  tff(c_6434, plain, (![A_187, C_188, B_189, B_190]: (r1_tarski(k3_xboole_0(A_187, C_188), B_189) | ~r1_tarski(B_190, B_189) | ~r1_tarski(A_187, B_190))), inference(superposition, [status(thm), theory('equality')], [c_1853, c_213])).
% 8.24/2.80  tff(c_8657, plain, (![A_216, C_217, A_218, B_219]: (r1_tarski(k3_xboole_0(A_216, C_217), A_218) | ~r1_tarski(A_216, k3_xboole_0(A_218, B_219)))), inference(resolution, [status(thm)], [c_4, c_6434])).
% 8.24/2.80  tff(c_8748, plain, (![B_220, A_221, C_222]: (r1_tarski(k3_xboole_0(k3_xboole_0(B_220, A_221), C_222), A_221))), inference(resolution, [status(thm)], [c_376, c_8657])).
% 8.24/2.80  tff(c_8928, plain, (![C_222]: (r1_tarski(k3_xboole_0('#skF_3', C_222), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_121, c_8748])).
% 8.24/2.80  tff(c_40, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.24/2.80  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.24/2.80  tff(c_32, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.24/2.80  tff(c_30, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.24/2.80  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.24/2.80  tff(c_630, plain, (![B_80, A_81]: (v4_pre_topc(B_80, A_81) | ~v2_compts_1(B_80, A_81) | ~v8_pre_topc(A_81) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.24/2.80  tff(c_637, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_630])).
% 8.24/2.80  tff(c_644, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_30, c_637])).
% 8.24/2.80  tff(c_28, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.24/2.80  tff(c_640, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_630])).
% 8.24/2.80  tff(c_647, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_28, c_640])).
% 8.24/2.80  tff(c_1200, plain, (![A_97, B_98, C_99]: (v4_pre_topc(k9_subset_1(u1_struct_0(A_97), B_98, C_99), A_97) | ~v4_pre_topc(C_99, A_97) | ~v4_pre_topc(B_98, A_97) | ~m1_subset_1(C_99, k1_zfmisc_1(u1_struct_0(A_97))) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97) | ~v2_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.24/2.80  tff(c_1212, plain, (![B_61]: (v4_pre_topc(k3_xboole_0(B_61, '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1') | ~v4_pre_topc(B_61, '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_249, c_1200])).
% 8.24/2.80  tff(c_1578, plain, (![B_110]: (v4_pre_topc(k3_xboole_0(B_110, '#skF_3'), '#skF_1') | ~v4_pre_topc(B_110, '#skF_1') | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_34, c_647, c_1212])).
% 8.24/2.80  tff(c_1585, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_36, c_1578])).
% 8.24/2.80  tff(c_1592, plain, (v4_pre_topc(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_644, c_178, c_1585])).
% 8.24/2.80  tff(c_410, plain, (![A_69, B_70]: (k3_xboole_0(k3_xboole_0(A_69, B_70), k3_xboole_0(A_69, B_70))=k3_xboole_0(A_69, B_70))), inference(resolution, [status(thm)], [c_364, c_6])).
% 8.24/2.80  tff(c_680, plain, (![B_87, A_88]: (k3_xboole_0(k3_xboole_0(B_87, A_88), A_88)=k3_xboole_0(A_88, B_87))), inference(superposition, [status(thm), theory('equality')], [c_178, c_301])).
% 8.24/2.80  tff(c_765, plain, (k3_xboole_0(u1_struct_0('#skF_1'), '#skF_3')=k3_xboole_0('#skF_3', u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_121, c_680])).
% 8.24/2.80  tff(c_785, plain, (k3_xboole_0(u1_struct_0('#skF_1'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_121, c_765])).
% 8.24/2.80  tff(c_107, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_96])).
% 8.24/2.80  tff(c_112, plain, (k3_xboole_0('#skF_2', u1_struct_0('#skF_1'))='#skF_2'), inference(resolution, [status(thm)], [c_107, c_6])).
% 8.24/2.80  tff(c_128, plain, (r1_tarski('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_112, c_4])).
% 8.24/2.80  tff(c_18, plain, (![A_18, B_19]: (m1_subset_1(A_18, k1_zfmisc_1(B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.24/2.80  tff(c_1526, plain, (![B_105, B_106, A_107]: (k9_subset_1(B_105, B_106, A_107)=k3_xboole_0(B_106, A_107) | ~r1_tarski(A_107, B_105))), inference(resolution, [status(thm)], [c_18, c_240])).
% 8.24/2.80  tff(c_1558, plain, (![A_4, B_106, B_5]: (k9_subset_1(A_4, B_106, k3_xboole_0(A_4, B_5))=k3_xboole_0(B_106, k3_xboole_0(A_4, B_5)))), inference(resolution, [status(thm)], [c_4, c_1526])).
% 8.24/2.80  tff(c_421, plain, (![A_71, C_72, B_73]: (k9_subset_1(A_71, C_72, B_73)=k9_subset_1(A_71, B_73, C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.24/2.80  tff(c_1756, plain, (![B_113, B_114, A_115]: (k9_subset_1(B_113, B_114, A_115)=k9_subset_1(B_113, A_115, B_114) | ~r1_tarski(A_115, B_113))), inference(resolution, [status(thm)], [c_18, c_421])).
% 8.24/2.80  tff(c_1790, plain, (![A_4, B_5, B_114]: (k9_subset_1(A_4, k3_xboole_0(A_4, B_5), B_114)=k9_subset_1(A_4, B_114, k3_xboole_0(A_4, B_5)))), inference(resolution, [status(thm)], [c_4, c_1756])).
% 8.24/2.80  tff(c_3724, plain, (![A_152, B_153, B_154]: (k9_subset_1(A_152, k3_xboole_0(A_152, B_153), B_154)=k3_xboole_0(B_154, k3_xboole_0(A_152, B_153)))), inference(demodulation, [status(thm), theory('equality')], [c_1558, c_1790])).
% 8.24/2.80  tff(c_3907, plain, (![A_156, B_157, B_158]: (k9_subset_1(A_156, k3_xboole_0(B_157, A_156), B_158)=k3_xboole_0(B_158, k3_xboole_0(A_156, B_157)))), inference(superposition, [status(thm), theory('equality')], [c_178, c_3724])).
% 8.24/2.80  tff(c_248, plain, (![B_61]: (k9_subset_1(u1_struct_0('#skF_1'), B_61, '#skF_2')=k3_xboole_0(B_61, '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_240])).
% 8.24/2.80  tff(c_3934, plain, (![B_157]: (k3_xboole_0(k3_xboole_0(B_157, u1_struct_0('#skF_1')), '#skF_2')=k3_xboole_0('#skF_2', k3_xboole_0(u1_struct_0('#skF_1'), B_157)))), inference(superposition, [status(thm), theory('equality')], [c_3907, c_248])).
% 8.24/2.80  tff(c_6578, plain, (![A_193, C_194]: (r1_tarski(k3_xboole_0(A_193, C_194), u1_struct_0('#skF_1')) | ~r1_tarski(A_193, '#skF_2'))), inference(resolution, [status(thm)], [c_107, c_6434])).
% 8.24/2.80  tff(c_723, plain, (![A_88, B_87, B_2]: (r1_tarski(k3_xboole_0(A_88, B_87), B_2) | ~r1_tarski(k3_xboole_0(B_87, A_88), B_2))), inference(superposition, [status(thm), theory('equality')], [c_680, c_2])).
% 8.24/2.80  tff(c_6804, plain, (![C_197, A_198]: (r1_tarski(k3_xboole_0(C_197, A_198), u1_struct_0('#skF_1')) | ~r1_tarski(A_198, '#skF_2'))), inference(resolution, [status(thm)], [c_6578, c_723])).
% 8.24/2.80  tff(c_6832, plain, (![B_157]: (r1_tarski(k3_xboole_0('#skF_2', k3_xboole_0(u1_struct_0('#skF_1'), B_157)), u1_struct_0('#skF_1')) | ~r1_tarski('#skF_2', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3934, c_6804])).
% 8.24/2.80  tff(c_7304, plain, (![B_204]: (r1_tarski(k3_xboole_0('#skF_2', k3_xboole_0(u1_struct_0('#skF_1'), B_204)), u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_6832])).
% 8.24/2.80  tff(c_7362, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_785, c_7304])).
% 8.24/2.80  tff(c_7393, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_7362])).
% 8.24/2.80  tff(c_7424, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), u1_struct_0('#skF_1'))=k3_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_7393, c_6])).
% 8.24/2.80  tff(c_250, plain, (![B_63, A_64]: (r1_tarski(k3_xboole_0(B_63, A_64), A_64))), inference(superposition, [status(thm), theory('equality')], [c_195, c_4])).
% 8.24/2.80  tff(c_1059, plain, (![B_95, A_96]: (k3_xboole_0(k3_xboole_0(B_95, A_96), A_96)=k3_xboole_0(B_95, A_96))), inference(resolution, [status(thm)], [c_250, c_6])).
% 8.24/2.80  tff(c_1229, plain, (![A_101, B_102]: (k3_xboole_0(k3_xboole_0(A_101, B_102), A_101)=k3_xboole_0(B_102, A_101))), inference(superposition, [status(thm), theory('equality')], [c_178, c_1059])).
% 8.24/2.80  tff(c_1343, plain, (![A_56, B_102]: (k3_xboole_0(A_56, k3_xboole_0(A_56, B_102))=k3_xboole_0(B_102, A_56))), inference(superposition, [status(thm), theory('equality')], [c_178, c_1229])).
% 8.24/2.80  tff(c_7871, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), k3_xboole_0('#skF_3', '#skF_2'))=k3_xboole_0(u1_struct_0('#skF_1'), k3_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_7424, c_1343])).
% 8.24/2.80  tff(c_7977, plain, (k3_xboole_0(u1_struct_0('#skF_1'), k3_xboole_0('#skF_3', '#skF_2'))=k3_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_410, c_7871])).
% 8.24/2.80  tff(c_911, plain, (![C_89, A_90, B_91]: (v2_compts_1(C_89, A_90) | ~v4_pre_topc(C_89, A_90) | ~r1_tarski(C_89, B_91) | ~v2_compts_1(B_91, A_90) | ~m1_subset_1(C_89, k1_zfmisc_1(u1_struct_0(A_90))) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90) | ~v2_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.24/2.80  tff(c_3422, plain, (![A_143, C_144, A_145, B_146]: (v2_compts_1(k3_xboole_0(A_143, C_144), A_145) | ~v4_pre_topc(k3_xboole_0(A_143, C_144), A_145) | ~v2_compts_1(B_146, A_145) | ~m1_subset_1(k3_xboole_0(A_143, C_144), k1_zfmisc_1(u1_struct_0(A_145))) | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_pre_topc(A_145) | ~v2_pre_topc(A_145) | ~r1_tarski(A_143, B_146))), inference(resolution, [status(thm)], [c_2, c_911])).
% 8.24/2.80  tff(c_9647, plain, (![A_232, C_233, A_234, B_235]: (v2_compts_1(k3_xboole_0(A_232, C_233), A_234) | ~v4_pre_topc(k3_xboole_0(A_232, C_233), A_234) | ~v2_compts_1(B_235, A_234) | ~m1_subset_1(B_235, k1_zfmisc_1(u1_struct_0(A_234))) | ~l1_pre_topc(A_234) | ~v2_pre_topc(A_234) | ~r1_tarski(A_232, B_235) | ~r1_tarski(k3_xboole_0(A_232, C_233), u1_struct_0(A_234)))), inference(resolution, [status(thm)], [c_18, c_3422])).
% 8.24/2.80  tff(c_9654, plain, (![A_232, C_233]: (v2_compts_1(k3_xboole_0(A_232, C_233), '#skF_1') | ~v4_pre_topc(k3_xboole_0(A_232, C_233), '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_232, '#skF_3') | ~r1_tarski(k3_xboole_0(A_232, C_233), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_34, c_9647])).
% 8.24/2.80  tff(c_10122, plain, (![A_242, C_243]: (v2_compts_1(k3_xboole_0(A_242, C_243), '#skF_1') | ~v4_pre_topc(k3_xboole_0(A_242, C_243), '#skF_1') | ~r1_tarski(A_242, '#skF_3') | ~r1_tarski(k3_xboole_0(A_242, C_243), u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_28, c_9654])).
% 8.24/2.80  tff(c_10156, plain, (v2_compts_1(k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), u1_struct_0('#skF_1')), '#skF_1') | ~v4_pre_topc(k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), u1_struct_0('#skF_1')), '#skF_1') | ~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_3') | ~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_7424, c_10122])).
% 8.24/2.80  tff(c_10283, plain, (v2_compts_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8928, c_4, c_1592, c_7977, c_178, c_7977, c_178, c_10156])).
% 8.24/2.80  tff(c_10285, plain, $false, inference(negUnitSimplification, [status(thm)], [c_281, c_10283])).
% 8.24/2.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.24/2.80  
% 8.24/2.80  Inference rules
% 8.24/2.80  ----------------------
% 8.24/2.80  #Ref     : 0
% 8.24/2.80  #Sup     : 2630
% 8.24/2.80  #Fact    : 0
% 8.24/2.80  #Define  : 0
% 8.24/2.80  #Split   : 0
% 8.24/2.80  #Chain   : 0
% 8.24/2.80  #Close   : 0
% 8.24/2.80  
% 8.24/2.80  Ordering : KBO
% 8.24/2.80  
% 8.24/2.80  Simplification rules
% 8.24/2.80  ----------------------
% 8.24/2.80  #Subsume      : 395
% 8.24/2.80  #Demod        : 2684
% 8.24/2.80  #Tautology    : 1196
% 8.24/2.80  #SimpNegUnit  : 3
% 8.24/2.80  #BackRed      : 1
% 8.24/2.80  
% 8.24/2.80  #Partial instantiations: 0
% 8.24/2.80  #Strategies tried      : 1
% 8.24/2.80  
% 8.24/2.80  Timing (in seconds)
% 8.24/2.80  ----------------------
% 8.24/2.81  Preprocessing        : 0.33
% 8.24/2.81  Parsing              : 0.18
% 8.24/2.81  CNF conversion       : 0.02
% 8.24/2.81  Main loop            : 1.70
% 8.24/2.81  Inferencing          : 0.41
% 8.24/2.81  Reduction            : 0.88
% 8.24/2.81  Demodulation         : 0.76
% 8.24/2.81  BG Simplification    : 0.05
% 8.24/2.81  Subsumption          : 0.28
% 8.24/2.81  Abstraction          : 0.08
% 8.24/2.81  MUC search           : 0.00
% 8.24/2.81  Cooper               : 0.00
% 8.24/2.81  Total                : 2.07
% 8.24/2.81  Index Insertion      : 0.00
% 8.24/2.81  Index Deletion       : 0.00
% 8.24/2.81  Index Matching       : 0.00
% 8.63/2.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
