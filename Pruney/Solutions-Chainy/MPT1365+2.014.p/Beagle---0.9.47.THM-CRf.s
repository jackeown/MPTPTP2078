%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:56 EST 2020

% Result     : Theorem 21.38s
% Output     : CNFRefutation 21.56s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 225 expanded)
%              Number of leaves         :   36 (  96 expanded)
%              Depth                    :   16
%              Number of atoms          :  208 ( 650 expanded)
%              Number of equality atoms :   19 (  60 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_138,negated_conjecture,(
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

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_101,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_compts_1)).

tff(f_88,axiom,(
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

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_119,axiom,(
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

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_174,plain,(
    ! [A_68,B_69,C_70] :
      ( k9_subset_1(A_68,B_69,C_70) = k3_xboole_0(B_69,C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_182,plain,(
    ! [B_69] : k9_subset_1(u1_struct_0('#skF_1'),B_69,'#skF_2') = k3_xboole_0(B_69,'#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_174])).

tff(c_493,plain,(
    ! [A_87,C_88,B_89] :
      ( k9_subset_1(A_87,C_88,B_89) = k9_subset_1(A_87,B_89,C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_497,plain,(
    ! [B_89] : k9_subset_1(u1_struct_0('#skF_1'),B_89,'#skF_2') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_89) ),
    inference(resolution,[status(thm)],[c_42,c_493])).

tff(c_505,plain,(
    ! [B_90] : k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_90) = k3_xboole_0(B_90,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_497])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_183,plain,(
    ! [B_69] : k9_subset_1(u1_struct_0('#skF_1'),B_69,'#skF_3') = k3_xboole_0(B_69,'#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_174])).

tff(c_512,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_183])).

tff(c_32,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_239,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_32])).

tff(c_532,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_239])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_34,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_38,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_36,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1212,plain,(
    ! [B_120,A_121] :
      ( v4_pre_topc(B_120,A_121)
      | ~ v2_compts_1(B_120,A_121)
      | ~ v8_pre_topc(A_121)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ l1_pre_topc(A_121)
      | ~ v2_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1234,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1212])).

tff(c_1243,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_38,c_36,c_1234])).

tff(c_1237,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1212])).

tff(c_1246,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_38,c_34,c_1237])).

tff(c_1825,plain,(
    ! [A_143,B_144,C_145] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(A_143),B_144,C_145),A_143)
      | ~ v4_pre_topc(C_145,A_143)
      | ~ v4_pre_topc(B_144,A_143)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_pre_topc(A_143)
      | ~ v2_pre_topc(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1850,plain,(
    ! [B_69] :
      ( v4_pre_topc(k3_xboole_0(B_69,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc('#skF_3','#skF_1')
      | ~ v4_pre_topc(B_69,'#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_1825])).

tff(c_5322,plain,(
    ! [B_214] :
      ( v4_pre_topc(k3_xboole_0(B_214,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(B_214,'#skF_1')
      | ~ m1_subset_1(B_214,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40,c_1246,c_1850])).

tff(c_5343,plain,
    ( v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_5322])).

tff(c_5358,plain,(
    v4_pre_topc(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1243,c_512,c_5343])).

tff(c_54,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(A_56,B_57)
      | ~ m1_subset_1(A_56,k1_zfmisc_1(B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_65,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_42,c_54])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_70,plain,(
    k3_xboole_0('#skF_2',u1_struct_0('#skF_1')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_65,c_2])).

tff(c_92,plain,(
    ! [A_60,B_61] : k4_xboole_0(A_60,k4_xboole_0(A_60,B_61)) = k3_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_110,plain,(
    ! [A_62,B_63] : r1_tarski(k3_xboole_0(A_62,B_63),A_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_4])).

tff(c_119,plain,(
    r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_110])).

tff(c_643,plain,(
    ! [A_95,B_96] :
      ( u1_struct_0(k1_pre_topc(A_95,B_96)) = B_96
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_650,plain,
    ( u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2'
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_643])).

tff(c_657,plain,(
    u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_650])).

tff(c_101,plain,(
    ! [A_60,B_61] : r1_tarski(k3_xboole_0(A_60,B_61),A_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_4])).

tff(c_942,plain,(
    ! [A_103,B_104] :
      ( m1_pre_topc(k1_pre_topc(A_103,B_104),A_103)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_951,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_942])).

tff(c_957,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_951])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_998,plain,(
    ! [C_108,A_109,B_110] :
      ( m1_subset_1(C_108,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ m1_subset_1(C_108,k1_zfmisc_1(u1_struct_0(B_110)))
      | ~ m1_pre_topc(B_110,A_109)
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2176,plain,(
    ! [A_151,A_152,B_153] :
      ( m1_subset_1(A_151,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ m1_pre_topc(B_153,A_152)
      | ~ l1_pre_topc(A_152)
      | ~ r1_tarski(A_151,u1_struct_0(B_153)) ) ),
    inference(resolution,[status(thm)],[c_16,c_998])).

tff(c_2188,plain,(
    ! [A_151] :
      ( m1_subset_1(A_151,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_151,u1_struct_0(k1_pre_topc('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_957,c_2176])).

tff(c_2331,plain,(
    ! [A_159] :
      ( m1_subset_1(A_159,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_159,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_657,c_44,c_2188])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( m1_pre_topc(k1_pre_topc(A_17,B_18),A_17)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2338,plain,(
    ! [A_159] :
      ( m1_pre_topc(k1_pre_topc('#skF_1',A_159),'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_159,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_2331,c_18])).

tff(c_2578,plain,(
    ! [A_166] :
      ( m1_pre_topc(k1_pre_topc('#skF_1',A_166),'#skF_1')
      | ~ r1_tarski(A_166,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2338])).

tff(c_1010,plain,(
    ! [A_15,A_109,B_110] :
      ( m1_subset_1(A_15,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ m1_pre_topc(B_110,A_109)
      | ~ l1_pre_topc(A_109)
      | ~ r1_tarski(A_15,u1_struct_0(B_110)) ) ),
    inference(resolution,[status(thm)],[c_16,c_998])).

tff(c_2580,plain,(
    ! [A_15,A_166] :
      ( m1_subset_1(A_15,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_15,u1_struct_0(k1_pre_topc('#skF_1',A_166)))
      | ~ r1_tarski(A_166,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_2578,c_1010])).

tff(c_71890,plain,(
    ! [A_711,A_712] :
      ( m1_subset_1(A_711,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_711,u1_struct_0(k1_pre_topc('#skF_1',A_712)))
      | ~ r1_tarski(A_712,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2580])).

tff(c_72043,plain,(
    ! [A_713,B_714] :
      ( m1_subset_1(k3_xboole_0(u1_struct_0(k1_pre_topc('#skF_1',A_713)),B_714),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_713,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_101,c_71890])).

tff(c_72264,plain,(
    ! [B_714] :
      ( m1_subset_1(k3_xboole_0('#skF_2',B_714),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski('#skF_2','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_657,c_72043])).

tff(c_72301,plain,(
    ! [B_715] : m1_subset_1(k3_xboole_0('#skF_2',B_715),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_72264])).

tff(c_72496,plain,(
    m1_subset_1(k3_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_512,c_72301])).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1473,plain,(
    ! [C_131,A_132,B_133] :
      ( v2_compts_1(C_131,A_132)
      | ~ v4_pre_topc(C_131,A_132)
      | ~ r1_tarski(C_131,B_133)
      | ~ v2_compts_1(B_133,A_132)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_3064,plain,(
    ! [A_174,B_175,A_176] :
      ( v2_compts_1(k4_xboole_0(A_174,B_175),A_176)
      | ~ v4_pre_topc(k4_xboole_0(A_174,B_175),A_176)
      | ~ v2_compts_1(A_174,A_176)
      | ~ m1_subset_1(k4_xboole_0(A_174,B_175),k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ m1_subset_1(A_174,k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176) ) ),
    inference(resolution,[status(thm)],[c_4,c_1473])).

tff(c_3102,plain,(
    ! [A_5,B_6,A_176] :
      ( v2_compts_1(k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)),A_176)
      | ~ v4_pre_topc(k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)),A_176)
      | ~ v2_compts_1(A_5,A_176)
      | ~ m1_subset_1(k3_xboole_0(A_5,B_6),k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ m1_subset_1(A_5,k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_3064])).

tff(c_3117,plain,(
    ! [A_5,B_6,A_176] :
      ( v2_compts_1(k3_xboole_0(A_5,B_6),A_176)
      | ~ v4_pre_topc(k3_xboole_0(A_5,B_6),A_176)
      | ~ v2_compts_1(A_5,A_176)
      | ~ m1_subset_1(k3_xboole_0(A_5,B_6),k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ m1_subset_1(A_5,k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_3102])).

tff(c_73231,plain,
    ( v2_compts_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1')
    | ~ v4_pre_topc(k3_xboole_0('#skF_3','#skF_2'),'#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_72496,c_3117])).

tff(c_73260,plain,(
    v2_compts_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40,c_34,c_5358,c_73231])).

tff(c_73262,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_532,c_73260])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:44:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.38/12.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.38/12.79  
% 21.38/12.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.38/12.79  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v8_pre_topc > v2_pre_topc > v1_pre_topc > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 21.38/12.79  
% 21.38/12.79  %Foreground sorts:
% 21.38/12.79  
% 21.38/12.79  
% 21.38/12.79  %Background operators:
% 21.38/12.79  
% 21.38/12.79  
% 21.38/12.79  %Foreground operators:
% 21.38/12.79  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 21.38/12.79  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 21.38/12.79  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 21.38/12.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.38/12.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 21.38/12.79  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 21.38/12.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 21.38/12.79  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 21.38/12.79  tff('#skF_2', type, '#skF_2': $i).
% 21.38/12.79  tff('#skF_3', type, '#skF_3': $i).
% 21.38/12.79  tff('#skF_1', type, '#skF_1': $i).
% 21.38/12.79  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 21.38/12.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 21.38/12.79  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 21.38/12.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.38/12.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.38/12.79  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 21.38/12.79  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 21.38/12.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 21.38/12.79  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 21.38/12.79  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 21.38/12.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 21.38/12.79  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 21.38/12.79  
% 21.56/12.81  tff(f_138, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v8_pre_topc(A) & v2_compts_1(B, A)) & v2_compts_1(C, A)) => v2_compts_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_compts_1)).
% 21.56/12.81  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 21.56/12.81  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 21.56/12.81  tff(f_101, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_compts_1)).
% 21.56/12.81  tff(f_88, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => v4_pre_topc(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tops_1)).
% 21.56/12.81  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 21.56/12.81  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 21.56/12.81  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 21.56/12.81  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 21.56/12.81  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_pre_topc)).
% 21.56/12.81  tff(f_55, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 21.56/12.81  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 21.56/12.81  tff(f_119, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_compts_1)).
% 21.56/12.81  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 21.56/12.81  tff(c_174, plain, (![A_68, B_69, C_70]: (k9_subset_1(A_68, B_69, C_70)=k3_xboole_0(B_69, C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 21.56/12.81  tff(c_182, plain, (![B_69]: (k9_subset_1(u1_struct_0('#skF_1'), B_69, '#skF_2')=k3_xboole_0(B_69, '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_174])).
% 21.56/12.81  tff(c_493, plain, (![A_87, C_88, B_89]: (k9_subset_1(A_87, C_88, B_89)=k9_subset_1(A_87, B_89, C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 21.56/12.81  tff(c_497, plain, (![B_89]: (k9_subset_1(u1_struct_0('#skF_1'), B_89, '#skF_2')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_89))), inference(resolution, [status(thm)], [c_42, c_493])).
% 21.56/12.81  tff(c_505, plain, (![B_90]: (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_90)=k3_xboole_0(B_90, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_497])).
% 21.56/12.81  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 21.56/12.81  tff(c_183, plain, (![B_69]: (k9_subset_1(u1_struct_0('#skF_1'), B_69, '#skF_3')=k3_xboole_0(B_69, '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_174])).
% 21.56/12.81  tff(c_512, plain, (k3_xboole_0('#skF_2', '#skF_3')=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_505, c_183])).
% 21.56/12.81  tff(c_32, plain, (~v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 21.56/12.81  tff(c_239, plain, (~v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_183, c_32])).
% 21.56/12.81  tff(c_532, plain, (~v2_compts_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_512, c_239])).
% 21.56/12.81  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 21.56/12.81  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 21.56/12.81  tff(c_34, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 21.56/12.81  tff(c_38, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 21.56/12.81  tff(c_36, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 21.56/12.81  tff(c_1212, plain, (![B_120, A_121]: (v4_pre_topc(B_120, A_121) | ~v2_compts_1(B_120, A_121) | ~v8_pre_topc(A_121) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_121))) | ~l1_pre_topc(A_121) | ~v2_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_101])).
% 21.56/12.81  tff(c_1234, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1212])).
% 21.56/12.81  tff(c_1243, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_38, c_36, c_1234])).
% 21.56/12.81  tff(c_1237, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1212])).
% 21.56/12.81  tff(c_1246, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_38, c_34, c_1237])).
% 21.56/12.81  tff(c_1825, plain, (![A_143, B_144, C_145]: (v4_pre_topc(k9_subset_1(u1_struct_0(A_143), B_144, C_145), A_143) | ~v4_pre_topc(C_145, A_143) | ~v4_pre_topc(B_144, A_143) | ~m1_subset_1(C_145, k1_zfmisc_1(u1_struct_0(A_143))) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_pre_topc(A_143) | ~v2_pre_topc(A_143))), inference(cnfTransformation, [status(thm)], [f_88])).
% 21.56/12.81  tff(c_1850, plain, (![B_69]: (v4_pre_topc(k3_xboole_0(B_69, '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1') | ~v4_pre_topc(B_69, '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_183, c_1825])).
% 21.56/12.81  tff(c_5322, plain, (![B_214]: (v4_pre_topc(k3_xboole_0(B_214, '#skF_3'), '#skF_1') | ~v4_pre_topc(B_214, '#skF_1') | ~m1_subset_1(B_214, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_40, c_1246, c_1850])).
% 21.56/12.81  tff(c_5343, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_5322])).
% 21.56/12.81  tff(c_5358, plain, (v4_pre_topc(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1243, c_512, c_5343])).
% 21.56/12.81  tff(c_54, plain, (![A_56, B_57]: (r1_tarski(A_56, B_57) | ~m1_subset_1(A_56, k1_zfmisc_1(B_57)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 21.56/12.81  tff(c_65, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_54])).
% 21.56/12.81  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 21.56/12.81  tff(c_70, plain, (k3_xboole_0('#skF_2', u1_struct_0('#skF_1'))='#skF_2'), inference(resolution, [status(thm)], [c_65, c_2])).
% 21.56/12.81  tff(c_92, plain, (![A_60, B_61]: (k4_xboole_0(A_60, k4_xboole_0(A_60, B_61))=k3_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_33])).
% 21.56/12.81  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 21.56/12.81  tff(c_110, plain, (![A_62, B_63]: (r1_tarski(k3_xboole_0(A_62, B_63), A_62))), inference(superposition, [status(thm), theory('equality')], [c_92, c_4])).
% 21.56/12.81  tff(c_119, plain, (r1_tarski('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_70, c_110])).
% 21.56/12.81  tff(c_643, plain, (![A_95, B_96]: (u1_struct_0(k1_pre_topc(A_95, B_96))=B_96 | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_62])).
% 21.56/12.81  tff(c_650, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2' | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_643])).
% 21.56/12.81  tff(c_657, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_650])).
% 21.56/12.81  tff(c_101, plain, (![A_60, B_61]: (r1_tarski(k3_xboole_0(A_60, B_61), A_60))), inference(superposition, [status(thm), theory('equality')], [c_92, c_4])).
% 21.56/12.81  tff(c_942, plain, (![A_103, B_104]: (m1_pre_topc(k1_pre_topc(A_103, B_104), A_103) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_55])).
% 21.56/12.81  tff(c_951, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_942])).
% 21.56/12.81  tff(c_957, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_951])).
% 21.56/12.81  tff(c_16, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 21.56/12.81  tff(c_998, plain, (![C_108, A_109, B_110]: (m1_subset_1(C_108, k1_zfmisc_1(u1_struct_0(A_109))) | ~m1_subset_1(C_108, k1_zfmisc_1(u1_struct_0(B_110))) | ~m1_pre_topc(B_110, A_109) | ~l1_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_72])).
% 21.56/12.81  tff(c_2176, plain, (![A_151, A_152, B_153]: (m1_subset_1(A_151, k1_zfmisc_1(u1_struct_0(A_152))) | ~m1_pre_topc(B_153, A_152) | ~l1_pre_topc(A_152) | ~r1_tarski(A_151, u1_struct_0(B_153)))), inference(resolution, [status(thm)], [c_16, c_998])).
% 21.56/12.81  tff(c_2188, plain, (![A_151]: (m1_subset_1(A_151, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_151, u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_957, c_2176])).
% 21.56/12.81  tff(c_2331, plain, (![A_159]: (m1_subset_1(A_159, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_159, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_657, c_44, c_2188])).
% 21.56/12.81  tff(c_18, plain, (![A_17, B_18]: (m1_pre_topc(k1_pre_topc(A_17, B_18), A_17) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 21.56/12.81  tff(c_2338, plain, (![A_159]: (m1_pre_topc(k1_pre_topc('#skF_1', A_159), '#skF_1') | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_159, '#skF_2'))), inference(resolution, [status(thm)], [c_2331, c_18])).
% 21.56/12.81  tff(c_2578, plain, (![A_166]: (m1_pre_topc(k1_pre_topc('#skF_1', A_166), '#skF_1') | ~r1_tarski(A_166, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2338])).
% 21.56/12.81  tff(c_1010, plain, (![A_15, A_109, B_110]: (m1_subset_1(A_15, k1_zfmisc_1(u1_struct_0(A_109))) | ~m1_pre_topc(B_110, A_109) | ~l1_pre_topc(A_109) | ~r1_tarski(A_15, u1_struct_0(B_110)))), inference(resolution, [status(thm)], [c_16, c_998])).
% 21.56/12.81  tff(c_2580, plain, (![A_15, A_166]: (m1_subset_1(A_15, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_15, u1_struct_0(k1_pre_topc('#skF_1', A_166))) | ~r1_tarski(A_166, '#skF_2'))), inference(resolution, [status(thm)], [c_2578, c_1010])).
% 21.56/12.81  tff(c_71890, plain, (![A_711, A_712]: (m1_subset_1(A_711, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_711, u1_struct_0(k1_pre_topc('#skF_1', A_712))) | ~r1_tarski(A_712, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2580])).
% 21.56/12.81  tff(c_72043, plain, (![A_713, B_714]: (m1_subset_1(k3_xboole_0(u1_struct_0(k1_pre_topc('#skF_1', A_713)), B_714), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_713, '#skF_2'))), inference(resolution, [status(thm)], [c_101, c_71890])).
% 21.56/12.81  tff(c_72264, plain, (![B_714]: (m1_subset_1(k3_xboole_0('#skF_2', B_714), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski('#skF_2', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_657, c_72043])).
% 21.56/12.81  tff(c_72301, plain, (![B_715]: (m1_subset_1(k3_xboole_0('#skF_2', B_715), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_72264])).
% 21.56/12.81  tff(c_72496, plain, (m1_subset_1(k3_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_512, c_72301])).
% 21.56/12.81  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 21.56/12.81  tff(c_1473, plain, (![C_131, A_132, B_133]: (v2_compts_1(C_131, A_132) | ~v4_pre_topc(C_131, A_132) | ~r1_tarski(C_131, B_133) | ~v2_compts_1(B_133, A_132) | ~m1_subset_1(C_131, k1_zfmisc_1(u1_struct_0(A_132))) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132))), inference(cnfTransformation, [status(thm)], [f_119])).
% 21.56/12.81  tff(c_3064, plain, (![A_174, B_175, A_176]: (v2_compts_1(k4_xboole_0(A_174, B_175), A_176) | ~v4_pre_topc(k4_xboole_0(A_174, B_175), A_176) | ~v2_compts_1(A_174, A_176) | ~m1_subset_1(k4_xboole_0(A_174, B_175), k1_zfmisc_1(u1_struct_0(A_176))) | ~m1_subset_1(A_174, k1_zfmisc_1(u1_struct_0(A_176))) | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176))), inference(resolution, [status(thm)], [c_4, c_1473])).
% 21.56/12.81  tff(c_3102, plain, (![A_5, B_6, A_176]: (v2_compts_1(k4_xboole_0(A_5, k4_xboole_0(A_5, B_6)), A_176) | ~v4_pre_topc(k4_xboole_0(A_5, k4_xboole_0(A_5, B_6)), A_176) | ~v2_compts_1(A_5, A_176) | ~m1_subset_1(k3_xboole_0(A_5, B_6), k1_zfmisc_1(u1_struct_0(A_176))) | ~m1_subset_1(A_5, k1_zfmisc_1(u1_struct_0(A_176))) | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176))), inference(superposition, [status(thm), theory('equality')], [c_6, c_3064])).
% 21.56/12.81  tff(c_3117, plain, (![A_5, B_6, A_176]: (v2_compts_1(k3_xboole_0(A_5, B_6), A_176) | ~v4_pre_topc(k3_xboole_0(A_5, B_6), A_176) | ~v2_compts_1(A_5, A_176) | ~m1_subset_1(k3_xboole_0(A_5, B_6), k1_zfmisc_1(u1_struct_0(A_176))) | ~m1_subset_1(A_5, k1_zfmisc_1(u1_struct_0(A_176))) | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_3102])).
% 21.56/12.81  tff(c_73231, plain, (v2_compts_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1') | ~v4_pre_topc(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_72496, c_3117])).
% 21.56/12.81  tff(c_73260, plain, (v2_compts_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_40, c_34, c_5358, c_73231])).
% 21.56/12.81  tff(c_73262, plain, $false, inference(negUnitSimplification, [status(thm)], [c_532, c_73260])).
% 21.56/12.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.56/12.81  
% 21.56/12.81  Inference rules
% 21.56/12.81  ----------------------
% 21.56/12.81  #Ref     : 0
% 21.56/12.81  #Sup     : 17722
% 21.56/12.81  #Fact    : 0
% 21.56/12.81  #Define  : 0
% 21.56/12.81  #Split   : 9
% 21.56/12.81  #Chain   : 0
% 21.56/12.81  #Close   : 0
% 21.56/12.81  
% 21.56/12.81  Ordering : KBO
% 21.56/12.81  
% 21.56/12.81  Simplification rules
% 21.56/12.81  ----------------------
% 21.56/12.81  #Subsume      : 4223
% 21.56/12.81  #Demod        : 22747
% 21.56/12.81  #Tautology    : 6795
% 21.56/12.81  #SimpNegUnit  : 1
% 21.56/12.81  #BackRed      : 10
% 21.56/12.81  
% 21.56/12.81  #Partial instantiations: 0
% 21.56/12.81  #Strategies tried      : 1
% 21.56/12.81  
% 21.56/12.81  Timing (in seconds)
% 21.56/12.81  ----------------------
% 21.56/12.81  Preprocessing        : 0.36
% 21.56/12.81  Parsing              : 0.20
% 21.56/12.81  CNF conversion       : 0.02
% 21.56/12.81  Main loop            : 11.63
% 21.56/12.81  Inferencing          : 2.00
% 21.56/12.81  Reduction            : 5.80
% 21.56/12.81  Demodulation         : 5.05
% 21.56/12.81  BG Simplification    : 0.23
% 21.56/12.81  Subsumption          : 3.11
% 21.56/12.81  Abstraction          : 0.38
% 21.56/12.81  MUC search           : 0.00
% 21.56/12.81  Cooper               : 0.00
% 21.56/12.81  Total                : 12.03
% 21.56/12.81  Index Insertion      : 0.00
% 21.56/12.81  Index Deletion       : 0.00
% 21.56/12.81  Index Matching       : 0.00
% 21.56/12.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
