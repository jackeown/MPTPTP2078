%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:08 EST 2020

% Result     : Theorem 31.87s
% Output     : CNFRefutation 31.97s
% Verified   : 
% Statistics : Number of formulae       :  151 (2771 expanded)
%              Number of leaves         :   32 ( 953 expanded)
%              Depth                    :   22
%              Number of atoms          :  416 (9620 expanded)
%              Number of equality atoms :   52 (1551 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_135,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                        & C = D
                        & v2_tex_2(C,A) )
                     => v2_tex_2(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tex_2)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( r1_tarski(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v3_pre_topc(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                   => ( D = B
                     => v3_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_46,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_44,plain,(
    v2_tex_2('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_58,plain,(
    v2_tex_2('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44])).

tff(c_42,plain,(
    ~ v2_tex_2('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_54,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_34,plain,(
    ! [A_39,B_53] :
      ( m1_subset_1('#skF_2'(A_39,B_53),k1_zfmisc_1(u1_struct_0(A_39)))
      | v2_tex_2(B_53,A_39)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_483,plain,(
    ! [A_125,B_126] :
      ( m1_subset_1('#skF_2'(A_125,B_126),k1_zfmisc_1(u1_struct_0(A_125)))
      | v2_tex_2(B_126,A_125)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_496,plain,(
    ! [A_125,B_126] :
      ( r1_tarski('#skF_2'(A_125,B_126),u1_struct_0(A_125))
      | v2_tex_2(B_126,A_125)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125) ) ),
    inference(resolution,[status(thm)],[c_483,c_12])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8] :
      ( k9_subset_1(A_6,B_7,C_8) = k3_xboole_0(B_7,C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3697,plain,(
    ! [A_216,B_217,B_218] :
      ( k9_subset_1(u1_struct_0(A_216),B_217,'#skF_2'(A_216,B_218)) = k3_xboole_0(B_217,'#skF_2'(A_216,B_218))
      | v2_tex_2(B_218,A_216)
      | ~ m1_subset_1(B_218,k1_zfmisc_1(u1_struct_0(A_216)))
      | ~ l1_pre_topc(A_216) ) ),
    inference(resolution,[status(thm)],[c_483,c_10])).

tff(c_3718,plain,(
    ! [B_217] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_217,'#skF_2'('#skF_4','#skF_6')) = k3_xboole_0(B_217,'#skF_2'('#skF_4','#skF_6'))
      | v2_tex_2('#skF_6','#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_3697])).

tff(c_3737,plain,(
    ! [B_217] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_217,'#skF_2'('#skF_4','#skF_6')) = k3_xboole_0(B_217,'#skF_2'('#skF_4','#skF_6'))
      | v2_tex_2('#skF_6','#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3718])).

tff(c_3738,plain,(
    ! [B_217] : k9_subset_1(u1_struct_0('#skF_4'),B_217,'#skF_2'('#skF_4','#skF_6')) = k3_xboole_0(B_217,'#skF_2'('#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_3737])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( k9_subset_1(A_3,C_5,B_4) = k9_subset_1(A_3,B_4,C_5)
      | ~ m1_subset_1(C_5,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4710,plain,(
    ! [A_248,B_249,B_250] :
      ( k9_subset_1(u1_struct_0(A_248),B_249,'#skF_2'(A_248,B_250)) = k9_subset_1(u1_struct_0(A_248),'#skF_2'(A_248,B_250),B_249)
      | v2_tex_2(B_250,A_248)
      | ~ m1_subset_1(B_250,k1_zfmisc_1(u1_struct_0(A_248)))
      | ~ l1_pre_topc(A_248) ) ),
    inference(resolution,[status(thm)],[c_483,c_8])).

tff(c_4731,plain,(
    ! [B_249] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_249,'#skF_2'('#skF_4','#skF_6')) = k9_subset_1(u1_struct_0('#skF_4'),'#skF_2'('#skF_4','#skF_6'),B_249)
      | v2_tex_2('#skF_6','#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_4710])).

tff(c_4750,plain,(
    ! [B_249] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_2'('#skF_4','#skF_6'),B_249) = k3_xboole_0(B_249,'#skF_2'('#skF_4','#skF_6'))
      | v2_tex_2('#skF_6','#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3738,c_4731])).

tff(c_4751,plain,(
    ! [B_249] : k9_subset_1(u1_struct_0('#skF_4'),'#skF_2'('#skF_4','#skF_6'),B_249) = k3_xboole_0(B_249,'#skF_2'('#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_4750])).

tff(c_28,plain,(
    ! [A_38] :
      ( m1_pre_topc(A_38,A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_259,plain,(
    ! [A_107,B_108] :
      ( m1_pre_topc(A_107,g1_pre_topc(u1_struct_0(B_108),u1_pre_topc(B_108)))
      | ~ m1_pre_topc(A_107,B_108)
      | ~ l1_pre_topc(B_108)
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_56,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_48,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_144,plain,(
    ! [B_94,A_95] :
      ( m1_pre_topc(B_94,A_95)
      | ~ m1_pre_topc(B_94,g1_pre_topc(u1_struct_0(A_95),u1_pre_topc(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_147,plain,(
    ! [B_94] :
      ( m1_pre_topc(B_94,'#skF_3')
      | ~ m1_pre_topc(B_94,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_144])).

tff(c_153,plain,(
    ! [B_94] :
      ( m1_pre_topc(B_94,'#skF_3')
      | ~ m1_pre_topc(B_94,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_147])).

tff(c_263,plain,(
    ! [A_107] :
      ( m1_pre_topc(A_107,'#skF_3')
      | ~ m1_pre_topc(A_107,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_107) ) ),
    inference(resolution,[status(thm)],[c_259,c_153])).

tff(c_275,plain,(
    ! [A_107] :
      ( m1_pre_topc(A_107,'#skF_3')
      | ~ m1_pre_topc(A_107,'#skF_4')
      | ~ l1_pre_topc(A_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_263])).

tff(c_272,plain,(
    ! [A_107] :
      ( m1_pre_topc(A_107,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_pre_topc(A_107,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_259])).

tff(c_292,plain,(
    ! [A_110] :
      ( m1_pre_topc(A_110,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_pre_topc(A_110,'#skF_3')
      | ~ l1_pre_topc(A_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_272])).

tff(c_18,plain,(
    ! [B_16,A_14] :
      ( m1_pre_topc(B_16,A_14)
      | ~ m1_pre_topc(B_16,g1_pre_topc(u1_struct_0(A_14),u1_pre_topc(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_298,plain,(
    ! [A_110] :
      ( m1_pre_topc(A_110,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ m1_pre_topc(A_110,'#skF_3')
      | ~ l1_pre_topc(A_110) ) ),
    inference(resolution,[status(thm)],[c_292,c_18])).

tff(c_307,plain,(
    ! [A_111] :
      ( m1_pre_topc(A_111,'#skF_4')
      | ~ m1_pre_topc(A_111,'#skF_3')
      | ~ l1_pre_topc(A_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_298])).

tff(c_314,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_307])).

tff(c_318,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_314])).

tff(c_104,plain,(
    ! [B_85,A_86] :
      ( m1_subset_1(u1_struct_0(B_85),k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ m1_pre_topc(B_85,A_86)
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_108,plain,(
    ! [B_85,A_86] :
      ( r1_tarski(u1_struct_0(B_85),u1_struct_0(A_86))
      | ~ m1_pre_topc(B_85,A_86)
      | ~ l1_pre_topc(A_86) ) ),
    inference(resolution,[status(thm)],[c_104,c_12])).

tff(c_109,plain,(
    ! [B_87,A_88] :
      ( r1_tarski(u1_struct_0(B_87),u1_struct_0(A_88))
      | ~ m1_pre_topc(B_87,A_88)
      | ~ l1_pre_topc(A_88) ) ),
    inference(resolution,[status(thm)],[c_104,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_472,plain,(
    ! [B_123,A_124] :
      ( u1_struct_0(B_123) = u1_struct_0(A_124)
      | ~ r1_tarski(u1_struct_0(A_124),u1_struct_0(B_123))
      | ~ m1_pre_topc(B_123,A_124)
      | ~ l1_pre_topc(A_124) ) ),
    inference(resolution,[status(thm)],[c_109,c_2])).

tff(c_497,plain,(
    ! [B_127,A_128] :
      ( u1_struct_0(B_127) = u1_struct_0(A_128)
      | ~ m1_pre_topc(A_128,B_127)
      | ~ l1_pre_topc(B_127)
      | ~ m1_pre_topc(B_127,A_128)
      | ~ l1_pre_topc(A_128) ) ),
    inference(resolution,[status(thm)],[c_108,c_472])).

tff(c_499,plain,
    ( u1_struct_0('#skF_3') = u1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_318,c_497])).

tff(c_510,plain,
    ( u1_struct_0('#skF_3') = u1_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_499])).

tff(c_518,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_510])).

tff(c_521,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_275,c_518])).

tff(c_524,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_521])).

tff(c_527,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_524])).

tff(c_531,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_527])).

tff(c_532,plain,(
    u1_struct_0('#skF_3') = u1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_510])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1187,plain,(
    ! [A_157,B_158,C_159] :
      ( k9_subset_1(u1_struct_0(A_157),B_158,'#skF_1'(A_157,B_158,C_159)) = C_159
      | ~ r1_tarski(C_159,B_158)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ v2_tex_2(B_158,A_157)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ l1_pre_topc(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_5502,plain,(
    ! [A_275,B_276,A_277] :
      ( k9_subset_1(u1_struct_0(A_275),B_276,'#skF_1'(A_275,B_276,A_277)) = A_277
      | ~ r1_tarski(A_277,B_276)
      | ~ v2_tex_2(B_276,A_275)
      | ~ m1_subset_1(B_276,k1_zfmisc_1(u1_struct_0(A_275)))
      | ~ l1_pre_topc(A_275)
      | ~ r1_tarski(A_277,u1_struct_0(A_275)) ) ),
    inference(resolution,[status(thm)],[c_14,c_1187])).

tff(c_15311,plain,(
    ! [A_501,A_502,A_503] :
      ( k9_subset_1(u1_struct_0(A_501),A_502,'#skF_1'(A_501,A_502,A_503)) = A_503
      | ~ r1_tarski(A_503,A_502)
      | ~ v2_tex_2(A_502,A_501)
      | ~ l1_pre_topc(A_501)
      | ~ r1_tarski(A_503,u1_struct_0(A_501))
      | ~ r1_tarski(A_502,u1_struct_0(A_501)) ) ),
    inference(resolution,[status(thm)],[c_14,c_5502])).

tff(c_15442,plain,(
    ! [A_502,A_503] :
      ( k9_subset_1(u1_struct_0('#skF_4'),A_502,'#skF_1'('#skF_3',A_502,A_503)) = A_503
      | ~ r1_tarski(A_503,A_502)
      | ~ v2_tex_2(A_502,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_503,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_502,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_532,c_15311])).

tff(c_20401,plain,(
    ! [A_590,A_591] :
      ( k9_subset_1(u1_struct_0('#skF_4'),A_590,'#skF_1'('#skF_3',A_590,A_591)) = A_591
      | ~ r1_tarski(A_591,A_590)
      | ~ v2_tex_2(A_590,'#skF_3')
      | ~ r1_tarski(A_591,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_590,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_532,c_56,c_15442])).

tff(c_20481,plain,(
    ! [A_591] :
      ( k3_xboole_0('#skF_1'('#skF_3','#skF_2'('#skF_4','#skF_6'),A_591),'#skF_2'('#skF_4','#skF_6')) = A_591
      | ~ r1_tarski(A_591,'#skF_2'('#skF_4','#skF_6'))
      | ~ v2_tex_2('#skF_2'('#skF_4','#skF_6'),'#skF_3')
      | ~ r1_tarski(A_591,u1_struct_0('#skF_4'))
      | ~ r1_tarski('#skF_2'('#skF_4','#skF_6'),u1_struct_0('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4751,c_20401])).

tff(c_22516,plain,(
    ~ r1_tarski('#skF_2'('#skF_4','#skF_6'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_20481])).

tff(c_22519,plain,
    ( v2_tex_2('#skF_6','#skF_4')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_496,c_22516])).

tff(c_22522,plain,(
    v2_tex_2('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_22519])).

tff(c_22524,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_22522])).

tff(c_22526,plain,(
    r1_tarski('#skF_2'('#skF_4','#skF_6'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_20481])).

tff(c_20436,plain,(
    ! [A_591] :
      ( k3_xboole_0('#skF_1'('#skF_3','#skF_2'('#skF_4','#skF_6'),A_591),'#skF_2'('#skF_4','#skF_6')) = A_591
      | ~ r1_tarski(A_591,'#skF_2'('#skF_4','#skF_6'))
      | ~ v2_tex_2('#skF_2'('#skF_4','#skF_6'),'#skF_3')
      | ~ r1_tarski(A_591,u1_struct_0('#skF_4'))
      | ~ r1_tarski('#skF_2'('#skF_4','#skF_6'),u1_struct_0('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20401,c_4751])).

tff(c_22634,plain,(
    ! [A_591] :
      ( k3_xboole_0('#skF_1'('#skF_3','#skF_2'('#skF_4','#skF_6'),A_591),'#skF_2'('#skF_4','#skF_6')) = A_591
      | ~ r1_tarski(A_591,'#skF_2'('#skF_4','#skF_6'))
      | ~ v2_tex_2('#skF_2'('#skF_4','#skF_6'),'#skF_3')
      | ~ r1_tarski(A_591,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22526,c_20436])).

tff(c_22635,plain,(
    ~ v2_tex_2('#skF_2'('#skF_4','#skF_6'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_22634])).

tff(c_1034,plain,(
    ! [A_149,B_150,D_151] :
      ( k9_subset_1(u1_struct_0(A_149),B_150,D_151) != '#skF_2'(A_149,B_150)
      | ~ v3_pre_topc(D_151,A_149)
      | ~ m1_subset_1(D_151,k1_zfmisc_1(u1_struct_0(A_149)))
      | v2_tex_2(B_150,A_149)
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_pre_topc(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1036,plain,(
    ! [B_150,D_151] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_150,D_151) != '#skF_2'('#skF_3',B_150)
      | ~ v3_pre_topc(D_151,'#skF_3')
      | ~ m1_subset_1(D_151,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_tex_2(B_150,'#skF_3')
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_532,c_1034])).

tff(c_29276,plain,(
    ! [B_660,D_661] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_660,D_661) != '#skF_2'('#skF_3',B_660)
      | ~ v3_pre_topc(D_661,'#skF_3')
      | ~ m1_subset_1(D_661,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_660,'#skF_3')
      | ~ m1_subset_1(B_660,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_532,c_532,c_1036])).

tff(c_29453,plain,(
    ! [B_249] :
      ( k3_xboole_0(B_249,'#skF_2'('#skF_4','#skF_6')) != '#skF_2'('#skF_3','#skF_2'('#skF_4','#skF_6'))
      | ~ v3_pre_topc(B_249,'#skF_3')
      | ~ m1_subset_1(B_249,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2('#skF_2'('#skF_4','#skF_6'),'#skF_3')
      | ~ m1_subset_1('#skF_2'('#skF_4','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4751,c_29276])).

tff(c_29566,plain,(
    ! [B_249] :
      ( k3_xboole_0(B_249,'#skF_2'('#skF_4','#skF_6')) != '#skF_2'('#skF_3','#skF_2'('#skF_4','#skF_6'))
      | ~ v3_pre_topc(B_249,'#skF_3')
      | ~ m1_subset_1(B_249,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_2'('#skF_4','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22635,c_29453])).

tff(c_30857,plain,(
    ~ m1_subset_1('#skF_2'('#skF_4','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_29566])).

tff(c_30860,plain,
    ( v2_tex_2('#skF_6','#skF_4')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_30857])).

tff(c_30866,plain,(
    v2_tex_2('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_30860])).

tff(c_30868,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_30866])).

tff(c_30870,plain,(
    m1_subset_1('#skF_2'('#skF_4','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_29566])).

tff(c_381,plain,(
    ! [A_117,B_118] :
      ( r1_tarski('#skF_2'(A_117,B_118),B_118)
      | v2_tex_2(B_118,A_117)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_390,plain,
    ( r1_tarski('#skF_2'('#skF_4','#skF_6'),'#skF_6')
    | v2_tex_2('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_381])).

tff(c_398,plain,
    ( r1_tarski('#skF_2'('#skF_4','#skF_6'),'#skF_6')
    | v2_tex_2('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_390])).

tff(c_399,plain,(
    r1_tarski('#skF_2'('#skF_4','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_398])).

tff(c_75,plain,(
    ! [A_79,B_80] :
      ( r1_tarski(A_79,B_80)
      | ~ m1_subset_1(A_79,k1_zfmisc_1(B_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_83,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_50,c_75])).

tff(c_113,plain,(
    ! [A_89,B_90,C_91] :
      ( k9_subset_1(A_89,B_90,C_91) = k3_xboole_0(B_90,C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_125,plain,(
    ! [B_90] : k9_subset_1(u1_struct_0('#skF_4'),B_90,'#skF_6') = k3_xboole_0(B_90,'#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_113])).

tff(c_186,plain,(
    ! [A_102,C_103,B_104] :
      ( k9_subset_1(A_102,C_103,B_104) = k9_subset_1(A_102,B_104,C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(A_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_194,plain,(
    ! [B_104] : k9_subset_1(u1_struct_0('#skF_4'),B_104,'#skF_6') = k9_subset_1(u1_struct_0('#skF_4'),'#skF_6',B_104) ),
    inference(resolution,[status(thm)],[c_50,c_186])).

tff(c_200,plain,(
    ! [B_104] : k9_subset_1(u1_struct_0('#skF_4'),'#skF_6',B_104) = k3_xboole_0(B_104,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_194])).

tff(c_20446,plain,(
    ! [A_591] :
      ( k3_xboole_0('#skF_1'('#skF_3','#skF_6',A_591),'#skF_6') = A_591
      | ~ r1_tarski(A_591,'#skF_6')
      | ~ v2_tex_2('#skF_6','#skF_3')
      | ~ r1_tarski(A_591,u1_struct_0('#skF_4'))
      | ~ r1_tarski('#skF_6',u1_struct_0('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20401,c_200])).

tff(c_20506,plain,(
    ! [A_591] :
      ( k3_xboole_0('#skF_1'('#skF_3','#skF_6',A_591),'#skF_6') = A_591
      | ~ r1_tarski(A_591,'#skF_6')
      | ~ r1_tarski(A_591,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_58,c_20446])).

tff(c_22529,plain,
    ( k3_xboole_0('#skF_1'('#skF_3','#skF_6','#skF_2'('#skF_4','#skF_6')),'#skF_6') = '#skF_2'('#skF_4','#skF_6')
    | ~ r1_tarski('#skF_2'('#skF_4','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_22526,c_20506])).

tff(c_22572,plain,(
    k3_xboole_0('#skF_1'('#skF_3','#skF_6','#skF_2'('#skF_4','#skF_6')),'#skF_6') = '#skF_2'('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_399,c_22529])).

tff(c_779,plain,(
    ! [A_136,B_137,C_138] :
      ( v3_pre_topc('#skF_1'(A_136,B_137,C_138),A_136)
      | ~ r1_tarski(C_138,B_137)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ v2_tex_2(B_137,A_136)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_pre_topc(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_3855,plain,(
    ! [A_222,B_223,A_224] :
      ( v3_pre_topc('#skF_1'(A_222,B_223,A_224),A_222)
      | ~ r1_tarski(A_224,B_223)
      | ~ v2_tex_2(B_223,A_222)
      | ~ m1_subset_1(B_223,k1_zfmisc_1(u1_struct_0(A_222)))
      | ~ l1_pre_topc(A_222)
      | ~ r1_tarski(A_224,u1_struct_0(A_222)) ) ),
    inference(resolution,[status(thm)],[c_14,c_779])).

tff(c_3867,plain,(
    ! [B_223,A_224] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_223,A_224),'#skF_3')
      | ~ r1_tarski(A_224,B_223)
      | ~ v2_tex_2(B_223,'#skF_3')
      | ~ m1_subset_1(B_223,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_224,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_532,c_3855])).

tff(c_9942,plain,(
    ! [B_404,A_405] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_404,A_405),'#skF_3')
      | ~ r1_tarski(A_405,B_404)
      | ~ v2_tex_2(B_404,'#skF_3')
      | ~ m1_subset_1(B_404,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_405,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_56,c_3867])).

tff(c_9965,plain,(
    ! [A_405] :
      ( v3_pre_topc('#skF_1'('#skF_3','#skF_6',A_405),'#skF_3')
      | ~ r1_tarski(A_405,'#skF_6')
      | ~ v2_tex_2('#skF_6','#skF_3')
      | ~ r1_tarski(A_405,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_50,c_9942])).

tff(c_9986,plain,(
    ! [A_405] :
      ( v3_pre_topc('#skF_1'('#skF_3','#skF_6',A_405),'#skF_3')
      | ~ r1_tarski(A_405,'#skF_6')
      | ~ r1_tarski(A_405,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_9965])).

tff(c_920,plain,(
    ! [A_142,B_143,C_144] :
      ( m1_subset_1('#skF_1'(A_142,B_143,C_144),k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ r1_tarski(C_144,B_143)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ v2_tex_2(B_143,A_142)
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ l1_pre_topc(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_5277,plain,(
    ! [A_264,B_265,C_266] :
      ( r1_tarski('#skF_1'(A_264,B_265,C_266),u1_struct_0(A_264))
      | ~ r1_tarski(C_266,B_265)
      | ~ m1_subset_1(C_266,k1_zfmisc_1(u1_struct_0(A_264)))
      | ~ v2_tex_2(B_265,A_264)
      | ~ m1_subset_1(B_265,k1_zfmisc_1(u1_struct_0(A_264)))
      | ~ l1_pre_topc(A_264) ) ),
    inference(resolution,[status(thm)],[c_920,c_12])).

tff(c_5301,plain,(
    ! [B_265,C_266] :
      ( r1_tarski('#skF_1'('#skF_3',B_265,C_266),u1_struct_0('#skF_4'))
      | ~ r1_tarski(C_266,B_265)
      | ~ m1_subset_1(C_266,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_265,'#skF_3')
      | ~ m1_subset_1(B_265,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_532,c_5277])).

tff(c_19449,plain,(
    ! [B_579,C_580] :
      ( r1_tarski('#skF_1'('#skF_3',B_579,C_580),u1_struct_0('#skF_4'))
      | ~ r1_tarski(C_580,B_579)
      | ~ m1_subset_1(C_580,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_579,'#skF_3')
      | ~ m1_subset_1(B_579,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_532,c_532,c_5301])).

tff(c_533,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_510])).

tff(c_642,plain,(
    ! [D_130,C_131,A_132] :
      ( v3_pre_topc(D_130,C_131)
      | ~ m1_subset_1(D_130,k1_zfmisc_1(u1_struct_0(C_131)))
      | ~ v3_pre_topc(D_130,A_132)
      | ~ m1_pre_topc(C_131,A_132)
      | ~ m1_subset_1(D_130,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_3356,plain,(
    ! [A_206,C_207,A_208] :
      ( v3_pre_topc(A_206,C_207)
      | ~ v3_pre_topc(A_206,A_208)
      | ~ m1_pre_topc(C_207,A_208)
      | ~ m1_subset_1(A_206,k1_zfmisc_1(u1_struct_0(A_208)))
      | ~ l1_pre_topc(A_208)
      | ~ r1_tarski(A_206,u1_struct_0(C_207)) ) ),
    inference(resolution,[status(thm)],[c_14,c_642])).

tff(c_3364,plain,(
    ! [A_206] :
      ( v3_pre_topc(A_206,'#skF_4')
      | ~ v3_pre_topc(A_206,'#skF_3')
      | ~ m1_subset_1(A_206,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_206,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_533,c_3356])).

tff(c_3544,plain,(
    ! [A_214] :
      ( v3_pre_topc(A_214,'#skF_4')
      | ~ v3_pre_topc(A_214,'#skF_3')
      | ~ m1_subset_1(A_214,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_214,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_532,c_3364])).

tff(c_3596,plain,(
    ! [A_9] :
      ( v3_pre_topc(A_9,'#skF_4')
      | ~ v3_pre_topc(A_9,'#skF_3')
      | ~ r1_tarski(A_9,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_14,c_3544])).

tff(c_110737,plain,(
    ! [B_1295,C_1296] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_1295,C_1296),'#skF_4')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_1295,C_1296),'#skF_3')
      | ~ r1_tarski(C_1296,B_1295)
      | ~ m1_subset_1(C_1296,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_1295,'#skF_3')
      | ~ m1_subset_1(B_1295,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_19449,c_3596])).

tff(c_110788,plain,(
    ! [A_405] :
      ( v3_pre_topc('#skF_1'('#skF_3','#skF_6',A_405),'#skF_4')
      | ~ m1_subset_1(A_405,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2('#skF_6','#skF_3')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_405,'#skF_6')
      | ~ r1_tarski(A_405,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_9986,c_110737])).

tff(c_110935,plain,(
    ! [A_1300] :
      ( v3_pre_topc('#skF_1'('#skF_3','#skF_6',A_1300),'#skF_4')
      | ~ m1_subset_1(A_1300,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_1300,'#skF_6')
      | ~ r1_tarski(A_1300,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_58,c_110788])).

tff(c_110941,plain,
    ( v3_pre_topc('#skF_1'('#skF_3','#skF_6','#skF_2'('#skF_4','#skF_6')),'#skF_4')
    | ~ r1_tarski('#skF_2'('#skF_4','#skF_6'),'#skF_6')
    | ~ r1_tarski('#skF_2'('#skF_4','#skF_6'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_30870,c_110935])).

tff(c_110982,plain,(
    v3_pre_topc('#skF_1'('#skF_3','#skF_6','#skF_2'('#skF_4','#skF_6')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22526,c_399,c_110941])).

tff(c_936,plain,(
    ! [B_143,C_144] :
      ( m1_subset_1('#skF_1'('#skF_3',B_143,C_144),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(C_144,B_143)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_143,'#skF_3')
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_532,c_920])).

tff(c_29676,plain,(
    ! [B_666,C_667] :
      ( m1_subset_1('#skF_1'('#skF_3',B_666,C_667),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(C_667,B_666)
      | ~ m1_subset_1(C_667,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_666,'#skF_3')
      | ~ m1_subset_1(B_666,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_532,c_532,c_936])).

tff(c_1041,plain,(
    ! [B_104] :
      ( k3_xboole_0(B_104,'#skF_6') != '#skF_2'('#skF_4','#skF_6')
      | ~ v3_pre_topc(B_104,'#skF_4')
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2('#skF_6','#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_1034])).

tff(c_1050,plain,(
    ! [B_104] :
      ( k3_xboole_0(B_104,'#skF_6') != '#skF_2'('#skF_4','#skF_6')
      | ~ v3_pre_topc(B_104,'#skF_4')
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2('#skF_6','#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_1041])).

tff(c_1051,plain,(
    ! [B_104] :
      ( k3_xboole_0(B_104,'#skF_6') != '#skF_2'('#skF_4','#skF_6')
      | ~ v3_pre_topc(B_104,'#skF_4')
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1050])).

tff(c_29811,plain,(
    ! [B_666,C_667] :
      ( k3_xboole_0('#skF_1'('#skF_3',B_666,C_667),'#skF_6') != '#skF_2'('#skF_4','#skF_6')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_666,C_667),'#skF_4')
      | ~ r1_tarski(C_667,B_666)
      | ~ m1_subset_1(C_667,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_666,'#skF_3')
      | ~ m1_subset_1(B_666,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_29676,c_1051])).

tff(c_111006,plain,
    ( k3_xboole_0('#skF_1'('#skF_3','#skF_6','#skF_2'('#skF_4','#skF_6')),'#skF_6') != '#skF_2'('#skF_4','#skF_6')
    | ~ r1_tarski('#skF_2'('#skF_4','#skF_6'),'#skF_6')
    | ~ m1_subset_1('#skF_2'('#skF_4','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ v2_tex_2('#skF_6','#skF_3')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_110982,c_29811])).

tff(c_111010,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_58,c_30870,c_399,c_22572,c_111006])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:27:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 31.87/22.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.97/22.20  
% 31.97/22.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.97/22.21  %$ v3_pre_topc > v2_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 31.97/22.21  
% 31.97/22.21  %Foreground sorts:
% 31.97/22.21  
% 31.97/22.21  
% 31.97/22.21  %Background operators:
% 31.97/22.21  
% 31.97/22.21  
% 31.97/22.21  %Foreground operators:
% 31.97/22.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 31.97/22.21  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 31.97/22.21  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 31.97/22.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 31.97/22.21  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 31.97/22.21  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 31.97/22.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 31.97/22.21  tff('#skF_5', type, '#skF_5': $i).
% 31.97/22.21  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 31.97/22.21  tff('#skF_6', type, '#skF_6': $i).
% 31.97/22.21  tff('#skF_3', type, '#skF_3': $i).
% 31.97/22.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 31.97/22.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 31.97/22.21  tff('#skF_4', type, '#skF_4': $i).
% 31.97/22.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 31.97/22.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 31.97/22.21  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 31.97/22.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 31.97/22.21  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 31.97/22.21  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 31.97/22.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 31.97/22.21  
% 31.97/22.23  tff(f_135, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (C = D)) & v2_tex_2(C, A)) => v2_tex_2(D, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_tex_2)).
% 31.97/22.23  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 31.97/22.23  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 31.97/22.23  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 31.97/22.23  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 31.97/22.23  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 31.97/22.23  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 31.97/22.23  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 31.97/22.23  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 31.97/22.23  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 31.97/22.23  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tops_2)).
% 31.97/22.23  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 31.97/22.23  tff(c_46, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_135])).
% 31.97/22.23  tff(c_44, plain, (v2_tex_2('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 31.97/22.23  tff(c_58, plain, (v2_tex_2('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44])).
% 31.97/22.23  tff(c_42, plain, (~v2_tex_2('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 31.97/22.23  tff(c_54, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 31.97/22.23  tff(c_34, plain, (![A_39, B_53]: (m1_subset_1('#skF_2'(A_39, B_53), k1_zfmisc_1(u1_struct_0(A_39))) | v2_tex_2(B_53, A_39) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_115])).
% 31.97/22.23  tff(c_483, plain, (![A_125, B_126]: (m1_subset_1('#skF_2'(A_125, B_126), k1_zfmisc_1(u1_struct_0(A_125))) | v2_tex_2(B_126, A_125) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_pre_topc(A_125))), inference(cnfTransformation, [status(thm)], [f_115])).
% 31.97/22.23  tff(c_12, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 31.97/22.23  tff(c_496, plain, (![A_125, B_126]: (r1_tarski('#skF_2'(A_125, B_126), u1_struct_0(A_125)) | v2_tex_2(B_126, A_125) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_pre_topc(A_125))), inference(resolution, [status(thm)], [c_483, c_12])).
% 31.97/22.23  tff(c_10, plain, (![A_6, B_7, C_8]: (k9_subset_1(A_6, B_7, C_8)=k3_xboole_0(B_7, C_8) | ~m1_subset_1(C_8, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 31.97/22.23  tff(c_3697, plain, (![A_216, B_217, B_218]: (k9_subset_1(u1_struct_0(A_216), B_217, '#skF_2'(A_216, B_218))=k3_xboole_0(B_217, '#skF_2'(A_216, B_218)) | v2_tex_2(B_218, A_216) | ~m1_subset_1(B_218, k1_zfmisc_1(u1_struct_0(A_216))) | ~l1_pre_topc(A_216))), inference(resolution, [status(thm)], [c_483, c_10])).
% 31.97/22.23  tff(c_3718, plain, (![B_217]: (k9_subset_1(u1_struct_0('#skF_4'), B_217, '#skF_2'('#skF_4', '#skF_6'))=k3_xboole_0(B_217, '#skF_2'('#skF_4', '#skF_6')) | v2_tex_2('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_3697])).
% 31.97/22.23  tff(c_3737, plain, (![B_217]: (k9_subset_1(u1_struct_0('#skF_4'), B_217, '#skF_2'('#skF_4', '#skF_6'))=k3_xboole_0(B_217, '#skF_2'('#skF_4', '#skF_6')) | v2_tex_2('#skF_6', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3718])).
% 31.97/22.23  tff(c_3738, plain, (![B_217]: (k9_subset_1(u1_struct_0('#skF_4'), B_217, '#skF_2'('#skF_4', '#skF_6'))=k3_xboole_0(B_217, '#skF_2'('#skF_4', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_42, c_3737])).
% 31.97/22.23  tff(c_8, plain, (![A_3, C_5, B_4]: (k9_subset_1(A_3, C_5, B_4)=k9_subset_1(A_3, B_4, C_5) | ~m1_subset_1(C_5, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 31.97/22.23  tff(c_4710, plain, (![A_248, B_249, B_250]: (k9_subset_1(u1_struct_0(A_248), B_249, '#skF_2'(A_248, B_250))=k9_subset_1(u1_struct_0(A_248), '#skF_2'(A_248, B_250), B_249) | v2_tex_2(B_250, A_248) | ~m1_subset_1(B_250, k1_zfmisc_1(u1_struct_0(A_248))) | ~l1_pre_topc(A_248))), inference(resolution, [status(thm)], [c_483, c_8])).
% 31.97/22.23  tff(c_4731, plain, (![B_249]: (k9_subset_1(u1_struct_0('#skF_4'), B_249, '#skF_2'('#skF_4', '#skF_6'))=k9_subset_1(u1_struct_0('#skF_4'), '#skF_2'('#skF_4', '#skF_6'), B_249) | v2_tex_2('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_4710])).
% 31.97/22.23  tff(c_4750, plain, (![B_249]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_2'('#skF_4', '#skF_6'), B_249)=k3_xboole_0(B_249, '#skF_2'('#skF_4', '#skF_6')) | v2_tex_2('#skF_6', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3738, c_4731])).
% 31.97/22.23  tff(c_4751, plain, (![B_249]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_2'('#skF_4', '#skF_6'), B_249)=k3_xboole_0(B_249, '#skF_2'('#skF_4', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_42, c_4750])).
% 31.97/22.23  tff(c_28, plain, (![A_38]: (m1_pre_topc(A_38, A_38) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_94])).
% 31.97/22.23  tff(c_259, plain, (![A_107, B_108]: (m1_pre_topc(A_107, g1_pre_topc(u1_struct_0(B_108), u1_pre_topc(B_108))) | ~m1_pre_topc(A_107, B_108) | ~l1_pre_topc(B_108) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_66])).
% 31.97/22.23  tff(c_56, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 31.97/22.23  tff(c_48, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 31.97/22.23  tff(c_144, plain, (![B_94, A_95]: (m1_pre_topc(B_94, A_95) | ~m1_pre_topc(B_94, g1_pre_topc(u1_struct_0(A_95), u1_pre_topc(A_95))) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_57])).
% 31.97/22.23  tff(c_147, plain, (![B_94]: (m1_pre_topc(B_94, '#skF_3') | ~m1_pre_topc(B_94, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_144])).
% 31.97/22.23  tff(c_153, plain, (![B_94]: (m1_pre_topc(B_94, '#skF_3') | ~m1_pre_topc(B_94, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_147])).
% 31.97/22.23  tff(c_263, plain, (![A_107]: (m1_pre_topc(A_107, '#skF_3') | ~m1_pre_topc(A_107, '#skF_4') | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_107))), inference(resolution, [status(thm)], [c_259, c_153])).
% 31.97/22.23  tff(c_275, plain, (![A_107]: (m1_pre_topc(A_107, '#skF_3') | ~m1_pre_topc(A_107, '#skF_4') | ~l1_pre_topc(A_107))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_263])).
% 31.97/22.23  tff(c_272, plain, (![A_107]: (m1_pre_topc(A_107, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~m1_pre_topc(A_107, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_107))), inference(superposition, [status(thm), theory('equality')], [c_48, c_259])).
% 31.97/22.23  tff(c_292, plain, (![A_110]: (m1_pre_topc(A_110, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~m1_pre_topc(A_110, '#skF_3') | ~l1_pre_topc(A_110))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_272])).
% 31.97/22.23  tff(c_18, plain, (![B_16, A_14]: (m1_pre_topc(B_16, A_14) | ~m1_pre_topc(B_16, g1_pre_topc(u1_struct_0(A_14), u1_pre_topc(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 31.97/22.23  tff(c_298, plain, (![A_110]: (m1_pre_topc(A_110, '#skF_4') | ~l1_pre_topc('#skF_4') | ~m1_pre_topc(A_110, '#skF_3') | ~l1_pre_topc(A_110))), inference(resolution, [status(thm)], [c_292, c_18])).
% 31.97/22.23  tff(c_307, plain, (![A_111]: (m1_pre_topc(A_111, '#skF_4') | ~m1_pre_topc(A_111, '#skF_3') | ~l1_pre_topc(A_111))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_298])).
% 31.97/22.23  tff(c_314, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_28, c_307])).
% 31.97/22.23  tff(c_318, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_314])).
% 31.97/22.23  tff(c_104, plain, (![B_85, A_86]: (m1_subset_1(u1_struct_0(B_85), k1_zfmisc_1(u1_struct_0(A_86))) | ~m1_pre_topc(B_85, A_86) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_90])).
% 31.97/22.23  tff(c_108, plain, (![B_85, A_86]: (r1_tarski(u1_struct_0(B_85), u1_struct_0(A_86)) | ~m1_pre_topc(B_85, A_86) | ~l1_pre_topc(A_86))), inference(resolution, [status(thm)], [c_104, c_12])).
% 31.97/22.23  tff(c_109, plain, (![B_87, A_88]: (r1_tarski(u1_struct_0(B_87), u1_struct_0(A_88)) | ~m1_pre_topc(B_87, A_88) | ~l1_pre_topc(A_88))), inference(resolution, [status(thm)], [c_104, c_12])).
% 31.97/22.23  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 31.97/22.23  tff(c_472, plain, (![B_123, A_124]: (u1_struct_0(B_123)=u1_struct_0(A_124) | ~r1_tarski(u1_struct_0(A_124), u1_struct_0(B_123)) | ~m1_pre_topc(B_123, A_124) | ~l1_pre_topc(A_124))), inference(resolution, [status(thm)], [c_109, c_2])).
% 31.97/22.23  tff(c_497, plain, (![B_127, A_128]: (u1_struct_0(B_127)=u1_struct_0(A_128) | ~m1_pre_topc(A_128, B_127) | ~l1_pre_topc(B_127) | ~m1_pre_topc(B_127, A_128) | ~l1_pre_topc(A_128))), inference(resolution, [status(thm)], [c_108, c_472])).
% 31.97/22.23  tff(c_499, plain, (u1_struct_0('#skF_3')=u1_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_318, c_497])).
% 31.97/22.23  tff(c_510, plain, (u1_struct_0('#skF_3')=u1_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_499])).
% 31.97/22.23  tff(c_518, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_510])).
% 31.97/22.23  tff(c_521, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_275, c_518])).
% 31.97/22.23  tff(c_524, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_521])).
% 31.97/22.23  tff(c_527, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_28, c_524])).
% 31.97/22.23  tff(c_531, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_527])).
% 31.97/22.23  tff(c_532, plain, (u1_struct_0('#skF_3')=u1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_510])).
% 31.97/22.23  tff(c_14, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 31.97/22.23  tff(c_1187, plain, (![A_157, B_158, C_159]: (k9_subset_1(u1_struct_0(A_157), B_158, '#skF_1'(A_157, B_158, C_159))=C_159 | ~r1_tarski(C_159, B_158) | ~m1_subset_1(C_159, k1_zfmisc_1(u1_struct_0(A_157))) | ~v2_tex_2(B_158, A_157) | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0(A_157))) | ~l1_pre_topc(A_157))), inference(cnfTransformation, [status(thm)], [f_115])).
% 31.97/22.23  tff(c_5502, plain, (![A_275, B_276, A_277]: (k9_subset_1(u1_struct_0(A_275), B_276, '#skF_1'(A_275, B_276, A_277))=A_277 | ~r1_tarski(A_277, B_276) | ~v2_tex_2(B_276, A_275) | ~m1_subset_1(B_276, k1_zfmisc_1(u1_struct_0(A_275))) | ~l1_pre_topc(A_275) | ~r1_tarski(A_277, u1_struct_0(A_275)))), inference(resolution, [status(thm)], [c_14, c_1187])).
% 31.97/22.23  tff(c_15311, plain, (![A_501, A_502, A_503]: (k9_subset_1(u1_struct_0(A_501), A_502, '#skF_1'(A_501, A_502, A_503))=A_503 | ~r1_tarski(A_503, A_502) | ~v2_tex_2(A_502, A_501) | ~l1_pre_topc(A_501) | ~r1_tarski(A_503, u1_struct_0(A_501)) | ~r1_tarski(A_502, u1_struct_0(A_501)))), inference(resolution, [status(thm)], [c_14, c_5502])).
% 31.97/22.23  tff(c_15442, plain, (![A_502, A_503]: (k9_subset_1(u1_struct_0('#skF_4'), A_502, '#skF_1'('#skF_3', A_502, A_503))=A_503 | ~r1_tarski(A_503, A_502) | ~v2_tex_2(A_502, '#skF_3') | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_503, u1_struct_0('#skF_3')) | ~r1_tarski(A_502, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_532, c_15311])).
% 31.97/22.23  tff(c_20401, plain, (![A_590, A_591]: (k9_subset_1(u1_struct_0('#skF_4'), A_590, '#skF_1'('#skF_3', A_590, A_591))=A_591 | ~r1_tarski(A_591, A_590) | ~v2_tex_2(A_590, '#skF_3') | ~r1_tarski(A_591, u1_struct_0('#skF_4')) | ~r1_tarski(A_590, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_532, c_532, c_56, c_15442])).
% 31.97/22.23  tff(c_20481, plain, (![A_591]: (k3_xboole_0('#skF_1'('#skF_3', '#skF_2'('#skF_4', '#skF_6'), A_591), '#skF_2'('#skF_4', '#skF_6'))=A_591 | ~r1_tarski(A_591, '#skF_2'('#skF_4', '#skF_6')) | ~v2_tex_2('#skF_2'('#skF_4', '#skF_6'), '#skF_3') | ~r1_tarski(A_591, u1_struct_0('#skF_4')) | ~r1_tarski('#skF_2'('#skF_4', '#skF_6'), u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_4751, c_20401])).
% 31.97/22.23  tff(c_22516, plain, (~r1_tarski('#skF_2'('#skF_4', '#skF_6'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_20481])).
% 31.97/22.23  tff(c_22519, plain, (v2_tex_2('#skF_6', '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_496, c_22516])).
% 31.97/22.23  tff(c_22522, plain, (v2_tex_2('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_22519])).
% 31.97/22.23  tff(c_22524, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_22522])).
% 31.97/22.23  tff(c_22526, plain, (r1_tarski('#skF_2'('#skF_4', '#skF_6'), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_20481])).
% 31.97/22.23  tff(c_20436, plain, (![A_591]: (k3_xboole_0('#skF_1'('#skF_3', '#skF_2'('#skF_4', '#skF_6'), A_591), '#skF_2'('#skF_4', '#skF_6'))=A_591 | ~r1_tarski(A_591, '#skF_2'('#skF_4', '#skF_6')) | ~v2_tex_2('#skF_2'('#skF_4', '#skF_6'), '#skF_3') | ~r1_tarski(A_591, u1_struct_0('#skF_4')) | ~r1_tarski('#skF_2'('#skF_4', '#skF_6'), u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_20401, c_4751])).
% 31.97/22.23  tff(c_22634, plain, (![A_591]: (k3_xboole_0('#skF_1'('#skF_3', '#skF_2'('#skF_4', '#skF_6'), A_591), '#skF_2'('#skF_4', '#skF_6'))=A_591 | ~r1_tarski(A_591, '#skF_2'('#skF_4', '#skF_6')) | ~v2_tex_2('#skF_2'('#skF_4', '#skF_6'), '#skF_3') | ~r1_tarski(A_591, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_22526, c_20436])).
% 31.97/22.23  tff(c_22635, plain, (~v2_tex_2('#skF_2'('#skF_4', '#skF_6'), '#skF_3')), inference(splitLeft, [status(thm)], [c_22634])).
% 31.97/22.23  tff(c_1034, plain, (![A_149, B_150, D_151]: (k9_subset_1(u1_struct_0(A_149), B_150, D_151)!='#skF_2'(A_149, B_150) | ~v3_pre_topc(D_151, A_149) | ~m1_subset_1(D_151, k1_zfmisc_1(u1_struct_0(A_149))) | v2_tex_2(B_150, A_149) | ~m1_subset_1(B_150, k1_zfmisc_1(u1_struct_0(A_149))) | ~l1_pre_topc(A_149))), inference(cnfTransformation, [status(thm)], [f_115])).
% 31.97/22.23  tff(c_1036, plain, (![B_150, D_151]: (k9_subset_1(u1_struct_0('#skF_4'), B_150, D_151)!='#skF_2'('#skF_3', B_150) | ~v3_pre_topc(D_151, '#skF_3') | ~m1_subset_1(D_151, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_tex_2(B_150, '#skF_3') | ~m1_subset_1(B_150, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_532, c_1034])).
% 31.97/22.23  tff(c_29276, plain, (![B_660, D_661]: (k9_subset_1(u1_struct_0('#skF_4'), B_660, D_661)!='#skF_2'('#skF_3', B_660) | ~v3_pre_topc(D_661, '#skF_3') | ~m1_subset_1(D_661, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_660, '#skF_3') | ~m1_subset_1(B_660, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_532, c_532, c_1036])).
% 31.97/22.23  tff(c_29453, plain, (![B_249]: (k3_xboole_0(B_249, '#skF_2'('#skF_4', '#skF_6'))!='#skF_2'('#skF_3', '#skF_2'('#skF_4', '#skF_6')) | ~v3_pre_topc(B_249, '#skF_3') | ~m1_subset_1(B_249, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2('#skF_2'('#skF_4', '#skF_6'), '#skF_3') | ~m1_subset_1('#skF_2'('#skF_4', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_4751, c_29276])).
% 31.97/22.23  tff(c_29566, plain, (![B_249]: (k3_xboole_0(B_249, '#skF_2'('#skF_4', '#skF_6'))!='#skF_2'('#skF_3', '#skF_2'('#skF_4', '#skF_6')) | ~v3_pre_topc(B_249, '#skF_3') | ~m1_subset_1(B_249, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_2'('#skF_4', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_22635, c_29453])).
% 31.97/22.23  tff(c_30857, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_29566])).
% 31.97/22.23  tff(c_30860, plain, (v2_tex_2('#skF_6', '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_34, c_30857])).
% 31.97/22.23  tff(c_30866, plain, (v2_tex_2('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_30860])).
% 31.97/22.23  tff(c_30868, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_30866])).
% 31.97/22.23  tff(c_30870, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_29566])).
% 31.97/22.23  tff(c_381, plain, (![A_117, B_118]: (r1_tarski('#skF_2'(A_117, B_118), B_118) | v2_tex_2(B_118, A_117) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117))), inference(cnfTransformation, [status(thm)], [f_115])).
% 31.97/22.23  tff(c_390, plain, (r1_tarski('#skF_2'('#skF_4', '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_50, c_381])).
% 31.97/22.23  tff(c_398, plain, (r1_tarski('#skF_2'('#skF_4', '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_390])).
% 31.97/22.23  tff(c_399, plain, (r1_tarski('#skF_2'('#skF_4', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_42, c_398])).
% 31.97/22.23  tff(c_75, plain, (![A_79, B_80]: (r1_tarski(A_79, B_80) | ~m1_subset_1(A_79, k1_zfmisc_1(B_80)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 31.97/22.23  tff(c_83, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_75])).
% 31.97/22.23  tff(c_113, plain, (![A_89, B_90, C_91]: (k9_subset_1(A_89, B_90, C_91)=k3_xboole_0(B_90, C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(A_89)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 31.97/22.23  tff(c_125, plain, (![B_90]: (k9_subset_1(u1_struct_0('#skF_4'), B_90, '#skF_6')=k3_xboole_0(B_90, '#skF_6'))), inference(resolution, [status(thm)], [c_50, c_113])).
% 31.97/22.23  tff(c_186, plain, (![A_102, C_103, B_104]: (k9_subset_1(A_102, C_103, B_104)=k9_subset_1(A_102, B_104, C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(A_102)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 31.97/22.23  tff(c_194, plain, (![B_104]: (k9_subset_1(u1_struct_0('#skF_4'), B_104, '#skF_6')=k9_subset_1(u1_struct_0('#skF_4'), '#skF_6', B_104))), inference(resolution, [status(thm)], [c_50, c_186])).
% 31.97/22.23  tff(c_200, plain, (![B_104]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_6', B_104)=k3_xboole_0(B_104, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_194])).
% 31.97/22.23  tff(c_20446, plain, (![A_591]: (k3_xboole_0('#skF_1'('#skF_3', '#skF_6', A_591), '#skF_6')=A_591 | ~r1_tarski(A_591, '#skF_6') | ~v2_tex_2('#skF_6', '#skF_3') | ~r1_tarski(A_591, u1_struct_0('#skF_4')) | ~r1_tarski('#skF_6', u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_20401, c_200])).
% 31.97/22.23  tff(c_20506, plain, (![A_591]: (k3_xboole_0('#skF_1'('#skF_3', '#skF_6', A_591), '#skF_6')=A_591 | ~r1_tarski(A_591, '#skF_6') | ~r1_tarski(A_591, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_58, c_20446])).
% 31.97/22.23  tff(c_22529, plain, (k3_xboole_0('#skF_1'('#skF_3', '#skF_6', '#skF_2'('#skF_4', '#skF_6')), '#skF_6')='#skF_2'('#skF_4', '#skF_6') | ~r1_tarski('#skF_2'('#skF_4', '#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_22526, c_20506])).
% 31.97/22.23  tff(c_22572, plain, (k3_xboole_0('#skF_1'('#skF_3', '#skF_6', '#skF_2'('#skF_4', '#skF_6')), '#skF_6')='#skF_2'('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_399, c_22529])).
% 31.97/22.23  tff(c_779, plain, (![A_136, B_137, C_138]: (v3_pre_topc('#skF_1'(A_136, B_137, C_138), A_136) | ~r1_tarski(C_138, B_137) | ~m1_subset_1(C_138, k1_zfmisc_1(u1_struct_0(A_136))) | ~v2_tex_2(B_137, A_136) | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0(A_136))) | ~l1_pre_topc(A_136))), inference(cnfTransformation, [status(thm)], [f_115])).
% 31.97/22.23  tff(c_3855, plain, (![A_222, B_223, A_224]: (v3_pre_topc('#skF_1'(A_222, B_223, A_224), A_222) | ~r1_tarski(A_224, B_223) | ~v2_tex_2(B_223, A_222) | ~m1_subset_1(B_223, k1_zfmisc_1(u1_struct_0(A_222))) | ~l1_pre_topc(A_222) | ~r1_tarski(A_224, u1_struct_0(A_222)))), inference(resolution, [status(thm)], [c_14, c_779])).
% 31.97/22.23  tff(c_3867, plain, (![B_223, A_224]: (v3_pre_topc('#skF_1'('#skF_3', B_223, A_224), '#skF_3') | ~r1_tarski(A_224, B_223) | ~v2_tex_2(B_223, '#skF_3') | ~m1_subset_1(B_223, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_224, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_532, c_3855])).
% 31.97/22.23  tff(c_9942, plain, (![B_404, A_405]: (v3_pre_topc('#skF_1'('#skF_3', B_404, A_405), '#skF_3') | ~r1_tarski(A_405, B_404) | ~v2_tex_2(B_404, '#skF_3') | ~m1_subset_1(B_404, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_405, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_532, c_56, c_3867])).
% 31.97/22.23  tff(c_9965, plain, (![A_405]: (v3_pre_topc('#skF_1'('#skF_3', '#skF_6', A_405), '#skF_3') | ~r1_tarski(A_405, '#skF_6') | ~v2_tex_2('#skF_6', '#skF_3') | ~r1_tarski(A_405, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_50, c_9942])).
% 31.97/22.23  tff(c_9986, plain, (![A_405]: (v3_pre_topc('#skF_1'('#skF_3', '#skF_6', A_405), '#skF_3') | ~r1_tarski(A_405, '#skF_6') | ~r1_tarski(A_405, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_9965])).
% 31.97/22.23  tff(c_920, plain, (![A_142, B_143, C_144]: (m1_subset_1('#skF_1'(A_142, B_143, C_144), k1_zfmisc_1(u1_struct_0(A_142))) | ~r1_tarski(C_144, B_143) | ~m1_subset_1(C_144, k1_zfmisc_1(u1_struct_0(A_142))) | ~v2_tex_2(B_143, A_142) | ~m1_subset_1(B_143, k1_zfmisc_1(u1_struct_0(A_142))) | ~l1_pre_topc(A_142))), inference(cnfTransformation, [status(thm)], [f_115])).
% 31.97/22.23  tff(c_5277, plain, (![A_264, B_265, C_266]: (r1_tarski('#skF_1'(A_264, B_265, C_266), u1_struct_0(A_264)) | ~r1_tarski(C_266, B_265) | ~m1_subset_1(C_266, k1_zfmisc_1(u1_struct_0(A_264))) | ~v2_tex_2(B_265, A_264) | ~m1_subset_1(B_265, k1_zfmisc_1(u1_struct_0(A_264))) | ~l1_pre_topc(A_264))), inference(resolution, [status(thm)], [c_920, c_12])).
% 31.97/22.23  tff(c_5301, plain, (![B_265, C_266]: (r1_tarski('#skF_1'('#skF_3', B_265, C_266), u1_struct_0('#skF_4')) | ~r1_tarski(C_266, B_265) | ~m1_subset_1(C_266, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_265, '#skF_3') | ~m1_subset_1(B_265, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_532, c_5277])).
% 31.97/22.23  tff(c_19449, plain, (![B_579, C_580]: (r1_tarski('#skF_1'('#skF_3', B_579, C_580), u1_struct_0('#skF_4')) | ~r1_tarski(C_580, B_579) | ~m1_subset_1(C_580, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_579, '#skF_3') | ~m1_subset_1(B_579, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_532, c_532, c_5301])).
% 31.97/22.23  tff(c_533, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_510])).
% 31.97/22.23  tff(c_642, plain, (![D_130, C_131, A_132]: (v3_pre_topc(D_130, C_131) | ~m1_subset_1(D_130, k1_zfmisc_1(u1_struct_0(C_131))) | ~v3_pre_topc(D_130, A_132) | ~m1_pre_topc(C_131, A_132) | ~m1_subset_1(D_130, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132))), inference(cnfTransformation, [status(thm)], [f_83])).
% 31.97/22.23  tff(c_3356, plain, (![A_206, C_207, A_208]: (v3_pre_topc(A_206, C_207) | ~v3_pre_topc(A_206, A_208) | ~m1_pre_topc(C_207, A_208) | ~m1_subset_1(A_206, k1_zfmisc_1(u1_struct_0(A_208))) | ~l1_pre_topc(A_208) | ~r1_tarski(A_206, u1_struct_0(C_207)))), inference(resolution, [status(thm)], [c_14, c_642])).
% 31.97/22.23  tff(c_3364, plain, (![A_206]: (v3_pre_topc(A_206, '#skF_4') | ~v3_pre_topc(A_206, '#skF_3') | ~m1_subset_1(A_206, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_206, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_533, c_3356])).
% 31.97/22.23  tff(c_3544, plain, (![A_214]: (v3_pre_topc(A_214, '#skF_4') | ~v3_pre_topc(A_214, '#skF_3') | ~m1_subset_1(A_214, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_214, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_532, c_3364])).
% 31.97/22.23  tff(c_3596, plain, (![A_9]: (v3_pre_topc(A_9, '#skF_4') | ~v3_pre_topc(A_9, '#skF_3') | ~r1_tarski(A_9, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_14, c_3544])).
% 31.97/22.23  tff(c_110737, plain, (![B_1295, C_1296]: (v3_pre_topc('#skF_1'('#skF_3', B_1295, C_1296), '#skF_4') | ~v3_pre_topc('#skF_1'('#skF_3', B_1295, C_1296), '#skF_3') | ~r1_tarski(C_1296, B_1295) | ~m1_subset_1(C_1296, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_1295, '#skF_3') | ~m1_subset_1(B_1295, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_19449, c_3596])).
% 31.97/22.23  tff(c_110788, plain, (![A_405]: (v3_pre_topc('#skF_1'('#skF_3', '#skF_6', A_405), '#skF_4') | ~m1_subset_1(A_405, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2('#skF_6', '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_405, '#skF_6') | ~r1_tarski(A_405, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_9986, c_110737])).
% 31.97/22.23  tff(c_110935, plain, (![A_1300]: (v3_pre_topc('#skF_1'('#skF_3', '#skF_6', A_1300), '#skF_4') | ~m1_subset_1(A_1300, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_1300, '#skF_6') | ~r1_tarski(A_1300, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_58, c_110788])).
% 31.97/22.23  tff(c_110941, plain, (v3_pre_topc('#skF_1'('#skF_3', '#skF_6', '#skF_2'('#skF_4', '#skF_6')), '#skF_4') | ~r1_tarski('#skF_2'('#skF_4', '#skF_6'), '#skF_6') | ~r1_tarski('#skF_2'('#skF_4', '#skF_6'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_30870, c_110935])).
% 31.97/22.23  tff(c_110982, plain, (v3_pre_topc('#skF_1'('#skF_3', '#skF_6', '#skF_2'('#skF_4', '#skF_6')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22526, c_399, c_110941])).
% 31.97/22.23  tff(c_936, plain, (![B_143, C_144]: (m1_subset_1('#skF_1'('#skF_3', B_143, C_144), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(C_144, B_143) | ~m1_subset_1(C_144, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_143, '#skF_3') | ~m1_subset_1(B_143, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_532, c_920])).
% 31.97/22.23  tff(c_29676, plain, (![B_666, C_667]: (m1_subset_1('#skF_1'('#skF_3', B_666, C_667), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(C_667, B_666) | ~m1_subset_1(C_667, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_666, '#skF_3') | ~m1_subset_1(B_666, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_532, c_532, c_936])).
% 31.97/22.23  tff(c_1041, plain, (![B_104]: (k3_xboole_0(B_104, '#skF_6')!='#skF_2'('#skF_4', '#skF_6') | ~v3_pre_topc(B_104, '#skF_4') | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2('#skF_6', '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_200, c_1034])).
% 31.97/22.23  tff(c_1050, plain, (![B_104]: (k3_xboole_0(B_104, '#skF_6')!='#skF_2'('#skF_4', '#skF_6') | ~v3_pre_topc(B_104, '#skF_4') | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2('#skF_6', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_1041])).
% 31.97/22.23  tff(c_1051, plain, (![B_104]: (k3_xboole_0(B_104, '#skF_6')!='#skF_2'('#skF_4', '#skF_6') | ~v3_pre_topc(B_104, '#skF_4') | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_1050])).
% 31.97/22.23  tff(c_29811, plain, (![B_666, C_667]: (k3_xboole_0('#skF_1'('#skF_3', B_666, C_667), '#skF_6')!='#skF_2'('#skF_4', '#skF_6') | ~v3_pre_topc('#skF_1'('#skF_3', B_666, C_667), '#skF_4') | ~r1_tarski(C_667, B_666) | ~m1_subset_1(C_667, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_666, '#skF_3') | ~m1_subset_1(B_666, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_29676, c_1051])).
% 31.97/22.23  tff(c_111006, plain, (k3_xboole_0('#skF_1'('#skF_3', '#skF_6', '#skF_2'('#skF_4', '#skF_6')), '#skF_6')!='#skF_2'('#skF_4', '#skF_6') | ~r1_tarski('#skF_2'('#skF_4', '#skF_6'), '#skF_6') | ~m1_subset_1('#skF_2'('#skF_4', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2('#skF_6', '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_110982, c_29811])).
% 31.97/22.23  tff(c_111010, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_58, c_30870, c_399, c_22572, c_111006])).
% 31.97/22.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.97/22.23  
% 31.97/22.23  Inference rules
% 31.97/22.23  ----------------------
% 31.97/22.23  #Ref     : 0
% 31.97/22.23  #Sup     : 21319
% 31.97/22.23  #Fact    : 0
% 31.97/22.23  #Define  : 0
% 31.97/22.23  #Split   : 33
% 31.97/22.23  #Chain   : 0
% 31.97/22.23  #Close   : 0
% 31.97/22.23  
% 31.97/22.23  Ordering : KBO
% 31.97/22.23  
% 31.97/22.23  Simplification rules
% 31.97/22.23  ----------------------
% 31.97/22.23  #Subsume      : 4524
% 31.97/22.23  #Demod        : 37384
% 31.97/22.23  #Tautology    : 10689
% 31.97/22.23  #SimpNegUnit  : 532
% 31.97/22.23  #BackRed      : 8
% 31.97/22.23  
% 31.97/22.23  #Partial instantiations: 0
% 31.97/22.23  #Strategies tried      : 1
% 31.97/22.23  
% 31.97/22.23  Timing (in seconds)
% 31.97/22.23  ----------------------
% 31.97/22.24  Preprocessing        : 0.54
% 31.97/22.24  Parsing              : 0.27
% 31.97/22.24  CNF conversion       : 0.04
% 31.97/22.24  Main loop            : 20.77
% 31.97/22.24  Inferencing          : 4.90
% 31.97/22.24  Reduction            : 7.10
% 31.97/22.24  Demodulation         : 5.50
% 31.97/22.24  BG Simplification    : 0.44
% 31.97/22.24  Subsumption          : 7.44
% 31.97/22.24  Abstraction          : 0.90
% 31.97/22.24  MUC search           : 0.00
% 31.97/22.24  Cooper               : 0.00
% 31.97/22.24  Total                : 21.36
% 31.97/22.24  Index Insertion      : 0.00
% 31.97/22.24  Index Deletion       : 0.00
% 31.97/22.24  Index Matching       : 0.00
% 31.97/22.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
