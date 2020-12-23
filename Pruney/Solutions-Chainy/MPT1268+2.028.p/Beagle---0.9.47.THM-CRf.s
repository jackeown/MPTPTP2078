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
% DateTime   : Thu Dec  3 10:21:50 EST 2020

% Result     : Theorem 4.79s
% Output     : CNFRefutation 5.14s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 281 expanded)
%              Number of leaves         :   30 ( 105 expanded)
%              Depth                    :   12
%              Number of atoms          :  223 ( 795 expanded)
%              Number of equality atoms :   34 ( 117 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_125,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r1_tarski(C,B)
                      & v3_pre_topc(C,A) )
                   => C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_97,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( v3_pre_topc(D,B)
                     => k1_tops_1(B,D) = D )
                    & ( k1_tops_1(A,C) = C
                     => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

tff(c_40,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_68,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_748,plain,(
    ! [B_120,A_121] :
      ( v2_tops_1(B_120,A_121)
      | k1_tops_1(A_121,B_120) != k1_xboole_0
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ l1_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_755,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_748])).

tff(c_759,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_755])).

tff(c_760,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_759])).

tff(c_295,plain,(
    ! [A_85,B_86] :
      ( r1_tarski(k1_tops_1(A_85,B_86),B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_300,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_295])).

tff(c_304,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_300])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_607,plain,(
    ! [A_107,B_108] :
      ( v3_pre_topc(k1_tops_1(A_107,B_108),A_107)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107)
      | ~ v2_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_612,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_607])).

tff(c_616,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_612])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_79,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(A_58,B_59)
      | ~ m1_subset_1(A_58,k1_zfmisc_1(B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_87,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_34,c_79])).

tff(c_154,plain,(
    ! [A_71,C_72,B_73] :
      ( r1_tarski(A_71,C_72)
      | ~ r1_tarski(B_73,C_72)
      | ~ r1_tarski(A_71,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_217,plain,(
    ! [A_78] :
      ( r1_tarski(A_78,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_78,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_87,c_154])).

tff(c_10,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(B_7,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_335,plain,(
    ! [A_88,A_89] :
      ( r1_tarski(A_88,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_88,A_89)
      | ~ r1_tarski(A_89,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_217,c_10])).

tff(c_337,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_304,c_335])).

tff(c_352,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_337])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_58,plain,(
    ! [C_51] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_51
      | ~ v3_pre_topc(C_51,'#skF_1')
      | ~ r1_tarski(C_51,'#skF_2')
      | ~ m1_subset_1(C_51,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_204,plain,(
    ! [C_77] :
      ( k1_xboole_0 = C_77
      | ~ v3_pre_topc(C_77,'#skF_1')
      | ~ r1_tarski(C_77,'#skF_2')
      | ~ m1_subset_1(C_77,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_58])).

tff(c_771,plain,(
    ! [A_127] :
      ( k1_xboole_0 = A_127
      | ~ v3_pre_topc(A_127,'#skF_1')
      | ~ r1_tarski(A_127,'#skF_2')
      | ~ r1_tarski(A_127,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_18,c_204])).

tff(c_785,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_352,c_771])).

tff(c_813,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_616,c_785])).

tff(c_815,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_760,c_813])).

tff(c_816,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_817,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_44,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_821,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_817,c_44])).

tff(c_42,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_819,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_817,c_42])).

tff(c_46,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_842,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_817,c_46])).

tff(c_12,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_847,plain,(
    ! [A_134,C_135,B_136] :
      ( r1_tarski(k3_xboole_0(A_134,C_135),B_136)
      | ~ r1_tarski(A_134,B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_851,plain,(
    ! [B_137,A_138] :
      ( r1_tarski(k1_xboole_0,B_137)
      | ~ r1_tarski(A_138,B_137) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_847])).

tff(c_866,plain,(
    ! [B_2] : r1_tarski(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_851])).

tff(c_1013,plain,(
    ! [A_154,B_155] :
      ( r1_tarski(k1_tops_1(A_154,B_155),B_155)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_pre_topc(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1610,plain,(
    ! [A_188,A_189] :
      ( r1_tarski(k1_tops_1(A_188,A_189),A_189)
      | ~ l1_pre_topc(A_188)
      | ~ r1_tarski(A_189,u1_struct_0(A_188)) ) ),
    inference(resolution,[status(thm)],[c_18,c_1013])).

tff(c_874,plain,(
    ! [B_140,A_141] :
      ( B_140 = A_141
      | ~ r1_tarski(B_140,A_141)
      | ~ r1_tarski(A_141,B_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_887,plain,(
    ! [B_2] :
      ( k1_xboole_0 = B_2
      | ~ r1_tarski(B_2,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_866,c_874])).

tff(c_1640,plain,(
    ! [A_188] :
      ( k1_tops_1(A_188,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_188)
      | ~ r1_tarski(k1_xboole_0,u1_struct_0(A_188)) ) ),
    inference(resolution,[status(thm)],[c_1610,c_887])).

tff(c_1665,plain,(
    ! [A_190] :
      ( k1_tops_1(A_190,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_866,c_1640])).

tff(c_1669,plain,(
    k1_tops_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_1665])).

tff(c_24,plain,(
    ! [A_19,B_23,C_25] :
      ( r1_tarski(k1_tops_1(A_19,B_23),k1_tops_1(A_19,C_25))
      | ~ r1_tarski(B_23,C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1679,plain,(
    ! [B_23] :
      ( r1_tarski(k1_tops_1('#skF_1',B_23),k1_xboole_0)
      | ~ r1_tarski(B_23,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1669,c_24])).

tff(c_1687,plain,(
    ! [B_23] :
      ( r1_tarski(k1_tops_1('#skF_1',B_23),k1_xboole_0)
      | ~ r1_tarski(B_23,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1679])).

tff(c_1689,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1687])).

tff(c_1692,plain,(
    ~ r1_tarski(k1_xboole_0,u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_18,c_1689])).

tff(c_1696,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_866,c_1692])).

tff(c_1698,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1687])).

tff(c_28,plain,(
    ! [B_34,D_40,C_38,A_26] :
      ( k1_tops_1(B_34,D_40) = D_40
      | ~ v3_pre_topc(D_40,B_34)
      | ~ m1_subset_1(D_40,k1_zfmisc_1(u1_struct_0(B_34)))
      | ~ m1_subset_1(C_38,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(B_34)
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2232,plain,(
    ! [C_227,A_228] :
      ( ~ m1_subset_1(C_227,k1_zfmisc_1(u1_struct_0(A_228)))
      | ~ l1_pre_topc(A_228)
      | ~ v2_pre_topc(A_228) ) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_2235,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1698,c_2232])).

tff(c_2249,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_2235])).

tff(c_2472,plain,(
    ! [B_245,D_246] :
      ( k1_tops_1(B_245,D_246) = D_246
      | ~ v3_pre_topc(D_246,B_245)
      | ~ m1_subset_1(D_246,k1_zfmisc_1(u1_struct_0(B_245)))
      | ~ l1_pre_topc(B_245) ) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_2478,plain,
    ( k1_tops_1('#skF_1','#skF_3') = '#skF_3'
    | ~ v3_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_842,c_2472])).

tff(c_2491,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_819,c_2478])).

tff(c_1015,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_842,c_1013])).

tff(c_1023,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1015])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1033,plain,
    ( k1_tops_1('#skF_1','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1023,c_2])).

tff(c_1138,plain,(
    ~ r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1033])).

tff(c_2510,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2491,c_1138])).

tff(c_2518,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2510])).

tff(c_2519,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1033])).

tff(c_2612,plain,(
    ! [A_252,B_253] :
      ( k1_tops_1(A_252,B_253) = k1_xboole_0
      | ~ v2_tops_1(B_253,A_252)
      | ~ m1_subset_1(B_253,k1_zfmisc_1(u1_struct_0(A_252)))
      | ~ l1_pre_topc(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2622,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_2612])).

tff(c_2630,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_817,c_2622])).

tff(c_3228,plain,(
    ! [A_297,B_298,C_299] :
      ( r1_tarski(k1_tops_1(A_297,B_298),k1_tops_1(A_297,C_299))
      | ~ r1_tarski(B_298,C_299)
      | ~ m1_subset_1(C_299,k1_zfmisc_1(u1_struct_0(A_297)))
      | ~ m1_subset_1(B_298,k1_zfmisc_1(u1_struct_0(A_297)))
      | ~ l1_pre_topc(A_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3253,plain,(
    ! [B_298] :
      ( r1_tarski(k1_tops_1('#skF_1',B_298),k1_xboole_0)
      | ~ r1_tarski(B_298,'#skF_2')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_298,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2630,c_3228])).

tff(c_3768,plain,(
    ! [B_335] :
      ( r1_tarski(k1_tops_1('#skF_1',B_335),k1_xboole_0)
      | ~ r1_tarski(B_335,'#skF_2')
      | ~ m1_subset_1(B_335,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_3253])).

tff(c_3774,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_842,c_3768])).

tff(c_3787,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_821,c_2519,c_3774])).

tff(c_3808,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3787,c_887])).

tff(c_3829,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_816,c_3808])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:41:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.79/1.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.79/1.90  
% 4.79/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.79/1.91  %$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.79/1.91  
% 4.79/1.91  %Foreground sorts:
% 4.79/1.91  
% 4.79/1.91  
% 4.79/1.91  %Background operators:
% 4.79/1.91  
% 4.79/1.91  
% 4.79/1.91  %Foreground operators:
% 4.79/1.91  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.79/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.79/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.79/1.91  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 4.79/1.91  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.79/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.79/1.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.79/1.91  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.79/1.91  tff('#skF_2', type, '#skF_2': $i).
% 4.79/1.91  tff('#skF_3', type, '#skF_3': $i).
% 4.79/1.91  tff('#skF_1', type, '#skF_1': $i).
% 4.79/1.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.79/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.79/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.79/1.91  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.79/1.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.79/1.91  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.79/1.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.79/1.91  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.79/1.91  
% 5.14/1.93  tff(f_125, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tops_1)).
% 5.14/1.93  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 5.14/1.93  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 5.14/1.93  tff(f_57, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 5.14/1.93  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.14/1.93  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.14/1.93  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.14/1.93  tff(f_43, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 5.14/1.93  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 5.14/1.93  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 5.14/1.93  tff(f_97, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 5.14/1.93  tff(c_40, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.14/1.93  tff(c_68, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_40])).
% 5.14/1.93  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.14/1.93  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.14/1.93  tff(c_748, plain, (![B_120, A_121]: (v2_tops_1(B_120, A_121) | k1_tops_1(A_121, B_120)!=k1_xboole_0 | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_121))) | ~l1_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.14/1.93  tff(c_755, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_748])).
% 5.14/1.93  tff(c_759, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_755])).
% 5.14/1.93  tff(c_760, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_759])).
% 5.14/1.93  tff(c_295, plain, (![A_85, B_86]: (r1_tarski(k1_tops_1(A_85, B_86), B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.14/1.93  tff(c_300, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_295])).
% 5.14/1.93  tff(c_304, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_300])).
% 5.14/1.93  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.14/1.93  tff(c_607, plain, (![A_107, B_108]: (v3_pre_topc(k1_tops_1(A_107, B_108), A_107) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107) | ~v2_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.14/1.93  tff(c_612, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_607])).
% 5.14/1.93  tff(c_616, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_612])).
% 5.14/1.93  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.14/1.93  tff(c_79, plain, (![A_58, B_59]: (r1_tarski(A_58, B_59) | ~m1_subset_1(A_58, k1_zfmisc_1(B_59)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.14/1.93  tff(c_87, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_79])).
% 5.14/1.93  tff(c_154, plain, (![A_71, C_72, B_73]: (r1_tarski(A_71, C_72) | ~r1_tarski(B_73, C_72) | ~r1_tarski(A_71, B_73))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.14/1.93  tff(c_217, plain, (![A_78]: (r1_tarski(A_78, u1_struct_0('#skF_1')) | ~r1_tarski(A_78, '#skF_2'))), inference(resolution, [status(thm)], [c_87, c_154])).
% 5.14/1.93  tff(c_10, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(B_7, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.14/1.93  tff(c_335, plain, (![A_88, A_89]: (r1_tarski(A_88, u1_struct_0('#skF_1')) | ~r1_tarski(A_88, A_89) | ~r1_tarski(A_89, '#skF_2'))), inference(resolution, [status(thm)], [c_217, c_10])).
% 5.14/1.93  tff(c_337, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_304, c_335])).
% 5.14/1.93  tff(c_352, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_337])).
% 5.14/1.93  tff(c_18, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.14/1.93  tff(c_58, plain, (![C_51]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_51 | ~v3_pre_topc(C_51, '#skF_1') | ~r1_tarski(C_51, '#skF_2') | ~m1_subset_1(C_51, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.14/1.93  tff(c_204, plain, (![C_77]: (k1_xboole_0=C_77 | ~v3_pre_topc(C_77, '#skF_1') | ~r1_tarski(C_77, '#skF_2') | ~m1_subset_1(C_77, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_58])).
% 5.14/1.93  tff(c_771, plain, (![A_127]: (k1_xboole_0=A_127 | ~v3_pre_topc(A_127, '#skF_1') | ~r1_tarski(A_127, '#skF_2') | ~r1_tarski(A_127, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_18, c_204])).
% 5.14/1.93  tff(c_785, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_352, c_771])).
% 5.14/1.93  tff(c_813, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_304, c_616, c_785])).
% 5.14/1.93  tff(c_815, plain, $false, inference(negUnitSimplification, [status(thm)], [c_760, c_813])).
% 5.14/1.93  tff(c_816, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_40])).
% 5.14/1.93  tff(c_817, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_40])).
% 5.14/1.93  tff(c_44, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.14/1.93  tff(c_821, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_817, c_44])).
% 5.14/1.93  tff(c_42, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.14/1.93  tff(c_819, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_817, c_42])).
% 5.14/1.93  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.14/1.93  tff(c_842, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_817, c_46])).
% 5.14/1.93  tff(c_12, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.14/1.93  tff(c_847, plain, (![A_134, C_135, B_136]: (r1_tarski(k3_xboole_0(A_134, C_135), B_136) | ~r1_tarski(A_134, B_136))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.14/1.93  tff(c_851, plain, (![B_137, A_138]: (r1_tarski(k1_xboole_0, B_137) | ~r1_tarski(A_138, B_137))), inference(superposition, [status(thm), theory('equality')], [c_12, c_847])).
% 5.14/1.93  tff(c_866, plain, (![B_2]: (r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_851])).
% 5.14/1.93  tff(c_1013, plain, (![A_154, B_155]: (r1_tarski(k1_tops_1(A_154, B_155), B_155) | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0(A_154))) | ~l1_pre_topc(A_154))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.14/1.93  tff(c_1610, plain, (![A_188, A_189]: (r1_tarski(k1_tops_1(A_188, A_189), A_189) | ~l1_pre_topc(A_188) | ~r1_tarski(A_189, u1_struct_0(A_188)))), inference(resolution, [status(thm)], [c_18, c_1013])).
% 5.14/1.93  tff(c_874, plain, (![B_140, A_141]: (B_140=A_141 | ~r1_tarski(B_140, A_141) | ~r1_tarski(A_141, B_140))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.14/1.93  tff(c_887, plain, (![B_2]: (k1_xboole_0=B_2 | ~r1_tarski(B_2, k1_xboole_0))), inference(resolution, [status(thm)], [c_866, c_874])).
% 5.14/1.93  tff(c_1640, plain, (![A_188]: (k1_tops_1(A_188, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_188) | ~r1_tarski(k1_xboole_0, u1_struct_0(A_188)))), inference(resolution, [status(thm)], [c_1610, c_887])).
% 5.14/1.93  tff(c_1665, plain, (![A_190]: (k1_tops_1(A_190, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_190))), inference(demodulation, [status(thm), theory('equality')], [c_866, c_1640])).
% 5.14/1.93  tff(c_1669, plain, (k1_tops_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_1665])).
% 5.14/1.93  tff(c_24, plain, (![A_19, B_23, C_25]: (r1_tarski(k1_tops_1(A_19, B_23), k1_tops_1(A_19, C_25)) | ~r1_tarski(B_23, C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(u1_struct_0(A_19))) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.14/1.93  tff(c_1679, plain, (![B_23]: (r1_tarski(k1_tops_1('#skF_1', B_23), k1_xboole_0) | ~r1_tarski(B_23, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1669, c_24])).
% 5.14/1.93  tff(c_1687, plain, (![B_23]: (r1_tarski(k1_tops_1('#skF_1', B_23), k1_xboole_0) | ~r1_tarski(B_23, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1679])).
% 5.14/1.93  tff(c_1689, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1687])).
% 5.14/1.93  tff(c_1692, plain, (~r1_tarski(k1_xboole_0, u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_1689])).
% 5.14/1.93  tff(c_1696, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_866, c_1692])).
% 5.14/1.93  tff(c_1698, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1687])).
% 5.14/1.93  tff(c_28, plain, (![B_34, D_40, C_38, A_26]: (k1_tops_1(B_34, D_40)=D_40 | ~v3_pre_topc(D_40, B_34) | ~m1_subset_1(D_40, k1_zfmisc_1(u1_struct_0(B_34))) | ~m1_subset_1(C_38, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(B_34) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.14/1.93  tff(c_2232, plain, (![C_227, A_228]: (~m1_subset_1(C_227, k1_zfmisc_1(u1_struct_0(A_228))) | ~l1_pre_topc(A_228) | ~v2_pre_topc(A_228))), inference(splitLeft, [status(thm)], [c_28])).
% 5.14/1.93  tff(c_2235, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1698, c_2232])).
% 5.14/1.93  tff(c_2249, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_2235])).
% 5.14/1.93  tff(c_2472, plain, (![B_245, D_246]: (k1_tops_1(B_245, D_246)=D_246 | ~v3_pre_topc(D_246, B_245) | ~m1_subset_1(D_246, k1_zfmisc_1(u1_struct_0(B_245))) | ~l1_pre_topc(B_245))), inference(splitRight, [status(thm)], [c_28])).
% 5.14/1.93  tff(c_2478, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3' | ~v3_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_842, c_2472])).
% 5.14/1.93  tff(c_2491, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_819, c_2478])).
% 5.14/1.93  tff(c_1015, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_842, c_1013])).
% 5.14/1.93  tff(c_1023, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1015])).
% 5.14/1.93  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.14/1.93  tff(c_1033, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_1023, c_2])).
% 5.14/1.93  tff(c_1138, plain, (~r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1033])).
% 5.14/1.93  tff(c_2510, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2491, c_1138])).
% 5.14/1.93  tff(c_2518, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2510])).
% 5.14/1.93  tff(c_2519, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_1033])).
% 5.14/1.93  tff(c_2612, plain, (![A_252, B_253]: (k1_tops_1(A_252, B_253)=k1_xboole_0 | ~v2_tops_1(B_253, A_252) | ~m1_subset_1(B_253, k1_zfmisc_1(u1_struct_0(A_252))) | ~l1_pre_topc(A_252))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.14/1.93  tff(c_2622, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_2612])).
% 5.14/1.93  tff(c_2630, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_817, c_2622])).
% 5.14/1.93  tff(c_3228, plain, (![A_297, B_298, C_299]: (r1_tarski(k1_tops_1(A_297, B_298), k1_tops_1(A_297, C_299)) | ~r1_tarski(B_298, C_299) | ~m1_subset_1(C_299, k1_zfmisc_1(u1_struct_0(A_297))) | ~m1_subset_1(B_298, k1_zfmisc_1(u1_struct_0(A_297))) | ~l1_pre_topc(A_297))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.14/1.93  tff(c_3253, plain, (![B_298]: (r1_tarski(k1_tops_1('#skF_1', B_298), k1_xboole_0) | ~r1_tarski(B_298, '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_298, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2630, c_3228])).
% 5.14/1.93  tff(c_3768, plain, (![B_335]: (r1_tarski(k1_tops_1('#skF_1', B_335), k1_xboole_0) | ~r1_tarski(B_335, '#skF_2') | ~m1_subset_1(B_335, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_3253])).
% 5.14/1.93  tff(c_3774, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_842, c_3768])).
% 5.14/1.93  tff(c_3787, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_821, c_2519, c_3774])).
% 5.14/1.93  tff(c_3808, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3787, c_887])).
% 5.14/1.93  tff(c_3829, plain, $false, inference(negUnitSimplification, [status(thm)], [c_816, c_3808])).
% 5.14/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.14/1.93  
% 5.14/1.93  Inference rules
% 5.14/1.93  ----------------------
% 5.14/1.93  #Ref     : 0
% 5.14/1.93  #Sup     : 873
% 5.14/1.93  #Fact    : 0
% 5.14/1.93  #Define  : 0
% 5.14/1.93  #Split   : 21
% 5.14/1.93  #Chain   : 0
% 5.14/1.93  #Close   : 0
% 5.14/1.93  
% 5.14/1.93  Ordering : KBO
% 5.14/1.93  
% 5.14/1.93  Simplification rules
% 5.14/1.93  ----------------------
% 5.14/1.93  #Subsume      : 342
% 5.14/1.93  #Demod        : 493
% 5.14/1.93  #Tautology    : 268
% 5.14/1.93  #SimpNegUnit  : 9
% 5.14/1.93  #BackRed      : 22
% 5.14/1.93  
% 5.14/1.93  #Partial instantiations: 0
% 5.14/1.93  #Strategies tried      : 1
% 5.14/1.93  
% 5.14/1.93  Timing (in seconds)
% 5.14/1.93  ----------------------
% 5.14/1.93  Preprocessing        : 0.34
% 5.14/1.93  Parsing              : 0.18
% 5.14/1.93  CNF conversion       : 0.02
% 5.14/1.93  Main loop            : 0.82
% 5.14/1.93  Inferencing          : 0.26
% 5.14/1.93  Reduction            : 0.28
% 5.14/1.93  Demodulation         : 0.20
% 5.14/1.93  BG Simplification    : 0.03
% 5.14/1.93  Subsumption          : 0.19
% 5.14/1.93  Abstraction          : 0.04
% 5.14/1.93  MUC search           : 0.00
% 5.14/1.93  Cooper               : 0.00
% 5.14/1.93  Total                : 1.21
% 5.14/1.93  Index Insertion      : 0.00
% 5.14/1.93  Index Deletion       : 0.00
% 5.14/1.93  Index Matching       : 0.00
% 5.14/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
