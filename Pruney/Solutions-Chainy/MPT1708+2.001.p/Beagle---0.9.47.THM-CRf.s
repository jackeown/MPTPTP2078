%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:27 EST 2020

% Result     : Theorem 3.98s
% Output     : CNFRefutation 4.40s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 333 expanded)
%              Number of leaves         :   35 ( 139 expanded)
%              Depth                    :   19
%              Number of atoms          :  446 (1857 expanded)
%              Number of equality atoms :   17 ( 168 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k2_tsep_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_tsep_1,type,(
    k2_tsep_1: ( $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_156,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ( ~ r1_tsep_1(B,C)
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(k2_tsep_1(A,B,C)))
                     => ( ? [E] :
                            ( m1_subset_1(E,u1_struct_0(B))
                            & E = D )
                        & ? [E] :
                            ( m1_subset_1(E,u1_struct_0(C))
                            & E = D ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tmap_1)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k2_tsep_1(A,B,C))
        & v1_pre_topc(k2_tsep_1(A,B,C))
        & m1_pre_topc(k2_tsep_1(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_98,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( ~ r1_tsep_1(B,C)
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & v1_pre_topc(D)
                      & m1_pre_topc(D,A) )
                   => ( D = k2_tsep_1(A,B,C)
                    <=> u1_struct_0(D) = k3_xboole_0(u1_struct_0(B),u1_struct_0(C)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tsep_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_66,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_38,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_42,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_713,plain,(
    ! [A_215,B_216,C_217] :
      ( m1_pre_topc(k2_tsep_1(A_215,B_216,C_217),A_215)
      | ~ m1_pre_topc(C_217,A_215)
      | v2_struct_0(C_217)
      | ~ m1_pre_topc(B_216,A_215)
      | v2_struct_0(B_216)
      | ~ l1_pre_topc(A_215)
      | v2_struct_0(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_18,plain,(
    ! [B_17,A_15] :
      ( l1_pre_topc(B_17)
      | ~ m1_pre_topc(B_17,A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_717,plain,(
    ! [A_215,B_216,C_217] :
      ( l1_pre_topc(k2_tsep_1(A_215,B_216,C_217))
      | ~ m1_pre_topc(C_217,A_215)
      | v2_struct_0(C_217)
      | ~ m1_pre_topc(B_216,A_215)
      | v2_struct_0(B_216)
      | ~ l1_pre_topc(A_215)
      | v2_struct_0(A_215) ) ),
    inference(resolution,[status(thm)],[c_713,c_18])).

tff(c_16,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_36,plain,(
    ~ r1_tsep_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_178,plain,(
    ! [A_125,B_126,C_127] :
      ( m1_pre_topc(k2_tsep_1(A_125,B_126,C_127),A_125)
      | ~ m1_pre_topc(C_127,A_125)
      | v2_struct_0(C_127)
      | ~ m1_pre_topc(B_126,A_125)
      | v2_struct_0(B_126)
      | ~ l1_pre_topc(A_125)
      | v2_struct_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_182,plain,(
    ! [A_125,B_126,C_127] :
      ( l1_pre_topc(k2_tsep_1(A_125,B_126,C_127))
      | ~ m1_pre_topc(C_127,A_125)
      | v2_struct_0(C_127)
      | ~ m1_pre_topc(B_126,A_125)
      | v2_struct_0(B_126)
      | ~ l1_pre_topc(A_125)
      | v2_struct_0(A_125) ) ),
    inference(resolution,[status(thm)],[c_178,c_18])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_28,plain,(
    ! [A_34,B_35,C_36] :
      ( v1_pre_topc(k2_tsep_1(A_34,B_35,C_36))
      | ~ m1_pre_topc(C_36,A_34)
      | v2_struct_0(C_36)
      | ~ m1_pre_topc(B_35,A_34)
      | v2_struct_0(B_35)
      | ~ l1_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_26,plain,(
    ! [A_34,B_35,C_36] :
      ( m1_pre_topc(k2_tsep_1(A_34,B_35,C_36),A_34)
      | ~ m1_pre_topc(C_36,A_34)
      | v2_struct_0(C_36)
      | ~ m1_pre_topc(B_35,A_34)
      | v2_struct_0(B_35)
      | ~ l1_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_198,plain,(
    ! [A_139,B_140,C_141] :
      ( u1_struct_0(k2_tsep_1(A_139,B_140,C_141)) = k3_xboole_0(u1_struct_0(B_140),u1_struct_0(C_141))
      | ~ m1_pre_topc(k2_tsep_1(A_139,B_140,C_141),A_139)
      | ~ v1_pre_topc(k2_tsep_1(A_139,B_140,C_141))
      | v2_struct_0(k2_tsep_1(A_139,B_140,C_141))
      | r1_tsep_1(B_140,C_141)
      | ~ m1_pre_topc(C_141,A_139)
      | v2_struct_0(C_141)
      | ~ m1_pre_topc(B_140,A_139)
      | v2_struct_0(B_140)
      | ~ l1_pre_topc(A_139)
      | v2_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_202,plain,(
    ! [A_142,B_143,C_144] :
      ( u1_struct_0(k2_tsep_1(A_142,B_143,C_144)) = k3_xboole_0(u1_struct_0(B_143),u1_struct_0(C_144))
      | ~ v1_pre_topc(k2_tsep_1(A_142,B_143,C_144))
      | v2_struct_0(k2_tsep_1(A_142,B_143,C_144))
      | r1_tsep_1(B_143,C_144)
      | ~ m1_pre_topc(C_144,A_142)
      | v2_struct_0(C_144)
      | ~ m1_pre_topc(B_143,A_142)
      | v2_struct_0(B_143)
      | ~ l1_pre_topc(A_142)
      | v2_struct_0(A_142) ) ),
    inference(resolution,[status(thm)],[c_26,c_198])).

tff(c_30,plain,(
    ! [A_34,B_35,C_36] :
      ( ~ v2_struct_0(k2_tsep_1(A_34,B_35,C_36))
      | ~ m1_pre_topc(C_36,A_34)
      | v2_struct_0(C_36)
      | ~ m1_pre_topc(B_35,A_34)
      | v2_struct_0(B_35)
      | ~ l1_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_282,plain,(
    ! [A_145,B_146,C_147] :
      ( u1_struct_0(k2_tsep_1(A_145,B_146,C_147)) = k3_xboole_0(u1_struct_0(B_146),u1_struct_0(C_147))
      | ~ v1_pre_topc(k2_tsep_1(A_145,B_146,C_147))
      | r1_tsep_1(B_146,C_147)
      | ~ m1_pre_topc(C_147,A_145)
      | v2_struct_0(C_147)
      | ~ m1_pre_topc(B_146,A_145)
      | v2_struct_0(B_146)
      | ~ l1_pre_topc(A_145)
      | v2_struct_0(A_145) ) ),
    inference(resolution,[status(thm)],[c_202,c_30])).

tff(c_286,plain,(
    ! [A_148,B_149,C_150] :
      ( u1_struct_0(k2_tsep_1(A_148,B_149,C_150)) = k3_xboole_0(u1_struct_0(B_149),u1_struct_0(C_150))
      | r1_tsep_1(B_149,C_150)
      | ~ m1_pre_topc(C_150,A_148)
      | v2_struct_0(C_150)
      | ~ m1_pre_topc(B_149,A_148)
      | v2_struct_0(B_149)
      | ~ l1_pre_topc(A_148)
      | v2_struct_0(A_148) ) ),
    inference(resolution,[status(thm)],[c_28,c_282])).

tff(c_53,plain,(
    ! [B_83,A_84] : k3_xboole_0(B_83,A_84) = k3_xboole_0(A_84,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_68,plain,(
    ! [B_83,A_84] : r1_tarski(k3_xboole_0(B_83,A_84),A_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_4])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_133,plain,(
    ! [A_98,C_99,B_100] :
      ( m1_subset_1(A_98,C_99)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(C_99))
      | ~ r2_hidden(A_98,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_138,plain,(
    ! [A_104,B_105,A_106] :
      ( m1_subset_1(A_104,B_105)
      | ~ r2_hidden(A_104,A_106)
      | ~ r1_tarski(A_106,B_105) ) ),
    inference(resolution,[status(thm)],[c_12,c_133])).

tff(c_142,plain,(
    ! [A_107,B_108,B_109] :
      ( m1_subset_1(A_107,B_108)
      | ~ r1_tarski(B_109,B_108)
      | v1_xboole_0(B_109)
      | ~ m1_subset_1(A_107,B_109) ) ),
    inference(resolution,[status(thm)],[c_8,c_138])).

tff(c_147,plain,(
    ! [A_107,A_84,B_83] :
      ( m1_subset_1(A_107,A_84)
      | v1_xboole_0(k3_xboole_0(B_83,A_84))
      | ~ m1_subset_1(A_107,k3_xboole_0(B_83,A_84)) ) ),
    inference(resolution,[status(thm)],[c_68,c_142])).

tff(c_547,plain,(
    ! [A_169,C_170,B_171,A_172] :
      ( m1_subset_1(A_169,u1_struct_0(C_170))
      | v1_xboole_0(k3_xboole_0(u1_struct_0(B_171),u1_struct_0(C_170)))
      | ~ m1_subset_1(A_169,u1_struct_0(k2_tsep_1(A_172,B_171,C_170)))
      | r1_tsep_1(B_171,C_170)
      | ~ m1_pre_topc(C_170,A_172)
      | v2_struct_0(C_170)
      | ~ m1_pre_topc(B_171,A_172)
      | v2_struct_0(B_171)
      | ~ l1_pre_topc(A_172)
      | v2_struct_0(A_172) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_147])).

tff(c_553,plain,
    ( m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))
    | r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_547])).

tff(c_556,plain,
    ( m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))
    | r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_38,c_2,c_553])).

tff(c_557,plain,
    ( m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_44,c_40,c_36,c_556])).

tff(c_558,plain,(
    v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_557])).

tff(c_395,plain,(
    ! [A_160,B_161,C_162] :
      ( u1_struct_0(k2_tsep_1(A_160,B_161,C_162)) = k3_xboole_0(u1_struct_0(C_162),u1_struct_0(B_161))
      | r1_tsep_1(B_161,C_162)
      | ~ m1_pre_topc(C_162,A_160)
      | v2_struct_0(C_162)
      | ~ m1_pre_topc(B_161,A_160)
      | v2_struct_0(B_161)
      | ~ l1_pre_topc(A_160)
      | v2_struct_0(A_160) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_286])).

tff(c_20,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(u1_struct_0(A_18))
      | ~ l1_struct_0(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_462,plain,(
    ! [C_162,B_161,A_160] :
      ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(C_162),u1_struct_0(B_161)))
      | ~ l1_struct_0(k2_tsep_1(A_160,B_161,C_162))
      | v2_struct_0(k2_tsep_1(A_160,B_161,C_162))
      | r1_tsep_1(B_161,C_162)
      | ~ m1_pre_topc(C_162,A_160)
      | v2_struct_0(C_162)
      | ~ m1_pre_topc(B_161,A_160)
      | v2_struct_0(B_161)
      | ~ l1_pre_topc(A_160)
      | v2_struct_0(A_160) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_395,c_20])).

tff(c_560,plain,(
    ! [A_160] :
      ( ~ l1_struct_0(k2_tsep_1(A_160,'#skF_2','#skF_3'))
      | v2_struct_0(k2_tsep_1(A_160,'#skF_2','#skF_3'))
      | r1_tsep_1('#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_160)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_160)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_160)
      | v2_struct_0(A_160) ) ),
    inference(resolution,[status(thm)],[c_558,c_462])).

tff(c_595,plain,(
    ! [A_174] :
      ( ~ l1_struct_0(k2_tsep_1(A_174,'#skF_2','#skF_3'))
      | v2_struct_0(k2_tsep_1(A_174,'#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_174)
      | ~ m1_pre_topc('#skF_2',A_174)
      | ~ l1_pre_topc(A_174)
      | v2_struct_0(A_174) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_40,c_36,c_560])).

tff(c_598,plain,(
    ! [A_174] :
      ( v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(k2_tsep_1(A_174,'#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_174)
      | ~ m1_pre_topc('#skF_2',A_174)
      | ~ l1_pre_topc(A_174)
      | v2_struct_0(A_174) ) ),
    inference(resolution,[status(thm)],[c_595,c_30])).

tff(c_602,plain,(
    ! [A_175] :
      ( ~ l1_struct_0(k2_tsep_1(A_175,'#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_175)
      | ~ m1_pre_topc('#skF_2',A_175)
      | ~ l1_pre_topc(A_175)
      | v2_struct_0(A_175) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_40,c_598])).

tff(c_607,plain,(
    ! [A_176] :
      ( ~ m1_pre_topc('#skF_3',A_176)
      | ~ m1_pre_topc('#skF_2',A_176)
      | ~ l1_pre_topc(A_176)
      | v2_struct_0(A_176)
      | ~ l1_pre_topc(k2_tsep_1(A_176,'#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_16,c_602])).

tff(c_611,plain,(
    ! [A_125] :
      ( ~ m1_pre_topc('#skF_3',A_125)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_125)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_125)
      | v2_struct_0(A_125) ) ),
    inference(resolution,[status(thm)],[c_182,c_607])).

tff(c_615,plain,(
    ! [A_177] :
      ( ~ m1_pre_topc('#skF_3',A_177)
      | ~ m1_pre_topc('#skF_2',A_177)
      | ~ l1_pre_topc(A_177)
      | v2_struct_0(A_177) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_40,c_611])).

tff(c_618,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_615])).

tff(c_621,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_38,c_618])).

tff(c_623,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_621])).

tff(c_625,plain,(
    ~ v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_557])).

tff(c_32,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_125,plain,(
    ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_148,plain,(
    ! [A_107,A_3,B_4] :
      ( m1_subset_1(A_107,A_3)
      | v1_xboole_0(k3_xboole_0(A_3,B_4))
      | ~ m1_subset_1(A_107,k3_xboole_0(A_3,B_4)) ) ),
    inference(resolution,[status(thm)],[c_4,c_142])).

tff(c_647,plain,(
    ! [A_179,B_180,C_181,A_182] :
      ( m1_subset_1(A_179,u1_struct_0(B_180))
      | v1_xboole_0(k3_xboole_0(u1_struct_0(B_180),u1_struct_0(C_181)))
      | ~ m1_subset_1(A_179,u1_struct_0(k2_tsep_1(A_182,B_180,C_181)))
      | r1_tsep_1(B_180,C_181)
      | ~ m1_pre_topc(C_181,A_182)
      | v2_struct_0(C_181)
      | ~ m1_pre_topc(B_180,A_182)
      | v2_struct_0(B_180)
      | ~ l1_pre_topc(A_182)
      | v2_struct_0(A_182) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_148])).

tff(c_653,plain,
    ( m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))
    | r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_647])).

tff(c_656,plain,
    ( m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))
    | r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_38,c_2,c_653])).

tff(c_658,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_44,c_40,c_36,c_625,c_125,c_656])).

tff(c_659,plain,(
    ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_733,plain,(
    ! [A_229,B_230,C_231] :
      ( u1_struct_0(k2_tsep_1(A_229,B_230,C_231)) = k3_xboole_0(u1_struct_0(B_230),u1_struct_0(C_231))
      | ~ m1_pre_topc(k2_tsep_1(A_229,B_230,C_231),A_229)
      | ~ v1_pre_topc(k2_tsep_1(A_229,B_230,C_231))
      | v2_struct_0(k2_tsep_1(A_229,B_230,C_231))
      | r1_tsep_1(B_230,C_231)
      | ~ m1_pre_topc(C_231,A_229)
      | v2_struct_0(C_231)
      | ~ m1_pre_topc(B_230,A_229)
      | v2_struct_0(B_230)
      | ~ l1_pre_topc(A_229)
      | v2_struct_0(A_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_737,plain,(
    ! [A_232,B_233,C_234] :
      ( u1_struct_0(k2_tsep_1(A_232,B_233,C_234)) = k3_xboole_0(u1_struct_0(B_233),u1_struct_0(C_234))
      | ~ v1_pre_topc(k2_tsep_1(A_232,B_233,C_234))
      | v2_struct_0(k2_tsep_1(A_232,B_233,C_234))
      | r1_tsep_1(B_233,C_234)
      | ~ m1_pre_topc(C_234,A_232)
      | v2_struct_0(C_234)
      | ~ m1_pre_topc(B_233,A_232)
      | v2_struct_0(B_233)
      | ~ l1_pre_topc(A_232)
      | v2_struct_0(A_232) ) ),
    inference(resolution,[status(thm)],[c_26,c_733])).

tff(c_817,plain,(
    ! [A_235,B_236,C_237] :
      ( u1_struct_0(k2_tsep_1(A_235,B_236,C_237)) = k3_xboole_0(u1_struct_0(B_236),u1_struct_0(C_237))
      | ~ v1_pre_topc(k2_tsep_1(A_235,B_236,C_237))
      | r1_tsep_1(B_236,C_237)
      | ~ m1_pre_topc(C_237,A_235)
      | v2_struct_0(C_237)
      | ~ m1_pre_topc(B_236,A_235)
      | v2_struct_0(B_236)
      | ~ l1_pre_topc(A_235)
      | v2_struct_0(A_235) ) ),
    inference(resolution,[status(thm)],[c_737,c_30])).

tff(c_821,plain,(
    ! [A_238,B_239,C_240] :
      ( u1_struct_0(k2_tsep_1(A_238,B_239,C_240)) = k3_xboole_0(u1_struct_0(B_239),u1_struct_0(C_240))
      | r1_tsep_1(B_239,C_240)
      | ~ m1_pre_topc(C_240,A_238)
      | v2_struct_0(C_240)
      | ~ m1_pre_topc(B_239,A_238)
      | v2_struct_0(B_239)
      | ~ l1_pre_topc(A_238)
      | v2_struct_0(A_238) ) ),
    inference(resolution,[status(thm)],[c_28,c_817])).

tff(c_668,plain,(
    ! [A_188,C_189,B_190] :
      ( m1_subset_1(A_188,C_189)
      | ~ m1_subset_1(B_190,k1_zfmisc_1(C_189))
      | ~ r2_hidden(A_188,B_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_673,plain,(
    ! [A_194,B_195,A_196] :
      ( m1_subset_1(A_194,B_195)
      | ~ r2_hidden(A_194,A_196)
      | ~ r1_tarski(A_196,B_195) ) ),
    inference(resolution,[status(thm)],[c_12,c_668])).

tff(c_677,plain,(
    ! [A_197,B_198,B_199] :
      ( m1_subset_1(A_197,B_198)
      | ~ r1_tarski(B_199,B_198)
      | v1_xboole_0(B_199)
      | ~ m1_subset_1(A_197,B_199) ) ),
    inference(resolution,[status(thm)],[c_8,c_673])).

tff(c_682,plain,(
    ! [A_197,A_84,B_83] :
      ( m1_subset_1(A_197,A_84)
      | v1_xboole_0(k3_xboole_0(B_83,A_84))
      | ~ m1_subset_1(A_197,k3_xboole_0(B_83,A_84)) ) ),
    inference(resolution,[status(thm)],[c_68,c_677])).

tff(c_1082,plain,(
    ! [A_260,C_261,B_262,A_263] :
      ( m1_subset_1(A_260,u1_struct_0(C_261))
      | v1_xboole_0(k3_xboole_0(u1_struct_0(B_262),u1_struct_0(C_261)))
      | ~ m1_subset_1(A_260,u1_struct_0(k2_tsep_1(A_263,B_262,C_261)))
      | r1_tsep_1(B_262,C_261)
      | ~ m1_pre_topc(C_261,A_263)
      | v2_struct_0(C_261)
      | ~ m1_pre_topc(B_262,A_263)
      | v2_struct_0(B_262)
      | ~ l1_pre_topc(A_263)
      | v2_struct_0(A_263) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_821,c_682])).

tff(c_1088,plain,
    ( m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))
    | r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_1082])).

tff(c_1091,plain,
    ( m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))
    | r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_38,c_2,c_1088])).

tff(c_1092,plain,(
    v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_44,c_40,c_36,c_659,c_1091])).

tff(c_919,plain,(
    ! [A_247,B_248,C_249] :
      ( u1_struct_0(k2_tsep_1(A_247,B_248,C_249)) = k3_xboole_0(u1_struct_0(C_249),u1_struct_0(B_248))
      | r1_tsep_1(B_248,C_249)
      | ~ m1_pre_topc(C_249,A_247)
      | v2_struct_0(C_249)
      | ~ m1_pre_topc(B_248,A_247)
      | v2_struct_0(B_248)
      | ~ l1_pre_topc(A_247)
      | v2_struct_0(A_247) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_821])).

tff(c_986,plain,(
    ! [C_249,B_248,A_247] :
      ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(C_249),u1_struct_0(B_248)))
      | ~ l1_struct_0(k2_tsep_1(A_247,B_248,C_249))
      | v2_struct_0(k2_tsep_1(A_247,B_248,C_249))
      | r1_tsep_1(B_248,C_249)
      | ~ m1_pre_topc(C_249,A_247)
      | v2_struct_0(C_249)
      | ~ m1_pre_topc(B_248,A_247)
      | v2_struct_0(B_248)
      | ~ l1_pre_topc(A_247)
      | v2_struct_0(A_247) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_919,c_20])).

tff(c_1094,plain,(
    ! [A_247] :
      ( ~ l1_struct_0(k2_tsep_1(A_247,'#skF_2','#skF_3'))
      | v2_struct_0(k2_tsep_1(A_247,'#skF_2','#skF_3'))
      | r1_tsep_1('#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_247)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_247)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_247)
      | v2_struct_0(A_247) ) ),
    inference(resolution,[status(thm)],[c_1092,c_986])).

tff(c_1129,plain,(
    ! [A_265] :
      ( ~ l1_struct_0(k2_tsep_1(A_265,'#skF_2','#skF_3'))
      | v2_struct_0(k2_tsep_1(A_265,'#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_265)
      | ~ m1_pre_topc('#skF_2',A_265)
      | ~ l1_pre_topc(A_265)
      | v2_struct_0(A_265) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_40,c_36,c_1094])).

tff(c_1132,plain,(
    ! [A_265] :
      ( v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(k2_tsep_1(A_265,'#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_265)
      | ~ m1_pre_topc('#skF_2',A_265)
      | ~ l1_pre_topc(A_265)
      | v2_struct_0(A_265) ) ),
    inference(resolution,[status(thm)],[c_1129,c_30])).

tff(c_1136,plain,(
    ! [A_266] :
      ( ~ l1_struct_0(k2_tsep_1(A_266,'#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_266)
      | ~ m1_pre_topc('#skF_2',A_266)
      | ~ l1_pre_topc(A_266)
      | v2_struct_0(A_266) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_40,c_1132])).

tff(c_1142,plain,(
    ! [A_267] :
      ( ~ m1_pre_topc('#skF_3',A_267)
      | ~ m1_pre_topc('#skF_2',A_267)
      | ~ l1_pre_topc(A_267)
      | v2_struct_0(A_267)
      | ~ l1_pre_topc(k2_tsep_1(A_267,'#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_16,c_1136])).

tff(c_1146,plain,(
    ! [A_215] :
      ( ~ m1_pre_topc('#skF_3',A_215)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_215)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_215)
      | v2_struct_0(A_215) ) ),
    inference(resolution,[status(thm)],[c_717,c_1142])).

tff(c_1150,plain,(
    ! [A_268] :
      ( ~ m1_pre_topc('#skF_3',A_268)
      | ~ m1_pre_topc('#skF_2',A_268)
      | ~ l1_pre_topc(A_268)
      | v2_struct_0(A_268) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_40,c_1146])).

tff(c_1153,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1150])).

tff(c_1156,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_38,c_1153])).

tff(c_1158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1156])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:22:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.98/1.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/1.76  
% 3.98/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.40/1.76  %$ r2_hidden > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k2_tsep_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.40/1.76  
% 4.40/1.76  %Foreground sorts:
% 4.40/1.76  
% 4.40/1.76  
% 4.40/1.76  %Background operators:
% 4.40/1.76  
% 4.40/1.76  
% 4.40/1.76  %Foreground operators:
% 4.40/1.76  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.40/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.40/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.40/1.76  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.40/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.40/1.76  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.40/1.76  tff('#skF_2', type, '#skF_2': $i).
% 4.40/1.76  tff('#skF_3', type, '#skF_3': $i).
% 4.40/1.76  tff('#skF_1', type, '#skF_1': $i).
% 4.40/1.76  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.40/1.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.40/1.76  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.40/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.40/1.76  tff('#skF_4', type, '#skF_4': $i).
% 4.40/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.40/1.76  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.40/1.76  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 4.40/1.76  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.40/1.76  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 4.40/1.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.40/1.76  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.40/1.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.40/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.40/1.76  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.40/1.76  
% 4.40/1.78  tff(f_156, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (~r1_tsep_1(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(k2_tsep_1(A, B, C))) => ((?[E]: (m1_subset_1(E, u1_struct_0(B)) & (E = D))) & (?[E]: (m1_subset_1(E, u1_struct_0(C)) & (E = D))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_tmap_1)).
% 4.40/1.78  tff(f_120, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k2_tsep_1(A, B, C)) & v1_pre_topc(k2_tsep_1(A, B, C))) & m1_pre_topc(k2_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tsep_1)).
% 4.40/1.78  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.40/1.78  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.40/1.78  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.40/1.78  tff(f_98, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (~r1_tsep_1(B, C) => (![D]: (((~v2_struct_0(D) & v1_pre_topc(D)) & m1_pre_topc(D, A)) => ((D = k2_tsep_1(A, B, C)) <=> (u1_struct_0(D) = k3_xboole_0(u1_struct_0(B), u1_struct_0(C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tsep_1)).
% 4.40/1.78  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.40/1.78  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.40/1.78  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.40/1.78  tff(f_47, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 4.40/1.78  tff(f_66, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.40/1.78  tff(c_50, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.40/1.78  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.40/1.78  tff(c_38, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.40/1.78  tff(c_42, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.40/1.78  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.40/1.78  tff(c_40, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.40/1.78  tff(c_713, plain, (![A_215, B_216, C_217]: (m1_pre_topc(k2_tsep_1(A_215, B_216, C_217), A_215) | ~m1_pre_topc(C_217, A_215) | v2_struct_0(C_217) | ~m1_pre_topc(B_216, A_215) | v2_struct_0(B_216) | ~l1_pre_topc(A_215) | v2_struct_0(A_215))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.40/1.78  tff(c_18, plain, (![B_17, A_15]: (l1_pre_topc(B_17) | ~m1_pre_topc(B_17, A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.40/1.78  tff(c_717, plain, (![A_215, B_216, C_217]: (l1_pre_topc(k2_tsep_1(A_215, B_216, C_217)) | ~m1_pre_topc(C_217, A_215) | v2_struct_0(C_217) | ~m1_pre_topc(B_216, A_215) | v2_struct_0(B_216) | ~l1_pre_topc(A_215) | v2_struct_0(A_215))), inference(resolution, [status(thm)], [c_713, c_18])).
% 4.40/1.78  tff(c_16, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.40/1.78  tff(c_36, plain, (~r1_tsep_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.40/1.78  tff(c_178, plain, (![A_125, B_126, C_127]: (m1_pre_topc(k2_tsep_1(A_125, B_126, C_127), A_125) | ~m1_pre_topc(C_127, A_125) | v2_struct_0(C_127) | ~m1_pre_topc(B_126, A_125) | v2_struct_0(B_126) | ~l1_pre_topc(A_125) | v2_struct_0(A_125))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.40/1.78  tff(c_182, plain, (![A_125, B_126, C_127]: (l1_pre_topc(k2_tsep_1(A_125, B_126, C_127)) | ~m1_pre_topc(C_127, A_125) | v2_struct_0(C_127) | ~m1_pre_topc(B_126, A_125) | v2_struct_0(B_126) | ~l1_pre_topc(A_125) | v2_struct_0(A_125))), inference(resolution, [status(thm)], [c_178, c_18])).
% 4.40/1.78  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.40/1.78  tff(c_34, plain, (m1_subset_1('#skF_4', u1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.40/1.78  tff(c_28, plain, (![A_34, B_35, C_36]: (v1_pre_topc(k2_tsep_1(A_34, B_35, C_36)) | ~m1_pre_topc(C_36, A_34) | v2_struct_0(C_36) | ~m1_pre_topc(B_35, A_34) | v2_struct_0(B_35) | ~l1_pre_topc(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.40/1.78  tff(c_26, plain, (![A_34, B_35, C_36]: (m1_pre_topc(k2_tsep_1(A_34, B_35, C_36), A_34) | ~m1_pre_topc(C_36, A_34) | v2_struct_0(C_36) | ~m1_pre_topc(B_35, A_34) | v2_struct_0(B_35) | ~l1_pre_topc(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.40/1.78  tff(c_198, plain, (![A_139, B_140, C_141]: (u1_struct_0(k2_tsep_1(A_139, B_140, C_141))=k3_xboole_0(u1_struct_0(B_140), u1_struct_0(C_141)) | ~m1_pre_topc(k2_tsep_1(A_139, B_140, C_141), A_139) | ~v1_pre_topc(k2_tsep_1(A_139, B_140, C_141)) | v2_struct_0(k2_tsep_1(A_139, B_140, C_141)) | r1_tsep_1(B_140, C_141) | ~m1_pre_topc(C_141, A_139) | v2_struct_0(C_141) | ~m1_pre_topc(B_140, A_139) | v2_struct_0(B_140) | ~l1_pre_topc(A_139) | v2_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.40/1.78  tff(c_202, plain, (![A_142, B_143, C_144]: (u1_struct_0(k2_tsep_1(A_142, B_143, C_144))=k3_xboole_0(u1_struct_0(B_143), u1_struct_0(C_144)) | ~v1_pre_topc(k2_tsep_1(A_142, B_143, C_144)) | v2_struct_0(k2_tsep_1(A_142, B_143, C_144)) | r1_tsep_1(B_143, C_144) | ~m1_pre_topc(C_144, A_142) | v2_struct_0(C_144) | ~m1_pre_topc(B_143, A_142) | v2_struct_0(B_143) | ~l1_pre_topc(A_142) | v2_struct_0(A_142))), inference(resolution, [status(thm)], [c_26, c_198])).
% 4.40/1.78  tff(c_30, plain, (![A_34, B_35, C_36]: (~v2_struct_0(k2_tsep_1(A_34, B_35, C_36)) | ~m1_pre_topc(C_36, A_34) | v2_struct_0(C_36) | ~m1_pre_topc(B_35, A_34) | v2_struct_0(B_35) | ~l1_pre_topc(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.40/1.78  tff(c_282, plain, (![A_145, B_146, C_147]: (u1_struct_0(k2_tsep_1(A_145, B_146, C_147))=k3_xboole_0(u1_struct_0(B_146), u1_struct_0(C_147)) | ~v1_pre_topc(k2_tsep_1(A_145, B_146, C_147)) | r1_tsep_1(B_146, C_147) | ~m1_pre_topc(C_147, A_145) | v2_struct_0(C_147) | ~m1_pre_topc(B_146, A_145) | v2_struct_0(B_146) | ~l1_pre_topc(A_145) | v2_struct_0(A_145))), inference(resolution, [status(thm)], [c_202, c_30])).
% 4.40/1.78  tff(c_286, plain, (![A_148, B_149, C_150]: (u1_struct_0(k2_tsep_1(A_148, B_149, C_150))=k3_xboole_0(u1_struct_0(B_149), u1_struct_0(C_150)) | r1_tsep_1(B_149, C_150) | ~m1_pre_topc(C_150, A_148) | v2_struct_0(C_150) | ~m1_pre_topc(B_149, A_148) | v2_struct_0(B_149) | ~l1_pre_topc(A_148) | v2_struct_0(A_148))), inference(resolution, [status(thm)], [c_28, c_282])).
% 4.40/1.78  tff(c_53, plain, (![B_83, A_84]: (k3_xboole_0(B_83, A_84)=k3_xboole_0(A_84, B_83))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.40/1.78  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.40/1.78  tff(c_68, plain, (![B_83, A_84]: (r1_tarski(k3_xboole_0(B_83, A_84), A_84))), inference(superposition, [status(thm), theory('equality')], [c_53, c_4])).
% 4.40/1.78  tff(c_8, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.40/1.78  tff(c_12, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.40/1.78  tff(c_133, plain, (![A_98, C_99, B_100]: (m1_subset_1(A_98, C_99) | ~m1_subset_1(B_100, k1_zfmisc_1(C_99)) | ~r2_hidden(A_98, B_100))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.40/1.78  tff(c_138, plain, (![A_104, B_105, A_106]: (m1_subset_1(A_104, B_105) | ~r2_hidden(A_104, A_106) | ~r1_tarski(A_106, B_105))), inference(resolution, [status(thm)], [c_12, c_133])).
% 4.40/1.78  tff(c_142, plain, (![A_107, B_108, B_109]: (m1_subset_1(A_107, B_108) | ~r1_tarski(B_109, B_108) | v1_xboole_0(B_109) | ~m1_subset_1(A_107, B_109))), inference(resolution, [status(thm)], [c_8, c_138])).
% 4.40/1.78  tff(c_147, plain, (![A_107, A_84, B_83]: (m1_subset_1(A_107, A_84) | v1_xboole_0(k3_xboole_0(B_83, A_84)) | ~m1_subset_1(A_107, k3_xboole_0(B_83, A_84)))), inference(resolution, [status(thm)], [c_68, c_142])).
% 4.40/1.78  tff(c_547, plain, (![A_169, C_170, B_171, A_172]: (m1_subset_1(A_169, u1_struct_0(C_170)) | v1_xboole_0(k3_xboole_0(u1_struct_0(B_171), u1_struct_0(C_170))) | ~m1_subset_1(A_169, u1_struct_0(k2_tsep_1(A_172, B_171, C_170))) | r1_tsep_1(B_171, C_170) | ~m1_pre_topc(C_170, A_172) | v2_struct_0(C_170) | ~m1_pre_topc(B_171, A_172) | v2_struct_0(B_171) | ~l1_pre_topc(A_172) | v2_struct_0(A_172))), inference(superposition, [status(thm), theory('equality')], [c_286, c_147])).
% 4.40/1.78  tff(c_553, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))) | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_547])).
% 4.40/1.78  tff(c_556, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))) | r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_38, c_2, c_553])).
% 4.40/1.78  tff(c_557, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_44, c_40, c_36, c_556])).
% 4.40/1.78  tff(c_558, plain, (v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_557])).
% 4.40/1.78  tff(c_395, plain, (![A_160, B_161, C_162]: (u1_struct_0(k2_tsep_1(A_160, B_161, C_162))=k3_xboole_0(u1_struct_0(C_162), u1_struct_0(B_161)) | r1_tsep_1(B_161, C_162) | ~m1_pre_topc(C_162, A_160) | v2_struct_0(C_162) | ~m1_pre_topc(B_161, A_160) | v2_struct_0(B_161) | ~l1_pre_topc(A_160) | v2_struct_0(A_160))), inference(superposition, [status(thm), theory('equality')], [c_2, c_286])).
% 4.40/1.78  tff(c_20, plain, (![A_18]: (~v1_xboole_0(u1_struct_0(A_18)) | ~l1_struct_0(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.40/1.78  tff(c_462, plain, (![C_162, B_161, A_160]: (~v1_xboole_0(k3_xboole_0(u1_struct_0(C_162), u1_struct_0(B_161))) | ~l1_struct_0(k2_tsep_1(A_160, B_161, C_162)) | v2_struct_0(k2_tsep_1(A_160, B_161, C_162)) | r1_tsep_1(B_161, C_162) | ~m1_pre_topc(C_162, A_160) | v2_struct_0(C_162) | ~m1_pre_topc(B_161, A_160) | v2_struct_0(B_161) | ~l1_pre_topc(A_160) | v2_struct_0(A_160))), inference(superposition, [status(thm), theory('equality')], [c_395, c_20])).
% 4.40/1.78  tff(c_560, plain, (![A_160]: (~l1_struct_0(k2_tsep_1(A_160, '#skF_2', '#skF_3')) | v2_struct_0(k2_tsep_1(A_160, '#skF_2', '#skF_3')) | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', A_160) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_160) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_160) | v2_struct_0(A_160))), inference(resolution, [status(thm)], [c_558, c_462])).
% 4.40/1.78  tff(c_595, plain, (![A_174]: (~l1_struct_0(k2_tsep_1(A_174, '#skF_2', '#skF_3')) | v2_struct_0(k2_tsep_1(A_174, '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', A_174) | ~m1_pre_topc('#skF_2', A_174) | ~l1_pre_topc(A_174) | v2_struct_0(A_174))), inference(negUnitSimplification, [status(thm)], [c_44, c_40, c_36, c_560])).
% 4.40/1.78  tff(c_598, plain, (![A_174]: (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | ~l1_struct_0(k2_tsep_1(A_174, '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', A_174) | ~m1_pre_topc('#skF_2', A_174) | ~l1_pre_topc(A_174) | v2_struct_0(A_174))), inference(resolution, [status(thm)], [c_595, c_30])).
% 4.40/1.78  tff(c_602, plain, (![A_175]: (~l1_struct_0(k2_tsep_1(A_175, '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', A_175) | ~m1_pre_topc('#skF_2', A_175) | ~l1_pre_topc(A_175) | v2_struct_0(A_175))), inference(negUnitSimplification, [status(thm)], [c_44, c_40, c_598])).
% 4.40/1.78  tff(c_607, plain, (![A_176]: (~m1_pre_topc('#skF_3', A_176) | ~m1_pre_topc('#skF_2', A_176) | ~l1_pre_topc(A_176) | v2_struct_0(A_176) | ~l1_pre_topc(k2_tsep_1(A_176, '#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_16, c_602])).
% 4.40/1.78  tff(c_611, plain, (![A_125]: (~m1_pre_topc('#skF_3', A_125) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_125) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_125) | v2_struct_0(A_125))), inference(resolution, [status(thm)], [c_182, c_607])).
% 4.40/1.78  tff(c_615, plain, (![A_177]: (~m1_pre_topc('#skF_3', A_177) | ~m1_pre_topc('#skF_2', A_177) | ~l1_pre_topc(A_177) | v2_struct_0(A_177))), inference(negUnitSimplification, [status(thm)], [c_44, c_40, c_611])).
% 4.40/1.78  tff(c_618, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_615])).
% 4.40/1.78  tff(c_621, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_38, c_618])).
% 4.40/1.78  tff(c_623, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_621])).
% 4.40/1.78  tff(c_625, plain, (~v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_557])).
% 4.40/1.78  tff(c_32, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.40/1.78  tff(c_125, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_32])).
% 4.40/1.78  tff(c_148, plain, (![A_107, A_3, B_4]: (m1_subset_1(A_107, A_3) | v1_xboole_0(k3_xboole_0(A_3, B_4)) | ~m1_subset_1(A_107, k3_xboole_0(A_3, B_4)))), inference(resolution, [status(thm)], [c_4, c_142])).
% 4.40/1.78  tff(c_647, plain, (![A_179, B_180, C_181, A_182]: (m1_subset_1(A_179, u1_struct_0(B_180)) | v1_xboole_0(k3_xboole_0(u1_struct_0(B_180), u1_struct_0(C_181))) | ~m1_subset_1(A_179, u1_struct_0(k2_tsep_1(A_182, B_180, C_181))) | r1_tsep_1(B_180, C_181) | ~m1_pre_topc(C_181, A_182) | v2_struct_0(C_181) | ~m1_pre_topc(B_180, A_182) | v2_struct_0(B_180) | ~l1_pre_topc(A_182) | v2_struct_0(A_182))), inference(superposition, [status(thm), theory('equality')], [c_286, c_148])).
% 4.40/1.78  tff(c_653, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))) | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_647])).
% 4.40/1.78  tff(c_656, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))) | r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_38, c_2, c_653])).
% 4.40/1.78  tff(c_658, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_44, c_40, c_36, c_625, c_125, c_656])).
% 4.40/1.78  tff(c_659, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_32])).
% 4.40/1.78  tff(c_733, plain, (![A_229, B_230, C_231]: (u1_struct_0(k2_tsep_1(A_229, B_230, C_231))=k3_xboole_0(u1_struct_0(B_230), u1_struct_0(C_231)) | ~m1_pre_topc(k2_tsep_1(A_229, B_230, C_231), A_229) | ~v1_pre_topc(k2_tsep_1(A_229, B_230, C_231)) | v2_struct_0(k2_tsep_1(A_229, B_230, C_231)) | r1_tsep_1(B_230, C_231) | ~m1_pre_topc(C_231, A_229) | v2_struct_0(C_231) | ~m1_pre_topc(B_230, A_229) | v2_struct_0(B_230) | ~l1_pre_topc(A_229) | v2_struct_0(A_229))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.40/1.78  tff(c_737, plain, (![A_232, B_233, C_234]: (u1_struct_0(k2_tsep_1(A_232, B_233, C_234))=k3_xboole_0(u1_struct_0(B_233), u1_struct_0(C_234)) | ~v1_pre_topc(k2_tsep_1(A_232, B_233, C_234)) | v2_struct_0(k2_tsep_1(A_232, B_233, C_234)) | r1_tsep_1(B_233, C_234) | ~m1_pre_topc(C_234, A_232) | v2_struct_0(C_234) | ~m1_pre_topc(B_233, A_232) | v2_struct_0(B_233) | ~l1_pre_topc(A_232) | v2_struct_0(A_232))), inference(resolution, [status(thm)], [c_26, c_733])).
% 4.40/1.78  tff(c_817, plain, (![A_235, B_236, C_237]: (u1_struct_0(k2_tsep_1(A_235, B_236, C_237))=k3_xboole_0(u1_struct_0(B_236), u1_struct_0(C_237)) | ~v1_pre_topc(k2_tsep_1(A_235, B_236, C_237)) | r1_tsep_1(B_236, C_237) | ~m1_pre_topc(C_237, A_235) | v2_struct_0(C_237) | ~m1_pre_topc(B_236, A_235) | v2_struct_0(B_236) | ~l1_pre_topc(A_235) | v2_struct_0(A_235))), inference(resolution, [status(thm)], [c_737, c_30])).
% 4.40/1.78  tff(c_821, plain, (![A_238, B_239, C_240]: (u1_struct_0(k2_tsep_1(A_238, B_239, C_240))=k3_xboole_0(u1_struct_0(B_239), u1_struct_0(C_240)) | r1_tsep_1(B_239, C_240) | ~m1_pre_topc(C_240, A_238) | v2_struct_0(C_240) | ~m1_pre_topc(B_239, A_238) | v2_struct_0(B_239) | ~l1_pre_topc(A_238) | v2_struct_0(A_238))), inference(resolution, [status(thm)], [c_28, c_817])).
% 4.40/1.78  tff(c_668, plain, (![A_188, C_189, B_190]: (m1_subset_1(A_188, C_189) | ~m1_subset_1(B_190, k1_zfmisc_1(C_189)) | ~r2_hidden(A_188, B_190))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.40/1.78  tff(c_673, plain, (![A_194, B_195, A_196]: (m1_subset_1(A_194, B_195) | ~r2_hidden(A_194, A_196) | ~r1_tarski(A_196, B_195))), inference(resolution, [status(thm)], [c_12, c_668])).
% 4.40/1.78  tff(c_677, plain, (![A_197, B_198, B_199]: (m1_subset_1(A_197, B_198) | ~r1_tarski(B_199, B_198) | v1_xboole_0(B_199) | ~m1_subset_1(A_197, B_199))), inference(resolution, [status(thm)], [c_8, c_673])).
% 4.40/1.78  tff(c_682, plain, (![A_197, A_84, B_83]: (m1_subset_1(A_197, A_84) | v1_xboole_0(k3_xboole_0(B_83, A_84)) | ~m1_subset_1(A_197, k3_xboole_0(B_83, A_84)))), inference(resolution, [status(thm)], [c_68, c_677])).
% 4.40/1.78  tff(c_1082, plain, (![A_260, C_261, B_262, A_263]: (m1_subset_1(A_260, u1_struct_0(C_261)) | v1_xboole_0(k3_xboole_0(u1_struct_0(B_262), u1_struct_0(C_261))) | ~m1_subset_1(A_260, u1_struct_0(k2_tsep_1(A_263, B_262, C_261))) | r1_tsep_1(B_262, C_261) | ~m1_pre_topc(C_261, A_263) | v2_struct_0(C_261) | ~m1_pre_topc(B_262, A_263) | v2_struct_0(B_262) | ~l1_pre_topc(A_263) | v2_struct_0(A_263))), inference(superposition, [status(thm), theory('equality')], [c_821, c_682])).
% 4.40/1.78  tff(c_1088, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))) | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_1082])).
% 4.40/1.78  tff(c_1091, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))) | r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_38, c_2, c_1088])).
% 4.40/1.78  tff(c_1092, plain, (v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_44, c_40, c_36, c_659, c_1091])).
% 4.40/1.78  tff(c_919, plain, (![A_247, B_248, C_249]: (u1_struct_0(k2_tsep_1(A_247, B_248, C_249))=k3_xboole_0(u1_struct_0(C_249), u1_struct_0(B_248)) | r1_tsep_1(B_248, C_249) | ~m1_pre_topc(C_249, A_247) | v2_struct_0(C_249) | ~m1_pre_topc(B_248, A_247) | v2_struct_0(B_248) | ~l1_pre_topc(A_247) | v2_struct_0(A_247))), inference(superposition, [status(thm), theory('equality')], [c_2, c_821])).
% 4.40/1.78  tff(c_986, plain, (![C_249, B_248, A_247]: (~v1_xboole_0(k3_xboole_0(u1_struct_0(C_249), u1_struct_0(B_248))) | ~l1_struct_0(k2_tsep_1(A_247, B_248, C_249)) | v2_struct_0(k2_tsep_1(A_247, B_248, C_249)) | r1_tsep_1(B_248, C_249) | ~m1_pre_topc(C_249, A_247) | v2_struct_0(C_249) | ~m1_pre_topc(B_248, A_247) | v2_struct_0(B_248) | ~l1_pre_topc(A_247) | v2_struct_0(A_247))), inference(superposition, [status(thm), theory('equality')], [c_919, c_20])).
% 4.40/1.78  tff(c_1094, plain, (![A_247]: (~l1_struct_0(k2_tsep_1(A_247, '#skF_2', '#skF_3')) | v2_struct_0(k2_tsep_1(A_247, '#skF_2', '#skF_3')) | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', A_247) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_247) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_247) | v2_struct_0(A_247))), inference(resolution, [status(thm)], [c_1092, c_986])).
% 4.40/1.78  tff(c_1129, plain, (![A_265]: (~l1_struct_0(k2_tsep_1(A_265, '#skF_2', '#skF_3')) | v2_struct_0(k2_tsep_1(A_265, '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', A_265) | ~m1_pre_topc('#skF_2', A_265) | ~l1_pre_topc(A_265) | v2_struct_0(A_265))), inference(negUnitSimplification, [status(thm)], [c_44, c_40, c_36, c_1094])).
% 4.40/1.78  tff(c_1132, plain, (![A_265]: (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | ~l1_struct_0(k2_tsep_1(A_265, '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', A_265) | ~m1_pre_topc('#skF_2', A_265) | ~l1_pre_topc(A_265) | v2_struct_0(A_265))), inference(resolution, [status(thm)], [c_1129, c_30])).
% 4.40/1.78  tff(c_1136, plain, (![A_266]: (~l1_struct_0(k2_tsep_1(A_266, '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', A_266) | ~m1_pre_topc('#skF_2', A_266) | ~l1_pre_topc(A_266) | v2_struct_0(A_266))), inference(negUnitSimplification, [status(thm)], [c_44, c_40, c_1132])).
% 4.40/1.78  tff(c_1142, plain, (![A_267]: (~m1_pre_topc('#skF_3', A_267) | ~m1_pre_topc('#skF_2', A_267) | ~l1_pre_topc(A_267) | v2_struct_0(A_267) | ~l1_pre_topc(k2_tsep_1(A_267, '#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_16, c_1136])).
% 4.40/1.78  tff(c_1146, plain, (![A_215]: (~m1_pre_topc('#skF_3', A_215) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_215) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_215) | v2_struct_0(A_215))), inference(resolution, [status(thm)], [c_717, c_1142])).
% 4.40/1.78  tff(c_1150, plain, (![A_268]: (~m1_pre_topc('#skF_3', A_268) | ~m1_pre_topc('#skF_2', A_268) | ~l1_pre_topc(A_268) | v2_struct_0(A_268))), inference(negUnitSimplification, [status(thm)], [c_44, c_40, c_1146])).
% 4.40/1.78  tff(c_1153, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1150])).
% 4.40/1.78  tff(c_1156, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_38, c_1153])).
% 4.40/1.78  tff(c_1158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_1156])).
% 4.40/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.40/1.78  
% 4.40/1.78  Inference rules
% 4.40/1.78  ----------------------
% 4.40/1.78  #Ref     : 0
% 4.40/1.78  #Sup     : 329
% 4.40/1.78  #Fact    : 0
% 4.40/1.78  #Define  : 0
% 4.40/1.78  #Split   : 5
% 4.40/1.78  #Chain   : 0
% 4.40/1.78  #Close   : 0
% 4.40/1.78  
% 4.40/1.78  Ordering : KBO
% 4.40/1.78  
% 4.40/1.78  Simplification rules
% 4.40/1.78  ----------------------
% 4.40/1.78  #Subsume      : 78
% 4.40/1.78  #Demod        : 43
% 4.40/1.78  #Tautology    : 42
% 4.40/1.78  #SimpNegUnit  : 26
% 4.40/1.78  #BackRed      : 0
% 4.40/1.78  
% 4.40/1.78  #Partial instantiations: 0
% 4.40/1.78  #Strategies tried      : 1
% 4.40/1.78  
% 4.40/1.78  Timing (in seconds)
% 4.40/1.78  ----------------------
% 4.40/1.79  Preprocessing        : 0.31
% 4.40/1.79  Parsing              : 0.17
% 4.40/1.79  CNF conversion       : 0.03
% 4.40/1.79  Main loop            : 0.65
% 4.40/1.79  Inferencing          : 0.23
% 4.40/1.79  Reduction            : 0.19
% 4.40/1.79  Demodulation         : 0.14
% 4.40/1.79  BG Simplification    : 0.04
% 4.40/1.79  Subsumption          : 0.17
% 4.40/1.79  Abstraction          : 0.03
% 4.40/1.79  MUC search           : 0.00
% 4.40/1.79  Cooper               : 0.00
% 4.40/1.79  Total                : 1.01
% 4.40/1.79  Index Insertion      : 0.00
% 4.40/1.79  Index Deletion       : 0.00
% 4.40/1.79  Index Matching       : 0.00
% 4.40/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
