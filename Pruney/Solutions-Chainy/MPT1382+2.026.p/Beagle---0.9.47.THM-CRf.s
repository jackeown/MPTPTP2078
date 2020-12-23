%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:10 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 511 expanded)
%              Number of leaves         :   25 ( 201 expanded)
%              Depth                    :   19
%              Number of atoms          :  349 (2706 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( m1_connsp_2(C,A,B)
                    & ! [D] :
                        ( ( ~ v1_xboole_0(D)
                          & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A))) )
                       => ~ ( m1_connsp_2(D,A,B)
                            & v3_pre_topc(D,A)
                            & r1_tarski(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_connsp_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_77,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> r2_hidden(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B,C] :
          ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,k1_tops_1(A,C))
          <=> ? [D] :
                ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                & v3_pre_topc(D,A)
                & r1_tarski(D,C)
                & r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( v3_pre_topc(B,A)
                  & r2_hidden(C,B) )
               => m1_connsp_2(B,A,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_40,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_40])).

tff(c_36,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_28,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_133,plain,(
    ! [B_94,A_95,C_96] :
      ( r2_hidden(B_94,k1_tops_1(A_95,C_96))
      | ~ m1_connsp_2(C_96,A_95,B_94)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ m1_subset_1(B_94,u1_struct_0(A_95))
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_142,plain,(
    ! [B_94,A_95,A_1] :
      ( r2_hidden(B_94,k1_tops_1(A_95,A_1))
      | ~ m1_connsp_2(A_1,A_95,B_94)
      | ~ m1_subset_1(B_94,u1_struct_0(A_95))
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95)
      | v2_struct_0(A_95)
      | ~ r1_tarski(A_1,u1_struct_0(A_95)) ) ),
    inference(resolution,[status(thm)],[c_4,c_133])).

tff(c_140,plain,(
    ! [B_94] :
      ( r2_hidden(B_94,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_94)
      | ~ m1_subset_1(B_94,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_133])).

tff(c_145,plain,(
    ! [B_94] :
      ( r2_hidden(B_94,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_94)
      | ~ m1_subset_1(B_94,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_140])).

tff(c_147,plain,(
    ! [B_97] :
      ( r2_hidden(B_97,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_97)
      | ~ m1_subset_1(B_97,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_145])).

tff(c_12,plain,(
    ! [B_16,A_9,C_17] :
      ( r2_hidden(B_16,'#skF_1'(A_9,B_16,C_17))
      | ~ r2_hidden(B_16,k1_tops_1(A_9,C_17))
      | ~ m1_subset_1(C_17,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_pre_topc(A_9)
      | ~ v2_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_151,plain,(
    ! [B_97] :
      ( r2_hidden(B_97,'#skF_1'('#skF_2',B_97,'#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ m1_connsp_2('#skF_4','#skF_2',B_97)
      | ~ m1_subset_1(B_97,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_147,c_12])).

tff(c_164,plain,(
    ! [B_97] :
      ( r2_hidden(B_97,'#skF_1'('#skF_2',B_97,'#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_97)
      | ~ m1_subset_1(B_97,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_151])).

tff(c_87,plain,(
    ! [A_66,B_67,C_68] :
      ( v3_pre_topc('#skF_1'(A_66,B_67,C_68),A_66)
      | ~ r2_hidden(B_67,k1_tops_1(A_66,C_68))
      | ~ m1_subset_1(C_68,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_93,plain,(
    ! [A_66,B_67,A_1] :
      ( v3_pre_topc('#skF_1'(A_66,B_67,A_1),A_66)
      | ~ r2_hidden(B_67,k1_tops_1(A_66,A_1))
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66)
      | ~ r1_tarski(A_1,u1_struct_0(A_66)) ) ),
    inference(resolution,[status(thm)],[c_4,c_87])).

tff(c_18,plain,(
    ! [A_9,B_16,C_17] :
      ( m1_subset_1('#skF_1'(A_9,B_16,C_17),k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ r2_hidden(B_16,k1_tops_1(A_9,C_17))
      | ~ m1_subset_1(C_17,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_pre_topc(A_9)
      | ~ v2_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_248,plain,(
    ! [B_112,A_113,C_114] :
      ( m1_connsp_2(B_112,A_113,C_114)
      | ~ r2_hidden(C_114,B_112)
      | ~ v3_pre_topc(B_112,A_113)
      | ~ m1_subset_1(C_114,u1_struct_0(A_113))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113)
      | ~ v2_pre_topc(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_252,plain,(
    ! [B_112] :
      ( m1_connsp_2(B_112,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_112)
      | ~ v3_pre_topc(B_112,'#skF_2')
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_248])).

tff(c_259,plain,(
    ! [B_112] :
      ( m1_connsp_2(B_112,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_112)
      | ~ v3_pre_topc(B_112,'#skF_2')
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_252])).

tff(c_267,plain,(
    ! [B_116] :
      ( m1_connsp_2(B_116,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_116)
      | ~ v3_pre_topc(B_116,'#skF_2')
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_259])).

tff(c_271,plain,(
    ! [B_16,C_17] :
      ( m1_connsp_2('#skF_1'('#skF_2',B_16,C_17),'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_16,C_17))
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_16,C_17),'#skF_2')
      | ~ r2_hidden(B_16,k1_tops_1('#skF_2',C_17))
      | ~ m1_subset_1(C_17,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_267])).

tff(c_356,plain,(
    ! [B_141,C_142] :
      ( m1_connsp_2('#skF_1'('#skF_2',B_141,C_142),'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_141,C_142))
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_141,C_142),'#skF_2')
      | ~ r2_hidden(B_141,k1_tops_1('#skF_2',C_142))
      | ~ m1_subset_1(C_142,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_271])).

tff(c_370,plain,(
    ! [B_143] :
      ( m1_connsp_2('#skF_1'('#skF_2',B_143,'#skF_4'),'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_143,'#skF_4'))
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_143,'#skF_4'),'#skF_2')
      | ~ r2_hidden(B_143,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_30,c_356])).

tff(c_101,plain,(
    ! [A_79,B_80,C_81] :
      ( m1_subset_1('#skF_1'(A_79,B_80,C_81),k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ r2_hidden(B_80,k1_tops_1(A_79,C_81))
      | ~ m1_subset_1(C_81,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79)
      | ~ v2_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_26,plain,(
    ! [D_46] :
      ( ~ r1_tarski(D_46,'#skF_4')
      | ~ v3_pre_topc(D_46,'#skF_2')
      | ~ m1_connsp_2(D_46,'#skF_2','#skF_3')
      | ~ m1_subset_1(D_46,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v1_xboole_0(D_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_111,plain,(
    ! [B_80,C_81] :
      ( ~ r1_tarski('#skF_1'('#skF_2',B_80,C_81),'#skF_4')
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_80,C_81),'#skF_2')
      | ~ m1_connsp_2('#skF_1'('#skF_2',B_80,C_81),'#skF_2','#skF_3')
      | v1_xboole_0('#skF_1'('#skF_2',B_80,C_81))
      | ~ r2_hidden(B_80,k1_tops_1('#skF_2',C_81))
      | ~ m1_subset_1(C_81,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_101,c_26])).

tff(c_120,plain,(
    ! [B_80,C_81] :
      ( ~ r1_tarski('#skF_1'('#skF_2',B_80,C_81),'#skF_4')
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_80,C_81),'#skF_2')
      | ~ m1_connsp_2('#skF_1'('#skF_2',B_80,C_81),'#skF_2','#skF_3')
      | v1_xboole_0('#skF_1'('#skF_2',B_80,C_81))
      | ~ r2_hidden(B_80,k1_tops_1('#skF_2',C_81))
      | ~ m1_subset_1(C_81,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_111])).

tff(c_372,plain,(
    ! [B_143] :
      ( ~ r1_tarski('#skF_1'('#skF_2',B_143,'#skF_4'),'#skF_4')
      | v1_xboole_0('#skF_1'('#skF_2',B_143,'#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_143,'#skF_4'))
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_143,'#skF_4'),'#skF_2')
      | ~ r2_hidden(B_143,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_370,c_120])).

tff(c_385,plain,(
    ! [B_149] :
      ( ~ r1_tarski('#skF_1'('#skF_2',B_149,'#skF_4'),'#skF_4')
      | v1_xboole_0('#skF_1'('#skF_2',B_149,'#skF_4'))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_149,'#skF_4'))
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_149,'#skF_4'),'#skF_2')
      | ~ r2_hidden(B_149,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_372])).

tff(c_389,plain,(
    ! [B_67] :
      ( ~ r1_tarski('#skF_1'('#skF_2',B_67,'#skF_4'),'#skF_4')
      | v1_xboole_0('#skF_1'('#skF_2',B_67,'#skF_4'))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_67,'#skF_4'))
      | ~ r2_hidden(B_67,k1_tops_1('#skF_2','#skF_4'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ r1_tarski('#skF_4',u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_93,c_385])).

tff(c_397,plain,(
    ! [B_150] :
      ( ~ r1_tarski('#skF_1'('#skF_2',B_150,'#skF_4'),'#skF_4')
      | v1_xboole_0('#skF_1'('#skF_2',B_150,'#skF_4'))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_150,'#skF_4'))
      | ~ r2_hidden(B_150,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_36,c_34,c_389])).

tff(c_400,plain,
    ( ~ r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_164,c_397])).

tff(c_403,plain,
    ( ~ r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_400])).

tff(c_404,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_403])).

tff(c_407,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_142,c_404])).

tff(c_413,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_36,c_34,c_32,c_28,c_407])).

tff(c_415,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_413])).

tff(c_417,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_403])).

tff(c_14,plain,(
    ! [A_9,B_16,C_17] :
      ( r1_tarski('#skF_1'(A_9,B_16,C_17),C_17)
      | ~ r2_hidden(B_16,k1_tops_1(A_9,C_17))
      | ~ m1_subset_1(C_17,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_pre_topc(A_9)
      | ~ v2_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_426,plain,
    ( r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_417,c_14])).

tff(c_441,plain,(
    r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_426])).

tff(c_416,plain,
    ( ~ r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_403])).

tff(c_521,plain,(
    v1_xboole_0('#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_416])).

tff(c_322,plain,(
    ! [B_122,A_123,A_124] :
      ( r2_hidden(B_122,k1_tops_1(A_123,A_124))
      | ~ m1_connsp_2(A_124,A_123,B_122)
      | ~ m1_subset_1(B_122,u1_struct_0(A_123))
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123)
      | v2_struct_0(A_123)
      | ~ r1_tarski(A_124,u1_struct_0(A_123)) ) ),
    inference(resolution,[status(thm)],[c_4,c_133])).

tff(c_543,plain,(
    ! [B_162,A_163,A_164] :
      ( r2_hidden(B_162,'#skF_1'(A_163,B_162,A_164))
      | ~ m1_subset_1(A_164,k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ m1_connsp_2(A_164,A_163,B_162)
      | ~ m1_subset_1(B_162,u1_struct_0(A_163))
      | ~ l1_pre_topc(A_163)
      | ~ v2_pre_topc(A_163)
      | v2_struct_0(A_163)
      | ~ r1_tarski(A_164,u1_struct_0(A_163)) ) ),
    inference(resolution,[status(thm)],[c_322,c_12])).

tff(c_552,plain,(
    ! [B_162,A_163,A_1] :
      ( r2_hidden(B_162,'#skF_1'(A_163,B_162,A_1))
      | ~ m1_connsp_2(A_1,A_163,B_162)
      | ~ m1_subset_1(B_162,u1_struct_0(A_163))
      | ~ l1_pre_topc(A_163)
      | ~ v2_pre_topc(A_163)
      | v2_struct_0(A_163)
      | ~ r1_tarski(A_1,u1_struct_0(A_163)) ) ),
    inference(resolution,[status(thm)],[c_4,c_543])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_121,plain,(
    ! [A_79,B_80,C_81] :
      ( r1_tarski('#skF_1'(A_79,B_80,C_81),u1_struct_0(A_79))
      | ~ r2_hidden(B_80,k1_tops_1(A_79,C_81))
      | ~ m1_subset_1(C_81,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79)
      | ~ v2_pre_topc(A_79) ) ),
    inference(resolution,[status(thm)],[c_101,c_2])).

tff(c_369,plain,(
    ! [B_141] :
      ( m1_connsp_2('#skF_1'('#skF_2',B_141,'#skF_4'),'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_141,'#skF_4'))
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_141,'#skF_4'),'#skF_2')
      | ~ r2_hidden(B_141,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_30,c_356])).

tff(c_639,plain,(
    ! [A_181,B_182,A_183] :
      ( r1_tarski('#skF_1'(A_181,B_182,A_183),A_183)
      | ~ m1_subset_1(A_183,k1_zfmisc_1(u1_struct_0(A_181)))
      | ~ m1_connsp_2(A_183,A_181,B_182)
      | ~ m1_subset_1(B_182,u1_struct_0(A_181))
      | ~ l1_pre_topc(A_181)
      | ~ v2_pre_topc(A_181)
      | v2_struct_0(A_181)
      | ~ r1_tarski(A_183,u1_struct_0(A_181)) ) ),
    inference(resolution,[status(thm)],[c_322,c_14])).

tff(c_653,plain,(
    ! [A_184,B_185,A_186] :
      ( r1_tarski('#skF_1'(A_184,B_185,A_186),A_186)
      | ~ m1_connsp_2(A_186,A_184,B_185)
      | ~ m1_subset_1(B_185,u1_struct_0(A_184))
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184)
      | ~ r1_tarski(A_186,u1_struct_0(A_184)) ) ),
    inference(resolution,[status(thm)],[c_4,c_639])).

tff(c_557,plain,(
    ! [B_165,A_166,A_167] :
      ( r2_hidden(B_165,'#skF_1'(A_166,B_165,A_167))
      | ~ m1_connsp_2(A_167,A_166,B_165)
      | ~ m1_subset_1(B_165,u1_struct_0(A_166))
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166)
      | v2_struct_0(A_166)
      | ~ r1_tarski(A_167,u1_struct_0(A_166)) ) ),
    inference(resolution,[status(thm)],[c_4,c_543])).

tff(c_62,plain,(
    ! [C_52,B_53,A_54] :
      ( ~ v1_xboole_0(C_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(C_52))
      | ~ r2_hidden(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_67,plain,(
    ! [B_2,A_54,A_1] :
      ( ~ v1_xboole_0(B_2)
      | ~ r2_hidden(A_54,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_62])).

tff(c_579,plain,(
    ! [B_2,A_166,B_165,A_167] :
      ( ~ v1_xboole_0(B_2)
      | ~ r1_tarski('#skF_1'(A_166,B_165,A_167),B_2)
      | ~ m1_connsp_2(A_167,A_166,B_165)
      | ~ m1_subset_1(B_165,u1_struct_0(A_166))
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166)
      | v2_struct_0(A_166)
      | ~ r1_tarski(A_167,u1_struct_0(A_166)) ) ),
    inference(resolution,[status(thm)],[c_557,c_67])).

tff(c_708,plain,(
    ! [A_187,A_188,B_189] :
      ( ~ v1_xboole_0(A_187)
      | ~ m1_connsp_2(A_187,A_188,B_189)
      | ~ m1_subset_1(B_189,u1_struct_0(A_188))
      | ~ l1_pre_topc(A_188)
      | ~ v2_pre_topc(A_188)
      | v2_struct_0(A_188)
      | ~ r1_tarski(A_187,u1_struct_0(A_188)) ) ),
    inference(resolution,[status(thm)],[c_653,c_579])).

tff(c_714,plain,(
    ! [B_141] :
      ( ~ v1_xboole_0('#skF_1'('#skF_2',B_141,'#skF_4'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski('#skF_1'('#skF_2',B_141,'#skF_4'),u1_struct_0('#skF_2'))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_141,'#skF_4'))
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_141,'#skF_4'),'#skF_2')
      | ~ r2_hidden(B_141,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_369,c_708])).

tff(c_727,plain,(
    ! [B_141] :
      ( ~ v1_xboole_0('#skF_1'('#skF_2',B_141,'#skF_4'))
      | v2_struct_0('#skF_2')
      | ~ r1_tarski('#skF_1'('#skF_2',B_141,'#skF_4'),u1_struct_0('#skF_2'))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_141,'#skF_4'))
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_141,'#skF_4'),'#skF_2')
      | ~ r2_hidden(B_141,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_714])).

tff(c_759,plain,(
    ! [B_198] :
      ( ~ v1_xboole_0('#skF_1'('#skF_2',B_198,'#skF_4'))
      | ~ r1_tarski('#skF_1'('#skF_2',B_198,'#skF_4'),u1_struct_0('#skF_2'))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_198,'#skF_4'))
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_198,'#skF_4'),'#skF_2')
      | ~ r2_hidden(B_198,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_727])).

tff(c_763,plain,(
    ! [B_80] :
      ( ~ v1_xboole_0('#skF_1'('#skF_2',B_80,'#skF_4'))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_80,'#skF_4'))
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_80,'#skF_4'),'#skF_2')
      | ~ r2_hidden(B_80,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_121,c_759])).

tff(c_775,plain,(
    ! [B_200] :
      ( ~ v1_xboole_0('#skF_1'('#skF_2',B_200,'#skF_4'))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_200,'#skF_4'))
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_200,'#skF_4'),'#skF_2')
      | ~ r2_hidden(B_200,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_763])).

tff(c_779,plain,(
    ! [B_67] :
      ( ~ v1_xboole_0('#skF_1'('#skF_2',B_67,'#skF_4'))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_67,'#skF_4'))
      | ~ r2_hidden(B_67,k1_tops_1('#skF_2','#skF_4'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ r1_tarski('#skF_4',u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_93,c_775])).

tff(c_787,plain,(
    ! [B_201] :
      ( ~ v1_xboole_0('#skF_1'('#skF_2',B_201,'#skF_4'))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_201,'#skF_4'))
      | ~ r2_hidden(B_201,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_36,c_34,c_779])).

tff(c_790,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_552,c_787])).

tff(c_798,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_36,c_34,c_32,c_28,c_417,c_521,c_790])).

tff(c_800,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_798])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:45:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.52  
% 3.04/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.52  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.04/1.52  
% 3.04/1.52  %Foreground sorts:
% 3.04/1.52  
% 3.04/1.52  
% 3.04/1.52  %Background operators:
% 3.04/1.52  
% 3.04/1.52  
% 3.04/1.52  %Foreground operators:
% 3.04/1.52  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.04/1.52  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.04/1.52  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.04/1.52  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.04/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.04/1.52  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.04/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.04/1.52  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.04/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.04/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.04/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.04/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.04/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.52  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.04/1.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.04/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.04/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.04/1.52  
% 3.38/1.54  tff(f_126, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(C, A, B) & (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~((m1_connsp_2(D, A, B) & v3_pre_topc(D, A)) & r1_tarski(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_connsp_2)).
% 3.38/1.54  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.38/1.54  tff(f_77, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 3.38/1.54  tff(f_60, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k1_tops_1(A, C)) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_tops_1)).
% 3.38/1.54  tff(f_96, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 3.38/1.54  tff(f_42, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.38/1.54  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.38/1.54  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.38/1.54  tff(c_40, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~m1_subset_1(A_49, k1_zfmisc_1(B_50)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.38/1.54  tff(c_48, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_40])).
% 3.38/1.54  tff(c_36, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.38/1.54  tff(c_34, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.38/1.54  tff(c_32, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.38/1.54  tff(c_28, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.38/1.54  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.38/1.54  tff(c_133, plain, (![B_94, A_95, C_96]: (r2_hidden(B_94, k1_tops_1(A_95, C_96)) | ~m1_connsp_2(C_96, A_95, B_94) | ~m1_subset_1(C_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~m1_subset_1(B_94, u1_struct_0(A_95)) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.38/1.54  tff(c_142, plain, (![B_94, A_95, A_1]: (r2_hidden(B_94, k1_tops_1(A_95, A_1)) | ~m1_connsp_2(A_1, A_95, B_94) | ~m1_subset_1(B_94, u1_struct_0(A_95)) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95) | v2_struct_0(A_95) | ~r1_tarski(A_1, u1_struct_0(A_95)))), inference(resolution, [status(thm)], [c_4, c_133])).
% 3.38/1.54  tff(c_140, plain, (![B_94]: (r2_hidden(B_94, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_94) | ~m1_subset_1(B_94, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_133])).
% 3.38/1.54  tff(c_145, plain, (![B_94]: (r2_hidden(B_94, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_94) | ~m1_subset_1(B_94, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_140])).
% 3.38/1.54  tff(c_147, plain, (![B_97]: (r2_hidden(B_97, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_97) | ~m1_subset_1(B_97, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_38, c_145])).
% 3.38/1.54  tff(c_12, plain, (![B_16, A_9, C_17]: (r2_hidden(B_16, '#skF_1'(A_9, B_16, C_17)) | ~r2_hidden(B_16, k1_tops_1(A_9, C_17)) | ~m1_subset_1(C_17, k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_pre_topc(A_9) | ~v2_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.38/1.54  tff(c_151, plain, (![B_97]: (r2_hidden(B_97, '#skF_1'('#skF_2', B_97, '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~m1_connsp_2('#skF_4', '#skF_2', B_97) | ~m1_subset_1(B_97, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_147, c_12])).
% 3.38/1.54  tff(c_164, plain, (![B_97]: (r2_hidden(B_97, '#skF_1'('#skF_2', B_97, '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_97) | ~m1_subset_1(B_97, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_151])).
% 3.38/1.54  tff(c_87, plain, (![A_66, B_67, C_68]: (v3_pre_topc('#skF_1'(A_66, B_67, C_68), A_66) | ~r2_hidden(B_67, k1_tops_1(A_66, C_68)) | ~m1_subset_1(C_68, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.38/1.54  tff(c_93, plain, (![A_66, B_67, A_1]: (v3_pre_topc('#skF_1'(A_66, B_67, A_1), A_66) | ~r2_hidden(B_67, k1_tops_1(A_66, A_1)) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66) | ~r1_tarski(A_1, u1_struct_0(A_66)))), inference(resolution, [status(thm)], [c_4, c_87])).
% 3.38/1.54  tff(c_18, plain, (![A_9, B_16, C_17]: (m1_subset_1('#skF_1'(A_9, B_16, C_17), k1_zfmisc_1(u1_struct_0(A_9))) | ~r2_hidden(B_16, k1_tops_1(A_9, C_17)) | ~m1_subset_1(C_17, k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_pre_topc(A_9) | ~v2_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.38/1.54  tff(c_248, plain, (![B_112, A_113, C_114]: (m1_connsp_2(B_112, A_113, C_114) | ~r2_hidden(C_114, B_112) | ~v3_pre_topc(B_112, A_113) | ~m1_subset_1(C_114, u1_struct_0(A_113)) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_pre_topc(A_113) | ~v2_pre_topc(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.38/1.54  tff(c_252, plain, (![B_112]: (m1_connsp_2(B_112, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_112) | ~v3_pre_topc(B_112, '#skF_2') | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_248])).
% 3.38/1.54  tff(c_259, plain, (![B_112]: (m1_connsp_2(B_112, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_112) | ~v3_pre_topc(B_112, '#skF_2') | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_252])).
% 3.38/1.54  tff(c_267, plain, (![B_116]: (m1_connsp_2(B_116, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_116) | ~v3_pre_topc(B_116, '#skF_2') | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_38, c_259])).
% 3.38/1.54  tff(c_271, plain, (![B_16, C_17]: (m1_connsp_2('#skF_1'('#skF_2', B_16, C_17), '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_16, C_17)) | ~v3_pre_topc('#skF_1'('#skF_2', B_16, C_17), '#skF_2') | ~r2_hidden(B_16, k1_tops_1('#skF_2', C_17)) | ~m1_subset_1(C_17, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_18, c_267])).
% 3.38/1.54  tff(c_356, plain, (![B_141, C_142]: (m1_connsp_2('#skF_1'('#skF_2', B_141, C_142), '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_141, C_142)) | ~v3_pre_topc('#skF_1'('#skF_2', B_141, C_142), '#skF_2') | ~r2_hidden(B_141, k1_tops_1('#skF_2', C_142)) | ~m1_subset_1(C_142, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_271])).
% 3.38/1.54  tff(c_370, plain, (![B_143]: (m1_connsp_2('#skF_1'('#skF_2', B_143, '#skF_4'), '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_143, '#skF_4')) | ~v3_pre_topc('#skF_1'('#skF_2', B_143, '#skF_4'), '#skF_2') | ~r2_hidden(B_143, k1_tops_1('#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_30, c_356])).
% 3.38/1.54  tff(c_101, plain, (![A_79, B_80, C_81]: (m1_subset_1('#skF_1'(A_79, B_80, C_81), k1_zfmisc_1(u1_struct_0(A_79))) | ~r2_hidden(B_80, k1_tops_1(A_79, C_81)) | ~m1_subset_1(C_81, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79) | ~v2_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.38/1.54  tff(c_26, plain, (![D_46]: (~r1_tarski(D_46, '#skF_4') | ~v3_pre_topc(D_46, '#skF_2') | ~m1_connsp_2(D_46, '#skF_2', '#skF_3') | ~m1_subset_1(D_46, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(D_46))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.38/1.54  tff(c_111, plain, (![B_80, C_81]: (~r1_tarski('#skF_1'('#skF_2', B_80, C_81), '#skF_4') | ~v3_pre_topc('#skF_1'('#skF_2', B_80, C_81), '#skF_2') | ~m1_connsp_2('#skF_1'('#skF_2', B_80, C_81), '#skF_2', '#skF_3') | v1_xboole_0('#skF_1'('#skF_2', B_80, C_81)) | ~r2_hidden(B_80, k1_tops_1('#skF_2', C_81)) | ~m1_subset_1(C_81, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_101, c_26])).
% 3.38/1.54  tff(c_120, plain, (![B_80, C_81]: (~r1_tarski('#skF_1'('#skF_2', B_80, C_81), '#skF_4') | ~v3_pre_topc('#skF_1'('#skF_2', B_80, C_81), '#skF_2') | ~m1_connsp_2('#skF_1'('#skF_2', B_80, C_81), '#skF_2', '#skF_3') | v1_xboole_0('#skF_1'('#skF_2', B_80, C_81)) | ~r2_hidden(B_80, k1_tops_1('#skF_2', C_81)) | ~m1_subset_1(C_81, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_111])).
% 3.38/1.54  tff(c_372, plain, (![B_143]: (~r1_tarski('#skF_1'('#skF_2', B_143, '#skF_4'), '#skF_4') | v1_xboole_0('#skF_1'('#skF_2', B_143, '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_143, '#skF_4')) | ~v3_pre_topc('#skF_1'('#skF_2', B_143, '#skF_4'), '#skF_2') | ~r2_hidden(B_143, k1_tops_1('#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_370, c_120])).
% 3.38/1.54  tff(c_385, plain, (![B_149]: (~r1_tarski('#skF_1'('#skF_2', B_149, '#skF_4'), '#skF_4') | v1_xboole_0('#skF_1'('#skF_2', B_149, '#skF_4')) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_149, '#skF_4')) | ~v3_pre_topc('#skF_1'('#skF_2', B_149, '#skF_4'), '#skF_2') | ~r2_hidden(B_149, k1_tops_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_372])).
% 3.38/1.54  tff(c_389, plain, (![B_67]: (~r1_tarski('#skF_1'('#skF_2', B_67, '#skF_4'), '#skF_4') | v1_xboole_0('#skF_1'('#skF_2', B_67, '#skF_4')) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_67, '#skF_4')) | ~r2_hidden(B_67, k1_tops_1('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r1_tarski('#skF_4', u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_93, c_385])).
% 3.38/1.54  tff(c_397, plain, (![B_150]: (~r1_tarski('#skF_1'('#skF_2', B_150, '#skF_4'), '#skF_4') | v1_xboole_0('#skF_1'('#skF_2', B_150, '#skF_4')) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_150, '#skF_4')) | ~r2_hidden(B_150, k1_tops_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_36, c_34, c_389])).
% 3.38/1.54  tff(c_400, plain, (~r1_tarski('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4') | v1_xboole_0('#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_164, c_397])).
% 3.38/1.54  tff(c_403, plain, (~r1_tarski('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4') | v1_xboole_0('#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_400])).
% 3.38/1.54  tff(c_404, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_403])).
% 3.38/1.54  tff(c_407, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_142, c_404])).
% 3.38/1.54  tff(c_413, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_36, c_34, c_32, c_28, c_407])).
% 3.38/1.54  tff(c_415, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_413])).
% 3.38/1.54  tff(c_417, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_403])).
% 3.38/1.54  tff(c_14, plain, (![A_9, B_16, C_17]: (r1_tarski('#skF_1'(A_9, B_16, C_17), C_17) | ~r2_hidden(B_16, k1_tops_1(A_9, C_17)) | ~m1_subset_1(C_17, k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_pre_topc(A_9) | ~v2_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.38/1.54  tff(c_426, plain, (r1_tarski('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_417, c_14])).
% 3.38/1.54  tff(c_441, plain, (r1_tarski('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_426])).
% 3.38/1.54  tff(c_416, plain, (~r1_tarski('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4') | v1_xboole_0('#skF_1'('#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_403])).
% 3.38/1.54  tff(c_521, plain, (v1_xboole_0('#skF_1'('#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_441, c_416])).
% 3.38/1.54  tff(c_322, plain, (![B_122, A_123, A_124]: (r2_hidden(B_122, k1_tops_1(A_123, A_124)) | ~m1_connsp_2(A_124, A_123, B_122) | ~m1_subset_1(B_122, u1_struct_0(A_123)) | ~l1_pre_topc(A_123) | ~v2_pre_topc(A_123) | v2_struct_0(A_123) | ~r1_tarski(A_124, u1_struct_0(A_123)))), inference(resolution, [status(thm)], [c_4, c_133])).
% 3.38/1.54  tff(c_543, plain, (![B_162, A_163, A_164]: (r2_hidden(B_162, '#skF_1'(A_163, B_162, A_164)) | ~m1_subset_1(A_164, k1_zfmisc_1(u1_struct_0(A_163))) | ~m1_connsp_2(A_164, A_163, B_162) | ~m1_subset_1(B_162, u1_struct_0(A_163)) | ~l1_pre_topc(A_163) | ~v2_pre_topc(A_163) | v2_struct_0(A_163) | ~r1_tarski(A_164, u1_struct_0(A_163)))), inference(resolution, [status(thm)], [c_322, c_12])).
% 3.38/1.54  tff(c_552, plain, (![B_162, A_163, A_1]: (r2_hidden(B_162, '#skF_1'(A_163, B_162, A_1)) | ~m1_connsp_2(A_1, A_163, B_162) | ~m1_subset_1(B_162, u1_struct_0(A_163)) | ~l1_pre_topc(A_163) | ~v2_pre_topc(A_163) | v2_struct_0(A_163) | ~r1_tarski(A_1, u1_struct_0(A_163)))), inference(resolution, [status(thm)], [c_4, c_543])).
% 3.38/1.54  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.38/1.54  tff(c_121, plain, (![A_79, B_80, C_81]: (r1_tarski('#skF_1'(A_79, B_80, C_81), u1_struct_0(A_79)) | ~r2_hidden(B_80, k1_tops_1(A_79, C_81)) | ~m1_subset_1(C_81, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79) | ~v2_pre_topc(A_79))), inference(resolution, [status(thm)], [c_101, c_2])).
% 3.38/1.54  tff(c_369, plain, (![B_141]: (m1_connsp_2('#skF_1'('#skF_2', B_141, '#skF_4'), '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_141, '#skF_4')) | ~v3_pre_topc('#skF_1'('#skF_2', B_141, '#skF_4'), '#skF_2') | ~r2_hidden(B_141, k1_tops_1('#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_30, c_356])).
% 3.38/1.54  tff(c_639, plain, (![A_181, B_182, A_183]: (r1_tarski('#skF_1'(A_181, B_182, A_183), A_183) | ~m1_subset_1(A_183, k1_zfmisc_1(u1_struct_0(A_181))) | ~m1_connsp_2(A_183, A_181, B_182) | ~m1_subset_1(B_182, u1_struct_0(A_181)) | ~l1_pre_topc(A_181) | ~v2_pre_topc(A_181) | v2_struct_0(A_181) | ~r1_tarski(A_183, u1_struct_0(A_181)))), inference(resolution, [status(thm)], [c_322, c_14])).
% 3.38/1.54  tff(c_653, plain, (![A_184, B_185, A_186]: (r1_tarski('#skF_1'(A_184, B_185, A_186), A_186) | ~m1_connsp_2(A_186, A_184, B_185) | ~m1_subset_1(B_185, u1_struct_0(A_184)) | ~l1_pre_topc(A_184) | ~v2_pre_topc(A_184) | v2_struct_0(A_184) | ~r1_tarski(A_186, u1_struct_0(A_184)))), inference(resolution, [status(thm)], [c_4, c_639])).
% 3.38/1.54  tff(c_557, plain, (![B_165, A_166, A_167]: (r2_hidden(B_165, '#skF_1'(A_166, B_165, A_167)) | ~m1_connsp_2(A_167, A_166, B_165) | ~m1_subset_1(B_165, u1_struct_0(A_166)) | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166) | v2_struct_0(A_166) | ~r1_tarski(A_167, u1_struct_0(A_166)))), inference(resolution, [status(thm)], [c_4, c_543])).
% 3.38/1.54  tff(c_62, plain, (![C_52, B_53, A_54]: (~v1_xboole_0(C_52) | ~m1_subset_1(B_53, k1_zfmisc_1(C_52)) | ~r2_hidden(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.38/1.54  tff(c_67, plain, (![B_2, A_54, A_1]: (~v1_xboole_0(B_2) | ~r2_hidden(A_54, A_1) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_62])).
% 3.38/1.54  tff(c_579, plain, (![B_2, A_166, B_165, A_167]: (~v1_xboole_0(B_2) | ~r1_tarski('#skF_1'(A_166, B_165, A_167), B_2) | ~m1_connsp_2(A_167, A_166, B_165) | ~m1_subset_1(B_165, u1_struct_0(A_166)) | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166) | v2_struct_0(A_166) | ~r1_tarski(A_167, u1_struct_0(A_166)))), inference(resolution, [status(thm)], [c_557, c_67])).
% 3.38/1.54  tff(c_708, plain, (![A_187, A_188, B_189]: (~v1_xboole_0(A_187) | ~m1_connsp_2(A_187, A_188, B_189) | ~m1_subset_1(B_189, u1_struct_0(A_188)) | ~l1_pre_topc(A_188) | ~v2_pre_topc(A_188) | v2_struct_0(A_188) | ~r1_tarski(A_187, u1_struct_0(A_188)))), inference(resolution, [status(thm)], [c_653, c_579])).
% 3.38/1.54  tff(c_714, plain, (![B_141]: (~v1_xboole_0('#skF_1'('#skF_2', B_141, '#skF_4')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski('#skF_1'('#skF_2', B_141, '#skF_4'), u1_struct_0('#skF_2')) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_141, '#skF_4')) | ~v3_pre_topc('#skF_1'('#skF_2', B_141, '#skF_4'), '#skF_2') | ~r2_hidden(B_141, k1_tops_1('#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_369, c_708])).
% 3.38/1.54  tff(c_727, plain, (![B_141]: (~v1_xboole_0('#skF_1'('#skF_2', B_141, '#skF_4')) | v2_struct_0('#skF_2') | ~r1_tarski('#skF_1'('#skF_2', B_141, '#skF_4'), u1_struct_0('#skF_2')) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_141, '#skF_4')) | ~v3_pre_topc('#skF_1'('#skF_2', B_141, '#skF_4'), '#skF_2') | ~r2_hidden(B_141, k1_tops_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_714])).
% 3.38/1.54  tff(c_759, plain, (![B_198]: (~v1_xboole_0('#skF_1'('#skF_2', B_198, '#skF_4')) | ~r1_tarski('#skF_1'('#skF_2', B_198, '#skF_4'), u1_struct_0('#skF_2')) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_198, '#skF_4')) | ~v3_pre_topc('#skF_1'('#skF_2', B_198, '#skF_4'), '#skF_2') | ~r2_hidden(B_198, k1_tops_1('#skF_2', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_38, c_727])).
% 3.38/1.54  tff(c_763, plain, (![B_80]: (~v1_xboole_0('#skF_1'('#skF_2', B_80, '#skF_4')) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_80, '#skF_4')) | ~v3_pre_topc('#skF_1'('#skF_2', B_80, '#skF_4'), '#skF_2') | ~r2_hidden(B_80, k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_121, c_759])).
% 3.38/1.54  tff(c_775, plain, (![B_200]: (~v1_xboole_0('#skF_1'('#skF_2', B_200, '#skF_4')) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_200, '#skF_4')) | ~v3_pre_topc('#skF_1'('#skF_2', B_200, '#skF_4'), '#skF_2') | ~r2_hidden(B_200, k1_tops_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_763])).
% 3.38/1.54  tff(c_779, plain, (![B_67]: (~v1_xboole_0('#skF_1'('#skF_2', B_67, '#skF_4')) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_67, '#skF_4')) | ~r2_hidden(B_67, k1_tops_1('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r1_tarski('#skF_4', u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_93, c_775])).
% 3.38/1.54  tff(c_787, plain, (![B_201]: (~v1_xboole_0('#skF_1'('#skF_2', B_201, '#skF_4')) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_201, '#skF_4')) | ~r2_hidden(B_201, k1_tops_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_36, c_34, c_779])).
% 3.38/1.54  tff(c_790, plain, (~v1_xboole_0('#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_552, c_787])).
% 3.38/1.54  tff(c_798, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_36, c_34, c_32, c_28, c_417, c_521, c_790])).
% 3.38/1.54  tff(c_800, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_798])).
% 3.38/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.54  
% 3.38/1.54  Inference rules
% 3.38/1.54  ----------------------
% 3.38/1.54  #Ref     : 0
% 3.38/1.54  #Sup     : 143
% 3.38/1.54  #Fact    : 0
% 3.38/1.54  #Define  : 0
% 3.38/1.54  #Split   : 5
% 3.38/1.54  #Chain   : 0
% 3.38/1.54  #Close   : 0
% 3.38/1.54  
% 3.38/1.54  Ordering : KBO
% 3.38/1.54  
% 3.38/1.54  Simplification rules
% 3.38/1.54  ----------------------
% 3.38/1.54  #Subsume      : 34
% 3.38/1.54  #Demod        : 201
% 3.38/1.54  #Tautology    : 20
% 3.38/1.54  #SimpNegUnit  : 28
% 3.38/1.54  #BackRed      : 0
% 3.38/1.54  
% 3.38/1.54  #Partial instantiations: 0
% 3.38/1.54  #Strategies tried      : 1
% 3.38/1.54  
% 3.38/1.54  Timing (in seconds)
% 3.38/1.54  ----------------------
% 3.38/1.55  Preprocessing        : 0.31
% 3.38/1.55  Parsing              : 0.18
% 3.38/1.55  CNF conversion       : 0.02
% 3.38/1.55  Main loop            : 0.41
% 3.38/1.55  Inferencing          : 0.16
% 3.38/1.55  Reduction            : 0.11
% 3.38/1.55  Demodulation         : 0.08
% 3.38/1.55  BG Simplification    : 0.02
% 3.38/1.55  Subsumption          : 0.09
% 3.38/1.55  Abstraction          : 0.02
% 3.38/1.55  MUC search           : 0.00
% 3.38/1.55  Cooper               : 0.00
% 3.38/1.55  Total                : 0.76
% 3.38/1.55  Index Insertion      : 0.00
% 3.38/1.55  Index Deletion       : 0.00
% 3.38/1.55  Index Matching       : 0.00
% 3.38/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
