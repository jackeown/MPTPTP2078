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
% DateTime   : Thu Dec  3 10:24:08 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 155 expanded)
%              Number of leaves         :   27 (  67 expanded)
%              Depth                    :   12
%              Number of atoms          :  190 ( 647 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_129,negated_conjecture,(
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

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_80,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_99,axiom,(
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

tff(c_38,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_41,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | ~ m1_subset_1(A_42,k1_zfmisc_1(B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_45,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_41])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_28,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_167,plain,(
    ! [B_76,A_77,C_78] :
      ( r2_hidden(B_76,k1_tops_1(A_77,C_78))
      | ~ m1_connsp_2(C_78,A_77,B_76)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ m1_subset_1(B_76,u1_struct_0(A_77))
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_176,plain,(
    ! [B_76,A_77,A_3] :
      ( r2_hidden(B_76,k1_tops_1(A_77,A_3))
      | ~ m1_connsp_2(A_3,A_77,B_76)
      | ~ m1_subset_1(B_76,u1_struct_0(A_77))
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77)
      | v2_struct_0(A_77)
      | ~ r1_tarski(A_3,u1_struct_0(A_77)) ) ),
    inference(resolution,[status(thm)],[c_10,c_167])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_174,plain,(
    ! [B_76] :
      ( r2_hidden(B_76,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_76)
      | ~ m1_subset_1(B_76,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_167])).

tff(c_179,plain,(
    ! [B_76] :
      ( r2_hidden(B_76,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_76)
      | ~ m1_subset_1(B_76,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_174])).

tff(c_181,plain,(
    ! [B_79] :
      ( r2_hidden(B_79,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_79)
      | ~ m1_subset_1(B_79,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_179])).

tff(c_75,plain,(
    ! [C_49,B_50,A_51] :
      ( ~ v1_xboole_0(C_49)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(C_49))
      | ~ r2_hidden(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_80,plain,(
    ! [B_4,A_51,A_3] :
      ( ~ v1_xboole_0(B_4)
      | ~ r2_hidden(A_51,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_75])).

tff(c_189,plain,(
    ! [B_4,B_79] :
      ( ~ v1_xboole_0(B_4)
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),B_4)
      | ~ m1_connsp_2('#skF_3','#skF_1',B_79)
      | ~ m1_subset_1(B_79,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_181,c_80])).

tff(c_191,plain,(
    ! [B_80] :
      ( ~ m1_connsp_2('#skF_3','#skF_1',B_80)
      | ~ m1_subset_1(B_80,u1_struct_0('#skF_1')) ) ),
    inference(splitLeft,[status(thm)],[c_189])).

tff(c_194,plain,(
    ~ m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_191])).

tff(c_198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_194])).

tff(c_219,plain,(
    ! [B_82] :
      ( ~ v1_xboole_0(B_82)
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),B_82) ) ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_242,plain,(
    ~ v1_xboole_0(k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_219])).

tff(c_111,plain,(
    ! [A_58,B_59] :
      ( v3_pre_topc(k1_tops_1(A_58,B_59),A_58)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_116,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_111])).

tff(c_120,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_116])).

tff(c_97,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(k1_tops_1(A_56,B_57),B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_102,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_97])).

tff(c_106,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_102])).

tff(c_132,plain,(
    ! [A_65,B_66] :
      ( m1_subset_1(k1_tops_1(A_65,B_66),k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_26,plain,(
    ! [D_40] :
      ( ~ r1_tarski(D_40,'#skF_3')
      | ~ v3_pre_topc(D_40,'#skF_1')
      | ~ m1_connsp_2(D_40,'#skF_1','#skF_2')
      | ~ m1_subset_1(D_40,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v1_xboole_0(D_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_142,plain,(
    ! [B_66] :
      ( ~ r1_tarski(k1_tops_1('#skF_1',B_66),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_66),'#skF_1')
      | ~ m1_connsp_2(k1_tops_1('#skF_1',B_66),'#skF_1','#skF_2')
      | v1_xboole_0(k1_tops_1('#skF_1',B_66))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_132,c_26])).

tff(c_200,plain,(
    ! [B_81] :
      ( ~ r1_tarski(k1_tops_1('#skF_1',B_81),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_81),'#skF_1')
      | ~ m1_connsp_2(k1_tops_1('#skF_1',B_81),'#skF_1','#skF_2')
      | v1_xboole_0(k1_tops_1('#skF_1',B_81))
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_142])).

tff(c_211,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1','#skF_2')
    | v1_xboole_0(k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_200])).

tff(c_218,plain,
    ( ~ m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1','#skF_2')
    | v1_xboole_0(k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_106,c_211])).

tff(c_243,plain,(
    ~ m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_242,c_218])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k1_tops_1(A_8,B_9),k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_268,plain,(
    ! [B_96,A_97,C_98] :
      ( m1_connsp_2(B_96,A_97,C_98)
      | ~ r2_hidden(C_98,B_96)
      | ~ v3_pre_topc(B_96,A_97)
      | ~ m1_subset_1(C_98,u1_struct_0(A_97))
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97)
      | ~ v2_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_270,plain,(
    ! [B_96] :
      ( m1_connsp_2(B_96,'#skF_1','#skF_2')
      | ~ r2_hidden('#skF_2',B_96)
      | ~ v3_pre_topc(B_96,'#skF_1')
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_268])).

tff(c_273,plain,(
    ! [B_96] :
      ( m1_connsp_2(B_96,'#skF_1','#skF_2')
      | ~ r2_hidden('#skF_2',B_96)
      | ~ v3_pre_topc(B_96,'#skF_1')
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_270])).

tff(c_275,plain,(
    ! [B_99] :
      ( m1_connsp_2(B_99,'#skF_1','#skF_2')
      | ~ r2_hidden('#skF_2',B_99)
      | ~ v3_pre_topc(B_99,'#skF_1')
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_273])).

tff(c_279,plain,(
    ! [B_9] :
      ( m1_connsp_2(k1_tops_1('#skF_1',B_9),'#skF_1','#skF_2')
      | ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_9))
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_9),'#skF_1')
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_275])).

tff(c_327,plain,(
    ! [B_104] :
      ( m1_connsp_2(k1_tops_1('#skF_1',B_104),'#skF_1','#skF_2')
      | ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_104))
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_104),'#skF_1')
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_279])).

tff(c_338,plain,
    ( m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1','#skF_2')
    | ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_327])).

tff(c_345,plain,
    ( m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1','#skF_2')
    | ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_338])).

tff(c_346,plain,(
    ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_243,c_345])).

tff(c_349,plain,
    ( ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_176,c_346])).

tff(c_355,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_36,c_34,c_32,c_28,c_349])).

tff(c_357,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_355])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:53:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.64/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.34  
% 2.64/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.34  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.64/1.34  
% 2.64/1.34  %Foreground sorts:
% 2.64/1.34  
% 2.64/1.34  
% 2.64/1.34  %Background operators:
% 2.64/1.34  
% 2.64/1.34  
% 2.64/1.34  %Foreground operators:
% 2.64/1.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.64/1.34  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.64/1.34  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.64/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.64/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.64/1.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.64/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.64/1.34  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.64/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.64/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.64/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.64/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.64/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.64/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.64/1.34  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.64/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.64/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.64/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.64/1.34  
% 2.64/1.36  tff(f_129, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(C, A, B) & (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~((m1_connsp_2(D, A, B) & v3_pre_topc(D, A)) & r1_tarski(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_connsp_2)).
% 2.64/1.36  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.64/1.36  tff(f_80, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 2.64/1.36  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.64/1.36  tff(f_42, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.64/1.36  tff(f_56, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 2.64/1.36  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 2.64/1.36  tff(f_48, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 2.64/1.36  tff(f_99, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 2.64/1.36  tff(c_38, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.64/1.36  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.64/1.36  tff(c_41, plain, (![A_42, B_43]: (r1_tarski(A_42, B_43) | ~m1_subset_1(A_42, k1_zfmisc_1(B_43)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.64/1.36  tff(c_45, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_41])).
% 2.64/1.36  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.64/1.36  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.64/1.36  tff(c_32, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.64/1.36  tff(c_28, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.64/1.36  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.64/1.36  tff(c_167, plain, (![B_76, A_77, C_78]: (r2_hidden(B_76, k1_tops_1(A_77, C_78)) | ~m1_connsp_2(C_78, A_77, B_76) | ~m1_subset_1(C_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~m1_subset_1(B_76, u1_struct_0(A_77)) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.64/1.36  tff(c_176, plain, (![B_76, A_77, A_3]: (r2_hidden(B_76, k1_tops_1(A_77, A_3)) | ~m1_connsp_2(A_3, A_77, B_76) | ~m1_subset_1(B_76, u1_struct_0(A_77)) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77) | v2_struct_0(A_77) | ~r1_tarski(A_3, u1_struct_0(A_77)))), inference(resolution, [status(thm)], [c_10, c_167])).
% 2.64/1.36  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.64/1.36  tff(c_174, plain, (![B_76]: (r2_hidden(B_76, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_76) | ~m1_subset_1(B_76, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_167])).
% 2.64/1.36  tff(c_179, plain, (![B_76]: (r2_hidden(B_76, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_76) | ~m1_subset_1(B_76, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_174])).
% 2.64/1.36  tff(c_181, plain, (![B_79]: (r2_hidden(B_79, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_79) | ~m1_subset_1(B_79, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_38, c_179])).
% 2.64/1.36  tff(c_75, plain, (![C_49, B_50, A_51]: (~v1_xboole_0(C_49) | ~m1_subset_1(B_50, k1_zfmisc_1(C_49)) | ~r2_hidden(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.64/1.36  tff(c_80, plain, (![B_4, A_51, A_3]: (~v1_xboole_0(B_4) | ~r2_hidden(A_51, A_3) | ~r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_10, c_75])).
% 2.64/1.36  tff(c_189, plain, (![B_4, B_79]: (~v1_xboole_0(B_4) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), B_4) | ~m1_connsp_2('#skF_3', '#skF_1', B_79) | ~m1_subset_1(B_79, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_181, c_80])).
% 2.64/1.36  tff(c_191, plain, (![B_80]: (~m1_connsp_2('#skF_3', '#skF_1', B_80) | ~m1_subset_1(B_80, u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_189])).
% 2.64/1.36  tff(c_194, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_191])).
% 2.64/1.36  tff(c_198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_194])).
% 2.64/1.36  tff(c_219, plain, (![B_82]: (~v1_xboole_0(B_82) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), B_82))), inference(splitRight, [status(thm)], [c_189])).
% 2.64/1.36  tff(c_242, plain, (~v1_xboole_0(k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_6, c_219])).
% 2.64/1.36  tff(c_111, plain, (![A_58, B_59]: (v3_pre_topc(k1_tops_1(A_58, B_59), A_58) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.64/1.36  tff(c_116, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_111])).
% 2.64/1.36  tff(c_120, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_116])).
% 2.64/1.36  tff(c_97, plain, (![A_56, B_57]: (r1_tarski(k1_tops_1(A_56, B_57), B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.64/1.36  tff(c_102, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_97])).
% 2.64/1.36  tff(c_106, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_102])).
% 2.64/1.36  tff(c_132, plain, (![A_65, B_66]: (m1_subset_1(k1_tops_1(A_65, B_66), k1_zfmisc_1(u1_struct_0(A_65))) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.64/1.36  tff(c_26, plain, (![D_40]: (~r1_tarski(D_40, '#skF_3') | ~v3_pre_topc(D_40, '#skF_1') | ~m1_connsp_2(D_40, '#skF_1', '#skF_2') | ~m1_subset_1(D_40, k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(D_40))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.64/1.36  tff(c_142, plain, (![B_66]: (~r1_tarski(k1_tops_1('#skF_1', B_66), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_66), '#skF_1') | ~m1_connsp_2(k1_tops_1('#skF_1', B_66), '#skF_1', '#skF_2') | v1_xboole_0(k1_tops_1('#skF_1', B_66)) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_132, c_26])).
% 2.64/1.36  tff(c_200, plain, (![B_81]: (~r1_tarski(k1_tops_1('#skF_1', B_81), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_81), '#skF_1') | ~m1_connsp_2(k1_tops_1('#skF_1', B_81), '#skF_1', '#skF_2') | v1_xboole_0(k1_tops_1('#skF_1', B_81)) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_142])).
% 2.64/1.36  tff(c_211, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', '#skF_2') | v1_xboole_0(k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_200])).
% 2.64/1.36  tff(c_218, plain, (~m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', '#skF_2') | v1_xboole_0(k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_106, c_211])).
% 2.64/1.36  tff(c_243, plain, (~m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_242, c_218])).
% 2.64/1.36  tff(c_14, plain, (![A_8, B_9]: (m1_subset_1(k1_tops_1(A_8, B_9), k1_zfmisc_1(u1_struct_0(A_8))) | ~m1_subset_1(B_9, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.64/1.36  tff(c_268, plain, (![B_96, A_97, C_98]: (m1_connsp_2(B_96, A_97, C_98) | ~r2_hidden(C_98, B_96) | ~v3_pre_topc(B_96, A_97) | ~m1_subset_1(C_98, u1_struct_0(A_97)) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97) | ~v2_pre_topc(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.64/1.36  tff(c_270, plain, (![B_96]: (m1_connsp_2(B_96, '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', B_96) | ~v3_pre_topc(B_96, '#skF_1') | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_268])).
% 2.64/1.36  tff(c_273, plain, (![B_96]: (m1_connsp_2(B_96, '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', B_96) | ~v3_pre_topc(B_96, '#skF_1') | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_270])).
% 2.64/1.36  tff(c_275, plain, (![B_99]: (m1_connsp_2(B_99, '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', B_99) | ~v3_pre_topc(B_99, '#skF_1') | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_38, c_273])).
% 2.64/1.36  tff(c_279, plain, (![B_9]: (m1_connsp_2(k1_tops_1('#skF_1', B_9), '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_9)) | ~v3_pre_topc(k1_tops_1('#skF_1', B_9), '#skF_1') | ~m1_subset_1(B_9, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_275])).
% 2.64/1.36  tff(c_327, plain, (![B_104]: (m1_connsp_2(k1_tops_1('#skF_1', B_104), '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_104)) | ~v3_pre_topc(k1_tops_1('#skF_1', B_104), '#skF_1') | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_279])).
% 2.64/1.36  tff(c_338, plain, (m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_30, c_327])).
% 2.64/1.36  tff(c_345, plain, (m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_338])).
% 2.64/1.36  tff(c_346, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_243, c_345])).
% 2.64/1.36  tff(c_349, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_176, c_346])).
% 2.64/1.36  tff(c_355, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_45, c_36, c_34, c_32, c_28, c_349])).
% 2.64/1.36  tff(c_357, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_355])).
% 2.64/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.36  
% 2.64/1.36  Inference rules
% 2.64/1.36  ----------------------
% 2.64/1.36  #Ref     : 0
% 2.64/1.36  #Sup     : 58
% 2.64/1.36  #Fact    : 0
% 2.64/1.36  #Define  : 0
% 2.64/1.36  #Split   : 6
% 2.64/1.36  #Chain   : 0
% 2.64/1.36  #Close   : 0
% 2.64/1.36  
% 2.64/1.36  Ordering : KBO
% 2.64/1.36  
% 2.64/1.36  Simplification rules
% 2.64/1.36  ----------------------
% 2.64/1.36  #Subsume      : 8
% 2.64/1.36  #Demod        : 39
% 2.64/1.36  #Tautology    : 6
% 2.64/1.36  #SimpNegUnit  : 7
% 2.64/1.36  #BackRed      : 0
% 2.64/1.36  
% 2.64/1.36  #Partial instantiations: 0
% 2.64/1.36  #Strategies tried      : 1
% 2.64/1.36  
% 2.64/1.36  Timing (in seconds)
% 2.64/1.36  ----------------------
% 2.64/1.36  Preprocessing        : 0.30
% 2.64/1.36  Parsing              : 0.17
% 2.64/1.36  CNF conversion       : 0.02
% 2.64/1.36  Main loop            : 0.29
% 2.64/1.36  Inferencing          : 0.11
% 2.64/1.36  Reduction            : 0.08
% 2.64/1.36  Demodulation         : 0.06
% 2.64/1.36  BG Simplification    : 0.01
% 2.64/1.36  Subsumption          : 0.06
% 2.64/1.36  Abstraction          : 0.01
% 2.64/1.36  MUC search           : 0.00
% 2.64/1.36  Cooper               : 0.00
% 2.64/1.36  Total                : 0.63
% 2.64/1.37  Index Insertion      : 0.00
% 2.64/1.37  Index Deletion       : 0.00
% 2.64/1.37  Index Matching       : 0.00
% 2.64/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
