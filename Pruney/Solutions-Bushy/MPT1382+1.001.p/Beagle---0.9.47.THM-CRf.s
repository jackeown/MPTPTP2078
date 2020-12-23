%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1382+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:53 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 291 expanded)
%              Number of leaves         :   24 ( 119 expanded)
%              Depth                    :   16
%              Number of atoms          :  217 (1520 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   5 average)
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

tff(f_133,negated_conjecture,(
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

tff(f_41,axiom,(
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

tff(f_79,axiom,(
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

tff(f_103,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_98,axiom,(
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

tff(c_30,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_26,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_34,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_83,plain,(
    ! [B_76,A_77,C_78] :
      ( r2_hidden(B_76,k1_tops_1(A_77,C_78))
      | ~ m1_connsp_2(C_78,A_77,B_76)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ m1_subset_1(B_76,u1_struct_0(A_77))
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_87,plain,(
    ! [B_76] :
      ( r2_hidden(B_76,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_76)
      | ~ m1_subset_1(B_76,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_83])).

tff(c_91,plain,(
    ! [B_76] :
      ( r2_hidden(B_76,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_76)
      | ~ m1_subset_1(B_76,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_87])).

tff(c_93,plain,(
    ! [B_79] :
      ( r2_hidden(B_79,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_79)
      | ~ m1_subset_1(B_79,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_91])).

tff(c_14,plain,(
    ! [A_15,B_22,C_23] :
      ( r1_tarski('#skF_1'(A_15,B_22,C_23),C_23)
      | ~ r2_hidden(B_22,k1_tops_1(A_15,C_23))
      | ~ m1_subset_1(C_23,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_97,plain,(
    ! [B_79] :
      ( r1_tarski('#skF_1'('#skF_2',B_79,'#skF_4'),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ m1_connsp_2('#skF_4','#skF_2',B_79)
      | ~ m1_subset_1(B_79,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_93,c_14])).

tff(c_109,plain,(
    ! [B_79] :
      ( r1_tarski('#skF_1'('#skF_2',B_79,'#skF_4'),'#skF_4')
      | ~ m1_connsp_2('#skF_4','#skF_2',B_79)
      | ~ m1_subset_1(B_79,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_28,c_97])).

tff(c_92,plain,(
    ! [B_76] :
      ( r2_hidden(B_76,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_76)
      | ~ m1_subset_1(B_76,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_91])).

tff(c_12,plain,(
    ! [B_22,A_15,C_23] :
      ( r2_hidden(B_22,'#skF_1'(A_15,B_22,C_23))
      | ~ r2_hidden(B_22,k1_tops_1(A_15,C_23))
      | ~ m1_subset_1(C_23,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_99,plain,(
    ! [B_79] :
      ( r2_hidden(B_79,'#skF_1'('#skF_2',B_79,'#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ m1_connsp_2('#skF_4','#skF_2',B_79)
      | ~ m1_subset_1(B_79,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_93,c_12])).

tff(c_129,plain,(
    ! [B_84] :
      ( r2_hidden(B_84,'#skF_1'('#skF_2',B_84,'#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_84)
      | ~ m1_subset_1(B_84,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_28,c_99])).

tff(c_22,plain,(
    ! [B_35,A_34] :
      ( ~ v1_xboole_0(B_35)
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_134,plain,(
    ! [B_85] :
      ( ~ v1_xboole_0('#skF_1'('#skF_2',B_85,'#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_85)
      | ~ m1_subset_1(B_85,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_129,c_22])).

tff(c_140,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_134])).

tff(c_144,plain,(
    ~ v1_xboole_0('#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_140])).

tff(c_112,plain,(
    ! [B_79] :
      ( r2_hidden(B_79,'#skF_1'('#skF_2',B_79,'#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_79)
      | ~ m1_subset_1(B_79,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_28,c_99])).

tff(c_58,plain,(
    ! [A_58,B_59,C_60] :
      ( v3_pre_topc('#skF_1'(A_58,B_59,C_60),A_58)
      | ~ r2_hidden(B_59,k1_tops_1(A_58,C_60))
      | ~ m1_subset_1(C_60,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_60,plain,(
    ! [B_59] :
      ( v3_pre_topc('#skF_1'('#skF_2',B_59,'#skF_4'),'#skF_2')
      | ~ r2_hidden(B_59,k1_tops_1('#skF_2','#skF_4'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_58])).

tff(c_63,plain,(
    ! [B_59] :
      ( v3_pre_topc('#skF_1'('#skF_2',B_59,'#skF_4'),'#skF_2')
      | ~ r2_hidden(B_59,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_60])).

tff(c_18,plain,(
    ! [A_15,B_22,C_23] :
      ( m1_subset_1('#skF_1'(A_15,B_22,C_23),k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ r2_hidden(B_22,k1_tops_1(A_15,C_23))
      | ~ m1_subset_1(C_23,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_116,plain,(
    ! [B_81,A_82,C_83] :
      ( m1_connsp_2(B_81,A_82,C_83)
      | ~ r2_hidden(C_83,B_81)
      | ~ v3_pre_topc(B_81,A_82)
      | ~ m1_subset_1(C_83,u1_struct_0(A_82))
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82)
      | ~ v2_pre_topc(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_120,plain,(
    ! [B_81] :
      ( m1_connsp_2(B_81,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_81)
      | ~ v3_pre_topc(B_81,'#skF_2')
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_116])).

tff(c_127,plain,(
    ! [B_81] :
      ( m1_connsp_2(B_81,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_81)
      | ~ v3_pre_topc(B_81,'#skF_2')
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_120])).

tff(c_145,plain,(
    ! [B_86] :
      ( m1_connsp_2(B_86,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_86)
      | ~ v3_pre_topc(B_86,'#skF_2')
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_127])).

tff(c_149,plain,(
    ! [B_22,C_23] :
      ( m1_connsp_2('#skF_1'('#skF_2',B_22,C_23),'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_22,C_23))
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_22,C_23),'#skF_2')
      | ~ r2_hidden(B_22,k1_tops_1('#skF_2',C_23))
      | ~ m1_subset_1(C_23,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_145])).

tff(c_182,plain,(
    ! [B_98,C_99] :
      ( m1_connsp_2('#skF_1'('#skF_2',B_98,C_99),'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_98,C_99))
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_98,C_99),'#skF_2')
      | ~ r2_hidden(B_98,k1_tops_1('#skF_2',C_99))
      | ~ m1_subset_1(C_99,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_149])).

tff(c_193,plain,(
    ! [B_104] :
      ( m1_connsp_2('#skF_1'('#skF_2',B_104,'#skF_4'),'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_104,'#skF_4'))
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_104,'#skF_4'),'#skF_2')
      | ~ r2_hidden(B_104,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_28,c_182])).

tff(c_67,plain,(
    ! [A_68,B_69,C_70] :
      ( m1_subset_1('#skF_1'(A_68,B_69,C_70),k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ r2_hidden(B_69,k1_tops_1(A_68,C_70))
      | ~ m1_subset_1(C_70,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_24,plain,(
    ! [D_47] :
      ( ~ r1_tarski(D_47,'#skF_4')
      | ~ v3_pre_topc(D_47,'#skF_2')
      | ~ m1_connsp_2(D_47,'#skF_2','#skF_3')
      | ~ m1_subset_1(D_47,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v1_xboole_0(D_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_73,plain,(
    ! [B_69,C_70] :
      ( ~ r1_tarski('#skF_1'('#skF_2',B_69,C_70),'#skF_4')
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_69,C_70),'#skF_2')
      | ~ m1_connsp_2('#skF_1'('#skF_2',B_69,C_70),'#skF_2','#skF_3')
      | v1_xboole_0('#skF_1'('#skF_2',B_69,C_70))
      | ~ r2_hidden(B_69,k1_tops_1('#skF_2',C_70))
      | ~ m1_subset_1(C_70,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_67,c_24])).

tff(c_79,plain,(
    ! [B_69,C_70] :
      ( ~ r1_tarski('#skF_1'('#skF_2',B_69,C_70),'#skF_4')
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_69,C_70),'#skF_2')
      | ~ m1_connsp_2('#skF_1'('#skF_2',B_69,C_70),'#skF_2','#skF_3')
      | v1_xboole_0('#skF_1'('#skF_2',B_69,C_70))
      | ~ r2_hidden(B_69,k1_tops_1('#skF_2',C_70))
      | ~ m1_subset_1(C_70,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_73])).

tff(c_195,plain,(
    ! [B_104] :
      ( ~ r1_tarski('#skF_1'('#skF_2',B_104,'#skF_4'),'#skF_4')
      | v1_xboole_0('#skF_1'('#skF_2',B_104,'#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_104,'#skF_4'))
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_104,'#skF_4'),'#skF_2')
      | ~ r2_hidden(B_104,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_193,c_79])).

tff(c_243,plain,(
    ! [B_109] :
      ( ~ r1_tarski('#skF_1'('#skF_2',B_109,'#skF_4'),'#skF_4')
      | v1_xboole_0('#skF_1'('#skF_2',B_109,'#skF_4'))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_109,'#skF_4'))
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_109,'#skF_4'),'#skF_2')
      | ~ r2_hidden(B_109,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_195])).

tff(c_248,plain,(
    ! [B_110] :
      ( ~ r1_tarski('#skF_1'('#skF_2',B_110,'#skF_4'),'#skF_4')
      | v1_xboole_0('#skF_1'('#skF_2',B_110,'#skF_4'))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_110,'#skF_4'))
      | ~ r2_hidden(B_110,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_63,c_243])).

tff(c_251,plain,
    ( ~ r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_112,c_248])).

tff(c_254,plain,
    ( ~ r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_251])).

tff(c_255,plain,
    ( ~ r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_254])).

tff(c_256,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_255])).

tff(c_259,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_92,c_256])).

tff(c_263,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_259])).

tff(c_264,plain,(
    ~ r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_255])).

tff(c_308,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_109,c_264])).

tff(c_312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_308])).

%------------------------------------------------------------------------------
