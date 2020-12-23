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
% DateTime   : Thu Dec  3 10:24:13 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 751 expanded)
%              Number of leaves         :   22 ( 279 expanded)
%              Depth                    :   12
%              Number of atoms          :  507 (3741 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( m1_connsp_2(C,A,B)
                <=> ? [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                      & v3_pre_topc(D,A)
                      & r1_tarski(D,C)
                      & r2_hidden(B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).

tff(f_43,axiom,(
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

tff(f_60,axiom,(
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

tff(c_18,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_40,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | v3_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_45,plain,(
    v3_pre_topc('#skF_5','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_36,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_47,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_32,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_46,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_44,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_24,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_26,plain,(
    ! [D_38] :
      ( ~ r2_hidden('#skF_3',D_38)
      | ~ r1_tarski(D_38,'#skF_4')
      | ~ v3_pre_topc(D_38,'#skF_2')
      | ~ m1_subset_1(D_38,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_52,plain,(
    ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_22,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_20,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_16,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_128,plain,(
    ! [B_65,A_66,C_67,D_68] :
      ( r2_hidden(B_65,k1_tops_1(A_66,C_67))
      | ~ r2_hidden(B_65,D_68)
      | ~ r1_tarski(D_68,C_67)
      | ~ v3_pre_topc(D_68,A_66)
      | ~ m1_subset_1(D_68,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ m1_subset_1(C_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_144,plain,(
    ! [A_69,C_70] :
      ( r2_hidden('#skF_3',k1_tops_1(A_69,C_70))
      | ~ r1_tarski('#skF_5',C_70)
      | ~ v3_pre_topc('#skF_5',A_69)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ m1_subset_1(C_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69)
      | ~ v2_pre_topc(A_69) ) ),
    inference(resolution,[status(thm)],[c_46,c_128])).

tff(c_146,plain,(
    ! [C_70] :
      ( r2_hidden('#skF_3',k1_tops_1('#skF_2',C_70))
      | ~ r1_tarski('#skF_5',C_70)
      | ~ v3_pre_topc('#skF_5','#skF_2')
      | ~ m1_subset_1(C_70,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_48,c_144])).

tff(c_151,plain,(
    ! [C_75] :
      ( r2_hidden('#skF_3',k1_tops_1('#skF_2',C_75))
      | ~ r1_tarski('#skF_5',C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_45,c_146])).

tff(c_161,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_151])).

tff(c_168,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_161])).

tff(c_12,plain,(
    ! [C_19,A_13,B_17] :
      ( m1_connsp_2(C_19,A_13,B_17)
      | ~ r2_hidden(B_17,k1_tops_1(A_13,C_19))
      | ~ m1_subset_1(C_19,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ m1_subset_1(B_17,u1_struct_0(A_13))
      | ~ l1_pre_topc(A_13)
      | ~ v2_pre_topc(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_172,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_168,c_12])).

tff(c_180,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_16,c_172])).

tff(c_182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_52,c_180])).

tff(c_186,plain,(
    ! [D_76] :
      ( ~ r2_hidden('#skF_3',D_76)
      | ~ r1_tarski(D_76,'#skF_4')
      | ~ v3_pre_topc(D_76,'#skF_2')
      | ~ m1_subset_1(D_76,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_189,plain,
    ( ~ r2_hidden('#skF_3','#skF_5')
    | ~ r1_tarski('#skF_5','#skF_4')
    | ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_186])).

tff(c_196,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_47,c_46,c_189])).

tff(c_197,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_231,plain,(
    ! [B_91,A_92,C_93] :
      ( r2_hidden(B_91,k1_tops_1(A_92,C_93))
      | ~ m1_connsp_2(C_93,A_92,B_91)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ m1_subset_1(B_91,u1_struct_0(A_92))
      | ~ l1_pre_topc(A_92)
      | ~ v2_pre_topc(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_235,plain,(
    ! [B_91] :
      ( r2_hidden(B_91,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_91)
      | ~ m1_subset_1(B_91,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_231])).

tff(c_239,plain,(
    ! [B_91] :
      ( r2_hidden(B_91,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_91)
      | ~ m1_subset_1(B_91,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_235])).

tff(c_241,plain,(
    ! [B_94] :
      ( r2_hidden(B_94,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_94)
      | ~ m1_subset_1(B_94,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_239])).

tff(c_6,plain,(
    ! [A_1,B_8,C_9] :
      ( r1_tarski('#skF_1'(A_1,B_8,C_9),C_9)
      | ~ r2_hidden(B_8,k1_tops_1(A_1,C_9))
      | ~ m1_subset_1(C_9,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_245,plain,(
    ! [B_94] :
      ( r1_tarski('#skF_1'('#skF_2',B_94,'#skF_4'),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ m1_connsp_2('#skF_4','#skF_2',B_94)
      | ~ m1_subset_1(B_94,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_241,c_6])).

tff(c_251,plain,(
    ! [B_94] :
      ( r1_tarski('#skF_1'('#skF_2',B_94,'#skF_4'),'#skF_4')
      | ~ m1_connsp_2('#skF_4','#skF_2',B_94)
      | ~ m1_subset_1(B_94,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_16,c_245])).

tff(c_240,plain,(
    ! [B_91] :
      ( r2_hidden(B_91,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_91)
      | ~ m1_subset_1(B_91,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_239])).

tff(c_4,plain,(
    ! [B_8,A_1,C_9] :
      ( r2_hidden(B_8,'#skF_1'(A_1,B_8,C_9))
      | ~ r2_hidden(B_8,k1_tops_1(A_1,C_9))
      | ~ m1_subset_1(C_9,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_243,plain,(
    ! [B_94] :
      ( r2_hidden(B_94,'#skF_1'('#skF_2',B_94,'#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ m1_connsp_2('#skF_4','#skF_2',B_94)
      | ~ m1_subset_1(B_94,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_241,c_4])).

tff(c_248,plain,(
    ! [B_94] :
      ( r2_hidden(B_94,'#skF_1'('#skF_2',B_94,'#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_94)
      | ~ m1_subset_1(B_94,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_16,c_243])).

tff(c_212,plain,(
    ! [A_81,B_82,C_83] :
      ( v3_pre_topc('#skF_1'(A_81,B_82,C_83),A_81)
      | ~ r2_hidden(B_82,k1_tops_1(A_81,C_83))
      | ~ m1_subset_1(C_83,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_214,plain,(
    ! [B_82] :
      ( v3_pre_topc('#skF_1'('#skF_2',B_82,'#skF_4'),'#skF_2')
      | ~ r2_hidden(B_82,k1_tops_1('#skF_2','#skF_4'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_212])).

tff(c_217,plain,(
    ! [B_82] :
      ( v3_pre_topc('#skF_1'('#skF_2',B_82,'#skF_4'),'#skF_2')
      | ~ r2_hidden(B_82,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_214])).

tff(c_220,plain,(
    ! [A_88,B_89,C_90] :
      ( m1_subset_1('#skF_1'(A_88,B_89,C_90),k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ r2_hidden(B_89,k1_tops_1(A_88,C_90))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_203,plain,(
    ! [D_38] :
      ( ~ r2_hidden('#skF_3',D_38)
      | ~ r1_tarski(D_38,'#skF_4')
      | ~ v3_pre_topc(D_38,'#skF_2')
      | ~ m1_subset_1(D_38,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_26])).

tff(c_226,plain,(
    ! [B_89,C_90] :
      ( ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_89,C_90))
      | ~ r1_tarski('#skF_1'('#skF_2',B_89,C_90),'#skF_4')
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_89,C_90),'#skF_2')
      | ~ r2_hidden(B_89,k1_tops_1('#skF_2',C_90))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_220,c_203])).

tff(c_254,plain,(
    ! [B_97,C_98] :
      ( ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_97,C_98))
      | ~ r1_tarski('#skF_1'('#skF_2',B_97,C_98),'#skF_4')
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_97,C_98),'#skF_2')
      | ~ r2_hidden(B_97,k1_tops_1('#skF_2',C_98))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_226])).

tff(c_256,plain,(
    ! [B_82] :
      ( ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_82,'#skF_4'))
      | ~ r1_tarski('#skF_1'('#skF_2',B_82,'#skF_4'),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(B_82,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_217,c_254])).

tff(c_260,plain,(
    ! [B_99] :
      ( ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_99,'#skF_4'))
      | ~ r1_tarski('#skF_1'('#skF_2',B_99,'#skF_4'),'#skF_4')
      | ~ r2_hidden(B_99,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_256])).

tff(c_263,plain,
    ( ~ r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_248,c_260])).

tff(c_266,plain,
    ( ~ r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_197,c_263])).

tff(c_267,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_266])).

tff(c_270,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_240,c_267])).

tff(c_274,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_197,c_270])).

tff(c_275,plain,(
    ~ r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_266])).

tff(c_289,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_251,c_275])).

tff(c_293,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_197,c_289])).

tff(c_294,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_328,plain,(
    ! [B_114,A_115,C_116] :
      ( r2_hidden(B_114,k1_tops_1(A_115,C_116))
      | ~ m1_connsp_2(C_116,A_115,B_114)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ m1_subset_1(B_114,u1_struct_0(A_115))
      | ~ l1_pre_topc(A_115)
      | ~ v2_pre_topc(A_115)
      | v2_struct_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_332,plain,(
    ! [B_114] :
      ( r2_hidden(B_114,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_114)
      | ~ m1_subset_1(B_114,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_328])).

tff(c_336,plain,(
    ! [B_114] :
      ( r2_hidden(B_114,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_114)
      | ~ m1_subset_1(B_114,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_332])).

tff(c_338,plain,(
    ! [B_117] :
      ( r2_hidden(B_117,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_117)
      | ~ m1_subset_1(B_117,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_336])).

tff(c_340,plain,(
    ! [B_117] :
      ( r1_tarski('#skF_1'('#skF_2',B_117,'#skF_4'),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ m1_connsp_2('#skF_4','#skF_2',B_117)
      | ~ m1_subset_1(B_117,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_338,c_6])).

tff(c_345,plain,(
    ! [B_117] :
      ( r1_tarski('#skF_1'('#skF_2',B_117,'#skF_4'),'#skF_4')
      | ~ m1_connsp_2('#skF_4','#skF_2',B_117)
      | ~ m1_subset_1(B_117,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_16,c_340])).

tff(c_337,plain,(
    ! [B_114] :
      ( r2_hidden(B_114,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_114)
      | ~ m1_subset_1(B_114,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_336])).

tff(c_342,plain,(
    ! [B_117] :
      ( r2_hidden(B_117,'#skF_1'('#skF_2',B_117,'#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ m1_connsp_2('#skF_4','#skF_2',B_117)
      | ~ m1_subset_1(B_117,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_338,c_4])).

tff(c_348,plain,(
    ! [B_117] :
      ( r2_hidden(B_117,'#skF_1'('#skF_2',B_117,'#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_117)
      | ~ m1_subset_1(B_117,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_16,c_342])).

tff(c_310,plain,(
    ! [A_107,B_108,C_109] :
      ( v3_pre_topc('#skF_1'(A_107,B_108,C_109),A_107)
      | ~ r2_hidden(B_108,k1_tops_1(A_107,C_109))
      | ~ m1_subset_1(C_109,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107)
      | ~ v2_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_312,plain,(
    ! [B_108] :
      ( v3_pre_topc('#skF_1'('#skF_2',B_108,'#skF_4'),'#skF_2')
      | ~ r2_hidden(B_108,k1_tops_1('#skF_2','#skF_4'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_310])).

tff(c_315,plain,(
    ! [B_108] :
      ( v3_pre_topc('#skF_1'('#skF_2',B_108,'#skF_4'),'#skF_2')
      | ~ r2_hidden(B_108,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_312])).

tff(c_317,plain,(
    ! [A_111,B_112,C_113] :
      ( m1_subset_1('#skF_1'(A_111,B_112,C_113),k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ r2_hidden(B_112,k1_tops_1(A_111,C_113))
      | ~ m1_subset_1(C_113,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_pre_topc(A_111)
      | ~ v2_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_295,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_34,plain,(
    ! [D_38] :
      ( ~ r2_hidden('#skF_3',D_38)
      | ~ r1_tarski(D_38,'#skF_4')
      | ~ v3_pre_topc(D_38,'#skF_2')
      | ~ m1_subset_1(D_38,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r1_tarski('#skF_5','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_299,plain,(
    ! [D_38] :
      ( ~ r2_hidden('#skF_3',D_38)
      | ~ r1_tarski(D_38,'#skF_4')
      | ~ v3_pre_topc(D_38,'#skF_2')
      | ~ m1_subset_1(D_38,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_295,c_34])).

tff(c_323,plain,(
    ! [B_112,C_113] :
      ( ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_112,C_113))
      | ~ r1_tarski('#skF_1'('#skF_2',B_112,C_113),'#skF_4')
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_112,C_113),'#skF_2')
      | ~ r2_hidden(B_112,k1_tops_1('#skF_2',C_113))
      | ~ m1_subset_1(C_113,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_317,c_299])).

tff(c_369,plain,(
    ! [B_129,C_130] :
      ( ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_129,C_130))
      | ~ r1_tarski('#skF_1'('#skF_2',B_129,C_130),'#skF_4')
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_129,C_130),'#skF_2')
      | ~ r2_hidden(B_129,k1_tops_1('#skF_2',C_130))
      | ~ m1_subset_1(C_130,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_323])).

tff(c_371,plain,(
    ! [B_108] :
      ( ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_108,'#skF_4'))
      | ~ r1_tarski('#skF_1'('#skF_2',B_108,'#skF_4'),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(B_108,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_315,c_369])).

tff(c_375,plain,(
    ! [B_131] :
      ( ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_131,'#skF_4'))
      | ~ r1_tarski('#skF_1'('#skF_2',B_131,'#skF_4'),'#skF_4')
      | ~ r2_hidden(B_131,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_371])).

tff(c_378,plain,
    ( ~ r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_348,c_375])).

tff(c_381,plain,
    ( ~ r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_294,c_378])).

tff(c_383,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_381])).

tff(c_386,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_337,c_383])).

tff(c_390,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_294,c_386])).

tff(c_391,plain,(
    ~ r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_381])).

tff(c_414,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_345,c_391])).

tff(c_418,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_294,c_414])).

tff(c_419,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_454,plain,(
    ! [B_152,A_153,C_154] :
      ( r2_hidden(B_152,k1_tops_1(A_153,C_154))
      | ~ m1_connsp_2(C_154,A_153,B_152)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ m1_subset_1(B_152,u1_struct_0(A_153))
      | ~ l1_pre_topc(A_153)
      | ~ v2_pre_topc(A_153)
      | v2_struct_0(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_458,plain,(
    ! [B_152] :
      ( r2_hidden(B_152,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_152)
      | ~ m1_subset_1(B_152,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_454])).

tff(c_462,plain,(
    ! [B_152] :
      ( r2_hidden(B_152,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_152)
      | ~ m1_subset_1(B_152,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_458])).

tff(c_464,plain,(
    ! [B_155] :
      ( r2_hidden(B_155,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_155)
      | ~ m1_subset_1(B_155,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_462])).

tff(c_468,plain,(
    ! [B_155] :
      ( r1_tarski('#skF_1'('#skF_2',B_155,'#skF_4'),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ m1_connsp_2('#skF_4','#skF_2',B_155)
      | ~ m1_subset_1(B_155,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_464,c_6])).

tff(c_477,plain,(
    ! [B_155] :
      ( r1_tarski('#skF_1'('#skF_2',B_155,'#skF_4'),'#skF_4')
      | ~ m1_connsp_2('#skF_4','#skF_2',B_155)
      | ~ m1_subset_1(B_155,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_16,c_468])).

tff(c_463,plain,(
    ! [B_152] :
      ( r2_hidden(B_152,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_152)
      | ~ m1_subset_1(B_152,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_462])).

tff(c_470,plain,(
    ! [B_155] :
      ( r2_hidden(B_155,'#skF_1'('#skF_2',B_155,'#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ m1_connsp_2('#skF_4','#skF_2',B_155)
      | ~ m1_subset_1(B_155,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_464,c_4])).

tff(c_480,plain,(
    ! [B_155] :
      ( r2_hidden(B_155,'#skF_1'('#skF_2',B_155,'#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_155)
      | ~ m1_subset_1(B_155,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_16,c_470])).

tff(c_433,plain,(
    ! [A_136,B_137,C_138] :
      ( v3_pre_topc('#skF_1'(A_136,B_137,C_138),A_136)
      | ~ r2_hidden(B_137,k1_tops_1(A_136,C_138))
      | ~ m1_subset_1(C_138,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_pre_topc(A_136)
      | ~ v2_pre_topc(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_435,plain,(
    ! [B_137] :
      ( v3_pre_topc('#skF_1'('#skF_2',B_137,'#skF_4'),'#skF_2')
      | ~ r2_hidden(B_137,k1_tops_1('#skF_2','#skF_4'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_433])).

tff(c_438,plain,(
    ! [B_137] :
      ( v3_pre_topc('#skF_1'('#skF_2',B_137,'#skF_4'),'#skF_2')
      | ~ r2_hidden(B_137,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_435])).

tff(c_442,plain,(
    ! [A_146,B_147,C_148] :
      ( m1_subset_1('#skF_1'(A_146,B_147,C_148),k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ r2_hidden(B_147,k1_tops_1(A_146,C_148))
      | ~ m1_subset_1(C_148,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ l1_pre_topc(A_146)
      | ~ v2_pre_topc(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_420,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_30,plain,(
    ! [D_38] :
      ( ~ r2_hidden('#skF_3',D_38)
      | ~ r1_tarski(D_38,'#skF_4')
      | ~ v3_pre_topc(D_38,'#skF_2')
      | ~ m1_subset_1(D_38,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r2_hidden('#skF_3','#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_423,plain,(
    ! [D_38] :
      ( ~ r2_hidden('#skF_3',D_38)
      | ~ r1_tarski(D_38,'#skF_4')
      | ~ v3_pre_topc(D_38,'#skF_2')
      | ~ m1_subset_1(D_38,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_420,c_30])).

tff(c_448,plain,(
    ! [B_147,C_148] :
      ( ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_147,C_148))
      | ~ r1_tarski('#skF_1'('#skF_2',B_147,C_148),'#skF_4')
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_147,C_148),'#skF_2')
      | ~ r2_hidden(B_147,k1_tops_1('#skF_2',C_148))
      | ~ m1_subset_1(C_148,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_442,c_423])).

tff(c_490,plain,(
    ! [B_162,C_163] :
      ( ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_162,C_163))
      | ~ r1_tarski('#skF_1'('#skF_2',B_162,C_163),'#skF_4')
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_162,C_163),'#skF_2')
      | ~ r2_hidden(B_162,k1_tops_1('#skF_2',C_163))
      | ~ m1_subset_1(C_163,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_448])).

tff(c_492,plain,(
    ! [B_137] :
      ( ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_137,'#skF_4'))
      | ~ r1_tarski('#skF_1'('#skF_2',B_137,'#skF_4'),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(B_137,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_438,c_490])).

tff(c_496,plain,(
    ! [B_164] :
      ( ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_164,'#skF_4'))
      | ~ r1_tarski('#skF_1'('#skF_2',B_164,'#skF_4'),'#skF_4')
      | ~ r2_hidden(B_164,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_492])).

tff(c_499,plain,
    ( ~ r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_480,c_496])).

tff(c_502,plain,
    ( ~ r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_419,c_499])).

tff(c_503,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_502])).

tff(c_507,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_463,c_503])).

tff(c_511,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_419,c_507])).

tff(c_512,plain,(
    ~ r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_502])).

tff(c_535,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_477,c_512])).

tff(c_539,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_419,c_535])).

tff(c_540,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_576,plain,(
    ! [B_185,A_186,C_187] :
      ( r2_hidden(B_185,k1_tops_1(A_186,C_187))
      | ~ m1_connsp_2(C_187,A_186,B_185)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(u1_struct_0(A_186)))
      | ~ m1_subset_1(B_185,u1_struct_0(A_186))
      | ~ l1_pre_topc(A_186)
      | ~ v2_pre_topc(A_186)
      | v2_struct_0(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_580,plain,(
    ! [B_185] :
      ( r2_hidden(B_185,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_185)
      | ~ m1_subset_1(B_185,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_576])).

tff(c_584,plain,(
    ! [B_185] :
      ( r2_hidden(B_185,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_185)
      | ~ m1_subset_1(B_185,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_580])).

tff(c_586,plain,(
    ! [B_188] :
      ( r2_hidden(B_188,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_188)
      | ~ m1_subset_1(B_188,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_584])).

tff(c_592,plain,(
    ! [B_188] :
      ( r1_tarski('#skF_1'('#skF_2',B_188,'#skF_4'),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ m1_connsp_2('#skF_4','#skF_2',B_188)
      | ~ m1_subset_1(B_188,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_586,c_6])).

tff(c_602,plain,(
    ! [B_188] :
      ( r1_tarski('#skF_1'('#skF_2',B_188,'#skF_4'),'#skF_4')
      | ~ m1_connsp_2('#skF_4','#skF_2',B_188)
      | ~ m1_subset_1(B_188,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_16,c_592])).

tff(c_585,plain,(
    ! [B_185] :
      ( r2_hidden(B_185,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_185)
      | ~ m1_subset_1(B_185,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_584])).

tff(c_590,plain,(
    ! [B_188] :
      ( r2_hidden(B_188,'#skF_1'('#skF_2',B_188,'#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ m1_connsp_2('#skF_4','#skF_2',B_188)
      | ~ m1_subset_1(B_188,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_586,c_4])).

tff(c_599,plain,(
    ! [B_188] :
      ( r2_hidden(B_188,'#skF_1'('#skF_2',B_188,'#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_188)
      | ~ m1_subset_1(B_188,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_16,c_590])).

tff(c_556,plain,(
    ! [A_172,B_173,C_174] :
      ( v3_pre_topc('#skF_1'(A_172,B_173,C_174),A_172)
      | ~ r2_hidden(B_173,k1_tops_1(A_172,C_174))
      | ~ m1_subset_1(C_174,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ l1_pre_topc(A_172)
      | ~ v2_pre_topc(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_558,plain,(
    ! [B_173] :
      ( v3_pre_topc('#skF_1'('#skF_2',B_173,'#skF_4'),'#skF_2')
      | ~ r2_hidden(B_173,k1_tops_1('#skF_2','#skF_4'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_556])).

tff(c_561,plain,(
    ! [B_173] :
      ( v3_pre_topc('#skF_1'('#skF_2',B_173,'#skF_4'),'#skF_2')
      | ~ r2_hidden(B_173,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_558])).

tff(c_564,plain,(
    ! [A_179,B_180,C_181] :
      ( m1_subset_1('#skF_1'(A_179,B_180,C_181),k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ r2_hidden(B_180,k1_tops_1(A_179,C_181))
      | ~ m1_subset_1(C_181,k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ l1_pre_topc(A_179)
      | ~ v2_pre_topc(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_541,plain,(
    ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_38,plain,(
    ! [D_38] :
      ( ~ r2_hidden('#skF_3',D_38)
      | ~ r1_tarski(D_38,'#skF_4')
      | ~ v3_pre_topc(D_38,'#skF_2')
      | ~ m1_subset_1(D_38,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v3_pre_topc('#skF_5','#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_546,plain,(
    ! [D_38] :
      ( ~ r2_hidden('#skF_3',D_38)
      | ~ r1_tarski(D_38,'#skF_4')
      | ~ v3_pre_topc(D_38,'#skF_2')
      | ~ m1_subset_1(D_38,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_541,c_38])).

tff(c_570,plain,(
    ! [B_180,C_181] :
      ( ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_180,C_181))
      | ~ r1_tarski('#skF_1'('#skF_2',B_180,C_181),'#skF_4')
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_180,C_181),'#skF_2')
      | ~ r2_hidden(B_180,k1_tops_1('#skF_2',C_181))
      | ~ m1_subset_1(C_181,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_564,c_546])).

tff(c_612,plain,(
    ! [B_195,C_196] :
      ( ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_195,C_196))
      | ~ r1_tarski('#skF_1'('#skF_2',B_195,C_196),'#skF_4')
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_195,C_196),'#skF_2')
      | ~ r2_hidden(B_195,k1_tops_1('#skF_2',C_196))
      | ~ m1_subset_1(C_196,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_570])).

tff(c_614,plain,(
    ! [B_173] :
      ( ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_173,'#skF_4'))
      | ~ r1_tarski('#skF_1'('#skF_2',B_173,'#skF_4'),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(B_173,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_561,c_612])).

tff(c_618,plain,(
    ! [B_197] :
      ( ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_197,'#skF_4'))
      | ~ r1_tarski('#skF_1'('#skF_2',B_197,'#skF_4'),'#skF_4')
      | ~ r2_hidden(B_197,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_614])).

tff(c_621,plain,
    ( ~ r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_599,c_618])).

tff(c_624,plain,
    ( ~ r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_540,c_621])).

tff(c_626,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_624])).

tff(c_629,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_585,c_626])).

tff(c_633,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_540,c_629])).

tff(c_634,plain,(
    ~ r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_624])).

tff(c_657,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_602,c_634])).

tff(c_661,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_540,c_657])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:13:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.47  
% 3.06/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.47  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.06/1.47  
% 3.06/1.47  %Foreground sorts:
% 3.06/1.47  
% 3.06/1.47  
% 3.06/1.47  %Background operators:
% 3.06/1.47  
% 3.06/1.47  
% 3.06/1.47  %Foreground operators:
% 3.06/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.06/1.47  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.06/1.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.06/1.47  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.06/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.06/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.06/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.06/1.47  tff('#skF_5', type, '#skF_5': $i).
% 3.06/1.47  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.06/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.06/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.06/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.06/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.06/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.06/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.06/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.06/1.47  
% 3.20/1.50  tff(f_85, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_connsp_2)).
% 3.20/1.50  tff(f_43, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k1_tops_1(A, C)) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_tops_1)).
% 3.20/1.50  tff(f_60, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 3.20/1.50  tff(c_18, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.20/1.50  tff(c_40, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | v3_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.20/1.50  tff(c_45, plain, (v3_pre_topc('#skF_5', '#skF_2')), inference(splitLeft, [status(thm)], [c_40])).
% 3.20/1.50  tff(c_36, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.20/1.50  tff(c_47, plain, (r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_36])).
% 3.20/1.50  tff(c_32, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.20/1.50  tff(c_46, plain, (r2_hidden('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_32])).
% 3.20/1.50  tff(c_44, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.20/1.50  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_44])).
% 3.20/1.50  tff(c_24, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.20/1.50  tff(c_26, plain, (![D_38]: (~r2_hidden('#skF_3', D_38) | ~r1_tarski(D_38, '#skF_4') | ~v3_pre_topc(D_38, '#skF_2') | ~m1_subset_1(D_38, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_connsp_2('#skF_4', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.20/1.50  tff(c_52, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_26])).
% 3.20/1.50  tff(c_22, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.20/1.50  tff(c_20, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.20/1.50  tff(c_16, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.20/1.50  tff(c_128, plain, (![B_65, A_66, C_67, D_68]: (r2_hidden(B_65, k1_tops_1(A_66, C_67)) | ~r2_hidden(B_65, D_68) | ~r1_tarski(D_68, C_67) | ~v3_pre_topc(D_68, A_66) | ~m1_subset_1(D_68, k1_zfmisc_1(u1_struct_0(A_66))) | ~m1_subset_1(C_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.20/1.50  tff(c_144, plain, (![A_69, C_70]: (r2_hidden('#skF_3', k1_tops_1(A_69, C_70)) | ~r1_tarski('#skF_5', C_70) | ~v3_pre_topc('#skF_5', A_69) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_69))) | ~m1_subset_1(C_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69) | ~v2_pre_topc(A_69))), inference(resolution, [status(thm)], [c_46, c_128])).
% 3.20/1.50  tff(c_146, plain, (![C_70]: (r2_hidden('#skF_3', k1_tops_1('#skF_2', C_70)) | ~r1_tarski('#skF_5', C_70) | ~v3_pre_topc('#skF_5', '#skF_2') | ~m1_subset_1(C_70, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_144])).
% 3.20/1.50  tff(c_151, plain, (![C_75]: (r2_hidden('#skF_3', k1_tops_1('#skF_2', C_75)) | ~r1_tarski('#skF_5', C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_45, c_146])).
% 3.20/1.50  tff(c_161, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_16, c_151])).
% 3.20/1.50  tff(c_168, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_161])).
% 3.20/1.50  tff(c_12, plain, (![C_19, A_13, B_17]: (m1_connsp_2(C_19, A_13, B_17) | ~r2_hidden(B_17, k1_tops_1(A_13, C_19)) | ~m1_subset_1(C_19, k1_zfmisc_1(u1_struct_0(A_13))) | ~m1_subset_1(B_17, u1_struct_0(A_13)) | ~l1_pre_topc(A_13) | ~v2_pre_topc(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.20/1.50  tff(c_172, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_168, c_12])).
% 3.20/1.50  tff(c_180, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_18, c_16, c_172])).
% 3.20/1.50  tff(c_182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_52, c_180])).
% 3.20/1.50  tff(c_186, plain, (![D_76]: (~r2_hidden('#skF_3', D_76) | ~r1_tarski(D_76, '#skF_4') | ~v3_pre_topc(D_76, '#skF_2') | ~m1_subset_1(D_76, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_26])).
% 3.20/1.50  tff(c_189, plain, (~r2_hidden('#skF_3', '#skF_5') | ~r1_tarski('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_48, c_186])).
% 3.20/1.50  tff(c_196, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_45, c_47, c_46, c_189])).
% 3.20/1.50  tff(c_197, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 3.20/1.50  tff(c_231, plain, (![B_91, A_92, C_93]: (r2_hidden(B_91, k1_tops_1(A_92, C_93)) | ~m1_connsp_2(C_93, A_92, B_91) | ~m1_subset_1(C_93, k1_zfmisc_1(u1_struct_0(A_92))) | ~m1_subset_1(B_91, u1_struct_0(A_92)) | ~l1_pre_topc(A_92) | ~v2_pre_topc(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.20/1.50  tff(c_235, plain, (![B_91]: (r2_hidden(B_91, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_91) | ~m1_subset_1(B_91, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_231])).
% 3.20/1.50  tff(c_239, plain, (![B_91]: (r2_hidden(B_91, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_91) | ~m1_subset_1(B_91, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_235])).
% 3.20/1.50  tff(c_241, plain, (![B_94]: (r2_hidden(B_94, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_94) | ~m1_subset_1(B_94, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_24, c_239])).
% 3.20/1.50  tff(c_6, plain, (![A_1, B_8, C_9]: (r1_tarski('#skF_1'(A_1, B_8, C_9), C_9) | ~r2_hidden(B_8, k1_tops_1(A_1, C_9)) | ~m1_subset_1(C_9, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.20/1.50  tff(c_245, plain, (![B_94]: (r1_tarski('#skF_1'('#skF_2', B_94, '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~m1_connsp_2('#skF_4', '#skF_2', B_94) | ~m1_subset_1(B_94, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_241, c_6])).
% 3.20/1.50  tff(c_251, plain, (![B_94]: (r1_tarski('#skF_1'('#skF_2', B_94, '#skF_4'), '#skF_4') | ~m1_connsp_2('#skF_4', '#skF_2', B_94) | ~m1_subset_1(B_94, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_16, c_245])).
% 3.20/1.50  tff(c_240, plain, (![B_91]: (r2_hidden(B_91, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_91) | ~m1_subset_1(B_91, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_24, c_239])).
% 3.20/1.50  tff(c_4, plain, (![B_8, A_1, C_9]: (r2_hidden(B_8, '#skF_1'(A_1, B_8, C_9)) | ~r2_hidden(B_8, k1_tops_1(A_1, C_9)) | ~m1_subset_1(C_9, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.20/1.50  tff(c_243, plain, (![B_94]: (r2_hidden(B_94, '#skF_1'('#skF_2', B_94, '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~m1_connsp_2('#skF_4', '#skF_2', B_94) | ~m1_subset_1(B_94, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_241, c_4])).
% 3.20/1.50  tff(c_248, plain, (![B_94]: (r2_hidden(B_94, '#skF_1'('#skF_2', B_94, '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_94) | ~m1_subset_1(B_94, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_16, c_243])).
% 3.20/1.50  tff(c_212, plain, (![A_81, B_82, C_83]: (v3_pre_topc('#skF_1'(A_81, B_82, C_83), A_81) | ~r2_hidden(B_82, k1_tops_1(A_81, C_83)) | ~m1_subset_1(C_83, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.20/1.50  tff(c_214, plain, (![B_82]: (v3_pre_topc('#skF_1'('#skF_2', B_82, '#skF_4'), '#skF_2') | ~r2_hidden(B_82, k1_tops_1('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_212])).
% 3.20/1.50  tff(c_217, plain, (![B_82]: (v3_pre_topc('#skF_1'('#skF_2', B_82, '#skF_4'), '#skF_2') | ~r2_hidden(B_82, k1_tops_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_214])).
% 3.20/1.50  tff(c_220, plain, (![A_88, B_89, C_90]: (m1_subset_1('#skF_1'(A_88, B_89, C_90), k1_zfmisc_1(u1_struct_0(A_88))) | ~r2_hidden(B_89, k1_tops_1(A_88, C_90)) | ~m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.20/1.50  tff(c_203, plain, (![D_38]: (~r2_hidden('#skF_3', D_38) | ~r1_tarski(D_38, '#skF_4') | ~v3_pre_topc(D_38, '#skF_2') | ~m1_subset_1(D_38, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_197, c_26])).
% 3.20/1.50  tff(c_226, plain, (![B_89, C_90]: (~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_89, C_90)) | ~r1_tarski('#skF_1'('#skF_2', B_89, C_90), '#skF_4') | ~v3_pre_topc('#skF_1'('#skF_2', B_89, C_90), '#skF_2') | ~r2_hidden(B_89, k1_tops_1('#skF_2', C_90)) | ~m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_220, c_203])).
% 3.20/1.50  tff(c_254, plain, (![B_97, C_98]: (~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_97, C_98)) | ~r1_tarski('#skF_1'('#skF_2', B_97, C_98), '#skF_4') | ~v3_pre_topc('#skF_1'('#skF_2', B_97, C_98), '#skF_2') | ~r2_hidden(B_97, k1_tops_1('#skF_2', C_98)) | ~m1_subset_1(C_98, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_226])).
% 3.20/1.50  tff(c_256, plain, (![B_82]: (~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_82, '#skF_4')) | ~r1_tarski('#skF_1'('#skF_2', B_82, '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(B_82, k1_tops_1('#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_217, c_254])).
% 3.20/1.50  tff(c_260, plain, (![B_99]: (~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_99, '#skF_4')) | ~r1_tarski('#skF_1'('#skF_2', B_99, '#skF_4'), '#skF_4') | ~r2_hidden(B_99, k1_tops_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_256])).
% 3.20/1.50  tff(c_263, plain, (~r1_tarski('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_248, c_260])).
% 3.20/1.50  tff(c_266, plain, (~r1_tarski('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_197, c_263])).
% 3.20/1.50  tff(c_267, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_266])).
% 3.20/1.50  tff(c_270, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_240, c_267])).
% 3.20/1.50  tff(c_274, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_197, c_270])).
% 3.20/1.50  tff(c_275, plain, (~r1_tarski('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_266])).
% 3.20/1.50  tff(c_289, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_251, c_275])).
% 3.20/1.50  tff(c_293, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_197, c_289])).
% 3.20/1.50  tff(c_294, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_36])).
% 3.20/1.50  tff(c_328, plain, (![B_114, A_115, C_116]: (r2_hidden(B_114, k1_tops_1(A_115, C_116)) | ~m1_connsp_2(C_116, A_115, B_114) | ~m1_subset_1(C_116, k1_zfmisc_1(u1_struct_0(A_115))) | ~m1_subset_1(B_114, u1_struct_0(A_115)) | ~l1_pre_topc(A_115) | ~v2_pre_topc(A_115) | v2_struct_0(A_115))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.20/1.50  tff(c_332, plain, (![B_114]: (r2_hidden(B_114, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_114) | ~m1_subset_1(B_114, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_328])).
% 3.20/1.50  tff(c_336, plain, (![B_114]: (r2_hidden(B_114, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_114) | ~m1_subset_1(B_114, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_332])).
% 3.20/1.50  tff(c_338, plain, (![B_117]: (r2_hidden(B_117, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_117) | ~m1_subset_1(B_117, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_24, c_336])).
% 3.20/1.50  tff(c_340, plain, (![B_117]: (r1_tarski('#skF_1'('#skF_2', B_117, '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~m1_connsp_2('#skF_4', '#skF_2', B_117) | ~m1_subset_1(B_117, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_338, c_6])).
% 3.20/1.50  tff(c_345, plain, (![B_117]: (r1_tarski('#skF_1'('#skF_2', B_117, '#skF_4'), '#skF_4') | ~m1_connsp_2('#skF_4', '#skF_2', B_117) | ~m1_subset_1(B_117, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_16, c_340])).
% 3.20/1.50  tff(c_337, plain, (![B_114]: (r2_hidden(B_114, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_114) | ~m1_subset_1(B_114, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_24, c_336])).
% 3.20/1.50  tff(c_342, plain, (![B_117]: (r2_hidden(B_117, '#skF_1'('#skF_2', B_117, '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~m1_connsp_2('#skF_4', '#skF_2', B_117) | ~m1_subset_1(B_117, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_338, c_4])).
% 3.20/1.50  tff(c_348, plain, (![B_117]: (r2_hidden(B_117, '#skF_1'('#skF_2', B_117, '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_117) | ~m1_subset_1(B_117, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_16, c_342])).
% 3.20/1.50  tff(c_310, plain, (![A_107, B_108, C_109]: (v3_pre_topc('#skF_1'(A_107, B_108, C_109), A_107) | ~r2_hidden(B_108, k1_tops_1(A_107, C_109)) | ~m1_subset_1(C_109, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107) | ~v2_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.20/1.50  tff(c_312, plain, (![B_108]: (v3_pre_topc('#skF_1'('#skF_2', B_108, '#skF_4'), '#skF_2') | ~r2_hidden(B_108, k1_tops_1('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_310])).
% 3.20/1.50  tff(c_315, plain, (![B_108]: (v3_pre_topc('#skF_1'('#skF_2', B_108, '#skF_4'), '#skF_2') | ~r2_hidden(B_108, k1_tops_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_312])).
% 3.20/1.50  tff(c_317, plain, (![A_111, B_112, C_113]: (m1_subset_1('#skF_1'(A_111, B_112, C_113), k1_zfmisc_1(u1_struct_0(A_111))) | ~r2_hidden(B_112, k1_tops_1(A_111, C_113)) | ~m1_subset_1(C_113, k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_pre_topc(A_111) | ~v2_pre_topc(A_111))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.20/1.50  tff(c_295, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_36])).
% 3.20/1.50  tff(c_34, plain, (![D_38]: (~r2_hidden('#skF_3', D_38) | ~r1_tarski(D_38, '#skF_4') | ~v3_pre_topc(D_38, '#skF_2') | ~m1_subset_1(D_38, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r1_tarski('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.20/1.50  tff(c_299, plain, (![D_38]: (~r2_hidden('#skF_3', D_38) | ~r1_tarski(D_38, '#skF_4') | ~v3_pre_topc(D_38, '#skF_2') | ~m1_subset_1(D_38, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_295, c_34])).
% 3.20/1.50  tff(c_323, plain, (![B_112, C_113]: (~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_112, C_113)) | ~r1_tarski('#skF_1'('#skF_2', B_112, C_113), '#skF_4') | ~v3_pre_topc('#skF_1'('#skF_2', B_112, C_113), '#skF_2') | ~r2_hidden(B_112, k1_tops_1('#skF_2', C_113)) | ~m1_subset_1(C_113, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_317, c_299])).
% 3.20/1.50  tff(c_369, plain, (![B_129, C_130]: (~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_129, C_130)) | ~r1_tarski('#skF_1'('#skF_2', B_129, C_130), '#skF_4') | ~v3_pre_topc('#skF_1'('#skF_2', B_129, C_130), '#skF_2') | ~r2_hidden(B_129, k1_tops_1('#skF_2', C_130)) | ~m1_subset_1(C_130, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_323])).
% 3.20/1.50  tff(c_371, plain, (![B_108]: (~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_108, '#skF_4')) | ~r1_tarski('#skF_1'('#skF_2', B_108, '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(B_108, k1_tops_1('#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_315, c_369])).
% 3.20/1.50  tff(c_375, plain, (![B_131]: (~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_131, '#skF_4')) | ~r1_tarski('#skF_1'('#skF_2', B_131, '#skF_4'), '#skF_4') | ~r2_hidden(B_131, k1_tops_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_371])).
% 3.20/1.50  tff(c_378, plain, (~r1_tarski('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_348, c_375])).
% 3.20/1.50  tff(c_381, plain, (~r1_tarski('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_294, c_378])).
% 3.20/1.50  tff(c_383, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_381])).
% 3.20/1.50  tff(c_386, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_337, c_383])).
% 3.20/1.50  tff(c_390, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_294, c_386])).
% 3.20/1.50  tff(c_391, plain, (~r1_tarski('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_381])).
% 3.20/1.50  tff(c_414, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_345, c_391])).
% 3.20/1.50  tff(c_418, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_294, c_414])).
% 3.20/1.50  tff(c_419, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_32])).
% 3.20/1.50  tff(c_454, plain, (![B_152, A_153, C_154]: (r2_hidden(B_152, k1_tops_1(A_153, C_154)) | ~m1_connsp_2(C_154, A_153, B_152) | ~m1_subset_1(C_154, k1_zfmisc_1(u1_struct_0(A_153))) | ~m1_subset_1(B_152, u1_struct_0(A_153)) | ~l1_pre_topc(A_153) | ~v2_pre_topc(A_153) | v2_struct_0(A_153))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.20/1.50  tff(c_458, plain, (![B_152]: (r2_hidden(B_152, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_152) | ~m1_subset_1(B_152, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_454])).
% 3.20/1.50  tff(c_462, plain, (![B_152]: (r2_hidden(B_152, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_152) | ~m1_subset_1(B_152, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_458])).
% 3.20/1.50  tff(c_464, plain, (![B_155]: (r2_hidden(B_155, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_155) | ~m1_subset_1(B_155, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_24, c_462])).
% 3.20/1.50  tff(c_468, plain, (![B_155]: (r1_tarski('#skF_1'('#skF_2', B_155, '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~m1_connsp_2('#skF_4', '#skF_2', B_155) | ~m1_subset_1(B_155, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_464, c_6])).
% 3.20/1.50  tff(c_477, plain, (![B_155]: (r1_tarski('#skF_1'('#skF_2', B_155, '#skF_4'), '#skF_4') | ~m1_connsp_2('#skF_4', '#skF_2', B_155) | ~m1_subset_1(B_155, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_16, c_468])).
% 3.20/1.50  tff(c_463, plain, (![B_152]: (r2_hidden(B_152, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_152) | ~m1_subset_1(B_152, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_24, c_462])).
% 3.20/1.50  tff(c_470, plain, (![B_155]: (r2_hidden(B_155, '#skF_1'('#skF_2', B_155, '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~m1_connsp_2('#skF_4', '#skF_2', B_155) | ~m1_subset_1(B_155, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_464, c_4])).
% 3.20/1.50  tff(c_480, plain, (![B_155]: (r2_hidden(B_155, '#skF_1'('#skF_2', B_155, '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_155) | ~m1_subset_1(B_155, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_16, c_470])).
% 3.20/1.50  tff(c_433, plain, (![A_136, B_137, C_138]: (v3_pre_topc('#skF_1'(A_136, B_137, C_138), A_136) | ~r2_hidden(B_137, k1_tops_1(A_136, C_138)) | ~m1_subset_1(C_138, k1_zfmisc_1(u1_struct_0(A_136))) | ~l1_pre_topc(A_136) | ~v2_pre_topc(A_136))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.20/1.50  tff(c_435, plain, (![B_137]: (v3_pre_topc('#skF_1'('#skF_2', B_137, '#skF_4'), '#skF_2') | ~r2_hidden(B_137, k1_tops_1('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_433])).
% 3.20/1.50  tff(c_438, plain, (![B_137]: (v3_pre_topc('#skF_1'('#skF_2', B_137, '#skF_4'), '#skF_2') | ~r2_hidden(B_137, k1_tops_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_435])).
% 3.20/1.50  tff(c_442, plain, (![A_146, B_147, C_148]: (m1_subset_1('#skF_1'(A_146, B_147, C_148), k1_zfmisc_1(u1_struct_0(A_146))) | ~r2_hidden(B_147, k1_tops_1(A_146, C_148)) | ~m1_subset_1(C_148, k1_zfmisc_1(u1_struct_0(A_146))) | ~l1_pre_topc(A_146) | ~v2_pre_topc(A_146))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.20/1.50  tff(c_420, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_32])).
% 3.20/1.50  tff(c_30, plain, (![D_38]: (~r2_hidden('#skF_3', D_38) | ~r1_tarski(D_38, '#skF_4') | ~v3_pre_topc(D_38, '#skF_2') | ~m1_subset_1(D_38, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r2_hidden('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.20/1.50  tff(c_423, plain, (![D_38]: (~r2_hidden('#skF_3', D_38) | ~r1_tarski(D_38, '#skF_4') | ~v3_pre_topc(D_38, '#skF_2') | ~m1_subset_1(D_38, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_420, c_30])).
% 3.20/1.50  tff(c_448, plain, (![B_147, C_148]: (~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_147, C_148)) | ~r1_tarski('#skF_1'('#skF_2', B_147, C_148), '#skF_4') | ~v3_pre_topc('#skF_1'('#skF_2', B_147, C_148), '#skF_2') | ~r2_hidden(B_147, k1_tops_1('#skF_2', C_148)) | ~m1_subset_1(C_148, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_442, c_423])).
% 3.20/1.50  tff(c_490, plain, (![B_162, C_163]: (~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_162, C_163)) | ~r1_tarski('#skF_1'('#skF_2', B_162, C_163), '#skF_4') | ~v3_pre_topc('#skF_1'('#skF_2', B_162, C_163), '#skF_2') | ~r2_hidden(B_162, k1_tops_1('#skF_2', C_163)) | ~m1_subset_1(C_163, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_448])).
% 3.20/1.50  tff(c_492, plain, (![B_137]: (~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_137, '#skF_4')) | ~r1_tarski('#skF_1'('#skF_2', B_137, '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(B_137, k1_tops_1('#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_438, c_490])).
% 3.20/1.50  tff(c_496, plain, (![B_164]: (~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_164, '#skF_4')) | ~r1_tarski('#skF_1'('#skF_2', B_164, '#skF_4'), '#skF_4') | ~r2_hidden(B_164, k1_tops_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_492])).
% 3.20/1.50  tff(c_499, plain, (~r1_tarski('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_480, c_496])).
% 3.20/1.50  tff(c_502, plain, (~r1_tarski('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_419, c_499])).
% 3.20/1.50  tff(c_503, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_502])).
% 3.20/1.50  tff(c_507, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_463, c_503])).
% 3.20/1.50  tff(c_511, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_419, c_507])).
% 3.20/1.50  tff(c_512, plain, (~r1_tarski('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_502])).
% 3.20/1.50  tff(c_535, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_477, c_512])).
% 3.20/1.50  tff(c_539, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_419, c_535])).
% 3.20/1.50  tff(c_540, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_40])).
% 3.20/1.50  tff(c_576, plain, (![B_185, A_186, C_187]: (r2_hidden(B_185, k1_tops_1(A_186, C_187)) | ~m1_connsp_2(C_187, A_186, B_185) | ~m1_subset_1(C_187, k1_zfmisc_1(u1_struct_0(A_186))) | ~m1_subset_1(B_185, u1_struct_0(A_186)) | ~l1_pre_topc(A_186) | ~v2_pre_topc(A_186) | v2_struct_0(A_186))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.20/1.50  tff(c_580, plain, (![B_185]: (r2_hidden(B_185, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_185) | ~m1_subset_1(B_185, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_576])).
% 3.20/1.50  tff(c_584, plain, (![B_185]: (r2_hidden(B_185, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_185) | ~m1_subset_1(B_185, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_580])).
% 3.20/1.50  tff(c_586, plain, (![B_188]: (r2_hidden(B_188, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_188) | ~m1_subset_1(B_188, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_24, c_584])).
% 3.20/1.50  tff(c_592, plain, (![B_188]: (r1_tarski('#skF_1'('#skF_2', B_188, '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~m1_connsp_2('#skF_4', '#skF_2', B_188) | ~m1_subset_1(B_188, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_586, c_6])).
% 3.20/1.50  tff(c_602, plain, (![B_188]: (r1_tarski('#skF_1'('#skF_2', B_188, '#skF_4'), '#skF_4') | ~m1_connsp_2('#skF_4', '#skF_2', B_188) | ~m1_subset_1(B_188, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_16, c_592])).
% 3.20/1.50  tff(c_585, plain, (![B_185]: (r2_hidden(B_185, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_185) | ~m1_subset_1(B_185, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_24, c_584])).
% 3.20/1.50  tff(c_590, plain, (![B_188]: (r2_hidden(B_188, '#skF_1'('#skF_2', B_188, '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~m1_connsp_2('#skF_4', '#skF_2', B_188) | ~m1_subset_1(B_188, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_586, c_4])).
% 3.20/1.50  tff(c_599, plain, (![B_188]: (r2_hidden(B_188, '#skF_1'('#skF_2', B_188, '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_188) | ~m1_subset_1(B_188, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_16, c_590])).
% 3.20/1.50  tff(c_556, plain, (![A_172, B_173, C_174]: (v3_pre_topc('#skF_1'(A_172, B_173, C_174), A_172) | ~r2_hidden(B_173, k1_tops_1(A_172, C_174)) | ~m1_subset_1(C_174, k1_zfmisc_1(u1_struct_0(A_172))) | ~l1_pre_topc(A_172) | ~v2_pre_topc(A_172))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.20/1.50  tff(c_558, plain, (![B_173]: (v3_pre_topc('#skF_1'('#skF_2', B_173, '#skF_4'), '#skF_2') | ~r2_hidden(B_173, k1_tops_1('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_556])).
% 3.20/1.50  tff(c_561, plain, (![B_173]: (v3_pre_topc('#skF_1'('#skF_2', B_173, '#skF_4'), '#skF_2') | ~r2_hidden(B_173, k1_tops_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_558])).
% 3.20/1.50  tff(c_564, plain, (![A_179, B_180, C_181]: (m1_subset_1('#skF_1'(A_179, B_180, C_181), k1_zfmisc_1(u1_struct_0(A_179))) | ~r2_hidden(B_180, k1_tops_1(A_179, C_181)) | ~m1_subset_1(C_181, k1_zfmisc_1(u1_struct_0(A_179))) | ~l1_pre_topc(A_179) | ~v2_pre_topc(A_179))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.20/1.50  tff(c_541, plain, (~v3_pre_topc('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 3.20/1.50  tff(c_38, plain, (![D_38]: (~r2_hidden('#skF_3', D_38) | ~r1_tarski(D_38, '#skF_4') | ~v3_pre_topc(D_38, '#skF_2') | ~m1_subset_1(D_38, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v3_pre_topc('#skF_5', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.20/1.50  tff(c_546, plain, (![D_38]: (~r2_hidden('#skF_3', D_38) | ~r1_tarski(D_38, '#skF_4') | ~v3_pre_topc(D_38, '#skF_2') | ~m1_subset_1(D_38, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_541, c_38])).
% 3.20/1.50  tff(c_570, plain, (![B_180, C_181]: (~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_180, C_181)) | ~r1_tarski('#skF_1'('#skF_2', B_180, C_181), '#skF_4') | ~v3_pre_topc('#skF_1'('#skF_2', B_180, C_181), '#skF_2') | ~r2_hidden(B_180, k1_tops_1('#skF_2', C_181)) | ~m1_subset_1(C_181, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_564, c_546])).
% 3.20/1.50  tff(c_612, plain, (![B_195, C_196]: (~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_195, C_196)) | ~r1_tarski('#skF_1'('#skF_2', B_195, C_196), '#skF_4') | ~v3_pre_topc('#skF_1'('#skF_2', B_195, C_196), '#skF_2') | ~r2_hidden(B_195, k1_tops_1('#skF_2', C_196)) | ~m1_subset_1(C_196, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_570])).
% 3.20/1.50  tff(c_614, plain, (![B_173]: (~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_173, '#skF_4')) | ~r1_tarski('#skF_1'('#skF_2', B_173, '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(B_173, k1_tops_1('#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_561, c_612])).
% 3.20/1.50  tff(c_618, plain, (![B_197]: (~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_197, '#skF_4')) | ~r1_tarski('#skF_1'('#skF_2', B_197, '#skF_4'), '#skF_4') | ~r2_hidden(B_197, k1_tops_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_614])).
% 3.20/1.50  tff(c_621, plain, (~r1_tarski('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_599, c_618])).
% 3.20/1.50  tff(c_624, plain, (~r1_tarski('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_540, c_621])).
% 3.20/1.50  tff(c_626, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_624])).
% 3.20/1.50  tff(c_629, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_585, c_626])).
% 3.20/1.50  tff(c_633, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_540, c_629])).
% 3.20/1.50  tff(c_634, plain, (~r1_tarski('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_624])).
% 3.20/1.50  tff(c_657, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_602, c_634])).
% 3.20/1.50  tff(c_661, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_540, c_657])).
% 3.20/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.50  
% 3.20/1.50  Inference rules
% 3.20/1.50  ----------------------
% 3.20/1.50  #Ref     : 0
% 3.20/1.50  #Sup     : 99
% 3.20/1.50  #Fact    : 0
% 3.20/1.50  #Define  : 0
% 3.20/1.50  #Split   : 14
% 3.20/1.50  #Chain   : 0
% 3.20/1.50  #Close   : 0
% 3.20/1.50  
% 3.20/1.50  Ordering : KBO
% 3.20/1.50  
% 3.20/1.50  Simplification rules
% 3.20/1.50  ----------------------
% 3.20/1.50  #Subsume      : 11
% 3.20/1.50  #Demod        : 184
% 3.20/1.50  #Tautology    : 25
% 3.20/1.50  #SimpNegUnit  : 19
% 3.20/1.50  #BackRed      : 0
% 3.20/1.50  
% 3.20/1.50  #Partial instantiations: 0
% 3.20/1.50  #Strategies tried      : 1
% 3.20/1.50  
% 3.20/1.50  Timing (in seconds)
% 3.20/1.50  ----------------------
% 3.20/1.50  Preprocessing        : 0.27
% 3.20/1.50  Parsing              : 0.15
% 3.20/1.50  CNF conversion       : 0.03
% 3.20/1.50  Main loop            : 0.38
% 3.20/1.50  Inferencing          : 0.15
% 3.20/1.50  Reduction            : 0.11
% 3.20/1.50  Demodulation         : 0.08
% 3.20/1.50  BG Simplification    : 0.02
% 3.20/1.50  Subsumption          : 0.07
% 3.20/1.50  Abstraction          : 0.02
% 3.20/1.50  MUC search           : 0.00
% 3.20/1.50  Cooper               : 0.00
% 3.20/1.50  Total                : 0.72
% 3.20/1.50  Index Insertion      : 0.00
% 3.20/1.50  Index Deletion       : 0.00
% 3.20/1.50  Index Matching       : 0.00
% 3.20/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
