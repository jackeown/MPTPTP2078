%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:09 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 207 expanded)
%              Number of leaves         :   28 (  85 expanded)
%              Depth                    :   10
%              Number of atoms          :  218 ( 847 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_130,negated_conjecture,(
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

tff(f_81,axiom,(
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

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_100,axiom,(
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

tff(f_49,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_32,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_28,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_36,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_296,plain,(
    ! [B_99,A_100,C_101] :
      ( r2_hidden(B_99,k1_tops_1(A_100,C_101))
      | ~ m1_connsp_2(C_101,A_100,B_99)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ m1_subset_1(B_99,u1_struct_0(A_100))
      | ~ l1_pre_topc(A_100)
      | ~ v2_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_303,plain,(
    ! [B_99] :
      ( r2_hidden(B_99,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_99)
      | ~ m1_subset_1(B_99,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_296])).

tff(c_308,plain,(
    ! [B_99] :
      ( r2_hidden(B_99,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_99)
      | ~ m1_subset_1(B_99,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_303])).

tff(c_309,plain,(
    ! [B_99] :
      ( r2_hidden(B_99,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_99)
      | ~ m1_subset_1(B_99,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_308])).

tff(c_140,plain,(
    ! [A_76,B_77] :
      ( r1_tarski(k1_tops_1(A_76,B_77),B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_145,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_140])).

tff(c_149,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_145])).

tff(c_182,plain,(
    ! [A_83,B_84] :
      ( v3_pre_topc(k1_tops_1(A_83,B_84),A_83)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_187,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_182])).

tff(c_191,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_187])).

tff(c_40,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_48,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_40])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_72,plain,(
    ! [C_54,B_55,A_56] :
      ( r2_hidden(C_54,B_55)
      | ~ r2_hidden(C_54,A_56)
      | ~ r1_tarski(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_118,plain,(
    ! [A_69,B_70,B_71] :
      ( r2_hidden('#skF_1'(A_69,B_70),B_71)
      | ~ r1_tarski(A_69,B_71)
      | r1_tarski(A_69,B_70) ) ),
    inference(resolution,[status(thm)],[c_6,c_72])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_248,plain,(
    ! [A_92,B_93,B_94,B_95] :
      ( r2_hidden('#skF_1'(A_92,B_93),B_94)
      | ~ r1_tarski(B_95,B_94)
      | ~ r1_tarski(A_92,B_95)
      | r1_tarski(A_92,B_93) ) ),
    inference(resolution,[status(thm)],[c_118,c_2])).

tff(c_270,plain,(
    ! [A_96,B_97] :
      ( r2_hidden('#skF_1'(A_96,B_97),u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_96,'#skF_4')
      | r1_tarski(A_96,B_97) ) ),
    inference(resolution,[status(thm)],[c_48,c_248])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_281,plain,(
    ! [A_96] :
      ( ~ r1_tarski(A_96,'#skF_4')
      | r1_tarski(A_96,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_270,c_4])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_550,plain,(
    ! [B_121,A_122,C_123] :
      ( m1_connsp_2(B_121,A_122,C_123)
      | ~ r2_hidden(C_123,B_121)
      | ~ v3_pre_topc(B_121,A_122)
      | ~ m1_subset_1(C_123,u1_struct_0(A_122))
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_552,plain,(
    ! [B_121] :
      ( m1_connsp_2(B_121,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_121)
      | ~ v3_pre_topc(B_121,'#skF_2')
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_550])).

tff(c_555,plain,(
    ! [B_121] :
      ( m1_connsp_2(B_121,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_121)
      | ~ v3_pre_topc(B_121,'#skF_2')
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_552])).

tff(c_618,plain,(
    ! [B_128] :
      ( m1_connsp_2(B_128,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_128)
      | ~ v3_pre_topc(B_128,'#skF_2')
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_555])).

tff(c_712,plain,(
    ! [A_135] :
      ( m1_connsp_2(A_135,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',A_135)
      | ~ v3_pre_topc(A_135,'#skF_2')
      | ~ r1_tarski(A_135,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_10,c_618])).

tff(c_771,plain,(
    ! [A_138] :
      ( m1_connsp_2(A_138,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',A_138)
      | ~ v3_pre_topc(A_138,'#skF_2')
      | ~ r1_tarski(A_138,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_281,c_712])).

tff(c_192,plain,(
    ! [A_85,B_86] :
      ( m1_subset_1(k1_tops_1(A_85,B_86),k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [D_43] :
      ( ~ r1_tarski(D_43,'#skF_4')
      | ~ v3_pre_topc(D_43,'#skF_2')
      | ~ m1_connsp_2(D_43,'#skF_2','#skF_3')
      | ~ m1_subset_1(D_43,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v1_xboole_0(D_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_202,plain,(
    ! [B_86] :
      ( ~ r1_tarski(k1_tops_1('#skF_2',B_86),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_86),'#skF_2')
      | ~ m1_connsp_2(k1_tops_1('#skF_2',B_86),'#skF_2','#skF_3')
      | v1_xboole_0(k1_tops_1('#skF_2',B_86))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_192,c_26])).

tff(c_228,plain,(
    ! [B_91] :
      ( ~ r1_tarski(k1_tops_1('#skF_2',B_91),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_91),'#skF_2')
      | ~ m1_connsp_2(k1_tops_1('#skF_2',B_91),'#skF_2','#skF_3')
      | v1_xboole_0(k1_tops_1('#skF_2',B_91))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_202])).

tff(c_239,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2','#skF_3')
    | v1_xboole_0(k1_tops_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_30,c_228])).

tff(c_246,plain,
    ( ~ m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2','#skF_3')
    | v1_xboole_0(k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_149,c_239])).

tff(c_247,plain,(
    ~ m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_246])).

tff(c_777,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_771,c_247])).

tff(c_784,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_191,c_777])).

tff(c_793,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_309,c_784])).

tff(c_798,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_793])).

tff(c_799,plain,(
    v1_xboole_0(k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_62,plain,(
    ! [A_51,B_52] :
      ( ~ r2_hidden('#skF_1'(A_51,B_52),B_52)
      | r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_67,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_62])).

tff(c_801,plain,(
    ! [B_139,A_140,C_141] :
      ( r2_hidden(B_139,k1_tops_1(A_140,C_141))
      | ~ m1_connsp_2(C_141,A_140,B_139)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ m1_subset_1(B_139,u1_struct_0(A_140))
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_808,plain,(
    ! [B_139] :
      ( r2_hidden(B_139,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_139)
      | ~ m1_subset_1(B_139,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_801])).

tff(c_813,plain,(
    ! [B_139] :
      ( r2_hidden(B_139,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_139)
      | ~ m1_subset_1(B_139,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_808])).

tff(c_815,plain,(
    ! [B_142] :
      ( r2_hidden(B_142,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_142)
      | ~ m1_subset_1(B_142,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_813])).

tff(c_76,plain,(
    ! [C_57,B_58,A_59] :
      ( ~ v1_xboole_0(C_57)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(C_57))
      | ~ r2_hidden(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_81,plain,(
    ! [B_7,A_59,A_6] :
      ( ~ v1_xboole_0(B_7)
      | ~ r2_hidden(A_59,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_76])).

tff(c_824,plain,(
    ! [B_7,B_142] :
      ( ~ v1_xboole_0(B_7)
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),B_7)
      | ~ m1_connsp_2('#skF_4','#skF_2',B_142)
      | ~ m1_subset_1(B_142,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_815,c_81])).

tff(c_979,plain,(
    ! [B_159] :
      ( ~ m1_connsp_2('#skF_4','#skF_2',B_159)
      | ~ m1_subset_1(B_159,u1_struct_0('#skF_2')) ) ),
    inference(splitLeft,[status(thm)],[c_824])).

tff(c_982,plain,(
    ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_979])).

tff(c_986,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_982])).

tff(c_988,plain,(
    ! [B_160] :
      ( ~ v1_xboole_0(B_160)
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),B_160) ) ),
    inference(splitRight,[status(thm)],[c_824])).

tff(c_1015,plain,(
    ~ v1_xboole_0(k1_tops_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_67,c_988])).

tff(c_1035,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_1015])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:23:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.89/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.45  
% 2.89/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.45  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.89/1.45  
% 2.89/1.45  %Foreground sorts:
% 2.89/1.45  
% 2.89/1.45  
% 2.89/1.45  %Background operators:
% 2.89/1.45  
% 2.89/1.45  
% 2.89/1.45  %Foreground operators:
% 2.89/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.89/1.45  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.89/1.45  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.89/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.89/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.89/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.89/1.45  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.89/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.89/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.89/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.89/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.89/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.89/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.89/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.89/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.89/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.89/1.45  
% 3.31/1.47  tff(f_130, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(C, A, B) & (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~((m1_connsp_2(D, A, B) & v3_pre_topc(D, A)) & r1_tarski(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_connsp_2)).
% 3.31/1.47  tff(f_81, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 3.31/1.47  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 3.31/1.47  tff(f_57, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.31/1.47  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.31/1.47  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.31/1.47  tff(f_100, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 3.31/1.47  tff(f_49, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 3.31/1.47  tff(f_43, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.31/1.47  tff(c_32, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.31/1.47  tff(c_28, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.31/1.47  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.31/1.47  tff(c_36, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.31/1.47  tff(c_34, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.31/1.47  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.31/1.47  tff(c_296, plain, (![B_99, A_100, C_101]: (r2_hidden(B_99, k1_tops_1(A_100, C_101)) | ~m1_connsp_2(C_101, A_100, B_99) | ~m1_subset_1(C_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~m1_subset_1(B_99, u1_struct_0(A_100)) | ~l1_pre_topc(A_100) | ~v2_pre_topc(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.31/1.47  tff(c_303, plain, (![B_99]: (r2_hidden(B_99, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_99) | ~m1_subset_1(B_99, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_296])).
% 3.31/1.47  tff(c_308, plain, (![B_99]: (r2_hidden(B_99, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_99) | ~m1_subset_1(B_99, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_303])).
% 3.31/1.47  tff(c_309, plain, (![B_99]: (r2_hidden(B_99, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_99) | ~m1_subset_1(B_99, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_38, c_308])).
% 3.31/1.47  tff(c_140, plain, (![A_76, B_77]: (r1_tarski(k1_tops_1(A_76, B_77), B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.31/1.47  tff(c_145, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_140])).
% 3.31/1.47  tff(c_149, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_145])).
% 3.31/1.47  tff(c_182, plain, (![A_83, B_84]: (v3_pre_topc(k1_tops_1(A_83, B_84), A_83) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83) | ~v2_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.31/1.47  tff(c_187, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_182])).
% 3.31/1.47  tff(c_191, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_187])).
% 3.31/1.47  tff(c_40, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | ~m1_subset_1(A_46, k1_zfmisc_1(B_47)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.31/1.47  tff(c_48, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_40])).
% 3.31/1.47  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.31/1.47  tff(c_72, plain, (![C_54, B_55, A_56]: (r2_hidden(C_54, B_55) | ~r2_hidden(C_54, A_56) | ~r1_tarski(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.31/1.47  tff(c_118, plain, (![A_69, B_70, B_71]: (r2_hidden('#skF_1'(A_69, B_70), B_71) | ~r1_tarski(A_69, B_71) | r1_tarski(A_69, B_70))), inference(resolution, [status(thm)], [c_6, c_72])).
% 3.31/1.47  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.31/1.47  tff(c_248, plain, (![A_92, B_93, B_94, B_95]: (r2_hidden('#skF_1'(A_92, B_93), B_94) | ~r1_tarski(B_95, B_94) | ~r1_tarski(A_92, B_95) | r1_tarski(A_92, B_93))), inference(resolution, [status(thm)], [c_118, c_2])).
% 3.31/1.47  tff(c_270, plain, (![A_96, B_97]: (r2_hidden('#skF_1'(A_96, B_97), u1_struct_0('#skF_2')) | ~r1_tarski(A_96, '#skF_4') | r1_tarski(A_96, B_97))), inference(resolution, [status(thm)], [c_48, c_248])).
% 3.31/1.47  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.31/1.47  tff(c_281, plain, (![A_96]: (~r1_tarski(A_96, '#skF_4') | r1_tarski(A_96, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_270, c_4])).
% 3.31/1.47  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.31/1.47  tff(c_550, plain, (![B_121, A_122, C_123]: (m1_connsp_2(B_121, A_122, C_123) | ~r2_hidden(C_123, B_121) | ~v3_pre_topc(B_121, A_122) | ~m1_subset_1(C_123, u1_struct_0(A_122)) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_pre_topc(A_122) | ~v2_pre_topc(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.31/1.47  tff(c_552, plain, (![B_121]: (m1_connsp_2(B_121, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_121) | ~v3_pre_topc(B_121, '#skF_2') | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_550])).
% 3.31/1.47  tff(c_555, plain, (![B_121]: (m1_connsp_2(B_121, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_121) | ~v3_pre_topc(B_121, '#skF_2') | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_552])).
% 3.31/1.47  tff(c_618, plain, (![B_128]: (m1_connsp_2(B_128, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_128) | ~v3_pre_topc(B_128, '#skF_2') | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_38, c_555])).
% 3.31/1.47  tff(c_712, plain, (![A_135]: (m1_connsp_2(A_135, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', A_135) | ~v3_pre_topc(A_135, '#skF_2') | ~r1_tarski(A_135, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_10, c_618])).
% 3.31/1.47  tff(c_771, plain, (![A_138]: (m1_connsp_2(A_138, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', A_138) | ~v3_pre_topc(A_138, '#skF_2') | ~r1_tarski(A_138, '#skF_4'))), inference(resolution, [status(thm)], [c_281, c_712])).
% 3.31/1.47  tff(c_192, plain, (![A_85, B_86]: (m1_subset_1(k1_tops_1(A_85, B_86), k1_zfmisc_1(u1_struct_0(A_85))) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.31/1.47  tff(c_26, plain, (![D_43]: (~r1_tarski(D_43, '#skF_4') | ~v3_pre_topc(D_43, '#skF_2') | ~m1_connsp_2(D_43, '#skF_2', '#skF_3') | ~m1_subset_1(D_43, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(D_43))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.31/1.47  tff(c_202, plain, (![B_86]: (~r1_tarski(k1_tops_1('#skF_2', B_86), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_86), '#skF_2') | ~m1_connsp_2(k1_tops_1('#skF_2', B_86), '#skF_2', '#skF_3') | v1_xboole_0(k1_tops_1('#skF_2', B_86)) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_192, c_26])).
% 3.31/1.47  tff(c_228, plain, (![B_91]: (~r1_tarski(k1_tops_1('#skF_2', B_91), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_91), '#skF_2') | ~m1_connsp_2(k1_tops_1('#skF_2', B_91), '#skF_2', '#skF_3') | v1_xboole_0(k1_tops_1('#skF_2', B_91)) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_202])).
% 3.31/1.47  tff(c_239, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', '#skF_3') | v1_xboole_0(k1_tops_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_30, c_228])).
% 3.31/1.47  tff(c_246, plain, (~m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', '#skF_3') | v1_xboole_0(k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_149, c_239])).
% 3.31/1.47  tff(c_247, plain, (~m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_246])).
% 3.31/1.47  tff(c_777, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_771, c_247])).
% 3.31/1.47  tff(c_784, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_191, c_777])).
% 3.31/1.47  tff(c_793, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_309, c_784])).
% 3.31/1.47  tff(c_798, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_793])).
% 3.31/1.47  tff(c_799, plain, (v1_xboole_0(k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_246])).
% 3.31/1.47  tff(c_62, plain, (![A_51, B_52]: (~r2_hidden('#skF_1'(A_51, B_52), B_52) | r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.31/1.47  tff(c_67, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_62])).
% 3.31/1.47  tff(c_801, plain, (![B_139, A_140, C_141]: (r2_hidden(B_139, k1_tops_1(A_140, C_141)) | ~m1_connsp_2(C_141, A_140, B_139) | ~m1_subset_1(C_141, k1_zfmisc_1(u1_struct_0(A_140))) | ~m1_subset_1(B_139, u1_struct_0(A_140)) | ~l1_pre_topc(A_140) | ~v2_pre_topc(A_140) | v2_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.31/1.47  tff(c_808, plain, (![B_139]: (r2_hidden(B_139, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_139) | ~m1_subset_1(B_139, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_801])).
% 3.31/1.47  tff(c_813, plain, (![B_139]: (r2_hidden(B_139, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_139) | ~m1_subset_1(B_139, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_808])).
% 3.31/1.47  tff(c_815, plain, (![B_142]: (r2_hidden(B_142, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_142) | ~m1_subset_1(B_142, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_38, c_813])).
% 3.31/1.47  tff(c_76, plain, (![C_57, B_58, A_59]: (~v1_xboole_0(C_57) | ~m1_subset_1(B_58, k1_zfmisc_1(C_57)) | ~r2_hidden(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.31/1.47  tff(c_81, plain, (![B_7, A_59, A_6]: (~v1_xboole_0(B_7) | ~r2_hidden(A_59, A_6) | ~r1_tarski(A_6, B_7))), inference(resolution, [status(thm)], [c_10, c_76])).
% 3.31/1.47  tff(c_824, plain, (![B_7, B_142]: (~v1_xboole_0(B_7) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), B_7) | ~m1_connsp_2('#skF_4', '#skF_2', B_142) | ~m1_subset_1(B_142, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_815, c_81])).
% 3.31/1.47  tff(c_979, plain, (![B_159]: (~m1_connsp_2('#skF_4', '#skF_2', B_159) | ~m1_subset_1(B_159, u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_824])).
% 3.31/1.47  tff(c_982, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_979])).
% 3.31/1.47  tff(c_986, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_982])).
% 3.31/1.47  tff(c_988, plain, (![B_160]: (~v1_xboole_0(B_160) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), B_160))), inference(splitRight, [status(thm)], [c_824])).
% 3.31/1.47  tff(c_1015, plain, (~v1_xboole_0(k1_tops_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_67, c_988])).
% 3.31/1.47  tff(c_1035, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_799, c_1015])).
% 3.31/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.47  
% 3.31/1.47  Inference rules
% 3.31/1.47  ----------------------
% 3.31/1.47  #Ref     : 0
% 3.31/1.47  #Sup     : 209
% 3.31/1.47  #Fact    : 0
% 3.31/1.47  #Define  : 0
% 3.31/1.47  #Split   : 11
% 3.31/1.47  #Chain   : 0
% 3.31/1.47  #Close   : 0
% 3.31/1.47  
% 3.31/1.47  Ordering : KBO
% 3.31/1.47  
% 3.31/1.47  Simplification rules
% 3.31/1.47  ----------------------
% 3.31/1.47  #Subsume      : 80
% 3.31/1.47  #Demod        : 84
% 3.31/1.47  #Tautology    : 14
% 3.31/1.47  #SimpNegUnit  : 9
% 3.31/1.47  #BackRed      : 0
% 3.31/1.47  
% 3.31/1.47  #Partial instantiations: 0
% 3.31/1.47  #Strategies tried      : 1
% 3.31/1.47  
% 3.31/1.47  Timing (in seconds)
% 3.31/1.47  ----------------------
% 3.31/1.47  Preprocessing        : 0.30
% 3.31/1.47  Parsing              : 0.17
% 3.31/1.47  CNF conversion       : 0.02
% 3.31/1.47  Main loop            : 0.41
% 3.31/1.47  Inferencing          : 0.15
% 3.31/1.47  Reduction            : 0.11
% 3.31/1.47  Demodulation         : 0.08
% 3.31/1.47  BG Simplification    : 0.02
% 3.31/1.47  Subsumption          : 0.10
% 3.31/1.47  Abstraction          : 0.02
% 3.31/1.47  MUC search           : 0.00
% 3.31/1.47  Cooper               : 0.00
% 3.31/1.47  Total                : 0.74
% 3.31/1.47  Index Insertion      : 0.00
% 3.31/1.47  Index Deletion       : 0.00
% 3.31/1.47  Index Matching       : 0.00
% 3.31/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
