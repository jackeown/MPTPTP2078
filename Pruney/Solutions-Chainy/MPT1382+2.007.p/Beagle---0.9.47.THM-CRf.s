%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:08 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 162 expanded)
%              Number of leaves         :   28 (  70 expanded)
%              Depth                    :   13
%              Number of atoms          :  190 ( 617 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_connsp_2)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_74,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_93,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

tff(c_28,plain,(
    m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_58,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_66,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_58])).

tff(c_36,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_34,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_276,plain,(
    ! [B_95,A_96,C_97] :
      ( r2_hidden(B_95,k1_tops_1(A_96,C_97))
      | ~ m1_connsp_2(C_97,A_96,B_95)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ m1_subset_1(B_95,u1_struct_0(A_96))
      | ~ l1_pre_topc(A_96)
      | ~ v2_pre_topc(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_282,plain,(
    ! [B_95,A_96,A_10] :
      ( r2_hidden(B_95,k1_tops_1(A_96,A_10))
      | ~ m1_connsp_2(A_10,A_96,B_95)
      | ~ m1_subset_1(B_95,u1_struct_0(A_96))
      | ~ l1_pre_topc(A_96)
      | ~ v2_pre_topc(A_96)
      | v2_struct_0(A_96)
      | ~ r1_tarski(A_10,u1_struct_0(A_96)) ) ),
    inference(resolution,[status(thm)],[c_14,c_276])).

tff(c_281,plain,(
    ! [B_95] :
      ( r2_hidden(B_95,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_95)
      | ~ m1_subset_1(B_95,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_276])).

tff(c_285,plain,(
    ! [B_95] :
      ( r2_hidden(B_95,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_95)
      | ~ m1_subset_1(B_95,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_281])).

tff(c_299,plain,(
    ! [B_99] :
      ( r2_hidden(B_99,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_99)
      | ~ m1_subset_1(B_99,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_285])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_311,plain,(
    ! [B_99] :
      ( ~ v1_xboole_0(k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_99)
      | ~ m1_subset_1(B_99,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_299,c_2])).

tff(c_312,plain,(
    ~ v1_xboole_0(k1_tops_1('#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_311])).

tff(c_142,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(k1_tops_1(A_69,B_70),B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_147,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_5'),'#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_142])).

tff(c_151,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_147])).

tff(c_209,plain,(
    ! [A_80,B_81] :
      ( v3_pre_topc(k1_tops_1(A_80,B_81),A_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_214,plain,
    ( v3_pre_topc(k1_tops_1('#skF_3','#skF_5'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_209])).

tff(c_218,plain,(
    v3_pre_topc(k1_tops_1('#skF_3','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_214])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_79,plain,(
    ! [C_56,B_57,A_58] :
      ( r2_hidden(C_56,B_57)
      | ~ r2_hidden(C_56,A_58)
      | ~ r1_tarski(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_129,plain,(
    ! [A_66,B_67,B_68] :
      ( r2_hidden('#skF_2'(A_66,B_67),B_68)
      | ~ r1_tarski(A_66,B_68)
      | r1_tarski(A_66,B_67) ) ),
    inference(resolution,[status(thm)],[c_10,c_79])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_319,plain,(
    ! [A_100,B_101,B_102,B_103] :
      ( r2_hidden('#skF_2'(A_100,B_101),B_102)
      | ~ r1_tarski(B_103,B_102)
      | ~ r1_tarski(A_100,B_103)
      | r1_tarski(A_100,B_101) ) ),
    inference(resolution,[status(thm)],[c_129,c_6])).

tff(c_338,plain,(
    ! [A_104,B_105] :
      ( r2_hidden('#skF_2'(A_104,B_105),u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_104,'#skF_5')
      | r1_tarski(A_104,B_105) ) ),
    inference(resolution,[status(thm)],[c_66,c_319])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_349,plain,(
    ! [A_104] :
      ( ~ r1_tarski(A_104,'#skF_5')
      | r1_tarski(A_104,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_338,c_8])).

tff(c_532,plain,(
    ! [B_120,A_121,C_122] :
      ( m1_connsp_2(B_120,A_121,C_122)
      | ~ r2_hidden(C_122,B_120)
      | ~ v3_pre_topc(B_120,A_121)
      | ~ m1_subset_1(C_122,u1_struct_0(A_121))
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ l1_pre_topc(A_121)
      | ~ v2_pre_topc(A_121)
      | v2_struct_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_534,plain,(
    ! [B_120] :
      ( m1_connsp_2(B_120,'#skF_3','#skF_4')
      | ~ r2_hidden('#skF_4',B_120)
      | ~ v3_pre_topc(B_120,'#skF_3')
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_532])).

tff(c_537,plain,(
    ! [B_120] :
      ( m1_connsp_2(B_120,'#skF_3','#skF_4')
      | ~ r2_hidden('#skF_4',B_120)
      | ~ v3_pre_topc(B_120,'#skF_3')
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_534])).

tff(c_580,plain,(
    ! [B_125] :
      ( m1_connsp_2(B_125,'#skF_3','#skF_4')
      | ~ r2_hidden('#skF_4',B_125)
      | ~ v3_pre_topc(B_125,'#skF_3')
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_537])).

tff(c_697,plain,(
    ! [A_135] :
      ( m1_connsp_2(A_135,'#skF_3','#skF_4')
      | ~ r2_hidden('#skF_4',A_135)
      | ~ v3_pre_topc(A_135,'#skF_3')
      | ~ r1_tarski(A_135,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_14,c_580])).

tff(c_735,plain,(
    ! [A_136] :
      ( m1_connsp_2(A_136,'#skF_3','#skF_4')
      | ~ r2_hidden('#skF_4',A_136)
      | ~ v3_pre_topc(A_136,'#skF_3')
      | ~ r1_tarski(A_136,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_349,c_697])).

tff(c_351,plain,(
    ! [A_106] :
      ( ~ r1_tarski(A_106,'#skF_5')
      | r1_tarski(A_106,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_338,c_8])).

tff(c_46,plain,(
    ! [D_48] :
      ( ~ r1_tarski(D_48,'#skF_5')
      | ~ v3_pre_topc(D_48,'#skF_3')
      | ~ m1_connsp_2(D_48,'#skF_3','#skF_4')
      | ~ m1_subset_1(D_48,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v1_xboole_0(D_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_54,plain,(
    ! [A_10] :
      ( ~ r1_tarski(A_10,'#skF_5')
      | ~ v3_pre_topc(A_10,'#skF_3')
      | ~ m1_connsp_2(A_10,'#skF_3','#skF_4')
      | v1_xboole_0(A_10)
      | ~ r1_tarski(A_10,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_14,c_46])).

tff(c_373,plain,(
    ! [A_106] :
      ( ~ v3_pre_topc(A_106,'#skF_3')
      | ~ m1_connsp_2(A_106,'#skF_3','#skF_4')
      | v1_xboole_0(A_106)
      | ~ r1_tarski(A_106,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_351,c_54])).

tff(c_746,plain,(
    ! [A_137] :
      ( v1_xboole_0(A_137)
      | ~ r2_hidden('#skF_4',A_137)
      | ~ v3_pre_topc(A_137,'#skF_3')
      | ~ r1_tarski(A_137,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_735,c_373])).

tff(c_753,plain,
    ( v1_xboole_0(k1_tops_1('#skF_3','#skF_5'))
    | ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5'))
    | ~ r1_tarski(k1_tops_1('#skF_3','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_218,c_746])).

tff(c_759,plain,
    ( v1_xboole_0(k1_tops_1('#skF_3','#skF_5'))
    | ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_753])).

tff(c_760,plain,(
    ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_312,c_759])).

tff(c_763,plain,
    ( ~ m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_282,c_760])).

tff(c_772,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_36,c_34,c_32,c_28,c_763])).

tff(c_774,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_772])).

tff(c_804,plain,(
    ! [B_141] :
      ( ~ m1_connsp_2('#skF_5','#skF_3',B_141)
      | ~ m1_subset_1(B_141,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_311])).

tff(c_807,plain,(
    ~ m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_804])).

tff(c_811,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_807])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:12:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.33/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.62  
% 3.33/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.62  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.33/1.62  
% 3.33/1.62  %Foreground sorts:
% 3.33/1.62  
% 3.33/1.62  
% 3.33/1.62  %Background operators:
% 3.33/1.62  
% 3.33/1.62  
% 3.33/1.62  %Foreground operators:
% 3.33/1.62  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.33/1.62  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.33/1.62  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.33/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.33/1.62  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.33/1.62  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.33/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.33/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.33/1.62  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.33/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.33/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.33/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.33/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.62  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.33/1.62  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.33/1.62  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.33/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.33/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.33/1.62  
% 3.68/1.64  tff(f_123, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(C, A, B) & (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~((m1_connsp_2(D, A, B) & v3_pre_topc(D, A)) & r1_tarski(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_connsp_2)).
% 3.68/1.64  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.68/1.64  tff(f_74, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 3.68/1.64  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.68/1.64  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 3.68/1.64  tff(f_50, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.68/1.64  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.68/1.64  tff(f_93, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_connsp_2)).
% 3.68/1.64  tff(c_28, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.68/1.64  tff(c_32, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.68/1.64  tff(c_38, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.68/1.64  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.68/1.64  tff(c_58, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~m1_subset_1(A_49, k1_zfmisc_1(B_50)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.68/1.64  tff(c_66, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_58])).
% 3.68/1.64  tff(c_36, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.68/1.64  tff(c_34, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.68/1.64  tff(c_14, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.68/1.64  tff(c_276, plain, (![B_95, A_96, C_97]: (r2_hidden(B_95, k1_tops_1(A_96, C_97)) | ~m1_connsp_2(C_97, A_96, B_95) | ~m1_subset_1(C_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~m1_subset_1(B_95, u1_struct_0(A_96)) | ~l1_pre_topc(A_96) | ~v2_pre_topc(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.68/1.64  tff(c_282, plain, (![B_95, A_96, A_10]: (r2_hidden(B_95, k1_tops_1(A_96, A_10)) | ~m1_connsp_2(A_10, A_96, B_95) | ~m1_subset_1(B_95, u1_struct_0(A_96)) | ~l1_pre_topc(A_96) | ~v2_pre_topc(A_96) | v2_struct_0(A_96) | ~r1_tarski(A_10, u1_struct_0(A_96)))), inference(resolution, [status(thm)], [c_14, c_276])).
% 3.68/1.64  tff(c_281, plain, (![B_95]: (r2_hidden(B_95, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_95) | ~m1_subset_1(B_95, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_276])).
% 3.68/1.64  tff(c_285, plain, (![B_95]: (r2_hidden(B_95, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_95) | ~m1_subset_1(B_95, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_281])).
% 3.68/1.64  tff(c_299, plain, (![B_99]: (r2_hidden(B_99, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_99) | ~m1_subset_1(B_99, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_38, c_285])).
% 3.68/1.64  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.68/1.64  tff(c_311, plain, (![B_99]: (~v1_xboole_0(k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_99) | ~m1_subset_1(B_99, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_299, c_2])).
% 3.68/1.64  tff(c_312, plain, (~v1_xboole_0(k1_tops_1('#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_311])).
% 3.68/1.64  tff(c_142, plain, (![A_69, B_70]: (r1_tarski(k1_tops_1(A_69, B_70), B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.68/1.64  tff(c_147, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_5'), '#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_30, c_142])).
% 3.68/1.64  tff(c_151, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_147])).
% 3.68/1.64  tff(c_209, plain, (![A_80, B_81]: (v3_pre_topc(k1_tops_1(A_80, B_81), A_80) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80) | ~v2_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.68/1.64  tff(c_214, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_5'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_30, c_209])).
% 3.68/1.64  tff(c_218, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_214])).
% 3.68/1.64  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.68/1.64  tff(c_79, plain, (![C_56, B_57, A_58]: (r2_hidden(C_56, B_57) | ~r2_hidden(C_56, A_58) | ~r1_tarski(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.68/1.64  tff(c_129, plain, (![A_66, B_67, B_68]: (r2_hidden('#skF_2'(A_66, B_67), B_68) | ~r1_tarski(A_66, B_68) | r1_tarski(A_66, B_67))), inference(resolution, [status(thm)], [c_10, c_79])).
% 3.68/1.64  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.68/1.64  tff(c_319, plain, (![A_100, B_101, B_102, B_103]: (r2_hidden('#skF_2'(A_100, B_101), B_102) | ~r1_tarski(B_103, B_102) | ~r1_tarski(A_100, B_103) | r1_tarski(A_100, B_101))), inference(resolution, [status(thm)], [c_129, c_6])).
% 3.68/1.64  tff(c_338, plain, (![A_104, B_105]: (r2_hidden('#skF_2'(A_104, B_105), u1_struct_0('#skF_3')) | ~r1_tarski(A_104, '#skF_5') | r1_tarski(A_104, B_105))), inference(resolution, [status(thm)], [c_66, c_319])).
% 3.68/1.64  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.68/1.64  tff(c_349, plain, (![A_104]: (~r1_tarski(A_104, '#skF_5') | r1_tarski(A_104, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_338, c_8])).
% 3.68/1.64  tff(c_532, plain, (![B_120, A_121, C_122]: (m1_connsp_2(B_120, A_121, C_122) | ~r2_hidden(C_122, B_120) | ~v3_pre_topc(B_120, A_121) | ~m1_subset_1(C_122, u1_struct_0(A_121)) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_121))) | ~l1_pre_topc(A_121) | ~v2_pre_topc(A_121) | v2_struct_0(A_121))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.68/1.64  tff(c_534, plain, (![B_120]: (m1_connsp_2(B_120, '#skF_3', '#skF_4') | ~r2_hidden('#skF_4', B_120) | ~v3_pre_topc(B_120, '#skF_3') | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_532])).
% 3.68/1.64  tff(c_537, plain, (![B_120]: (m1_connsp_2(B_120, '#skF_3', '#skF_4') | ~r2_hidden('#skF_4', B_120) | ~v3_pre_topc(B_120, '#skF_3') | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_534])).
% 3.68/1.64  tff(c_580, plain, (![B_125]: (m1_connsp_2(B_125, '#skF_3', '#skF_4') | ~r2_hidden('#skF_4', B_125) | ~v3_pre_topc(B_125, '#skF_3') | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_38, c_537])).
% 3.68/1.64  tff(c_697, plain, (![A_135]: (m1_connsp_2(A_135, '#skF_3', '#skF_4') | ~r2_hidden('#skF_4', A_135) | ~v3_pre_topc(A_135, '#skF_3') | ~r1_tarski(A_135, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_14, c_580])).
% 3.68/1.64  tff(c_735, plain, (![A_136]: (m1_connsp_2(A_136, '#skF_3', '#skF_4') | ~r2_hidden('#skF_4', A_136) | ~v3_pre_topc(A_136, '#skF_3') | ~r1_tarski(A_136, '#skF_5'))), inference(resolution, [status(thm)], [c_349, c_697])).
% 3.68/1.64  tff(c_351, plain, (![A_106]: (~r1_tarski(A_106, '#skF_5') | r1_tarski(A_106, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_338, c_8])).
% 3.68/1.64  tff(c_46, plain, (![D_48]: (~r1_tarski(D_48, '#skF_5') | ~v3_pre_topc(D_48, '#skF_3') | ~m1_connsp_2(D_48, '#skF_3', '#skF_4') | ~m1_subset_1(D_48, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(D_48))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.68/1.64  tff(c_54, plain, (![A_10]: (~r1_tarski(A_10, '#skF_5') | ~v3_pre_topc(A_10, '#skF_3') | ~m1_connsp_2(A_10, '#skF_3', '#skF_4') | v1_xboole_0(A_10) | ~r1_tarski(A_10, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_14, c_46])).
% 3.68/1.64  tff(c_373, plain, (![A_106]: (~v3_pre_topc(A_106, '#skF_3') | ~m1_connsp_2(A_106, '#skF_3', '#skF_4') | v1_xboole_0(A_106) | ~r1_tarski(A_106, '#skF_5'))), inference(resolution, [status(thm)], [c_351, c_54])).
% 3.68/1.64  tff(c_746, plain, (![A_137]: (v1_xboole_0(A_137) | ~r2_hidden('#skF_4', A_137) | ~v3_pre_topc(A_137, '#skF_3') | ~r1_tarski(A_137, '#skF_5'))), inference(resolution, [status(thm)], [c_735, c_373])).
% 3.68/1.64  tff(c_753, plain, (v1_xboole_0(k1_tops_1('#skF_3', '#skF_5')) | ~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5')) | ~r1_tarski(k1_tops_1('#skF_3', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_218, c_746])).
% 3.68/1.64  tff(c_759, plain, (v1_xboole_0(k1_tops_1('#skF_3', '#skF_5')) | ~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_753])).
% 3.68/1.64  tff(c_760, plain, (~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_312, c_759])).
% 3.68/1.64  tff(c_763, plain, (~m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_282, c_760])).
% 3.68/1.64  tff(c_772, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_36, c_34, c_32, c_28, c_763])).
% 3.68/1.64  tff(c_774, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_772])).
% 3.68/1.64  tff(c_804, plain, (![B_141]: (~m1_connsp_2('#skF_5', '#skF_3', B_141) | ~m1_subset_1(B_141, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_311])).
% 3.68/1.64  tff(c_807, plain, (~m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_804])).
% 3.68/1.64  tff(c_811, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_807])).
% 3.68/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/1.64  
% 3.68/1.64  Inference rules
% 3.68/1.64  ----------------------
% 3.68/1.64  #Ref     : 0
% 3.68/1.64  #Sup     : 167
% 3.68/1.64  #Fact    : 0
% 3.68/1.64  #Define  : 0
% 3.68/1.64  #Split   : 8
% 3.68/1.64  #Chain   : 0
% 3.68/1.64  #Close   : 0
% 3.68/1.64  
% 3.68/1.64  Ordering : KBO
% 3.68/1.64  
% 3.68/1.64  Simplification rules
% 3.68/1.64  ----------------------
% 3.68/1.64  #Subsume      : 61
% 3.68/1.64  #Demod        : 51
% 3.68/1.64  #Tautology    : 15
% 3.68/1.64  #SimpNegUnit  : 11
% 3.68/1.64  #BackRed      : 0
% 3.68/1.64  
% 3.68/1.64  #Partial instantiations: 0
% 3.68/1.64  #Strategies tried      : 1
% 3.68/1.64  
% 3.68/1.64  Timing (in seconds)
% 3.68/1.64  ----------------------
% 3.68/1.65  Preprocessing        : 0.40
% 3.68/1.65  Parsing              : 0.20
% 3.68/1.65  CNF conversion       : 0.04
% 3.68/1.65  Main loop            : 0.46
% 3.68/1.65  Inferencing          : 0.17
% 3.68/1.65  Reduction            : 0.12
% 3.68/1.65  Demodulation         : 0.08
% 3.68/1.65  BG Simplification    : 0.02
% 3.68/1.65  Subsumption          : 0.11
% 3.68/1.65  Abstraction          : 0.02
% 3.68/1.65  MUC search           : 0.00
% 3.68/1.65  Cooper               : 0.00
% 3.68/1.65  Total                : 0.91
% 3.68/1.65  Index Insertion      : 0.00
% 3.68/1.65  Index Deletion       : 0.00
% 3.68/1.65  Index Matching       : 0.00
% 3.68/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
