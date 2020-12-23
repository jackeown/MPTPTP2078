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
% DateTime   : Thu Dec  3 10:24:07 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 289 expanded)
%              Number of leaves         :   28 ( 112 expanded)
%              Depth                    :   13
%              Number of atoms          :  184 (1073 expanded)
%              Number of equality atoms :    1 (   1 expanded)
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

tff(f_143,negated_conjecture,(
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

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_94,axiom,(
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

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_113,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_50,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,B_55)
      | ~ m1_subset_1(A_54,k1_zfmisc_1(B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_58,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_50])).

tff(c_44,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_36,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_268,plain,(
    ! [B_106,A_107,C_108] :
      ( r2_hidden(B_106,k1_tops_1(A_107,C_108))
      | ~ m1_connsp_2(C_108,A_107,B_106)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ m1_subset_1(B_106,u1_struct_0(A_107))
      | ~ l1_pre_topc(A_107)
      | ~ v2_pre_topc(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_278,plain,(
    ! [B_106,A_107,A_12] :
      ( r2_hidden(B_106,k1_tops_1(A_107,A_12))
      | ~ m1_connsp_2(A_12,A_107,B_106)
      | ~ m1_subset_1(B_106,u1_struct_0(A_107))
      | ~ l1_pre_topc(A_107)
      | ~ v2_pre_topc(A_107)
      | v2_struct_0(A_107)
      | ~ r1_tarski(A_12,u1_struct_0(A_107)) ) ),
    inference(resolution,[status(thm)],[c_18,c_268])).

tff(c_203,plain,(
    ! [A_101,B_102] :
      ( r1_tarski(k1_tops_1(A_101,B_102),B_102)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_211,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_203])).

tff(c_216,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_211])).

tff(c_217,plain,(
    ! [A_103,B_104] :
      ( v3_pre_topc(k1_tops_1(A_103,B_104),A_103)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103)
      | ~ v2_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_225,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_217])).

tff(c_230,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_225])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_135,plain,(
    ! [C_76,B_77,A_78] :
      ( r2_hidden(C_76,B_77)
      | ~ r2_hidden(C_76,A_78)
      | ~ r1_tarski(A_78,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_156,plain,(
    ! [A_91,B_92,B_93] :
      ( r2_hidden('#skF_1'(A_91,B_92),B_93)
      | ~ r1_tarski(A_91,B_93)
      | r1_tarski(A_91,B_92) ) ),
    inference(resolution,[status(thm)],[c_6,c_135])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_612,plain,(
    ! [A_153,B_154,B_155,B_156] :
      ( r2_hidden('#skF_1'(A_153,B_154),B_155)
      | ~ r1_tarski(B_156,B_155)
      | ~ r1_tarski(A_153,B_156)
      | r1_tarski(A_153,B_154) ) ),
    inference(resolution,[status(thm)],[c_156,c_2])).

tff(c_640,plain,(
    ! [A_157,B_158] :
      ( r2_hidden('#skF_1'(A_157,B_158),u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_157,'#skF_4')
      | r1_tarski(A_157,B_158) ) ),
    inference(resolution,[status(thm)],[c_58,c_612])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_663,plain,(
    ! [A_157] :
      ( ~ r1_tarski(A_157,'#skF_4')
      | r1_tarski(A_157,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_640,c_4])).

tff(c_595,plain,(
    ! [B_150,A_151,C_152] :
      ( m1_connsp_2(B_150,A_151,C_152)
      | ~ r2_hidden(C_152,B_150)
      | ~ v3_pre_topc(B_150,A_151)
      | ~ m1_subset_1(C_152,u1_struct_0(A_151))
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ l1_pre_topc(A_151)
      | ~ v2_pre_topc(A_151)
      | v2_struct_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_602,plain,(
    ! [B_150] :
      ( m1_connsp_2(B_150,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_150)
      | ~ v3_pre_topc(B_150,'#skF_2')
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_595])).

tff(c_610,plain,(
    ! [B_150] :
      ( m1_connsp_2(B_150,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_150)
      | ~ v3_pre_topc(B_150,'#skF_2')
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_602])).

tff(c_688,plain,(
    ! [B_160] :
      ( m1_connsp_2(B_160,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_160)
      | ~ v3_pre_topc(B_160,'#skF_2')
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_610])).

tff(c_907,plain,(
    ! [A_174] :
      ( m1_connsp_2(A_174,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',A_174)
      | ~ v3_pre_topc(A_174,'#skF_2')
      | ~ r1_tarski(A_174,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_18,c_688])).

tff(c_970,plain,(
    ! [A_179] :
      ( m1_connsp_2(A_179,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',A_179)
      | ~ v3_pre_topc(A_179,'#skF_2')
      | ~ r1_tarski(A_179,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_663,c_907])).

tff(c_664,plain,(
    ! [A_159] :
      ( ~ r1_tarski(A_159,'#skF_4')
      | r1_tarski(A_159,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_640,c_4])).

tff(c_59,plain,(
    ! [D_56] :
      ( ~ r1_tarski(D_56,'#skF_4')
      | ~ v3_pre_topc(D_56,'#skF_2')
      | ~ m1_connsp_2(D_56,'#skF_2','#skF_3')
      | ~ m1_subset_1(D_56,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v1_xboole_0(D_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_67,plain,(
    ! [A_12] :
      ( ~ r1_tarski(A_12,'#skF_4')
      | ~ v3_pre_topc(A_12,'#skF_2')
      | ~ m1_connsp_2(A_12,'#skF_2','#skF_3')
      | v1_xboole_0(A_12)
      | ~ r1_tarski(A_12,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_18,c_59])).

tff(c_683,plain,(
    ! [A_159] :
      ( ~ v3_pre_topc(A_159,'#skF_2')
      | ~ m1_connsp_2(A_159,'#skF_2','#skF_3')
      | v1_xboole_0(A_159)
      | ~ r1_tarski(A_159,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_664,c_67])).

tff(c_975,plain,(
    ! [A_180] :
      ( v1_xboole_0(A_180)
      | ~ r2_hidden('#skF_3',A_180)
      | ~ v3_pre_topc(A_180,'#skF_2')
      | ~ r1_tarski(A_180,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_970,c_683])).

tff(c_982,plain,
    ( v1_xboole_0(k1_tops_1('#skF_2','#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_230,c_975])).

tff(c_988,plain,
    ( v1_xboole_0(k1_tops_1('#skF_2','#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_982])).

tff(c_989,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_988])).

tff(c_993,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_278,c_989])).

tff(c_999,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_44,c_42,c_40,c_36,c_993])).

tff(c_1001,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_999])).

tff(c_1002,plain,(
    v1_xboole_0(k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_988])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1003,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_988])).

tff(c_91,plain,(
    ! [C_63,B_64,A_65] :
      ( ~ v1_xboole_0(C_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(C_63))
      | ~ r2_hidden(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_96,plain,(
    ! [B_13,A_65,A_12] :
      ( ~ v1_xboole_0(B_13)
      | ~ r2_hidden(A_65,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_18,c_91])).

tff(c_1035,plain,(
    ! [B_184] :
      ( ~ v1_xboole_0(B_184)
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),B_184) ) ),
    inference(resolution,[status(thm)],[c_1003,c_96])).

tff(c_1058,plain,(
    ~ v1_xboole_0(k1_tops_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_12,c_1035])).

tff(c_1075,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1002,c_1058])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:00:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.59  
% 3.32/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.59  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.32/1.59  
% 3.32/1.59  %Foreground sorts:
% 3.32/1.59  
% 3.32/1.59  
% 3.32/1.59  %Background operators:
% 3.32/1.59  
% 3.32/1.59  
% 3.32/1.59  %Foreground operators:
% 3.32/1.59  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.32/1.59  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.32/1.59  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.32/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.32/1.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.32/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.32/1.59  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.32/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.32/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.32/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.32/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.32/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.59  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.32/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.32/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.32/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.32/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.32/1.59  
% 3.32/1.61  tff(f_143, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(C, A, B) & (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~((m1_connsp_2(D, A, B) & v3_pre_topc(D, A)) & r1_tarski(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_connsp_2)).
% 3.32/1.61  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.32/1.61  tff(f_94, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 3.32/1.61  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 3.32/1.61  tff(f_70, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.32/1.61  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.32/1.61  tff(f_113, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 3.32/1.61  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.32/1.61  tff(f_62, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.32/1.61  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.32/1.61  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.32/1.61  tff(c_50, plain, (![A_54, B_55]: (r1_tarski(A_54, B_55) | ~m1_subset_1(A_54, k1_zfmisc_1(B_55)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.32/1.61  tff(c_58, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_50])).
% 3.32/1.61  tff(c_44, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.32/1.61  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.32/1.61  tff(c_40, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.32/1.61  tff(c_36, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.32/1.61  tff(c_18, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.32/1.61  tff(c_268, plain, (![B_106, A_107, C_108]: (r2_hidden(B_106, k1_tops_1(A_107, C_108)) | ~m1_connsp_2(C_108, A_107, B_106) | ~m1_subset_1(C_108, k1_zfmisc_1(u1_struct_0(A_107))) | ~m1_subset_1(B_106, u1_struct_0(A_107)) | ~l1_pre_topc(A_107) | ~v2_pre_topc(A_107) | v2_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.32/1.61  tff(c_278, plain, (![B_106, A_107, A_12]: (r2_hidden(B_106, k1_tops_1(A_107, A_12)) | ~m1_connsp_2(A_12, A_107, B_106) | ~m1_subset_1(B_106, u1_struct_0(A_107)) | ~l1_pre_topc(A_107) | ~v2_pre_topc(A_107) | v2_struct_0(A_107) | ~r1_tarski(A_12, u1_struct_0(A_107)))), inference(resolution, [status(thm)], [c_18, c_268])).
% 3.32/1.61  tff(c_203, plain, (![A_101, B_102]: (r1_tarski(k1_tops_1(A_101, B_102), B_102) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.32/1.61  tff(c_211, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_203])).
% 3.32/1.61  tff(c_216, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_211])).
% 3.32/1.61  tff(c_217, plain, (![A_103, B_104]: (v3_pre_topc(k1_tops_1(A_103, B_104), A_103) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103) | ~v2_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.32/1.61  tff(c_225, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_217])).
% 3.32/1.61  tff(c_230, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_225])).
% 3.32/1.61  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.32/1.61  tff(c_135, plain, (![C_76, B_77, A_78]: (r2_hidden(C_76, B_77) | ~r2_hidden(C_76, A_78) | ~r1_tarski(A_78, B_77))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.32/1.61  tff(c_156, plain, (![A_91, B_92, B_93]: (r2_hidden('#skF_1'(A_91, B_92), B_93) | ~r1_tarski(A_91, B_93) | r1_tarski(A_91, B_92))), inference(resolution, [status(thm)], [c_6, c_135])).
% 3.32/1.61  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.32/1.61  tff(c_612, plain, (![A_153, B_154, B_155, B_156]: (r2_hidden('#skF_1'(A_153, B_154), B_155) | ~r1_tarski(B_156, B_155) | ~r1_tarski(A_153, B_156) | r1_tarski(A_153, B_154))), inference(resolution, [status(thm)], [c_156, c_2])).
% 3.32/1.61  tff(c_640, plain, (![A_157, B_158]: (r2_hidden('#skF_1'(A_157, B_158), u1_struct_0('#skF_2')) | ~r1_tarski(A_157, '#skF_4') | r1_tarski(A_157, B_158))), inference(resolution, [status(thm)], [c_58, c_612])).
% 3.32/1.61  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.32/1.61  tff(c_663, plain, (![A_157]: (~r1_tarski(A_157, '#skF_4') | r1_tarski(A_157, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_640, c_4])).
% 3.32/1.61  tff(c_595, plain, (![B_150, A_151, C_152]: (m1_connsp_2(B_150, A_151, C_152) | ~r2_hidden(C_152, B_150) | ~v3_pre_topc(B_150, A_151) | ~m1_subset_1(C_152, u1_struct_0(A_151)) | ~m1_subset_1(B_150, k1_zfmisc_1(u1_struct_0(A_151))) | ~l1_pre_topc(A_151) | ~v2_pre_topc(A_151) | v2_struct_0(A_151))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.32/1.61  tff(c_602, plain, (![B_150]: (m1_connsp_2(B_150, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_150) | ~v3_pre_topc(B_150, '#skF_2') | ~m1_subset_1(B_150, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_595])).
% 3.32/1.61  tff(c_610, plain, (![B_150]: (m1_connsp_2(B_150, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_150) | ~v3_pre_topc(B_150, '#skF_2') | ~m1_subset_1(B_150, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_602])).
% 3.32/1.61  tff(c_688, plain, (![B_160]: (m1_connsp_2(B_160, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_160) | ~v3_pre_topc(B_160, '#skF_2') | ~m1_subset_1(B_160, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_46, c_610])).
% 3.32/1.61  tff(c_907, plain, (![A_174]: (m1_connsp_2(A_174, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', A_174) | ~v3_pre_topc(A_174, '#skF_2') | ~r1_tarski(A_174, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_18, c_688])).
% 3.32/1.61  tff(c_970, plain, (![A_179]: (m1_connsp_2(A_179, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', A_179) | ~v3_pre_topc(A_179, '#skF_2') | ~r1_tarski(A_179, '#skF_4'))), inference(resolution, [status(thm)], [c_663, c_907])).
% 3.32/1.61  tff(c_664, plain, (![A_159]: (~r1_tarski(A_159, '#skF_4') | r1_tarski(A_159, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_640, c_4])).
% 3.32/1.61  tff(c_59, plain, (![D_56]: (~r1_tarski(D_56, '#skF_4') | ~v3_pre_topc(D_56, '#skF_2') | ~m1_connsp_2(D_56, '#skF_2', '#skF_3') | ~m1_subset_1(D_56, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(D_56))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.32/1.61  tff(c_67, plain, (![A_12]: (~r1_tarski(A_12, '#skF_4') | ~v3_pre_topc(A_12, '#skF_2') | ~m1_connsp_2(A_12, '#skF_2', '#skF_3') | v1_xboole_0(A_12) | ~r1_tarski(A_12, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_18, c_59])).
% 3.32/1.61  tff(c_683, plain, (![A_159]: (~v3_pre_topc(A_159, '#skF_2') | ~m1_connsp_2(A_159, '#skF_2', '#skF_3') | v1_xboole_0(A_159) | ~r1_tarski(A_159, '#skF_4'))), inference(resolution, [status(thm)], [c_664, c_67])).
% 3.32/1.61  tff(c_975, plain, (![A_180]: (v1_xboole_0(A_180) | ~r2_hidden('#skF_3', A_180) | ~v3_pre_topc(A_180, '#skF_2') | ~r1_tarski(A_180, '#skF_4'))), inference(resolution, [status(thm)], [c_970, c_683])).
% 3.32/1.61  tff(c_982, plain, (v1_xboole_0(k1_tops_1('#skF_2', '#skF_4')) | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_230, c_975])).
% 3.32/1.61  tff(c_988, plain, (v1_xboole_0(k1_tops_1('#skF_2', '#skF_4')) | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_982])).
% 3.32/1.61  tff(c_989, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_988])).
% 3.32/1.61  tff(c_993, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_278, c_989])).
% 3.32/1.61  tff(c_999, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_44, c_42, c_40, c_36, c_993])).
% 3.32/1.61  tff(c_1001, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_999])).
% 3.32/1.61  tff(c_1002, plain, (v1_xboole_0(k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_988])).
% 3.32/1.61  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.32/1.61  tff(c_1003, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_988])).
% 3.32/1.61  tff(c_91, plain, (![C_63, B_64, A_65]: (~v1_xboole_0(C_63) | ~m1_subset_1(B_64, k1_zfmisc_1(C_63)) | ~r2_hidden(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.32/1.61  tff(c_96, plain, (![B_13, A_65, A_12]: (~v1_xboole_0(B_13) | ~r2_hidden(A_65, A_12) | ~r1_tarski(A_12, B_13))), inference(resolution, [status(thm)], [c_18, c_91])).
% 3.32/1.61  tff(c_1035, plain, (![B_184]: (~v1_xboole_0(B_184) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), B_184))), inference(resolution, [status(thm)], [c_1003, c_96])).
% 3.32/1.61  tff(c_1058, plain, (~v1_xboole_0(k1_tops_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_12, c_1035])).
% 3.32/1.61  tff(c_1075, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1002, c_1058])).
% 3.32/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.61  
% 3.32/1.61  Inference rules
% 3.32/1.61  ----------------------
% 3.32/1.61  #Ref     : 0
% 3.32/1.61  #Sup     : 244
% 3.32/1.61  #Fact    : 0
% 3.32/1.61  #Define  : 0
% 3.32/1.61  #Split   : 9
% 3.32/1.61  #Chain   : 0
% 3.32/1.61  #Close   : 0
% 3.32/1.61  
% 3.32/1.61  Ordering : KBO
% 3.32/1.61  
% 3.32/1.61  Simplification rules
% 3.32/1.61  ----------------------
% 3.32/1.61  #Subsume      : 72
% 3.32/1.61  #Demod        : 47
% 3.32/1.61  #Tautology    : 14
% 3.32/1.61  #SimpNegUnit  : 9
% 3.32/1.61  #BackRed      : 0
% 3.32/1.61  
% 3.32/1.61  #Partial instantiations: 0
% 3.32/1.61  #Strategies tried      : 1
% 3.32/1.61  
% 3.32/1.61  Timing (in seconds)
% 3.32/1.61  ----------------------
% 3.32/1.61  Preprocessing        : 0.32
% 3.32/1.61  Parsing              : 0.18
% 3.32/1.61  CNF conversion       : 0.02
% 3.32/1.61  Main loop            : 0.46
% 3.32/1.61  Inferencing          : 0.16
% 3.32/1.61  Reduction            : 0.12
% 3.32/1.61  Demodulation         : 0.08
% 3.32/1.61  BG Simplification    : 0.02
% 3.32/1.61  Subsumption          : 0.13
% 3.32/1.61  Abstraction          : 0.02
% 3.32/1.61  MUC search           : 0.00
% 3.32/1.61  Cooper               : 0.00
% 3.32/1.61  Total                : 0.81
% 3.32/1.61  Index Insertion      : 0.00
% 3.32/1.61  Index Deletion       : 0.00
% 3.32/1.61  Index Matching       : 0.00
% 3.32/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
