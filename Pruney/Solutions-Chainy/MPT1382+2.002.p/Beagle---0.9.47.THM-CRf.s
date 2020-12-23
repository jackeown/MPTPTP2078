%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:07 EST 2020

% Result     : Theorem 5.91s
% Output     : CNFRefutation 6.00s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 327 expanded)
%              Number of leaves         :   30 ( 125 expanded)
%              Depth                    :   14
%              Number of atoms          :  290 (1312 expanded)
%              Number of equality atoms :    1 (   3 expanded)
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

tff(f_152,negated_conjecture,(
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

tff(f_86,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_69,axiom,(
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

tff(f_105,axiom,(
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

tff(f_61,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_122,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( m1_connsp_2(B,A,C)
               => r2_hidden(C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).

tff(c_40,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_36,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_44,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_665,plain,(
    ! [B_151,A_152,C_153] :
      ( r2_hidden(B_151,k1_tops_1(A_152,C_153))
      | ~ m1_connsp_2(C_153,A_152,B_151)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ m1_subset_1(B_151,u1_struct_0(A_152))
      | ~ l1_pre_topc(A_152)
      | ~ v2_pre_topc(A_152)
      | v2_struct_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_675,plain,(
    ! [B_151] :
      ( r2_hidden(B_151,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_151)
      | ~ m1_subset_1(B_151,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_665])).

tff(c_681,plain,(
    ! [B_151] :
      ( r2_hidden(B_151,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_151)
      | ~ m1_subset_1(B_151,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_675])).

tff(c_682,plain,(
    ! [B_151] :
      ( r2_hidden(B_151,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_151)
      | ~ m1_subset_1(B_151,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_681])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_683,plain,(
    ! [B_154] :
      ( r2_hidden(B_154,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_154)
      | ~ m1_subset_1(B_154,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_681])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_91,plain,(
    ! [C_65,B_66,A_67] :
      ( ~ v1_xboole_0(C_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(C_65))
      | ~ r2_hidden(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_96,plain,(
    ! [B_9,A_67,A_8] :
      ( ~ v1_xboole_0(B_9)
      | ~ r2_hidden(A_67,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(resolution,[status(thm)],[c_16,c_91])).

tff(c_702,plain,(
    ! [B_9,B_154] :
      ( ~ v1_xboole_0(B_9)
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),B_9)
      | ~ m1_connsp_2('#skF_4','#skF_2',B_154)
      | ~ m1_subset_1(B_154,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_683,c_96])).

tff(c_817,plain,(
    ! [B_162] :
      ( ~ m1_connsp_2('#skF_4','#skF_2',B_162)
      | ~ m1_subset_1(B_162,u1_struct_0('#skF_2')) ) ),
    inference(splitLeft,[status(thm)],[c_702])).

tff(c_830,plain,(
    ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_817])).

tff(c_837,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_830])).

tff(c_839,plain,(
    ! [B_163] :
      ( ~ v1_xboole_0(B_163)
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),B_163) ) ),
    inference(splitRight,[status(thm)],[c_702])).

tff(c_856,plain,(
    ~ v1_xboole_0(k1_tops_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_12,c_839])).

tff(c_233,plain,(
    ! [A_104,B_105] :
      ( v3_pre_topc(k1_tops_1(A_104,B_105),A_104)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104)
      | ~ v2_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_241,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_233])).

tff(c_246,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_241])).

tff(c_49,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,B_55)
      | ~ m1_subset_1(A_54,k1_zfmisc_1(B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_53,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_49])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_135,plain,(
    ! [C_78,B_79,A_80] :
      ( r2_hidden(C_78,B_79)
      | ~ r2_hidden(C_78,A_80)
      | ~ r1_tarski(A_80,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_170,plain,(
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

tff(c_704,plain,(
    ! [A_155,B_156,B_157,B_158] :
      ( r2_hidden('#skF_1'(A_155,B_156),B_157)
      | ~ r1_tarski(B_158,B_157)
      | ~ r1_tarski(A_155,B_158)
      | r1_tarski(A_155,B_156) ) ),
    inference(resolution,[status(thm)],[c_170,c_2])).

tff(c_726,plain,(
    ! [A_159,B_160] :
      ( r2_hidden('#skF_1'(A_159,B_160),u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_159,'#skF_4')
      | r1_tarski(A_159,B_160) ) ),
    inference(resolution,[status(thm)],[c_53,c_704])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_749,plain,(
    ! [A_159] :
      ( ~ r1_tarski(A_159,'#skF_4')
      | r1_tarski(A_159,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_726,c_4])).

tff(c_857,plain,(
    ! [B_164,A_165,C_166] :
      ( m1_connsp_2(B_164,A_165,C_166)
      | ~ r2_hidden(C_166,B_164)
      | ~ v3_pre_topc(B_164,A_165)
      | ~ m1_subset_1(C_166,u1_struct_0(A_165))
      | ~ m1_subset_1(B_164,k1_zfmisc_1(u1_struct_0(A_165)))
      | ~ l1_pre_topc(A_165)
      | ~ v2_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_866,plain,(
    ! [B_164] :
      ( m1_connsp_2(B_164,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_164)
      | ~ v3_pre_topc(B_164,'#skF_2')
      | ~ m1_subset_1(B_164,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_857])).

tff(c_878,plain,(
    ! [B_164] :
      ( m1_connsp_2(B_164,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_164)
      | ~ v3_pre_topc(B_164,'#skF_2')
      | ~ m1_subset_1(B_164,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_866])).

tff(c_975,plain,(
    ! [B_170] :
      ( m1_connsp_2(B_170,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_170)
      | ~ v3_pre_topc(B_170,'#skF_2')
      | ~ m1_subset_1(B_170,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_878])).

tff(c_999,plain,(
    ! [A_171] :
      ( m1_connsp_2(A_171,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',A_171)
      | ~ v3_pre_topc(A_171,'#skF_2')
      | ~ r1_tarski(A_171,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_16,c_975])).

tff(c_1056,plain,(
    ! [A_173] :
      ( m1_connsp_2(A_173,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',A_173)
      | ~ v3_pre_topc(A_173,'#skF_2')
      | ~ r1_tarski(A_173,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_749,c_999])).

tff(c_880,plain,(
    ! [A_167] :
      ( ~ r1_tarski(A_167,'#skF_4')
      | r1_tarski(A_167,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_726,c_4])).

tff(c_62,plain,(
    ! [A_57,B_58] :
      ( m1_subset_1(A_57,k1_zfmisc_1(B_58))
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_34,plain,(
    ! [D_52] :
      ( ~ r1_tarski(D_52,'#skF_4')
      | ~ v3_pre_topc(D_52,'#skF_2')
      | ~ m1_connsp_2(D_52,'#skF_2','#skF_3')
      | ~ m1_subset_1(D_52,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v1_xboole_0(D_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_70,plain,(
    ! [A_57] :
      ( ~ r1_tarski(A_57,'#skF_4')
      | ~ v3_pre_topc(A_57,'#skF_2')
      | ~ m1_connsp_2(A_57,'#skF_2','#skF_3')
      | v1_xboole_0(A_57)
      | ~ r1_tarski(A_57,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_62,c_34])).

tff(c_947,plain,(
    ! [A_167] :
      ( ~ v3_pre_topc(A_167,'#skF_2')
      | ~ m1_connsp_2(A_167,'#skF_2','#skF_3')
      | v1_xboole_0(A_167)
      | ~ r1_tarski(A_167,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_880,c_70])).

tff(c_1085,plain,(
    ! [A_177] :
      ( v1_xboole_0(A_177)
      | ~ r2_hidden('#skF_3',A_177)
      | ~ v3_pre_topc(A_177,'#skF_2')
      | ~ r1_tarski(A_177,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1056,c_947])).

tff(c_1092,plain,
    ( v1_xboole_0(k1_tops_1('#skF_2','#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_246,c_1085])).

tff(c_1098,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_856,c_1092])).

tff(c_1099,plain,(
    ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1098])).

tff(c_138,plain,(
    ! [A_1,B_2,B_79] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_79)
      | ~ r1_tarski(A_1,B_79)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_135])).

tff(c_362,plain,(
    ! [A_120,B_121] :
      ( m1_subset_1(k1_tops_1(A_120,B_121),k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    ! [A_10,C_12,B_11] :
      ( m1_subset_1(A_10,C_12)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(C_12))
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1218,plain,(
    ! [A_197,A_198,B_199] :
      ( m1_subset_1(A_197,u1_struct_0(A_198))
      | ~ r2_hidden(A_197,k1_tops_1(A_198,B_199))
      | ~ m1_subset_1(B_199,k1_zfmisc_1(u1_struct_0(A_198)))
      | ~ l1_pre_topc(A_198) ) ),
    inference(resolution,[status(thm)],[c_362,c_18])).

tff(c_2034,plain,(
    ! [A_312,B_313,A_314,B_315] :
      ( m1_subset_1('#skF_1'(A_312,B_313),u1_struct_0(A_314))
      | ~ m1_subset_1(B_315,k1_zfmisc_1(u1_struct_0(A_314)))
      | ~ l1_pre_topc(A_314)
      | ~ r1_tarski(A_312,k1_tops_1(A_314,B_315))
      | r1_tarski(A_312,B_313) ) ),
    inference(resolution,[status(thm)],[c_138,c_1218])).

tff(c_2047,plain,(
    ! [A_312,B_313] :
      ( m1_subset_1('#skF_1'(A_312,B_313),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_312,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(A_312,B_313) ) ),
    inference(resolution,[status(thm)],[c_38,c_2034])).

tff(c_2054,plain,(
    ! [A_312,B_313] :
      ( m1_subset_1('#skF_1'(A_312,B_313),u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_312,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(A_312,B_313) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2047])).

tff(c_509,plain,(
    ! [C_134,A_135,B_136] :
      ( m1_connsp_2(C_134,A_135,B_136)
      | ~ r2_hidden(B_136,k1_tops_1(A_135,C_134))
      | ~ m1_subset_1(C_134,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ m1_subset_1(B_136,u1_struct_0(A_135))
      | ~ l1_pre_topc(A_135)
      | ~ v2_pre_topc(A_135)
      | v2_struct_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_3056,plain,(
    ! [C_426,A_427,A_428,B_429] :
      ( m1_connsp_2(C_426,A_427,'#skF_1'(A_428,B_429))
      | ~ m1_subset_1(C_426,k1_zfmisc_1(u1_struct_0(A_427)))
      | ~ m1_subset_1('#skF_1'(A_428,B_429),u1_struct_0(A_427))
      | ~ l1_pre_topc(A_427)
      | ~ v2_pre_topc(A_427)
      | v2_struct_0(A_427)
      | ~ r1_tarski(A_428,k1_tops_1(A_427,C_426))
      | r1_tarski(A_428,B_429) ) ),
    inference(resolution,[status(thm)],[c_138,c_509])).

tff(c_3069,plain,(
    ! [A_428,B_429] :
      ( m1_connsp_2('#skF_4','#skF_2','#skF_1'(A_428,B_429))
      | ~ m1_subset_1('#skF_1'(A_428,B_429),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_428,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(A_428,B_429) ) ),
    inference(resolution,[status(thm)],[c_38,c_3056])).

tff(c_3076,plain,(
    ! [A_428,B_429] :
      ( m1_connsp_2('#skF_4','#skF_2','#skF_1'(A_428,B_429))
      | ~ m1_subset_1('#skF_1'(A_428,B_429),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_428,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(A_428,B_429) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_3069])).

tff(c_3078,plain,(
    ! [A_430,B_431] :
      ( m1_connsp_2('#skF_4','#skF_2','#skF_1'(A_430,B_431))
      | ~ m1_subset_1('#skF_1'(A_430,B_431),u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_430,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(A_430,B_431) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_3076])).

tff(c_3115,plain,(
    ! [A_432,B_433] :
      ( m1_connsp_2('#skF_4','#skF_2','#skF_1'(A_432,B_433))
      | ~ r1_tarski(A_432,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(A_432,B_433) ) ),
    inference(resolution,[status(thm)],[c_2054,c_3078])).

tff(c_32,plain,(
    ! [C_40,B_38,A_34] :
      ( r2_hidden(C_40,B_38)
      | ~ m1_connsp_2(B_38,A_34,C_40)
      | ~ m1_subset_1(C_40,u1_struct_0(A_34))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_3148,plain,(
    ! [A_432,B_433] :
      ( r2_hidden('#skF_1'(A_432,B_433),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_432,B_433),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_432,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(A_432,B_433) ) ),
    inference(resolution,[status(thm)],[c_3115,c_32])).

tff(c_3163,plain,(
    ! [A_432,B_433] :
      ( r2_hidden('#skF_1'(A_432,B_433),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_432,B_433),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_432,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(A_432,B_433) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_38,c_3148])).

tff(c_3165,plain,(
    ! [A_434,B_435] :
      ( r2_hidden('#skF_1'(A_434,B_435),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_434,B_435),u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_434,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(A_434,B_435) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_3163])).

tff(c_3202,plain,(
    ! [A_436,B_437] :
      ( r2_hidden('#skF_1'(A_436,B_437),'#skF_4')
      | ~ r1_tarski(A_436,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(A_436,B_437) ) ),
    inference(resolution,[status(thm)],[c_2054,c_3165])).

tff(c_3220,plain,(
    ! [A_438] :
      ( ~ r1_tarski(A_438,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(A_438,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3202,c_4])).

tff(c_3236,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_3220])).

tff(c_3245,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1099,c_3236])).

tff(c_3246,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1098])).

tff(c_3250,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_682,c_3246])).

tff(c_3257,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_3250])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:14:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.91/2.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.97/2.11  
% 5.97/2.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.97/2.11  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.97/2.11  
% 5.97/2.11  %Foreground sorts:
% 5.97/2.11  
% 5.97/2.11  
% 5.97/2.11  %Background operators:
% 5.97/2.11  
% 5.97/2.11  
% 5.97/2.11  %Foreground operators:
% 5.97/2.11  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.97/2.11  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 5.97/2.11  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.97/2.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.97/2.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.97/2.11  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.97/2.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.97/2.11  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.97/2.11  tff('#skF_2', type, '#skF_2': $i).
% 5.97/2.11  tff('#skF_3', type, '#skF_3': $i).
% 5.97/2.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.97/2.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.97/2.11  tff('#skF_4', type, '#skF_4': $i).
% 5.97/2.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.97/2.11  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.97/2.11  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.97/2.11  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.97/2.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.97/2.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.97/2.11  
% 6.00/2.13  tff(f_152, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(C, A, B) & (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~((m1_connsp_2(D, A, B) & v3_pre_topc(D, A)) & r1_tarski(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_connsp_2)).
% 6.00/2.13  tff(f_86, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 6.00/2.13  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.00/2.13  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.00/2.13  tff(f_55, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 6.00/2.13  tff(f_69, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 6.00/2.13  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.00/2.13  tff(f_105, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 6.00/2.13  tff(f_61, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 6.00/2.13  tff(f_48, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 6.00/2.13  tff(f_122, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_connsp_2)).
% 6.00/2.13  tff(c_40, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.00/2.13  tff(c_36, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.00/2.13  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.00/2.13  tff(c_44, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.00/2.13  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.00/2.13  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.00/2.13  tff(c_665, plain, (![B_151, A_152, C_153]: (r2_hidden(B_151, k1_tops_1(A_152, C_153)) | ~m1_connsp_2(C_153, A_152, B_151) | ~m1_subset_1(C_153, k1_zfmisc_1(u1_struct_0(A_152))) | ~m1_subset_1(B_151, u1_struct_0(A_152)) | ~l1_pre_topc(A_152) | ~v2_pre_topc(A_152) | v2_struct_0(A_152))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.00/2.13  tff(c_675, plain, (![B_151]: (r2_hidden(B_151, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_151) | ~m1_subset_1(B_151, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_665])).
% 6.00/2.13  tff(c_681, plain, (![B_151]: (r2_hidden(B_151, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_151) | ~m1_subset_1(B_151, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_675])).
% 6.00/2.13  tff(c_682, plain, (![B_151]: (r2_hidden(B_151, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_151) | ~m1_subset_1(B_151, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_46, c_681])).
% 6.00/2.13  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.00/2.13  tff(c_683, plain, (![B_154]: (r2_hidden(B_154, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_154) | ~m1_subset_1(B_154, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_46, c_681])).
% 6.00/2.13  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.00/2.13  tff(c_91, plain, (![C_65, B_66, A_67]: (~v1_xboole_0(C_65) | ~m1_subset_1(B_66, k1_zfmisc_1(C_65)) | ~r2_hidden(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.00/2.13  tff(c_96, plain, (![B_9, A_67, A_8]: (~v1_xboole_0(B_9) | ~r2_hidden(A_67, A_8) | ~r1_tarski(A_8, B_9))), inference(resolution, [status(thm)], [c_16, c_91])).
% 6.00/2.13  tff(c_702, plain, (![B_9, B_154]: (~v1_xboole_0(B_9) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), B_9) | ~m1_connsp_2('#skF_4', '#skF_2', B_154) | ~m1_subset_1(B_154, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_683, c_96])).
% 6.00/2.13  tff(c_817, plain, (![B_162]: (~m1_connsp_2('#skF_4', '#skF_2', B_162) | ~m1_subset_1(B_162, u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_702])).
% 6.00/2.13  tff(c_830, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_817])).
% 6.00/2.13  tff(c_837, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_830])).
% 6.00/2.13  tff(c_839, plain, (![B_163]: (~v1_xboole_0(B_163) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), B_163))), inference(splitRight, [status(thm)], [c_702])).
% 6.00/2.13  tff(c_856, plain, (~v1_xboole_0(k1_tops_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_12, c_839])).
% 6.00/2.13  tff(c_233, plain, (![A_104, B_105]: (v3_pre_topc(k1_tops_1(A_104, B_105), A_104) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104) | ~v2_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.00/2.13  tff(c_241, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_233])).
% 6.00/2.13  tff(c_246, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_241])).
% 6.00/2.13  tff(c_49, plain, (![A_54, B_55]: (r1_tarski(A_54, B_55) | ~m1_subset_1(A_54, k1_zfmisc_1(B_55)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.00/2.13  tff(c_53, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_49])).
% 6.00/2.13  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.00/2.13  tff(c_135, plain, (![C_78, B_79, A_80]: (r2_hidden(C_78, B_79) | ~r2_hidden(C_78, A_80) | ~r1_tarski(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.00/2.13  tff(c_170, plain, (![A_91, B_92, B_93]: (r2_hidden('#skF_1'(A_91, B_92), B_93) | ~r1_tarski(A_91, B_93) | r1_tarski(A_91, B_92))), inference(resolution, [status(thm)], [c_6, c_135])).
% 6.00/2.13  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.00/2.13  tff(c_704, plain, (![A_155, B_156, B_157, B_158]: (r2_hidden('#skF_1'(A_155, B_156), B_157) | ~r1_tarski(B_158, B_157) | ~r1_tarski(A_155, B_158) | r1_tarski(A_155, B_156))), inference(resolution, [status(thm)], [c_170, c_2])).
% 6.00/2.13  tff(c_726, plain, (![A_159, B_160]: (r2_hidden('#skF_1'(A_159, B_160), u1_struct_0('#skF_2')) | ~r1_tarski(A_159, '#skF_4') | r1_tarski(A_159, B_160))), inference(resolution, [status(thm)], [c_53, c_704])).
% 6.00/2.13  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.00/2.13  tff(c_749, plain, (![A_159]: (~r1_tarski(A_159, '#skF_4') | r1_tarski(A_159, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_726, c_4])).
% 6.00/2.13  tff(c_857, plain, (![B_164, A_165, C_166]: (m1_connsp_2(B_164, A_165, C_166) | ~r2_hidden(C_166, B_164) | ~v3_pre_topc(B_164, A_165) | ~m1_subset_1(C_166, u1_struct_0(A_165)) | ~m1_subset_1(B_164, k1_zfmisc_1(u1_struct_0(A_165))) | ~l1_pre_topc(A_165) | ~v2_pre_topc(A_165) | v2_struct_0(A_165))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.00/2.13  tff(c_866, plain, (![B_164]: (m1_connsp_2(B_164, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_164) | ~v3_pre_topc(B_164, '#skF_2') | ~m1_subset_1(B_164, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_857])).
% 6.00/2.13  tff(c_878, plain, (![B_164]: (m1_connsp_2(B_164, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_164) | ~v3_pre_topc(B_164, '#skF_2') | ~m1_subset_1(B_164, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_866])).
% 6.00/2.13  tff(c_975, plain, (![B_170]: (m1_connsp_2(B_170, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_170) | ~v3_pre_topc(B_170, '#skF_2') | ~m1_subset_1(B_170, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_46, c_878])).
% 6.00/2.13  tff(c_999, plain, (![A_171]: (m1_connsp_2(A_171, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', A_171) | ~v3_pre_topc(A_171, '#skF_2') | ~r1_tarski(A_171, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_16, c_975])).
% 6.00/2.13  tff(c_1056, plain, (![A_173]: (m1_connsp_2(A_173, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', A_173) | ~v3_pre_topc(A_173, '#skF_2') | ~r1_tarski(A_173, '#skF_4'))), inference(resolution, [status(thm)], [c_749, c_999])).
% 6.00/2.13  tff(c_880, plain, (![A_167]: (~r1_tarski(A_167, '#skF_4') | r1_tarski(A_167, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_726, c_4])).
% 6.00/2.13  tff(c_62, plain, (![A_57, B_58]: (m1_subset_1(A_57, k1_zfmisc_1(B_58)) | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.00/2.13  tff(c_34, plain, (![D_52]: (~r1_tarski(D_52, '#skF_4') | ~v3_pre_topc(D_52, '#skF_2') | ~m1_connsp_2(D_52, '#skF_2', '#skF_3') | ~m1_subset_1(D_52, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(D_52))), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.00/2.13  tff(c_70, plain, (![A_57]: (~r1_tarski(A_57, '#skF_4') | ~v3_pre_topc(A_57, '#skF_2') | ~m1_connsp_2(A_57, '#skF_2', '#skF_3') | v1_xboole_0(A_57) | ~r1_tarski(A_57, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_62, c_34])).
% 6.00/2.13  tff(c_947, plain, (![A_167]: (~v3_pre_topc(A_167, '#skF_2') | ~m1_connsp_2(A_167, '#skF_2', '#skF_3') | v1_xboole_0(A_167) | ~r1_tarski(A_167, '#skF_4'))), inference(resolution, [status(thm)], [c_880, c_70])).
% 6.00/2.13  tff(c_1085, plain, (![A_177]: (v1_xboole_0(A_177) | ~r2_hidden('#skF_3', A_177) | ~v3_pre_topc(A_177, '#skF_2') | ~r1_tarski(A_177, '#skF_4'))), inference(resolution, [status(thm)], [c_1056, c_947])).
% 6.00/2.13  tff(c_1092, plain, (v1_xboole_0(k1_tops_1('#skF_2', '#skF_4')) | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_246, c_1085])).
% 6.00/2.13  tff(c_1098, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_856, c_1092])).
% 6.00/2.13  tff(c_1099, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_1098])).
% 6.00/2.13  tff(c_138, plain, (![A_1, B_2, B_79]: (r2_hidden('#skF_1'(A_1, B_2), B_79) | ~r1_tarski(A_1, B_79) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_135])).
% 6.00/2.13  tff(c_362, plain, (![A_120, B_121]: (m1_subset_1(k1_tops_1(A_120, B_121), k1_zfmisc_1(u1_struct_0(A_120))) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_pre_topc(A_120))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.00/2.13  tff(c_18, plain, (![A_10, C_12, B_11]: (m1_subset_1(A_10, C_12) | ~m1_subset_1(B_11, k1_zfmisc_1(C_12)) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.00/2.13  tff(c_1218, plain, (![A_197, A_198, B_199]: (m1_subset_1(A_197, u1_struct_0(A_198)) | ~r2_hidden(A_197, k1_tops_1(A_198, B_199)) | ~m1_subset_1(B_199, k1_zfmisc_1(u1_struct_0(A_198))) | ~l1_pre_topc(A_198))), inference(resolution, [status(thm)], [c_362, c_18])).
% 6.00/2.13  tff(c_2034, plain, (![A_312, B_313, A_314, B_315]: (m1_subset_1('#skF_1'(A_312, B_313), u1_struct_0(A_314)) | ~m1_subset_1(B_315, k1_zfmisc_1(u1_struct_0(A_314))) | ~l1_pre_topc(A_314) | ~r1_tarski(A_312, k1_tops_1(A_314, B_315)) | r1_tarski(A_312, B_313))), inference(resolution, [status(thm)], [c_138, c_1218])).
% 6.00/2.13  tff(c_2047, plain, (![A_312, B_313]: (m1_subset_1('#skF_1'(A_312, B_313), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_312, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(A_312, B_313))), inference(resolution, [status(thm)], [c_38, c_2034])).
% 6.00/2.13  tff(c_2054, plain, (![A_312, B_313]: (m1_subset_1('#skF_1'(A_312, B_313), u1_struct_0('#skF_2')) | ~r1_tarski(A_312, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(A_312, B_313))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2047])).
% 6.00/2.13  tff(c_509, plain, (![C_134, A_135, B_136]: (m1_connsp_2(C_134, A_135, B_136) | ~r2_hidden(B_136, k1_tops_1(A_135, C_134)) | ~m1_subset_1(C_134, k1_zfmisc_1(u1_struct_0(A_135))) | ~m1_subset_1(B_136, u1_struct_0(A_135)) | ~l1_pre_topc(A_135) | ~v2_pre_topc(A_135) | v2_struct_0(A_135))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.00/2.13  tff(c_3056, plain, (![C_426, A_427, A_428, B_429]: (m1_connsp_2(C_426, A_427, '#skF_1'(A_428, B_429)) | ~m1_subset_1(C_426, k1_zfmisc_1(u1_struct_0(A_427))) | ~m1_subset_1('#skF_1'(A_428, B_429), u1_struct_0(A_427)) | ~l1_pre_topc(A_427) | ~v2_pre_topc(A_427) | v2_struct_0(A_427) | ~r1_tarski(A_428, k1_tops_1(A_427, C_426)) | r1_tarski(A_428, B_429))), inference(resolution, [status(thm)], [c_138, c_509])).
% 6.00/2.13  tff(c_3069, plain, (![A_428, B_429]: (m1_connsp_2('#skF_4', '#skF_2', '#skF_1'(A_428, B_429)) | ~m1_subset_1('#skF_1'(A_428, B_429), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_428, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(A_428, B_429))), inference(resolution, [status(thm)], [c_38, c_3056])).
% 6.00/2.13  tff(c_3076, plain, (![A_428, B_429]: (m1_connsp_2('#skF_4', '#skF_2', '#skF_1'(A_428, B_429)) | ~m1_subset_1('#skF_1'(A_428, B_429), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~r1_tarski(A_428, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(A_428, B_429))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_3069])).
% 6.00/2.13  tff(c_3078, plain, (![A_430, B_431]: (m1_connsp_2('#skF_4', '#skF_2', '#skF_1'(A_430, B_431)) | ~m1_subset_1('#skF_1'(A_430, B_431), u1_struct_0('#skF_2')) | ~r1_tarski(A_430, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(A_430, B_431))), inference(negUnitSimplification, [status(thm)], [c_46, c_3076])).
% 6.00/2.13  tff(c_3115, plain, (![A_432, B_433]: (m1_connsp_2('#skF_4', '#skF_2', '#skF_1'(A_432, B_433)) | ~r1_tarski(A_432, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(A_432, B_433))), inference(resolution, [status(thm)], [c_2054, c_3078])).
% 6.00/2.13  tff(c_32, plain, (![C_40, B_38, A_34]: (r2_hidden(C_40, B_38) | ~m1_connsp_2(B_38, A_34, C_40) | ~m1_subset_1(C_40, u1_struct_0(A_34)) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.00/2.13  tff(c_3148, plain, (![A_432, B_433]: (r2_hidden('#skF_1'(A_432, B_433), '#skF_4') | ~m1_subset_1('#skF_1'(A_432, B_433), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_432, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(A_432, B_433))), inference(resolution, [status(thm)], [c_3115, c_32])).
% 6.00/2.13  tff(c_3163, plain, (![A_432, B_433]: (r2_hidden('#skF_1'(A_432, B_433), '#skF_4') | ~m1_subset_1('#skF_1'(A_432, B_433), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~r1_tarski(A_432, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(A_432, B_433))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_38, c_3148])).
% 6.00/2.13  tff(c_3165, plain, (![A_434, B_435]: (r2_hidden('#skF_1'(A_434, B_435), '#skF_4') | ~m1_subset_1('#skF_1'(A_434, B_435), u1_struct_0('#skF_2')) | ~r1_tarski(A_434, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(A_434, B_435))), inference(negUnitSimplification, [status(thm)], [c_46, c_3163])).
% 6.00/2.13  tff(c_3202, plain, (![A_436, B_437]: (r2_hidden('#skF_1'(A_436, B_437), '#skF_4') | ~r1_tarski(A_436, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(A_436, B_437))), inference(resolution, [status(thm)], [c_2054, c_3165])).
% 6.00/2.13  tff(c_3220, plain, (![A_438]: (~r1_tarski(A_438, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(A_438, '#skF_4'))), inference(resolution, [status(thm)], [c_3202, c_4])).
% 6.00/2.13  tff(c_3236, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_12, c_3220])).
% 6.00/2.13  tff(c_3245, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1099, c_3236])).
% 6.00/2.13  tff(c_3246, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_1098])).
% 6.00/2.13  tff(c_3250, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_682, c_3246])).
% 6.00/2.13  tff(c_3257, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_3250])).
% 6.00/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.00/2.13  
% 6.00/2.13  Inference rules
% 6.00/2.13  ----------------------
% 6.00/2.13  #Ref     : 0
% 6.00/2.13  #Sup     : 699
% 6.00/2.13  #Fact    : 0
% 6.00/2.13  #Define  : 0
% 6.00/2.13  #Split   : 10
% 6.00/2.13  #Chain   : 0
% 6.00/2.13  #Close   : 0
% 6.00/2.13  
% 6.00/2.13  Ordering : KBO
% 6.00/2.13  
% 6.00/2.13  Simplification rules
% 6.00/2.13  ----------------------
% 6.00/2.13  #Subsume      : 293
% 6.00/2.13  #Demod        : 315
% 6.00/2.13  #Tautology    : 80
% 6.00/2.13  #SimpNegUnit  : 49
% 6.00/2.13  #BackRed      : 2
% 6.00/2.13  
% 6.00/2.13  #Partial instantiations: 0
% 6.00/2.13  #Strategies tried      : 1
% 6.00/2.13  
% 6.00/2.13  Timing (in seconds)
% 6.00/2.13  ----------------------
% 6.00/2.14  Preprocessing        : 0.31
% 6.00/2.14  Parsing              : 0.17
% 6.00/2.14  CNF conversion       : 0.03
% 6.00/2.14  Main loop            : 1.05
% 6.00/2.14  Inferencing          : 0.34
% 6.00/2.14  Reduction            : 0.29
% 6.00/2.14  Demodulation         : 0.19
% 6.00/2.14  BG Simplification    : 0.03
% 6.00/2.14  Subsumption          : 0.31
% 6.00/2.14  Abstraction          : 0.04
% 6.00/2.14  MUC search           : 0.00
% 6.00/2.14  Cooper               : 0.00
% 6.00/2.14  Total                : 1.40
% 6.00/2.14  Index Insertion      : 0.00
% 6.00/2.14  Index Deletion       : 0.00
% 6.00/2.14  Index Matching       : 0.00
% 6.00/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
