%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:11 EST 2020

% Result     : Theorem 5.02s
% Output     : CNFRefutation 5.17s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 307 expanded)
%              Number of leaves         :   27 ( 118 expanded)
%              Depth                    :   10
%              Number of atoms          :  359 (1172 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_connsp_2)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_88,axiom,(
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

tff(c_26,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_44,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_55,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_56,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_60,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_56])).

tff(c_996,plain,(
    ! [A_132,C_133,B_134] :
      ( r1_tarski(A_132,C_133)
      | ~ r1_tarski(B_134,C_133)
      | ~ r1_tarski(A_132,B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1013,plain,(
    ! [A_136] :
      ( r1_tarski(A_136,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_136,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_996])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_48,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | v3_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_53,plain,(
    v3_pre_topc('#skF_5','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_40,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_54,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_52,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_74,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_34,plain,(
    ! [D_48] :
      ( ~ r2_hidden('#skF_3',D_48)
      | ~ r1_tarski(D_48,'#skF_4')
      | ~ v3_pre_topc(D_48,'#skF_2')
      | ~ m1_subset_1(D_48,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_357,plain,(
    ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_30,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_28,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_67,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_1'(A_55,B_56),A_55)
      | r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_72,plain,(
    ! [A_55] : r1_tarski(A_55,A_55) ),
    inference(resolution,[status(thm)],[c_67,c_4])).

tff(c_565,plain,(
    ! [B_102,A_103,C_104] :
      ( r1_tarski(B_102,k1_tops_1(A_103,C_104))
      | ~ r1_tarski(B_102,C_104)
      | ~ v3_pre_topc(B_102,A_103)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_572,plain,(
    ! [B_102] :
      ( r1_tarski(B_102,k1_tops_1('#skF_2','#skF_4'))
      | ~ r1_tarski(B_102,'#skF_4')
      | ~ v3_pre_topc(B_102,'#skF_2')
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_565])).

tff(c_607,plain,(
    ! [B_111] :
      ( r1_tarski(B_111,k1_tops_1('#skF_2','#skF_4'))
      | ~ r1_tarski(B_111,'#skF_4')
      | ~ v3_pre_topc(B_111,'#skF_2')
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_572])).

tff(c_610,plain,
    ( r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_4')
    | ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_607])).

tff(c_620,plain,(
    r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_55,c_610])).

tff(c_108,plain,(
    ! [C_64,B_65,A_66] :
      ( r2_hidden(C_64,B_65)
      | ~ r2_hidden(C_64,A_66)
      | ~ r1_tarski(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_115,plain,(
    ! [B_67] :
      ( r2_hidden('#skF_3',B_67)
      | ~ r1_tarski('#skF_5',B_67) ) ),
    inference(resolution,[status(thm)],[c_54,c_108])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_118,plain,(
    ! [B_2,B_67] :
      ( r2_hidden('#skF_3',B_2)
      | ~ r1_tarski(B_67,B_2)
      | ~ r1_tarski('#skF_5',B_67) ) ),
    inference(resolution,[status(thm)],[c_115,c_2])).

tff(c_640,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_620,c_118])).

tff(c_656,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_640])).

tff(c_876,plain,(
    ! [C_121,A_122,B_123] :
      ( m1_connsp_2(C_121,A_122,B_123)
      | ~ r2_hidden(B_123,k1_tops_1(A_122,C_121))
      | ~ m1_subset_1(C_121,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ m1_subset_1(B_123,u1_struct_0(A_122))
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_880,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_656,c_876])).

tff(c_899,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_880])).

tff(c_901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_357,c_899])).

tff(c_974,plain,(
    ! [D_131] :
      ( ~ r2_hidden('#skF_3',D_131)
      | ~ r1_tarski(D_131,'#skF_4')
      | ~ v3_pre_topc(D_131,'#skF_2')
      | ~ m1_subset_1(D_131,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_977,plain,
    ( ~ r2_hidden('#skF_3','#skF_5')
    | ~ r1_tarski('#skF_5','#skF_4')
    | ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_974])).

tff(c_988,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_55,c_54,c_977])).

tff(c_990,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_994,plain,(
    ~ r1_tarski('#skF_5',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_12,c_990])).

tff(c_1018,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1013,c_994])).

tff(c_1023,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_1018])).

tff(c_1024,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1026,plain,(
    ! [A_137,B_138] :
      ( r1_tarski(A_137,B_138)
      | ~ m1_subset_1(A_137,k1_zfmisc_1(B_138)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1030,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_1026])).

tff(c_1063,plain,(
    ! [A_153,B_154] :
      ( r1_tarski(k1_tops_1(A_153,B_154),B_154)
      | ~ m1_subset_1(B_154,k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ l1_pre_topc(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1068,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_1063])).

tff(c_1072,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1068])).

tff(c_1693,plain,(
    ! [B_231,A_232,C_233] :
      ( r2_hidden(B_231,k1_tops_1(A_232,C_233))
      | ~ m1_connsp_2(C_233,A_232,B_231)
      | ~ m1_subset_1(C_233,k1_zfmisc_1(u1_struct_0(A_232)))
      | ~ m1_subset_1(B_231,u1_struct_0(A_232))
      | ~ l1_pre_topc(A_232)
      | ~ v2_pre_topc(A_232)
      | v2_struct_0(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1698,plain,(
    ! [B_231] :
      ( r2_hidden(B_231,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_231)
      | ~ m1_subset_1(B_231,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_1693])).

tff(c_1702,plain,(
    ! [B_231] :
      ( r2_hidden(B_231,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_231)
      | ~ m1_subset_1(B_231,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_1698])).

tff(c_1704,plain,(
    ! [B_234] :
      ( r2_hidden(B_234,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_234)
      | ~ m1_subset_1(B_234,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1702])).

tff(c_1128,plain,(
    ! [A_161,B_162] :
      ( v3_pre_topc(k1_tops_1(A_161,B_162),A_161)
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0(A_161)))
      | ~ l1_pre_topc(A_161)
      | ~ v2_pre_topc(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1134,plain,(
    ! [A_161,A_9] :
      ( v3_pre_topc(k1_tops_1(A_161,A_9),A_161)
      | ~ l1_pre_topc(A_161)
      | ~ v2_pre_topc(A_161)
      | ~ r1_tarski(A_9,u1_struct_0(A_161)) ) ),
    inference(resolution,[status(thm)],[c_12,c_1128])).

tff(c_1056,plain,(
    ! [A_150,C_151,B_152] :
      ( r1_tarski(A_150,C_151)
      | ~ r1_tarski(B_152,C_151)
      | ~ r1_tarski(A_150,B_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1062,plain,(
    ! [A_150] :
      ( r1_tarski(A_150,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_150,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1030,c_1056])).

tff(c_1025,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,(
    ! [D_48] :
      ( ~ r2_hidden('#skF_3',D_48)
      | ~ r1_tarski(D_48,'#skF_4')
      | ~ v3_pre_topc(D_48,'#skF_2')
      | ~ m1_subset_1(D_48,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r1_tarski('#skF_5','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1147,plain,(
    ! [D_164] :
      ( ~ r2_hidden('#skF_3',D_164)
      | ~ r1_tarski(D_164,'#skF_4')
      | ~ v3_pre_topc(D_164,'#skF_2')
      | ~ m1_subset_1(D_164,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1025,c_42])).

tff(c_1200,plain,(
    ! [A_173] :
      ( ~ r2_hidden('#skF_3',A_173)
      | ~ r1_tarski(A_173,'#skF_4')
      | ~ v3_pre_topc(A_173,'#skF_2')
      | ~ r1_tarski(A_173,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_12,c_1147])).

tff(c_1233,plain,(
    ! [A_174] :
      ( ~ r2_hidden('#skF_3',A_174)
      | ~ v3_pre_topc(A_174,'#skF_2')
      | ~ r1_tarski(A_174,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1062,c_1200])).

tff(c_1237,plain,(
    ! [A_9] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',A_9))
      | ~ r1_tarski(k1_tops_1('#skF_2',A_9),'#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ r1_tarski(A_9,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1134,c_1233])).

tff(c_1246,plain,(
    ! [A_9] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',A_9))
      | ~ r1_tarski(k1_tops_1('#skF_2',A_9),'#skF_4')
      | ~ r1_tarski(A_9,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_1237])).

tff(c_1710,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ r1_tarski('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1704,c_1246])).

tff(c_1727,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1024,c_1030,c_1072,c_1710])).

tff(c_1728,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_2519,plain,(
    ! [B_345,A_346,C_347] :
      ( r2_hidden(B_345,k1_tops_1(A_346,C_347))
      | ~ m1_connsp_2(C_347,A_346,B_345)
      | ~ m1_subset_1(C_347,k1_zfmisc_1(u1_struct_0(A_346)))
      | ~ m1_subset_1(B_345,u1_struct_0(A_346))
      | ~ l1_pre_topc(A_346)
      | ~ v2_pre_topc(A_346)
      | v2_struct_0(A_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2524,plain,(
    ! [B_345] :
      ( r2_hidden(B_345,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_345)
      | ~ m1_subset_1(B_345,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_2519])).

tff(c_2528,plain,(
    ! [B_345] :
      ( r2_hidden(B_345,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_345)
      | ~ m1_subset_1(B_345,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_2524])).

tff(c_2530,plain,(
    ! [B_348] :
      ( r2_hidden(B_348,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_348)
      | ~ m1_subset_1(B_348,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_2528])).

tff(c_1804,plain,(
    ! [A_258,B_259] :
      ( v3_pre_topc(k1_tops_1(A_258,B_259),A_258)
      | ~ m1_subset_1(B_259,k1_zfmisc_1(u1_struct_0(A_258)))
      | ~ l1_pre_topc(A_258)
      | ~ v2_pre_topc(A_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1809,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_1804])).

tff(c_1813,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_1809])).

tff(c_1786,plain,(
    ! [A_256,B_257] :
      ( r1_tarski(k1_tops_1(A_256,B_257),B_257)
      | ~ m1_subset_1(B_257,k1_zfmisc_1(u1_struct_0(A_256)))
      | ~ l1_pre_topc(A_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1791,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_1786])).

tff(c_1795,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1791])).

tff(c_1742,plain,(
    ! [A_241,B_242] :
      ( r2_hidden('#skF_1'(A_241,B_242),A_241)
      | r1_tarski(A_241,B_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1747,plain,(
    ! [A_241] : r1_tarski(A_241,A_241) ),
    inference(resolution,[status(thm)],[c_1742,c_4])).

tff(c_1732,plain,(
    ! [A_237,B_238] :
      ( r1_tarski(A_237,B_238)
      | ~ m1_subset_1(A_237,k1_zfmisc_1(B_238)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1740,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_1732])).

tff(c_1750,plain,(
    ! [A_244,C_245,B_246] :
      ( r1_tarski(A_244,C_245)
      | ~ r1_tarski(B_246,C_245)
      | ~ r1_tarski(A_244,B_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1757,plain,(
    ! [A_247] :
      ( r1_tarski(A_247,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_247,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1740,c_1750])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(B_7,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1760,plain,(
    ! [A_6,A_247] :
      ( r1_tarski(A_6,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_6,A_247)
      | ~ r1_tarski(A_247,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1757,c_8])).

tff(c_1797,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_1795,c_1760])).

tff(c_1802,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1747,c_1797])).

tff(c_1729,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_38,plain,(
    ! [D_48] :
      ( ~ r2_hidden('#skF_3',D_48)
      | ~ r1_tarski(D_48,'#skF_4')
      | ~ v3_pre_topc(D_48,'#skF_2')
      | ~ m1_subset_1(D_48,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r2_hidden('#skF_3','#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2245,plain,(
    ! [D_315] :
      ( ~ r2_hidden('#skF_3',D_315)
      | ~ r1_tarski(D_315,'#skF_4')
      | ~ v3_pre_topc(D_315,'#skF_2')
      | ~ m1_subset_1(D_315,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1729,c_38])).

tff(c_2366,plain,(
    ! [A_327] :
      ( ~ r2_hidden('#skF_3',A_327)
      | ~ r1_tarski(A_327,'#skF_4')
      | ~ v3_pre_topc(A_327,'#skF_2')
      | ~ r1_tarski(A_327,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_12,c_2245])).

tff(c_2382,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1802,c_2366])).

tff(c_2401,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1813,c_1795,c_2382])).

tff(c_2533,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2530,c_2401])).

tff(c_2543,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1728,c_2533])).

tff(c_2544,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2548,plain,(
    ! [A_349,B_350] :
      ( r1_tarski(A_349,B_350)
      | ~ m1_subset_1(A_349,k1_zfmisc_1(B_350)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2552,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_2548])).

tff(c_2607,plain,(
    ! [A_368,B_369] :
      ( r1_tarski(k1_tops_1(A_368,B_369),B_369)
      | ~ m1_subset_1(B_369,k1_zfmisc_1(u1_struct_0(A_368)))
      | ~ l1_pre_topc(A_368) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2612,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_2607])).

tff(c_2616,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2612])).

tff(c_2973,plain,(
    ! [B_422,A_423,C_424] :
      ( r2_hidden(B_422,k1_tops_1(A_423,C_424))
      | ~ m1_connsp_2(C_424,A_423,B_422)
      | ~ m1_subset_1(C_424,k1_zfmisc_1(u1_struct_0(A_423)))
      | ~ m1_subset_1(B_422,u1_struct_0(A_423))
      | ~ l1_pre_topc(A_423)
      | ~ v2_pre_topc(A_423)
      | v2_struct_0(A_423) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2978,plain,(
    ! [B_422] :
      ( r2_hidden(B_422,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_422)
      | ~ m1_subset_1(B_422,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_2973])).

tff(c_2982,plain,(
    ! [B_422] :
      ( r2_hidden(B_422,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_422)
      | ~ m1_subset_1(B_422,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_2978])).

tff(c_3030,plain,(
    ! [B_428] :
      ( r2_hidden(B_428,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_428)
      | ~ m1_subset_1(B_428,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_2982])).

tff(c_2700,plain,(
    ! [A_379,B_380] :
      ( v3_pre_topc(k1_tops_1(A_379,B_380),A_379)
      | ~ m1_subset_1(B_380,k1_zfmisc_1(u1_struct_0(A_379)))
      | ~ l1_pre_topc(A_379)
      | ~ v2_pre_topc(A_379) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2718,plain,(
    ! [A_381,A_382] :
      ( v3_pre_topc(k1_tops_1(A_381,A_382),A_381)
      | ~ l1_pre_topc(A_381)
      | ~ v2_pre_topc(A_381)
      | ~ r1_tarski(A_382,u1_struct_0(A_381)) ) ),
    inference(resolution,[status(thm)],[c_12,c_2700])).

tff(c_2585,plain,(
    ! [A_362,C_363,B_364] :
      ( r1_tarski(A_362,C_363)
      | ~ r1_tarski(B_364,C_363)
      | ~ r1_tarski(A_362,B_364) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2591,plain,(
    ! [A_362] :
      ( r1_tarski(A_362,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_362,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2552,c_2585])).

tff(c_2545,plain,(
    ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,(
    ! [D_48] :
      ( ~ r2_hidden('#skF_3',D_48)
      | ~ r1_tarski(D_48,'#skF_4')
      | ~ v3_pre_topc(D_48,'#skF_2')
      | ~ m1_subset_1(D_48,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v3_pre_topc('#skF_5','#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2572,plain,(
    ! [D_361] :
      ( ~ r2_hidden('#skF_3',D_361)
      | ~ r1_tarski(D_361,'#skF_4')
      | ~ v3_pre_topc(D_361,'#skF_2')
      | ~ m1_subset_1(D_361,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2545,c_46])).

tff(c_2672,plain,(
    ! [A_377] :
      ( ~ r2_hidden('#skF_3',A_377)
      | ~ r1_tarski(A_377,'#skF_4')
      | ~ v3_pre_topc(A_377,'#skF_2')
      | ~ r1_tarski(A_377,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_12,c_2572])).

tff(c_2694,plain,(
    ! [A_362] :
      ( ~ r2_hidden('#skF_3',A_362)
      | ~ v3_pre_topc(A_362,'#skF_2')
      | ~ r1_tarski(A_362,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2591,c_2672])).

tff(c_2722,plain,(
    ! [A_382] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',A_382))
      | ~ r1_tarski(k1_tops_1('#skF_2',A_382),'#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ r1_tarski(A_382,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_2718,c_2694])).

tff(c_2725,plain,(
    ! [A_382] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',A_382))
      | ~ r1_tarski(k1_tops_1('#skF_2',A_382),'#skF_4')
      | ~ r1_tarski(A_382,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_2722])).

tff(c_3034,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ r1_tarski('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_3030,c_2725])).

tff(c_3047,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2544,c_2552,c_2616,c_3034])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:21:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.02/1.97  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.17/1.99  
% 5.17/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.17/1.99  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.17/1.99  
% 5.17/1.99  %Foreground sorts:
% 5.17/1.99  
% 5.17/1.99  
% 5.17/1.99  %Background operators:
% 5.17/1.99  
% 5.17/1.99  
% 5.17/1.99  %Foreground operators:
% 5.17/1.99  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.17/1.99  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 5.17/1.99  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.17/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.17/1.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.17/1.99  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.17/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.17/1.99  tff('#skF_5', type, '#skF_5': $i).
% 5.17/1.99  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.17/1.99  tff('#skF_2', type, '#skF_2': $i).
% 5.17/1.99  tff('#skF_3', type, '#skF_3': $i).
% 5.17/1.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.17/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.17/1.99  tff('#skF_4', type, '#skF_4': $i).
% 5.17/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.17/1.99  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.17/1.99  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.17/1.99  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.17/1.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.17/1.99  
% 5.17/2.02  tff(f_113, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_connsp_2)).
% 5.17/2.02  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.17/2.02  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.17/2.02  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.17/2.02  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 5.17/2.02  tff(f_88, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 5.17/2.02  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 5.17/2.02  tff(f_50, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 5.17/2.02  tff(c_26, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.17/2.02  tff(c_44, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.17/2.02  tff(c_55, plain, (r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_44])).
% 5.17/2.02  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.17/2.02  tff(c_56, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~m1_subset_1(A_49, k1_zfmisc_1(B_50)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.17/2.02  tff(c_60, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_56])).
% 5.17/2.02  tff(c_996, plain, (![A_132, C_133, B_134]: (r1_tarski(A_132, C_133) | ~r1_tarski(B_134, C_133) | ~r1_tarski(A_132, B_134))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.17/2.02  tff(c_1013, plain, (![A_136]: (r1_tarski(A_136, u1_struct_0('#skF_2')) | ~r1_tarski(A_136, '#skF_4'))), inference(resolution, [status(thm)], [c_60, c_996])).
% 5.17/2.02  tff(c_12, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.17/2.02  tff(c_48, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | v3_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.17/2.02  tff(c_53, plain, (v3_pre_topc('#skF_5', '#skF_2')), inference(splitLeft, [status(thm)], [c_48])).
% 5.17/2.02  tff(c_40, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.17/2.02  tff(c_54, plain, (r2_hidden('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_40])).
% 5.17/2.02  tff(c_52, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.17/2.02  tff(c_74, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_52])).
% 5.17/2.02  tff(c_32, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.17/2.02  tff(c_34, plain, (![D_48]: (~r2_hidden('#skF_3', D_48) | ~r1_tarski(D_48, '#skF_4') | ~v3_pre_topc(D_48, '#skF_2') | ~m1_subset_1(D_48, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_connsp_2('#skF_4', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.17/2.02  tff(c_357, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_34])).
% 5.17/2.02  tff(c_30, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.17/2.02  tff(c_28, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.17/2.02  tff(c_67, plain, (![A_55, B_56]: (r2_hidden('#skF_1'(A_55, B_56), A_55) | r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.17/2.02  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.17/2.02  tff(c_72, plain, (![A_55]: (r1_tarski(A_55, A_55))), inference(resolution, [status(thm)], [c_67, c_4])).
% 5.17/2.02  tff(c_565, plain, (![B_102, A_103, C_104]: (r1_tarski(B_102, k1_tops_1(A_103, C_104)) | ~r1_tarski(B_102, C_104) | ~v3_pre_topc(B_102, A_103) | ~m1_subset_1(C_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.17/2.02  tff(c_572, plain, (![B_102]: (r1_tarski(B_102, k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(B_102, '#skF_4') | ~v3_pre_topc(B_102, '#skF_2') | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_565])).
% 5.17/2.02  tff(c_607, plain, (![B_111]: (r1_tarski(B_111, k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(B_111, '#skF_4') | ~v3_pre_topc(B_111, '#skF_2') | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_572])).
% 5.17/2.02  tff(c_610, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_607])).
% 5.17/2.02  tff(c_620, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_55, c_610])).
% 5.17/2.02  tff(c_108, plain, (![C_64, B_65, A_66]: (r2_hidden(C_64, B_65) | ~r2_hidden(C_64, A_66) | ~r1_tarski(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.17/2.02  tff(c_115, plain, (![B_67]: (r2_hidden('#skF_3', B_67) | ~r1_tarski('#skF_5', B_67))), inference(resolution, [status(thm)], [c_54, c_108])).
% 5.17/2.02  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.17/2.02  tff(c_118, plain, (![B_2, B_67]: (r2_hidden('#skF_3', B_2) | ~r1_tarski(B_67, B_2) | ~r1_tarski('#skF_5', B_67))), inference(resolution, [status(thm)], [c_115, c_2])).
% 5.17/2.02  tff(c_640, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_620, c_118])).
% 5.17/2.02  tff(c_656, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_640])).
% 5.17/2.02  tff(c_876, plain, (![C_121, A_122, B_123]: (m1_connsp_2(C_121, A_122, B_123) | ~r2_hidden(B_123, k1_tops_1(A_122, C_121)) | ~m1_subset_1(C_121, k1_zfmisc_1(u1_struct_0(A_122))) | ~m1_subset_1(B_123, u1_struct_0(A_122)) | ~l1_pre_topc(A_122) | ~v2_pre_topc(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.17/2.02  tff(c_880, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_656, c_876])).
% 5.17/2.02  tff(c_899, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_880])).
% 5.17/2.02  tff(c_901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_357, c_899])).
% 5.17/2.02  tff(c_974, plain, (![D_131]: (~r2_hidden('#skF_3', D_131) | ~r1_tarski(D_131, '#skF_4') | ~v3_pre_topc(D_131, '#skF_2') | ~m1_subset_1(D_131, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_34])).
% 5.17/2.02  tff(c_977, plain, (~r2_hidden('#skF_3', '#skF_5') | ~r1_tarski('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_974])).
% 5.17/2.02  tff(c_988, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_53, c_55, c_54, c_977])).
% 5.17/2.02  tff(c_990, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_52])).
% 5.17/2.02  tff(c_994, plain, (~r1_tarski('#skF_5', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_12, c_990])).
% 5.17/2.02  tff(c_1018, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1013, c_994])).
% 5.17/2.02  tff(c_1023, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_1018])).
% 5.17/2.02  tff(c_1024, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 5.17/2.02  tff(c_1026, plain, (![A_137, B_138]: (r1_tarski(A_137, B_138) | ~m1_subset_1(A_137, k1_zfmisc_1(B_138)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.17/2.02  tff(c_1030, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_1026])).
% 5.17/2.02  tff(c_1063, plain, (![A_153, B_154]: (r1_tarski(k1_tops_1(A_153, B_154), B_154) | ~m1_subset_1(B_154, k1_zfmisc_1(u1_struct_0(A_153))) | ~l1_pre_topc(A_153))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.17/2.02  tff(c_1068, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_1063])).
% 5.17/2.02  tff(c_1072, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1068])).
% 5.17/2.02  tff(c_1693, plain, (![B_231, A_232, C_233]: (r2_hidden(B_231, k1_tops_1(A_232, C_233)) | ~m1_connsp_2(C_233, A_232, B_231) | ~m1_subset_1(C_233, k1_zfmisc_1(u1_struct_0(A_232))) | ~m1_subset_1(B_231, u1_struct_0(A_232)) | ~l1_pre_topc(A_232) | ~v2_pre_topc(A_232) | v2_struct_0(A_232))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.17/2.02  tff(c_1698, plain, (![B_231]: (r2_hidden(B_231, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_231) | ~m1_subset_1(B_231, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_1693])).
% 5.17/2.02  tff(c_1702, plain, (![B_231]: (r2_hidden(B_231, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_231) | ~m1_subset_1(B_231, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_1698])).
% 5.17/2.02  tff(c_1704, plain, (![B_234]: (r2_hidden(B_234, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_234) | ~m1_subset_1(B_234, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_32, c_1702])).
% 5.17/2.02  tff(c_1128, plain, (![A_161, B_162]: (v3_pre_topc(k1_tops_1(A_161, B_162), A_161) | ~m1_subset_1(B_162, k1_zfmisc_1(u1_struct_0(A_161))) | ~l1_pre_topc(A_161) | ~v2_pre_topc(A_161))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.17/2.02  tff(c_1134, plain, (![A_161, A_9]: (v3_pre_topc(k1_tops_1(A_161, A_9), A_161) | ~l1_pre_topc(A_161) | ~v2_pre_topc(A_161) | ~r1_tarski(A_9, u1_struct_0(A_161)))), inference(resolution, [status(thm)], [c_12, c_1128])).
% 5.17/2.02  tff(c_1056, plain, (![A_150, C_151, B_152]: (r1_tarski(A_150, C_151) | ~r1_tarski(B_152, C_151) | ~r1_tarski(A_150, B_152))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.17/2.02  tff(c_1062, plain, (![A_150]: (r1_tarski(A_150, u1_struct_0('#skF_2')) | ~r1_tarski(A_150, '#skF_4'))), inference(resolution, [status(thm)], [c_1030, c_1056])).
% 5.17/2.02  tff(c_1025, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_44])).
% 5.17/2.02  tff(c_42, plain, (![D_48]: (~r2_hidden('#skF_3', D_48) | ~r1_tarski(D_48, '#skF_4') | ~v3_pre_topc(D_48, '#skF_2') | ~m1_subset_1(D_48, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r1_tarski('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.17/2.02  tff(c_1147, plain, (![D_164]: (~r2_hidden('#skF_3', D_164) | ~r1_tarski(D_164, '#skF_4') | ~v3_pre_topc(D_164, '#skF_2') | ~m1_subset_1(D_164, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_1025, c_42])).
% 5.17/2.02  tff(c_1200, plain, (![A_173]: (~r2_hidden('#skF_3', A_173) | ~r1_tarski(A_173, '#skF_4') | ~v3_pre_topc(A_173, '#skF_2') | ~r1_tarski(A_173, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_12, c_1147])).
% 5.17/2.02  tff(c_1233, plain, (![A_174]: (~r2_hidden('#skF_3', A_174) | ~v3_pre_topc(A_174, '#skF_2') | ~r1_tarski(A_174, '#skF_4'))), inference(resolution, [status(thm)], [c_1062, c_1200])).
% 5.17/2.02  tff(c_1237, plain, (![A_9]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', A_9)) | ~r1_tarski(k1_tops_1('#skF_2', A_9), '#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r1_tarski(A_9, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1134, c_1233])).
% 5.17/2.02  tff(c_1246, plain, (![A_9]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', A_9)) | ~r1_tarski(k1_tops_1('#skF_2', A_9), '#skF_4') | ~r1_tarski(A_9, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_1237])).
% 5.17/2.02  tff(c_1710, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~r1_tarski('#skF_4', u1_struct_0('#skF_2')) | ~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_1704, c_1246])).
% 5.17/2.02  tff(c_1727, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_1024, c_1030, c_1072, c_1710])).
% 5.17/2.02  tff(c_1728, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_40])).
% 5.17/2.02  tff(c_2519, plain, (![B_345, A_346, C_347]: (r2_hidden(B_345, k1_tops_1(A_346, C_347)) | ~m1_connsp_2(C_347, A_346, B_345) | ~m1_subset_1(C_347, k1_zfmisc_1(u1_struct_0(A_346))) | ~m1_subset_1(B_345, u1_struct_0(A_346)) | ~l1_pre_topc(A_346) | ~v2_pre_topc(A_346) | v2_struct_0(A_346))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.17/2.02  tff(c_2524, plain, (![B_345]: (r2_hidden(B_345, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_345) | ~m1_subset_1(B_345, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_2519])).
% 5.17/2.02  tff(c_2528, plain, (![B_345]: (r2_hidden(B_345, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_345) | ~m1_subset_1(B_345, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_2524])).
% 5.17/2.02  tff(c_2530, plain, (![B_348]: (r2_hidden(B_348, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_348) | ~m1_subset_1(B_348, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_32, c_2528])).
% 5.17/2.02  tff(c_1804, plain, (![A_258, B_259]: (v3_pre_topc(k1_tops_1(A_258, B_259), A_258) | ~m1_subset_1(B_259, k1_zfmisc_1(u1_struct_0(A_258))) | ~l1_pre_topc(A_258) | ~v2_pre_topc(A_258))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.17/2.02  tff(c_1809, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_1804])).
% 5.17/2.02  tff(c_1813, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_1809])).
% 5.17/2.02  tff(c_1786, plain, (![A_256, B_257]: (r1_tarski(k1_tops_1(A_256, B_257), B_257) | ~m1_subset_1(B_257, k1_zfmisc_1(u1_struct_0(A_256))) | ~l1_pre_topc(A_256))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.17/2.02  tff(c_1791, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_1786])).
% 5.17/2.02  tff(c_1795, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1791])).
% 5.17/2.02  tff(c_1742, plain, (![A_241, B_242]: (r2_hidden('#skF_1'(A_241, B_242), A_241) | r1_tarski(A_241, B_242))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.17/2.02  tff(c_1747, plain, (![A_241]: (r1_tarski(A_241, A_241))), inference(resolution, [status(thm)], [c_1742, c_4])).
% 5.17/2.02  tff(c_1732, plain, (![A_237, B_238]: (r1_tarski(A_237, B_238) | ~m1_subset_1(A_237, k1_zfmisc_1(B_238)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.17/2.02  tff(c_1740, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_1732])).
% 5.17/2.02  tff(c_1750, plain, (![A_244, C_245, B_246]: (r1_tarski(A_244, C_245) | ~r1_tarski(B_246, C_245) | ~r1_tarski(A_244, B_246))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.17/2.02  tff(c_1757, plain, (![A_247]: (r1_tarski(A_247, u1_struct_0('#skF_2')) | ~r1_tarski(A_247, '#skF_4'))), inference(resolution, [status(thm)], [c_1740, c_1750])).
% 5.17/2.02  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(B_7, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.17/2.02  tff(c_1760, plain, (![A_6, A_247]: (r1_tarski(A_6, u1_struct_0('#skF_2')) | ~r1_tarski(A_6, A_247) | ~r1_tarski(A_247, '#skF_4'))), inference(resolution, [status(thm)], [c_1757, c_8])).
% 5.17/2.02  tff(c_1797, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2')) | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_1795, c_1760])).
% 5.17/2.02  tff(c_1802, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1747, c_1797])).
% 5.17/2.02  tff(c_1729, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_40])).
% 5.17/2.02  tff(c_38, plain, (![D_48]: (~r2_hidden('#skF_3', D_48) | ~r1_tarski(D_48, '#skF_4') | ~v3_pre_topc(D_48, '#skF_2') | ~m1_subset_1(D_48, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r2_hidden('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.17/2.02  tff(c_2245, plain, (![D_315]: (~r2_hidden('#skF_3', D_315) | ~r1_tarski(D_315, '#skF_4') | ~v3_pre_topc(D_315, '#skF_2') | ~m1_subset_1(D_315, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_1729, c_38])).
% 5.17/2.02  tff(c_2366, plain, (![A_327]: (~r2_hidden('#skF_3', A_327) | ~r1_tarski(A_327, '#skF_4') | ~v3_pre_topc(A_327, '#skF_2') | ~r1_tarski(A_327, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_12, c_2245])).
% 5.17/2.02  tff(c_2382, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_1802, c_2366])).
% 5.17/2.02  tff(c_2401, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1813, c_1795, c_2382])).
% 5.17/2.02  tff(c_2533, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_2530, c_2401])).
% 5.17/2.02  tff(c_2543, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_1728, c_2533])).
% 5.17/2.02  tff(c_2544, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 5.17/2.02  tff(c_2548, plain, (![A_349, B_350]: (r1_tarski(A_349, B_350) | ~m1_subset_1(A_349, k1_zfmisc_1(B_350)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.17/2.02  tff(c_2552, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_2548])).
% 5.17/2.02  tff(c_2607, plain, (![A_368, B_369]: (r1_tarski(k1_tops_1(A_368, B_369), B_369) | ~m1_subset_1(B_369, k1_zfmisc_1(u1_struct_0(A_368))) | ~l1_pre_topc(A_368))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.17/2.02  tff(c_2612, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_2607])).
% 5.17/2.02  tff(c_2616, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2612])).
% 5.17/2.02  tff(c_2973, plain, (![B_422, A_423, C_424]: (r2_hidden(B_422, k1_tops_1(A_423, C_424)) | ~m1_connsp_2(C_424, A_423, B_422) | ~m1_subset_1(C_424, k1_zfmisc_1(u1_struct_0(A_423))) | ~m1_subset_1(B_422, u1_struct_0(A_423)) | ~l1_pre_topc(A_423) | ~v2_pre_topc(A_423) | v2_struct_0(A_423))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.17/2.02  tff(c_2978, plain, (![B_422]: (r2_hidden(B_422, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_422) | ~m1_subset_1(B_422, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_2973])).
% 5.17/2.02  tff(c_2982, plain, (![B_422]: (r2_hidden(B_422, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_422) | ~m1_subset_1(B_422, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_2978])).
% 5.17/2.02  tff(c_3030, plain, (![B_428]: (r2_hidden(B_428, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_428) | ~m1_subset_1(B_428, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_32, c_2982])).
% 5.17/2.02  tff(c_2700, plain, (![A_379, B_380]: (v3_pre_topc(k1_tops_1(A_379, B_380), A_379) | ~m1_subset_1(B_380, k1_zfmisc_1(u1_struct_0(A_379))) | ~l1_pre_topc(A_379) | ~v2_pre_topc(A_379))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.17/2.02  tff(c_2718, plain, (![A_381, A_382]: (v3_pre_topc(k1_tops_1(A_381, A_382), A_381) | ~l1_pre_topc(A_381) | ~v2_pre_topc(A_381) | ~r1_tarski(A_382, u1_struct_0(A_381)))), inference(resolution, [status(thm)], [c_12, c_2700])).
% 5.17/2.02  tff(c_2585, plain, (![A_362, C_363, B_364]: (r1_tarski(A_362, C_363) | ~r1_tarski(B_364, C_363) | ~r1_tarski(A_362, B_364))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.17/2.02  tff(c_2591, plain, (![A_362]: (r1_tarski(A_362, u1_struct_0('#skF_2')) | ~r1_tarski(A_362, '#skF_4'))), inference(resolution, [status(thm)], [c_2552, c_2585])).
% 5.17/2.02  tff(c_2545, plain, (~v3_pre_topc('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 5.17/2.02  tff(c_46, plain, (![D_48]: (~r2_hidden('#skF_3', D_48) | ~r1_tarski(D_48, '#skF_4') | ~v3_pre_topc(D_48, '#skF_2') | ~m1_subset_1(D_48, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v3_pre_topc('#skF_5', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.17/2.02  tff(c_2572, plain, (![D_361]: (~r2_hidden('#skF_3', D_361) | ~r1_tarski(D_361, '#skF_4') | ~v3_pre_topc(D_361, '#skF_2') | ~m1_subset_1(D_361, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_2545, c_46])).
% 5.17/2.02  tff(c_2672, plain, (![A_377]: (~r2_hidden('#skF_3', A_377) | ~r1_tarski(A_377, '#skF_4') | ~v3_pre_topc(A_377, '#skF_2') | ~r1_tarski(A_377, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_12, c_2572])).
% 5.17/2.02  tff(c_2694, plain, (![A_362]: (~r2_hidden('#skF_3', A_362) | ~v3_pre_topc(A_362, '#skF_2') | ~r1_tarski(A_362, '#skF_4'))), inference(resolution, [status(thm)], [c_2591, c_2672])).
% 5.17/2.02  tff(c_2722, plain, (![A_382]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', A_382)) | ~r1_tarski(k1_tops_1('#skF_2', A_382), '#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r1_tarski(A_382, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_2718, c_2694])).
% 5.17/2.02  tff(c_2725, plain, (![A_382]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', A_382)) | ~r1_tarski(k1_tops_1('#skF_2', A_382), '#skF_4') | ~r1_tarski(A_382, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_2722])).
% 5.17/2.02  tff(c_3034, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~r1_tarski('#skF_4', u1_struct_0('#skF_2')) | ~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_3030, c_2725])).
% 5.17/2.02  tff(c_3047, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_2544, c_2552, c_2616, c_3034])).
% 5.17/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.17/2.02  
% 5.17/2.02  Inference rules
% 5.17/2.02  ----------------------
% 5.17/2.02  #Ref     : 0
% 5.17/2.02  #Sup     : 665
% 5.17/2.02  #Fact    : 0
% 5.17/2.02  #Define  : 0
% 5.17/2.02  #Split   : 17
% 5.17/2.02  #Chain   : 0
% 5.17/2.02  #Close   : 0
% 5.17/2.02  
% 5.17/2.02  Ordering : KBO
% 5.17/2.02  
% 5.17/2.02  Simplification rules
% 5.17/2.02  ----------------------
% 5.17/2.02  #Subsume      : 185
% 5.17/2.02  #Demod        : 325
% 5.17/2.02  #Tautology    : 158
% 5.17/2.02  #SimpNegUnit  : 15
% 5.17/2.02  #BackRed      : 0
% 5.17/2.02  
% 5.17/2.02  #Partial instantiations: 0
% 5.17/2.02  #Strategies tried      : 1
% 5.17/2.02  
% 5.17/2.02  Timing (in seconds)
% 5.17/2.02  ----------------------
% 5.17/2.02  Preprocessing        : 0.37
% 5.17/2.02  Parsing              : 0.18
% 5.17/2.02  CNF conversion       : 0.04
% 5.17/2.02  Main loop            : 0.82
% 5.17/2.02  Inferencing          : 0.29
% 5.17/2.02  Reduction            : 0.24
% 5.17/2.02  Demodulation         : 0.17
% 5.17/2.02  BG Simplification    : 0.03
% 5.17/2.02  Subsumption          : 0.20
% 5.17/2.02  Abstraction          : 0.03
% 5.17/2.02  MUC search           : 0.00
% 5.17/2.02  Cooper               : 0.00
% 5.17/2.02  Total                : 1.25
% 5.17/2.02  Index Insertion      : 0.00
% 5.17/2.02  Index Deletion       : 0.00
% 5.17/2.02  Index Matching       : 0.00
% 5.17/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
