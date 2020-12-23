%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:11 EST 2020

% Result     : Theorem 6.65s
% Output     : CNFRefutation 7.15s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 422 expanded)
%              Number of leaves         :   30 ( 160 expanded)
%              Depth                    :   14
%              Number of atoms          :  559 (1946 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_158,negated_conjecture,(
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

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_73,axiom,(
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

tff(f_133,axiom,(
    ! [A] :
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

tff(f_104,axiom,(
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

tff(f_87,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(c_36,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_54,plain,
    ( m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | r1_tarski('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_65,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_67,plain,(
    ! [A_71,B_72] :
      ( r1_tarski(A_71,B_72)
      | ~ m1_subset_1(A_71,k1_zfmisc_1(B_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_75,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_67])).

tff(c_1405,plain,(
    ! [A_197,C_198,B_199] :
      ( r1_tarski(A_197,C_198)
      | ~ r1_tarski(B_199,C_198)
      | ~ r1_tarski(A_197,B_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1419,plain,(
    ! [A_201] :
      ( r1_tarski(A_201,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_201,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_75,c_1405])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_58,plain,
    ( m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | v3_pre_topc('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_63,plain,(
    v3_pre_topc('#skF_6','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_50,plain,
    ( m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_64,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_62,plain,
    ( m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_95,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_44,plain,(
    ! [D_68] :
      ( ~ r2_hidden('#skF_4',D_68)
      | ~ r1_tarski(D_68,'#skF_5')
      | ~ v3_pre_topc(D_68,'#skF_3')
      | ~ m1_subset_1(D_68,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_connsp_2('#skF_5','#skF_3','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_275,plain,(
    ~ m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_40,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_77,plain,(
    ! [A_75,B_76] :
      ( ~ r2_hidden('#skF_1'(A_75,B_76),B_76)
      | r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_82,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_77])).

tff(c_636,plain,(
    ! [B_155,A_156,C_157] :
      ( r1_tarski(B_155,k1_tops_1(A_156,C_157))
      | ~ r1_tarski(B_155,C_157)
      | ~ v3_pre_topc(B_155,A_156)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_643,plain,(
    ! [B_155] :
      ( r1_tarski(B_155,k1_tops_1('#skF_3','#skF_5'))
      | ~ r1_tarski(B_155,'#skF_5')
      | ~ v3_pre_topc(B_155,'#skF_3')
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_636])).

tff(c_651,plain,(
    ! [B_158] :
      ( r1_tarski(B_158,k1_tops_1('#skF_3','#skF_5'))
      | ~ r1_tarski(B_158,'#skF_5')
      | ~ v3_pre_topc(B_158,'#skF_3')
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_643])).

tff(c_654,plain,
    ( r1_tarski('#skF_6',k1_tops_1('#skF_3','#skF_5'))
    | ~ r1_tarski('#skF_6','#skF_5')
    | ~ v3_pre_topc('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_95,c_651])).

tff(c_664,plain,(
    r1_tarski('#skF_6',k1_tops_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_65,c_654])).

tff(c_84,plain,(
    ! [C_78,B_79,A_80] :
      ( r2_hidden(C_78,B_79)
      | ~ r2_hidden(C_78,A_80)
      | ~ r1_tarski(A_80,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_91,plain,(
    ! [B_81] :
      ( r2_hidden('#skF_4',B_81)
      | ~ r1_tarski('#skF_6',B_81) ) ),
    inference(resolution,[status(thm)],[c_64,c_84])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_94,plain,(
    ! [B_2,B_81] :
      ( r2_hidden('#skF_4',B_2)
      | ~ r1_tarski(B_81,B_2)
      | ~ r1_tarski('#skF_6',B_81) ) ),
    inference(resolution,[status(thm)],[c_91,c_2])).

tff(c_688,plain,
    ( r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5'))
    | ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_664,c_94])).

tff(c_706,plain,(
    r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_688])).

tff(c_1279,plain,(
    ! [C_188,A_189,B_190] :
      ( m1_connsp_2(C_188,A_189,B_190)
      | ~ r2_hidden(B_190,k1_tops_1(A_189,C_188))
      | ~ m1_subset_1(C_188,k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ m1_subset_1(B_190,u1_struct_0(A_189))
      | ~ l1_pre_topc(A_189)
      | ~ v2_pre_topc(A_189)
      | v2_struct_0(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1294,plain,
    ( m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_706,c_1279])).

tff(c_1342,plain,
    ( m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_1294])).

tff(c_1344,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_275,c_1342])).

tff(c_1384,plain,(
    ! [D_196] :
      ( ~ r2_hidden('#skF_4',D_196)
      | ~ r1_tarski(D_196,'#skF_5')
      | ~ v3_pre_topc(D_196,'#skF_3')
      | ~ m1_subset_1(D_196,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1387,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | ~ r1_tarski('#skF_6','#skF_5')
    | ~ v3_pre_topc('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_95,c_1384])).

tff(c_1398,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_65,c_64,c_1387])).

tff(c_1400,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_1404,plain,(
    ~ r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_1400])).

tff(c_1422,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_1419,c_1404])).

tff(c_1428,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_1422])).

tff(c_1429,plain,(
    m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_2470,plain,(
    ! [A_329,B_330,C_331] :
      ( r1_tarski('#skF_2'(A_329,B_330,C_331),C_331)
      | ~ m1_connsp_2(C_331,A_329,B_330)
      | ~ m1_subset_1(C_331,k1_zfmisc_1(u1_struct_0(A_329)))
      | ~ m1_subset_1(B_330,u1_struct_0(A_329))
      | ~ l1_pre_topc(A_329)
      | ~ v2_pre_topc(A_329)
      | v2_struct_0(A_329) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2477,plain,(
    ! [B_330] :
      ( r1_tarski('#skF_2'('#skF_3',B_330,'#skF_5'),'#skF_5')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_330)
      | ~ m1_subset_1(B_330,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_2470])).

tff(c_2485,plain,(
    ! [B_330] :
      ( r1_tarski('#skF_2'('#skF_3',B_330,'#skF_5'),'#skF_5')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_330)
      | ~ m1_subset_1(B_330,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_2477])).

tff(c_2486,plain,(
    ! [B_330] :
      ( r1_tarski('#skF_2'('#skF_3',B_330,'#skF_5'),'#skF_5')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_330)
      | ~ m1_subset_1(B_330,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_2485])).

tff(c_30,plain,(
    ! [A_36,B_44,C_48] :
      ( m1_subset_1('#skF_2'(A_36,B_44,C_48),k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ m1_connsp_2(C_48,A_36,B_44)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ m1_subset_1(B_44,u1_struct_0(A_36))
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2749,plain,(
    ! [A_343,B_344,C_345] :
      ( m1_connsp_2('#skF_2'(A_343,B_344,C_345),A_343,B_344)
      | ~ m1_connsp_2(C_345,A_343,B_344)
      | ~ m1_subset_1(C_345,k1_zfmisc_1(u1_struct_0(A_343)))
      | ~ m1_subset_1(B_344,u1_struct_0(A_343))
      | ~ l1_pre_topc(A_343)
      | ~ v2_pre_topc(A_343)
      | v2_struct_0(A_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2756,plain,(
    ! [B_344] :
      ( m1_connsp_2('#skF_2'('#skF_3',B_344,'#skF_5'),'#skF_3',B_344)
      | ~ m1_connsp_2('#skF_5','#skF_3',B_344)
      | ~ m1_subset_1(B_344,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_2749])).

tff(c_2764,plain,(
    ! [B_344] :
      ( m1_connsp_2('#skF_2'('#skF_3',B_344,'#skF_5'),'#skF_3',B_344)
      | ~ m1_connsp_2('#skF_5','#skF_3',B_344)
      | ~ m1_subset_1(B_344,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_2756])).

tff(c_2766,plain,(
    ! [B_346] :
      ( m1_connsp_2('#skF_2'('#skF_3',B_346,'#skF_5'),'#skF_3',B_346)
      | ~ m1_connsp_2('#skF_5','#skF_3',B_346)
      | ~ m1_subset_1(B_346,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_2764])).

tff(c_22,plain,(
    ! [C_35,B_33,A_29] :
      ( r2_hidden(C_35,B_33)
      | ~ m1_connsp_2(B_33,A_29,C_35)
      | ~ m1_subset_1(C_35,u1_struct_0(A_29))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2768,plain,(
    ! [B_346] :
      ( r2_hidden(B_346,'#skF_2'('#skF_3',B_346,'#skF_5'))
      | ~ m1_subset_1('#skF_2'('#skF_3',B_346,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_346)
      | ~ m1_subset_1(B_346,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2766,c_22])).

tff(c_2773,plain,(
    ! [B_346] :
      ( r2_hidden(B_346,'#skF_2'('#skF_3',B_346,'#skF_5'))
      | ~ m1_subset_1('#skF_2'('#skF_3',B_346,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_346)
      | ~ m1_subset_1(B_346,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_2768])).

tff(c_2940,plain,(
    ! [B_360] :
      ( r2_hidden(B_360,'#skF_2'('#skF_3',B_360,'#skF_5'))
      | ~ m1_subset_1('#skF_2'('#skF_3',B_360,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_360)
      | ~ m1_subset_1(B_360,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_2773])).

tff(c_2943,plain,(
    ! [B_44] :
      ( r2_hidden(B_44,'#skF_2'('#skF_3',B_44,'#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_44)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_2940])).

tff(c_2951,plain,(
    ! [B_44] :
      ( r2_hidden(B_44,'#skF_2'('#skF_3',B_44,'#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_44)
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_34,c_2943])).

tff(c_2955,plain,(
    ! [B_361] :
      ( r2_hidden(B_361,'#skF_2'('#skF_3',B_361,'#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_361)
      | ~ m1_subset_1(B_361,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_2951])).

tff(c_2342,plain,(
    ! [A_311,B_312,C_313] :
      ( v3_pre_topc('#skF_2'(A_311,B_312,C_313),A_311)
      | ~ m1_connsp_2(C_313,A_311,B_312)
      | ~ m1_subset_1(C_313,k1_zfmisc_1(u1_struct_0(A_311)))
      | ~ m1_subset_1(B_312,u1_struct_0(A_311))
      | ~ l1_pre_topc(A_311)
      | ~ v2_pre_topc(A_311)
      | v2_struct_0(A_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2349,plain,(
    ! [B_312] :
      ( v3_pre_topc('#skF_2'('#skF_3',B_312,'#skF_5'),'#skF_3')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_312)
      | ~ m1_subset_1(B_312,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_2342])).

tff(c_2357,plain,(
    ! [B_312] :
      ( v3_pre_topc('#skF_2'('#skF_3',B_312,'#skF_5'),'#skF_3')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_312)
      | ~ m1_subset_1(B_312,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_2349])).

tff(c_2359,plain,(
    ! [B_314] :
      ( v3_pre_topc('#skF_2'('#skF_3',B_314,'#skF_5'),'#skF_3')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_314)
      | ~ m1_subset_1(B_314,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_2357])).

tff(c_1432,plain,(
    ! [A_202,B_203] :
      ( r1_tarski(A_202,B_203)
      | ~ m1_subset_1(A_202,k1_zfmisc_1(B_203)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1440,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_1432])).

tff(c_1455,plain,(
    ! [A_211,C_212,B_213] :
      ( r1_tarski(A_211,C_212)
      | ~ r1_tarski(B_213,C_212)
      | ~ r1_tarski(A_211,B_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1464,plain,(
    ! [A_211] :
      ( r1_tarski(A_211,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_211,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1440,c_1455])).

tff(c_1430,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,(
    ! [D_68] :
      ( ~ r2_hidden('#skF_4',D_68)
      | ~ r1_tarski(D_68,'#skF_5')
      | ~ v3_pre_topc(D_68,'#skF_3')
      | ~ m1_subset_1(D_68,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | r1_tarski('#skF_6','#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_1507,plain,(
    ! [D_222] :
      ( ~ r2_hidden('#skF_4',D_222)
      | ~ r1_tarski(D_222,'#skF_5')
      | ~ v3_pre_topc(D_222,'#skF_3')
      | ~ m1_subset_1(D_222,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1430,c_52])).

tff(c_1595,plain,(
    ! [A_231] :
      ( ~ r2_hidden('#skF_4',A_231)
      | ~ r1_tarski(A_231,'#skF_5')
      | ~ v3_pre_topc(A_231,'#skF_3')
      | ~ r1_tarski(A_231,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_12,c_1507])).

tff(c_1613,plain,(
    ! [A_211] :
      ( ~ r2_hidden('#skF_4',A_211)
      | ~ v3_pre_topc(A_211,'#skF_3')
      | ~ r1_tarski(A_211,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1464,c_1595])).

tff(c_2371,plain,(
    ! [B_314] :
      ( ~ r2_hidden('#skF_4','#skF_2'('#skF_3',B_314,'#skF_5'))
      | ~ r1_tarski('#skF_2'('#skF_3',B_314,'#skF_5'),'#skF_5')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_314)
      | ~ m1_subset_1(B_314,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2359,c_1613])).

tff(c_2959,plain,
    ( ~ r1_tarski('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5')
    | ~ m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2955,c_2371])).

tff(c_2964,plain,(
    ~ r1_tarski('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1429,c_2959])).

tff(c_2968,plain,
    ( ~ m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2486,c_2964])).

tff(c_2972,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1429,c_2968])).

tff(c_2973,plain,(
    m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_3658,plain,(
    ! [A_478,B_479,C_480] :
      ( r1_tarski('#skF_2'(A_478,B_479,C_480),C_480)
      | ~ m1_connsp_2(C_480,A_478,B_479)
      | ~ m1_subset_1(C_480,k1_zfmisc_1(u1_struct_0(A_478)))
      | ~ m1_subset_1(B_479,u1_struct_0(A_478))
      | ~ l1_pre_topc(A_478)
      | ~ v2_pre_topc(A_478)
      | v2_struct_0(A_478) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_3663,plain,(
    ! [B_479] :
      ( r1_tarski('#skF_2'('#skF_3',B_479,'#skF_5'),'#skF_5')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_479)
      | ~ m1_subset_1(B_479,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_3658])).

tff(c_3667,plain,(
    ! [B_479] :
      ( r1_tarski('#skF_2'('#skF_3',B_479,'#skF_5'),'#skF_5')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_479)
      | ~ m1_subset_1(B_479,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_3663])).

tff(c_3668,plain,(
    ! [B_479] :
      ( r1_tarski('#skF_2'('#skF_3',B_479,'#skF_5'),'#skF_5')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_479)
      | ~ m1_subset_1(B_479,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_3667])).

tff(c_3835,plain,(
    ! [A_498,B_499,C_500] :
      ( m1_connsp_2('#skF_2'(A_498,B_499,C_500),A_498,B_499)
      | ~ m1_connsp_2(C_500,A_498,B_499)
      | ~ m1_subset_1(C_500,k1_zfmisc_1(u1_struct_0(A_498)))
      | ~ m1_subset_1(B_499,u1_struct_0(A_498))
      | ~ l1_pre_topc(A_498)
      | ~ v2_pre_topc(A_498)
      | v2_struct_0(A_498) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_3840,plain,(
    ! [B_499] :
      ( m1_connsp_2('#skF_2'('#skF_3',B_499,'#skF_5'),'#skF_3',B_499)
      | ~ m1_connsp_2('#skF_5','#skF_3',B_499)
      | ~ m1_subset_1(B_499,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_3835])).

tff(c_3844,plain,(
    ! [B_499] :
      ( m1_connsp_2('#skF_2'('#skF_3',B_499,'#skF_5'),'#skF_3',B_499)
      | ~ m1_connsp_2('#skF_5','#skF_3',B_499)
      | ~ m1_subset_1(B_499,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_3840])).

tff(c_3846,plain,(
    ! [B_501] :
      ( m1_connsp_2('#skF_2'('#skF_3',B_501,'#skF_5'),'#skF_3',B_501)
      | ~ m1_connsp_2('#skF_5','#skF_3',B_501)
      | ~ m1_subset_1(B_501,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_3844])).

tff(c_20,plain,(
    ! [C_28,A_25,B_26] :
      ( m1_subset_1(C_28,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ m1_connsp_2(C_28,A_25,B_26)
      | ~ m1_subset_1(B_26,u1_struct_0(A_25))
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_3850,plain,(
    ! [B_501] :
      ( m1_subset_1('#skF_2'('#skF_3',B_501,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_501)
      | ~ m1_subset_1(B_501,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_3846,c_20])).

tff(c_3857,plain,(
    ! [B_501] :
      ( m1_subset_1('#skF_2'('#skF_3',B_501,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_501)
      | ~ m1_subset_1(B_501,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_3850])).

tff(c_3858,plain,(
    ! [B_501] :
      ( m1_subset_1('#skF_2'('#skF_3',B_501,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_501)
      | ~ m1_subset_1(B_501,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_3857])).

tff(c_3848,plain,(
    ! [B_501] :
      ( r2_hidden(B_501,'#skF_2'('#skF_3',B_501,'#skF_5'))
      | ~ m1_subset_1('#skF_2'('#skF_3',B_501,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_501)
      | ~ m1_subset_1(B_501,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_3846,c_22])).

tff(c_3853,plain,(
    ! [B_501] :
      ( r2_hidden(B_501,'#skF_2'('#skF_3',B_501,'#skF_5'))
      | ~ m1_subset_1('#skF_2'('#skF_3',B_501,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_501)
      | ~ m1_subset_1(B_501,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_3848])).

tff(c_3909,plain,(
    ! [B_503] :
      ( r2_hidden(B_503,'#skF_2'('#skF_3',B_503,'#skF_5'))
      | ~ m1_subset_1('#skF_2'('#skF_3',B_503,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_503)
      | ~ m1_subset_1(B_503,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_3853])).

tff(c_3924,plain,(
    ! [B_505] :
      ( r2_hidden(B_505,'#skF_2'('#skF_3',B_505,'#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_505)
      | ~ m1_subset_1(B_505,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_3858,c_3909])).

tff(c_3549,plain,(
    ! [A_462,B_463,C_464] :
      ( v3_pre_topc('#skF_2'(A_462,B_463,C_464),A_462)
      | ~ m1_connsp_2(C_464,A_462,B_463)
      | ~ m1_subset_1(C_464,k1_zfmisc_1(u1_struct_0(A_462)))
      | ~ m1_subset_1(B_463,u1_struct_0(A_462))
      | ~ l1_pre_topc(A_462)
      | ~ v2_pre_topc(A_462)
      | v2_struct_0(A_462) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_3554,plain,(
    ! [B_463] :
      ( v3_pre_topc('#skF_2'('#skF_3',B_463,'#skF_5'),'#skF_3')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_463)
      | ~ m1_subset_1(B_463,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_3549])).

tff(c_3558,plain,(
    ! [B_463] :
      ( v3_pre_topc('#skF_2'('#skF_3',B_463,'#skF_5'),'#skF_3')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_463)
      | ~ m1_subset_1(B_463,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_3554])).

tff(c_3560,plain,(
    ! [B_465] :
      ( v3_pre_topc('#skF_2'('#skF_3',B_465,'#skF_5'),'#skF_3')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_465)
      | ~ m1_subset_1(B_465,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_3558])).

tff(c_2977,plain,(
    ! [A_364,B_365] :
      ( r1_tarski(A_364,B_365)
      | ~ m1_subset_1(A_364,k1_zfmisc_1(B_365)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2985,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_2977])).

tff(c_2999,plain,(
    ! [A_374,C_375,B_376] :
      ( r1_tarski(A_374,C_375)
      | ~ r1_tarski(B_376,C_375)
      | ~ r1_tarski(A_374,B_376) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3005,plain,(
    ! [A_374] :
      ( r1_tarski(A_374,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_374,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2985,c_2999])).

tff(c_2974,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,(
    ! [D_68] :
      ( ~ r2_hidden('#skF_4',D_68)
      | ~ r1_tarski(D_68,'#skF_5')
      | ~ v3_pre_topc(D_68,'#skF_3')
      | ~ m1_subset_1(D_68,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | r2_hidden('#skF_4','#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_3042,plain,(
    ! [D_387] :
      ( ~ r2_hidden('#skF_4',D_387)
      | ~ r1_tarski(D_387,'#skF_5')
      | ~ v3_pre_topc(D_387,'#skF_3')
      | ~ m1_subset_1(D_387,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2974,c_48])).

tff(c_3064,plain,(
    ! [A_390] :
      ( ~ r2_hidden('#skF_4',A_390)
      | ~ r1_tarski(A_390,'#skF_5')
      | ~ v3_pre_topc(A_390,'#skF_3')
      | ~ r1_tarski(A_390,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_12,c_3042])).

tff(c_3075,plain,(
    ! [A_374] :
      ( ~ r2_hidden('#skF_4',A_374)
      | ~ v3_pre_topc(A_374,'#skF_3')
      | ~ r1_tarski(A_374,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3005,c_3064])).

tff(c_3568,plain,(
    ! [B_465] :
      ( ~ r2_hidden('#skF_4','#skF_2'('#skF_3',B_465,'#skF_5'))
      | ~ r1_tarski('#skF_2'('#skF_3',B_465,'#skF_5'),'#skF_5')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_465)
      | ~ m1_subset_1(B_465,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_3560,c_3075])).

tff(c_3928,plain,
    ( ~ r1_tarski('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5')
    | ~ m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3924,c_3568])).

tff(c_3933,plain,(
    ~ r1_tarski('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2973,c_3928])).

tff(c_3937,plain,
    ( ~ m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3668,c_3933])).

tff(c_3941,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2973,c_3937])).

tff(c_3942,plain,(
    m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_4505,plain,(
    ! [A_606,B_607,C_608] :
      ( r1_tarski('#skF_2'(A_606,B_607,C_608),C_608)
      | ~ m1_connsp_2(C_608,A_606,B_607)
      | ~ m1_subset_1(C_608,k1_zfmisc_1(u1_struct_0(A_606)))
      | ~ m1_subset_1(B_607,u1_struct_0(A_606))
      | ~ l1_pre_topc(A_606)
      | ~ v2_pre_topc(A_606)
      | v2_struct_0(A_606) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_4510,plain,(
    ! [B_607] :
      ( r1_tarski('#skF_2'('#skF_3',B_607,'#skF_5'),'#skF_5')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_607)
      | ~ m1_subset_1(B_607,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_4505])).

tff(c_4514,plain,(
    ! [B_607] :
      ( r1_tarski('#skF_2'('#skF_3',B_607,'#skF_5'),'#skF_5')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_607)
      | ~ m1_subset_1(B_607,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_4510])).

tff(c_4515,plain,(
    ! [B_607] :
      ( r1_tarski('#skF_2'('#skF_3',B_607,'#skF_5'),'#skF_5')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_607)
      | ~ m1_subset_1(B_607,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_4514])).

tff(c_4789,plain,(
    ! [A_642,B_643,C_644] :
      ( m1_connsp_2('#skF_2'(A_642,B_643,C_644),A_642,B_643)
      | ~ m1_connsp_2(C_644,A_642,B_643)
      | ~ m1_subset_1(C_644,k1_zfmisc_1(u1_struct_0(A_642)))
      | ~ m1_subset_1(B_643,u1_struct_0(A_642))
      | ~ l1_pre_topc(A_642)
      | ~ v2_pre_topc(A_642)
      | v2_struct_0(A_642) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_4794,plain,(
    ! [B_643] :
      ( m1_connsp_2('#skF_2'('#skF_3',B_643,'#skF_5'),'#skF_3',B_643)
      | ~ m1_connsp_2('#skF_5','#skF_3',B_643)
      | ~ m1_subset_1(B_643,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_4789])).

tff(c_4798,plain,(
    ! [B_643] :
      ( m1_connsp_2('#skF_2'('#skF_3',B_643,'#skF_5'),'#skF_3',B_643)
      | ~ m1_connsp_2('#skF_5','#skF_3',B_643)
      | ~ m1_subset_1(B_643,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_4794])).

tff(c_4800,plain,(
    ! [B_645] :
      ( m1_connsp_2('#skF_2'('#skF_3',B_645,'#skF_5'),'#skF_3',B_645)
      | ~ m1_connsp_2('#skF_5','#skF_3',B_645)
      | ~ m1_subset_1(B_645,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_4798])).

tff(c_4804,plain,(
    ! [B_645] :
      ( m1_subset_1('#skF_2'('#skF_3',B_645,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_645)
      | ~ m1_subset_1(B_645,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_4800,c_20])).

tff(c_4811,plain,(
    ! [B_645] :
      ( m1_subset_1('#skF_2'('#skF_3',B_645,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_645)
      | ~ m1_subset_1(B_645,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_4804])).

tff(c_4812,plain,(
    ! [B_645] :
      ( m1_subset_1('#skF_2'('#skF_3',B_645,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_645)
      | ~ m1_subset_1(B_645,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_4811])).

tff(c_4802,plain,(
    ! [B_645] :
      ( r2_hidden(B_645,'#skF_2'('#skF_3',B_645,'#skF_5'))
      | ~ m1_subset_1('#skF_2'('#skF_3',B_645,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_645)
      | ~ m1_subset_1(B_645,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_4800,c_22])).

tff(c_4807,plain,(
    ! [B_645] :
      ( r2_hidden(B_645,'#skF_2'('#skF_3',B_645,'#skF_5'))
      | ~ m1_subset_1('#skF_2'('#skF_3',B_645,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_645)
      | ~ m1_subset_1(B_645,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_4802])).

tff(c_4878,plain,(
    ! [B_649] :
      ( r2_hidden(B_649,'#skF_2'('#skF_3',B_649,'#skF_5'))
      | ~ m1_subset_1('#skF_2'('#skF_3',B_649,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_649)
      | ~ m1_subset_1(B_649,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_4807])).

tff(c_4886,plain,(
    ! [B_650] :
      ( r2_hidden(B_650,'#skF_2'('#skF_3',B_650,'#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_650)
      | ~ m1_subset_1(B_650,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_4812,c_4878])).

tff(c_4671,plain,(
    ! [A_624,B_625,C_626] :
      ( v3_pre_topc('#skF_2'(A_624,B_625,C_626),A_624)
      | ~ m1_connsp_2(C_626,A_624,B_625)
      | ~ m1_subset_1(C_626,k1_zfmisc_1(u1_struct_0(A_624)))
      | ~ m1_subset_1(B_625,u1_struct_0(A_624))
      | ~ l1_pre_topc(A_624)
      | ~ v2_pre_topc(A_624)
      | v2_struct_0(A_624) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_4676,plain,(
    ! [B_625] :
      ( v3_pre_topc('#skF_2'('#skF_3',B_625,'#skF_5'),'#skF_3')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_625)
      | ~ m1_subset_1(B_625,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_4671])).

tff(c_4680,plain,(
    ! [B_625] :
      ( v3_pre_topc('#skF_2'('#skF_3',B_625,'#skF_5'),'#skF_3')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_625)
      | ~ m1_subset_1(B_625,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_4676])).

tff(c_4682,plain,(
    ! [B_627] :
      ( v3_pre_topc('#skF_2'('#skF_3',B_627,'#skF_5'),'#skF_3')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_627)
      | ~ m1_subset_1(B_627,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_4680])).

tff(c_3947,plain,(
    ! [A_508,B_509] :
      ( r1_tarski(A_508,B_509)
      | ~ m1_subset_1(A_508,k1_zfmisc_1(B_509)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_3955,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_3947])).

tff(c_3969,plain,(
    ! [A_518,C_519,B_520] :
      ( r1_tarski(A_518,C_519)
      | ~ r1_tarski(B_520,C_519)
      | ~ r1_tarski(A_518,B_520) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3975,plain,(
    ! [A_518] :
      ( r1_tarski(A_518,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_518,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3955,c_3969])).

tff(c_3943,plain,(
    ~ v3_pre_topc('#skF_6','#skF_3') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_56,plain,(
    ! [D_68] :
      ( ~ r2_hidden('#skF_4',D_68)
      | ~ r1_tarski(D_68,'#skF_5')
      | ~ v3_pre_topc(D_68,'#skF_3')
      | ~ m1_subset_1(D_68,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v3_pre_topc('#skF_6','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_3977,plain,(
    ! [D_521] :
      ( ~ r2_hidden('#skF_4',D_521)
      | ~ r1_tarski(D_521,'#skF_5')
      | ~ v3_pre_topc(D_521,'#skF_3')
      | ~ m1_subset_1(D_521,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3943,c_56])).

tff(c_4014,plain,(
    ! [A_528] :
      ( ~ r2_hidden('#skF_4',A_528)
      | ~ r1_tarski(A_528,'#skF_5')
      | ~ v3_pre_topc(A_528,'#skF_3')
      | ~ r1_tarski(A_528,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_12,c_3977])).

tff(c_4025,plain,(
    ! [A_518] :
      ( ~ r2_hidden('#skF_4',A_518)
      | ~ v3_pre_topc(A_518,'#skF_3')
      | ~ r1_tarski(A_518,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3975,c_4014])).

tff(c_4690,plain,(
    ! [B_627] :
      ( ~ r2_hidden('#skF_4','#skF_2'('#skF_3',B_627,'#skF_5'))
      | ~ r1_tarski('#skF_2'('#skF_3',B_627,'#skF_5'),'#skF_5')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_627)
      | ~ m1_subset_1(B_627,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_4682,c_4025])).

tff(c_4890,plain,
    ( ~ r1_tarski('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5')
    | ~ m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4886,c_4690])).

tff(c_4895,plain,(
    ~ r1_tarski('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3942,c_4890])).

tff(c_4899,plain,
    ( ~ m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4515,c_4895])).

tff(c_4903,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3942,c_4899])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:29:25 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.65/2.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.65/2.36  
% 6.65/2.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.65/2.37  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 6.65/2.37  
% 6.65/2.37  %Foreground sorts:
% 6.65/2.37  
% 6.65/2.37  
% 6.65/2.37  %Background operators:
% 6.65/2.37  
% 6.65/2.37  
% 6.65/2.37  %Foreground operators:
% 6.65/2.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.65/2.37  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 6.65/2.37  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.65/2.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.65/2.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.65/2.37  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.65/2.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.65/2.37  tff('#skF_5', type, '#skF_5': $i).
% 6.65/2.37  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.65/2.37  tff('#skF_6', type, '#skF_6': $i).
% 6.65/2.37  tff('#skF_3', type, '#skF_3': $i).
% 6.65/2.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.65/2.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.65/2.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.65/2.37  tff('#skF_4', type, '#skF_4': $i).
% 6.65/2.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.65/2.37  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.65/2.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.65/2.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.65/2.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.65/2.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.65/2.37  
% 7.15/2.40  tff(f_158, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_connsp_2)).
% 7.15/2.40  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.15/2.40  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 7.15/2.40  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.15/2.40  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 7.15/2.40  tff(f_73, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 7.15/2.40  tff(f_133, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(C, A, B) & (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~((m1_connsp_2(D, A, B) & v3_pre_topc(D, A)) & r1_tarski(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_connsp_2)).
% 7.15/2.40  tff(f_104, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_connsp_2)).
% 7.15/2.40  tff(f_87, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 7.15/2.40  tff(c_36, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 7.15/2.40  tff(c_54, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | r1_tarski('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_158])).
% 7.15/2.40  tff(c_65, plain, (r1_tarski('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_54])).
% 7.15/2.40  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 7.15/2.40  tff(c_67, plain, (![A_71, B_72]: (r1_tarski(A_71, B_72) | ~m1_subset_1(A_71, k1_zfmisc_1(B_72)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.15/2.40  tff(c_75, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_67])).
% 7.15/2.40  tff(c_1405, plain, (![A_197, C_198, B_199]: (r1_tarski(A_197, C_198) | ~r1_tarski(B_199, C_198) | ~r1_tarski(A_197, B_199))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.15/2.40  tff(c_1419, plain, (![A_201]: (r1_tarski(A_201, u1_struct_0('#skF_3')) | ~r1_tarski(A_201, '#skF_5'))), inference(resolution, [status(thm)], [c_75, c_1405])).
% 7.15/2.40  tff(c_12, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.15/2.40  tff(c_58, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | v3_pre_topc('#skF_6', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 7.15/2.40  tff(c_63, plain, (v3_pre_topc('#skF_6', '#skF_3')), inference(splitLeft, [status(thm)], [c_58])).
% 7.15/2.40  tff(c_50, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_158])).
% 7.15/2.40  tff(c_64, plain, (r2_hidden('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_50])).
% 7.15/2.40  tff(c_62, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 7.15/2.40  tff(c_95, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_62])).
% 7.15/2.40  tff(c_42, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 7.15/2.40  tff(c_44, plain, (![D_68]: (~r2_hidden('#skF_4', D_68) | ~r1_tarski(D_68, '#skF_5') | ~v3_pre_topc(D_68, '#skF_3') | ~m1_subset_1(D_68, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_connsp_2('#skF_5', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 7.15/2.40  tff(c_275, plain, (~m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_44])).
% 7.15/2.40  tff(c_40, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 7.15/2.40  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 7.15/2.40  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.15/2.40  tff(c_77, plain, (![A_75, B_76]: (~r2_hidden('#skF_1'(A_75, B_76), B_76) | r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.15/2.40  tff(c_82, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_77])).
% 7.15/2.40  tff(c_636, plain, (![B_155, A_156, C_157]: (r1_tarski(B_155, k1_tops_1(A_156, C_157)) | ~r1_tarski(B_155, C_157) | ~v3_pre_topc(B_155, A_156) | ~m1_subset_1(C_157, k1_zfmisc_1(u1_struct_0(A_156))) | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0(A_156))) | ~l1_pre_topc(A_156))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.15/2.40  tff(c_643, plain, (![B_155]: (r1_tarski(B_155, k1_tops_1('#skF_3', '#skF_5')) | ~r1_tarski(B_155, '#skF_5') | ~v3_pre_topc(B_155, '#skF_3') | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_636])).
% 7.15/2.40  tff(c_651, plain, (![B_158]: (r1_tarski(B_158, k1_tops_1('#skF_3', '#skF_5')) | ~r1_tarski(B_158, '#skF_5') | ~v3_pre_topc(B_158, '#skF_3') | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_643])).
% 7.15/2.40  tff(c_654, plain, (r1_tarski('#skF_6', k1_tops_1('#skF_3', '#skF_5')) | ~r1_tarski('#skF_6', '#skF_5') | ~v3_pre_topc('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_95, c_651])).
% 7.15/2.40  tff(c_664, plain, (r1_tarski('#skF_6', k1_tops_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_65, c_654])).
% 7.15/2.40  tff(c_84, plain, (![C_78, B_79, A_80]: (r2_hidden(C_78, B_79) | ~r2_hidden(C_78, A_80) | ~r1_tarski(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.15/2.40  tff(c_91, plain, (![B_81]: (r2_hidden('#skF_4', B_81) | ~r1_tarski('#skF_6', B_81))), inference(resolution, [status(thm)], [c_64, c_84])).
% 7.15/2.40  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.15/2.40  tff(c_94, plain, (![B_2, B_81]: (r2_hidden('#skF_4', B_2) | ~r1_tarski(B_81, B_2) | ~r1_tarski('#skF_6', B_81))), inference(resolution, [status(thm)], [c_91, c_2])).
% 7.15/2.40  tff(c_688, plain, (r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5')) | ~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_664, c_94])).
% 7.15/2.40  tff(c_706, plain, (r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_688])).
% 7.15/2.40  tff(c_1279, plain, (![C_188, A_189, B_190]: (m1_connsp_2(C_188, A_189, B_190) | ~r2_hidden(B_190, k1_tops_1(A_189, C_188)) | ~m1_subset_1(C_188, k1_zfmisc_1(u1_struct_0(A_189))) | ~m1_subset_1(B_190, u1_struct_0(A_189)) | ~l1_pre_topc(A_189) | ~v2_pre_topc(A_189) | v2_struct_0(A_189))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.15/2.40  tff(c_1294, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_706, c_1279])).
% 7.15/2.40  tff(c_1342, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_1294])).
% 7.15/2.40  tff(c_1344, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_275, c_1342])).
% 7.15/2.40  tff(c_1384, plain, (![D_196]: (~r2_hidden('#skF_4', D_196) | ~r1_tarski(D_196, '#skF_5') | ~v3_pre_topc(D_196, '#skF_3') | ~m1_subset_1(D_196, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(splitRight, [status(thm)], [c_44])).
% 7.15/2.40  tff(c_1387, plain, (~r2_hidden('#skF_4', '#skF_6') | ~r1_tarski('#skF_6', '#skF_5') | ~v3_pre_topc('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_95, c_1384])).
% 7.15/2.40  tff(c_1398, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_65, c_64, c_1387])).
% 7.15/2.40  tff(c_1400, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_62])).
% 7.15/2.40  tff(c_1404, plain, (~r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_12, c_1400])).
% 7.15/2.40  tff(c_1422, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_1419, c_1404])).
% 7.15/2.40  tff(c_1428, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_1422])).
% 7.15/2.40  tff(c_1429, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_54])).
% 7.15/2.40  tff(c_2470, plain, (![A_329, B_330, C_331]: (r1_tarski('#skF_2'(A_329, B_330, C_331), C_331) | ~m1_connsp_2(C_331, A_329, B_330) | ~m1_subset_1(C_331, k1_zfmisc_1(u1_struct_0(A_329))) | ~m1_subset_1(B_330, u1_struct_0(A_329)) | ~l1_pre_topc(A_329) | ~v2_pre_topc(A_329) | v2_struct_0(A_329))), inference(cnfTransformation, [status(thm)], [f_133])).
% 7.15/2.40  tff(c_2477, plain, (![B_330]: (r1_tarski('#skF_2'('#skF_3', B_330, '#skF_5'), '#skF_5') | ~m1_connsp_2('#skF_5', '#skF_3', B_330) | ~m1_subset_1(B_330, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_2470])).
% 7.15/2.40  tff(c_2485, plain, (![B_330]: (r1_tarski('#skF_2'('#skF_3', B_330, '#skF_5'), '#skF_5') | ~m1_connsp_2('#skF_5', '#skF_3', B_330) | ~m1_subset_1(B_330, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_2477])).
% 7.15/2.40  tff(c_2486, plain, (![B_330]: (r1_tarski('#skF_2'('#skF_3', B_330, '#skF_5'), '#skF_5') | ~m1_connsp_2('#skF_5', '#skF_3', B_330) | ~m1_subset_1(B_330, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_42, c_2485])).
% 7.15/2.40  tff(c_30, plain, (![A_36, B_44, C_48]: (m1_subset_1('#skF_2'(A_36, B_44, C_48), k1_zfmisc_1(u1_struct_0(A_36))) | ~m1_connsp_2(C_48, A_36, B_44) | ~m1_subset_1(C_48, k1_zfmisc_1(u1_struct_0(A_36))) | ~m1_subset_1(B_44, u1_struct_0(A_36)) | ~l1_pre_topc(A_36) | ~v2_pre_topc(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_133])).
% 7.15/2.40  tff(c_2749, plain, (![A_343, B_344, C_345]: (m1_connsp_2('#skF_2'(A_343, B_344, C_345), A_343, B_344) | ~m1_connsp_2(C_345, A_343, B_344) | ~m1_subset_1(C_345, k1_zfmisc_1(u1_struct_0(A_343))) | ~m1_subset_1(B_344, u1_struct_0(A_343)) | ~l1_pre_topc(A_343) | ~v2_pre_topc(A_343) | v2_struct_0(A_343))), inference(cnfTransformation, [status(thm)], [f_133])).
% 7.15/2.40  tff(c_2756, plain, (![B_344]: (m1_connsp_2('#skF_2'('#skF_3', B_344, '#skF_5'), '#skF_3', B_344) | ~m1_connsp_2('#skF_5', '#skF_3', B_344) | ~m1_subset_1(B_344, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_2749])).
% 7.15/2.40  tff(c_2764, plain, (![B_344]: (m1_connsp_2('#skF_2'('#skF_3', B_344, '#skF_5'), '#skF_3', B_344) | ~m1_connsp_2('#skF_5', '#skF_3', B_344) | ~m1_subset_1(B_344, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_2756])).
% 7.15/2.40  tff(c_2766, plain, (![B_346]: (m1_connsp_2('#skF_2'('#skF_3', B_346, '#skF_5'), '#skF_3', B_346) | ~m1_connsp_2('#skF_5', '#skF_3', B_346) | ~m1_subset_1(B_346, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_42, c_2764])).
% 7.15/2.40  tff(c_22, plain, (![C_35, B_33, A_29]: (r2_hidden(C_35, B_33) | ~m1_connsp_2(B_33, A_29, C_35) | ~m1_subset_1(C_35, u1_struct_0(A_29)) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29) | ~v2_pre_topc(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.15/2.40  tff(c_2768, plain, (![B_346]: (r2_hidden(B_346, '#skF_2'('#skF_3', B_346, '#skF_5')) | ~m1_subset_1('#skF_2'('#skF_3', B_346, '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_connsp_2('#skF_5', '#skF_3', B_346) | ~m1_subset_1(B_346, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_2766, c_22])).
% 7.15/2.40  tff(c_2773, plain, (![B_346]: (r2_hidden(B_346, '#skF_2'('#skF_3', B_346, '#skF_5')) | ~m1_subset_1('#skF_2'('#skF_3', B_346, '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3') | ~m1_connsp_2('#skF_5', '#skF_3', B_346) | ~m1_subset_1(B_346, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_2768])).
% 7.15/2.40  tff(c_2940, plain, (![B_360]: (r2_hidden(B_360, '#skF_2'('#skF_3', B_360, '#skF_5')) | ~m1_subset_1('#skF_2'('#skF_3', B_360, '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_connsp_2('#skF_5', '#skF_3', B_360) | ~m1_subset_1(B_360, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_42, c_2773])).
% 7.15/2.40  tff(c_2943, plain, (![B_44]: (r2_hidden(B_44, '#skF_2'('#skF_3', B_44, '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_44) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_44, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_2940])).
% 7.15/2.40  tff(c_2951, plain, (![B_44]: (r2_hidden(B_44, '#skF_2'('#skF_3', B_44, '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_44) | ~m1_subset_1(B_44, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_34, c_2943])).
% 7.15/2.40  tff(c_2955, plain, (![B_361]: (r2_hidden(B_361, '#skF_2'('#skF_3', B_361, '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_361) | ~m1_subset_1(B_361, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_42, c_2951])).
% 7.15/2.40  tff(c_2342, plain, (![A_311, B_312, C_313]: (v3_pre_topc('#skF_2'(A_311, B_312, C_313), A_311) | ~m1_connsp_2(C_313, A_311, B_312) | ~m1_subset_1(C_313, k1_zfmisc_1(u1_struct_0(A_311))) | ~m1_subset_1(B_312, u1_struct_0(A_311)) | ~l1_pre_topc(A_311) | ~v2_pre_topc(A_311) | v2_struct_0(A_311))), inference(cnfTransformation, [status(thm)], [f_133])).
% 7.15/2.40  tff(c_2349, plain, (![B_312]: (v3_pre_topc('#skF_2'('#skF_3', B_312, '#skF_5'), '#skF_3') | ~m1_connsp_2('#skF_5', '#skF_3', B_312) | ~m1_subset_1(B_312, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_2342])).
% 7.15/2.40  tff(c_2357, plain, (![B_312]: (v3_pre_topc('#skF_2'('#skF_3', B_312, '#skF_5'), '#skF_3') | ~m1_connsp_2('#skF_5', '#skF_3', B_312) | ~m1_subset_1(B_312, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_2349])).
% 7.15/2.40  tff(c_2359, plain, (![B_314]: (v3_pre_topc('#skF_2'('#skF_3', B_314, '#skF_5'), '#skF_3') | ~m1_connsp_2('#skF_5', '#skF_3', B_314) | ~m1_subset_1(B_314, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_42, c_2357])).
% 7.15/2.40  tff(c_1432, plain, (![A_202, B_203]: (r1_tarski(A_202, B_203) | ~m1_subset_1(A_202, k1_zfmisc_1(B_203)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.15/2.40  tff(c_1440, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_1432])).
% 7.15/2.40  tff(c_1455, plain, (![A_211, C_212, B_213]: (r1_tarski(A_211, C_212) | ~r1_tarski(B_213, C_212) | ~r1_tarski(A_211, B_213))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.15/2.40  tff(c_1464, plain, (![A_211]: (r1_tarski(A_211, u1_struct_0('#skF_3')) | ~r1_tarski(A_211, '#skF_5'))), inference(resolution, [status(thm)], [c_1440, c_1455])).
% 7.15/2.40  tff(c_1430, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_54])).
% 7.15/2.40  tff(c_52, plain, (![D_68]: (~r2_hidden('#skF_4', D_68) | ~r1_tarski(D_68, '#skF_5') | ~v3_pre_topc(D_68, '#skF_3') | ~m1_subset_1(D_68, k1_zfmisc_1(u1_struct_0('#skF_3'))) | r1_tarski('#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 7.15/2.40  tff(c_1507, plain, (![D_222]: (~r2_hidden('#skF_4', D_222) | ~r1_tarski(D_222, '#skF_5') | ~v3_pre_topc(D_222, '#skF_3') | ~m1_subset_1(D_222, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_1430, c_52])).
% 7.15/2.40  tff(c_1595, plain, (![A_231]: (~r2_hidden('#skF_4', A_231) | ~r1_tarski(A_231, '#skF_5') | ~v3_pre_topc(A_231, '#skF_3') | ~r1_tarski(A_231, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_12, c_1507])).
% 7.15/2.40  tff(c_1613, plain, (![A_211]: (~r2_hidden('#skF_4', A_211) | ~v3_pre_topc(A_211, '#skF_3') | ~r1_tarski(A_211, '#skF_5'))), inference(resolution, [status(thm)], [c_1464, c_1595])).
% 7.15/2.40  tff(c_2371, plain, (![B_314]: (~r2_hidden('#skF_4', '#skF_2'('#skF_3', B_314, '#skF_5')) | ~r1_tarski('#skF_2'('#skF_3', B_314, '#skF_5'), '#skF_5') | ~m1_connsp_2('#skF_5', '#skF_3', B_314) | ~m1_subset_1(B_314, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_2359, c_1613])).
% 7.15/2.40  tff(c_2959, plain, (~r1_tarski('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_5') | ~m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_2955, c_2371])).
% 7.15/2.40  tff(c_2964, plain, (~r1_tarski('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1429, c_2959])).
% 7.15/2.40  tff(c_2968, plain, (~m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_2486, c_2964])).
% 7.15/2.40  tff(c_2972, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_1429, c_2968])).
% 7.15/2.40  tff(c_2973, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_50])).
% 7.15/2.40  tff(c_3658, plain, (![A_478, B_479, C_480]: (r1_tarski('#skF_2'(A_478, B_479, C_480), C_480) | ~m1_connsp_2(C_480, A_478, B_479) | ~m1_subset_1(C_480, k1_zfmisc_1(u1_struct_0(A_478))) | ~m1_subset_1(B_479, u1_struct_0(A_478)) | ~l1_pre_topc(A_478) | ~v2_pre_topc(A_478) | v2_struct_0(A_478))), inference(cnfTransformation, [status(thm)], [f_133])).
% 7.15/2.40  tff(c_3663, plain, (![B_479]: (r1_tarski('#skF_2'('#skF_3', B_479, '#skF_5'), '#skF_5') | ~m1_connsp_2('#skF_5', '#skF_3', B_479) | ~m1_subset_1(B_479, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_3658])).
% 7.15/2.40  tff(c_3667, plain, (![B_479]: (r1_tarski('#skF_2'('#skF_3', B_479, '#skF_5'), '#skF_5') | ~m1_connsp_2('#skF_5', '#skF_3', B_479) | ~m1_subset_1(B_479, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_3663])).
% 7.15/2.40  tff(c_3668, plain, (![B_479]: (r1_tarski('#skF_2'('#skF_3', B_479, '#skF_5'), '#skF_5') | ~m1_connsp_2('#skF_5', '#skF_3', B_479) | ~m1_subset_1(B_479, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_42, c_3667])).
% 7.15/2.40  tff(c_3835, plain, (![A_498, B_499, C_500]: (m1_connsp_2('#skF_2'(A_498, B_499, C_500), A_498, B_499) | ~m1_connsp_2(C_500, A_498, B_499) | ~m1_subset_1(C_500, k1_zfmisc_1(u1_struct_0(A_498))) | ~m1_subset_1(B_499, u1_struct_0(A_498)) | ~l1_pre_topc(A_498) | ~v2_pre_topc(A_498) | v2_struct_0(A_498))), inference(cnfTransformation, [status(thm)], [f_133])).
% 7.15/2.40  tff(c_3840, plain, (![B_499]: (m1_connsp_2('#skF_2'('#skF_3', B_499, '#skF_5'), '#skF_3', B_499) | ~m1_connsp_2('#skF_5', '#skF_3', B_499) | ~m1_subset_1(B_499, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_3835])).
% 7.15/2.40  tff(c_3844, plain, (![B_499]: (m1_connsp_2('#skF_2'('#skF_3', B_499, '#skF_5'), '#skF_3', B_499) | ~m1_connsp_2('#skF_5', '#skF_3', B_499) | ~m1_subset_1(B_499, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_3840])).
% 7.15/2.40  tff(c_3846, plain, (![B_501]: (m1_connsp_2('#skF_2'('#skF_3', B_501, '#skF_5'), '#skF_3', B_501) | ~m1_connsp_2('#skF_5', '#skF_3', B_501) | ~m1_subset_1(B_501, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_42, c_3844])).
% 7.15/2.40  tff(c_20, plain, (![C_28, A_25, B_26]: (m1_subset_1(C_28, k1_zfmisc_1(u1_struct_0(A_25))) | ~m1_connsp_2(C_28, A_25, B_26) | ~m1_subset_1(B_26, u1_struct_0(A_25)) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.15/2.40  tff(c_3850, plain, (![B_501]: (m1_subset_1('#skF_2'('#skF_3', B_501, '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_connsp_2('#skF_5', '#skF_3', B_501) | ~m1_subset_1(B_501, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_3846, c_20])).
% 7.15/2.40  tff(c_3857, plain, (![B_501]: (m1_subset_1('#skF_2'('#skF_3', B_501, '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3') | ~m1_connsp_2('#skF_5', '#skF_3', B_501) | ~m1_subset_1(B_501, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_3850])).
% 7.15/2.40  tff(c_3858, plain, (![B_501]: (m1_subset_1('#skF_2'('#skF_3', B_501, '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_connsp_2('#skF_5', '#skF_3', B_501) | ~m1_subset_1(B_501, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_42, c_3857])).
% 7.15/2.40  tff(c_3848, plain, (![B_501]: (r2_hidden(B_501, '#skF_2'('#skF_3', B_501, '#skF_5')) | ~m1_subset_1('#skF_2'('#skF_3', B_501, '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_connsp_2('#skF_5', '#skF_3', B_501) | ~m1_subset_1(B_501, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_3846, c_22])).
% 7.15/2.40  tff(c_3853, plain, (![B_501]: (r2_hidden(B_501, '#skF_2'('#skF_3', B_501, '#skF_5')) | ~m1_subset_1('#skF_2'('#skF_3', B_501, '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3') | ~m1_connsp_2('#skF_5', '#skF_3', B_501) | ~m1_subset_1(B_501, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_3848])).
% 7.15/2.40  tff(c_3909, plain, (![B_503]: (r2_hidden(B_503, '#skF_2'('#skF_3', B_503, '#skF_5')) | ~m1_subset_1('#skF_2'('#skF_3', B_503, '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_connsp_2('#skF_5', '#skF_3', B_503) | ~m1_subset_1(B_503, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_42, c_3853])).
% 7.15/2.40  tff(c_3924, plain, (![B_505]: (r2_hidden(B_505, '#skF_2'('#skF_3', B_505, '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_505) | ~m1_subset_1(B_505, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_3858, c_3909])).
% 7.15/2.40  tff(c_3549, plain, (![A_462, B_463, C_464]: (v3_pre_topc('#skF_2'(A_462, B_463, C_464), A_462) | ~m1_connsp_2(C_464, A_462, B_463) | ~m1_subset_1(C_464, k1_zfmisc_1(u1_struct_0(A_462))) | ~m1_subset_1(B_463, u1_struct_0(A_462)) | ~l1_pre_topc(A_462) | ~v2_pre_topc(A_462) | v2_struct_0(A_462))), inference(cnfTransformation, [status(thm)], [f_133])).
% 7.15/2.40  tff(c_3554, plain, (![B_463]: (v3_pre_topc('#skF_2'('#skF_3', B_463, '#skF_5'), '#skF_3') | ~m1_connsp_2('#skF_5', '#skF_3', B_463) | ~m1_subset_1(B_463, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_3549])).
% 7.15/2.40  tff(c_3558, plain, (![B_463]: (v3_pre_topc('#skF_2'('#skF_3', B_463, '#skF_5'), '#skF_3') | ~m1_connsp_2('#skF_5', '#skF_3', B_463) | ~m1_subset_1(B_463, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_3554])).
% 7.15/2.40  tff(c_3560, plain, (![B_465]: (v3_pre_topc('#skF_2'('#skF_3', B_465, '#skF_5'), '#skF_3') | ~m1_connsp_2('#skF_5', '#skF_3', B_465) | ~m1_subset_1(B_465, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_42, c_3558])).
% 7.15/2.40  tff(c_2977, plain, (![A_364, B_365]: (r1_tarski(A_364, B_365) | ~m1_subset_1(A_364, k1_zfmisc_1(B_365)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.15/2.40  tff(c_2985, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_2977])).
% 7.15/2.40  tff(c_2999, plain, (![A_374, C_375, B_376]: (r1_tarski(A_374, C_375) | ~r1_tarski(B_376, C_375) | ~r1_tarski(A_374, B_376))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.15/2.40  tff(c_3005, plain, (![A_374]: (r1_tarski(A_374, u1_struct_0('#skF_3')) | ~r1_tarski(A_374, '#skF_5'))), inference(resolution, [status(thm)], [c_2985, c_2999])).
% 7.15/2.40  tff(c_2974, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_50])).
% 7.15/2.40  tff(c_48, plain, (![D_68]: (~r2_hidden('#skF_4', D_68) | ~r1_tarski(D_68, '#skF_5') | ~v3_pre_topc(D_68, '#skF_3') | ~m1_subset_1(D_68, k1_zfmisc_1(u1_struct_0('#skF_3'))) | r2_hidden('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 7.15/2.40  tff(c_3042, plain, (![D_387]: (~r2_hidden('#skF_4', D_387) | ~r1_tarski(D_387, '#skF_5') | ~v3_pre_topc(D_387, '#skF_3') | ~m1_subset_1(D_387, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_2974, c_48])).
% 7.15/2.40  tff(c_3064, plain, (![A_390]: (~r2_hidden('#skF_4', A_390) | ~r1_tarski(A_390, '#skF_5') | ~v3_pre_topc(A_390, '#skF_3') | ~r1_tarski(A_390, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_12, c_3042])).
% 7.15/2.40  tff(c_3075, plain, (![A_374]: (~r2_hidden('#skF_4', A_374) | ~v3_pre_topc(A_374, '#skF_3') | ~r1_tarski(A_374, '#skF_5'))), inference(resolution, [status(thm)], [c_3005, c_3064])).
% 7.15/2.40  tff(c_3568, plain, (![B_465]: (~r2_hidden('#skF_4', '#skF_2'('#skF_3', B_465, '#skF_5')) | ~r1_tarski('#skF_2'('#skF_3', B_465, '#skF_5'), '#skF_5') | ~m1_connsp_2('#skF_5', '#skF_3', B_465) | ~m1_subset_1(B_465, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_3560, c_3075])).
% 7.15/2.40  tff(c_3928, plain, (~r1_tarski('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_5') | ~m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_3924, c_3568])).
% 7.15/2.40  tff(c_3933, plain, (~r1_tarski('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2973, c_3928])).
% 7.15/2.40  tff(c_3937, plain, (~m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_3668, c_3933])).
% 7.15/2.40  tff(c_3941, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_2973, c_3937])).
% 7.15/2.40  tff(c_3942, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_58])).
% 7.15/2.40  tff(c_4505, plain, (![A_606, B_607, C_608]: (r1_tarski('#skF_2'(A_606, B_607, C_608), C_608) | ~m1_connsp_2(C_608, A_606, B_607) | ~m1_subset_1(C_608, k1_zfmisc_1(u1_struct_0(A_606))) | ~m1_subset_1(B_607, u1_struct_0(A_606)) | ~l1_pre_topc(A_606) | ~v2_pre_topc(A_606) | v2_struct_0(A_606))), inference(cnfTransformation, [status(thm)], [f_133])).
% 7.15/2.40  tff(c_4510, plain, (![B_607]: (r1_tarski('#skF_2'('#skF_3', B_607, '#skF_5'), '#skF_5') | ~m1_connsp_2('#skF_5', '#skF_3', B_607) | ~m1_subset_1(B_607, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_4505])).
% 7.15/2.40  tff(c_4514, plain, (![B_607]: (r1_tarski('#skF_2'('#skF_3', B_607, '#skF_5'), '#skF_5') | ~m1_connsp_2('#skF_5', '#skF_3', B_607) | ~m1_subset_1(B_607, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_4510])).
% 7.15/2.40  tff(c_4515, plain, (![B_607]: (r1_tarski('#skF_2'('#skF_3', B_607, '#skF_5'), '#skF_5') | ~m1_connsp_2('#skF_5', '#skF_3', B_607) | ~m1_subset_1(B_607, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_42, c_4514])).
% 7.15/2.40  tff(c_4789, plain, (![A_642, B_643, C_644]: (m1_connsp_2('#skF_2'(A_642, B_643, C_644), A_642, B_643) | ~m1_connsp_2(C_644, A_642, B_643) | ~m1_subset_1(C_644, k1_zfmisc_1(u1_struct_0(A_642))) | ~m1_subset_1(B_643, u1_struct_0(A_642)) | ~l1_pre_topc(A_642) | ~v2_pre_topc(A_642) | v2_struct_0(A_642))), inference(cnfTransformation, [status(thm)], [f_133])).
% 7.15/2.40  tff(c_4794, plain, (![B_643]: (m1_connsp_2('#skF_2'('#skF_3', B_643, '#skF_5'), '#skF_3', B_643) | ~m1_connsp_2('#skF_5', '#skF_3', B_643) | ~m1_subset_1(B_643, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_4789])).
% 7.15/2.40  tff(c_4798, plain, (![B_643]: (m1_connsp_2('#skF_2'('#skF_3', B_643, '#skF_5'), '#skF_3', B_643) | ~m1_connsp_2('#skF_5', '#skF_3', B_643) | ~m1_subset_1(B_643, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_4794])).
% 7.15/2.40  tff(c_4800, plain, (![B_645]: (m1_connsp_2('#skF_2'('#skF_3', B_645, '#skF_5'), '#skF_3', B_645) | ~m1_connsp_2('#skF_5', '#skF_3', B_645) | ~m1_subset_1(B_645, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_42, c_4798])).
% 7.15/2.40  tff(c_4804, plain, (![B_645]: (m1_subset_1('#skF_2'('#skF_3', B_645, '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_connsp_2('#skF_5', '#skF_3', B_645) | ~m1_subset_1(B_645, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_4800, c_20])).
% 7.15/2.40  tff(c_4811, plain, (![B_645]: (m1_subset_1('#skF_2'('#skF_3', B_645, '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3') | ~m1_connsp_2('#skF_5', '#skF_3', B_645) | ~m1_subset_1(B_645, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_4804])).
% 7.15/2.40  tff(c_4812, plain, (![B_645]: (m1_subset_1('#skF_2'('#skF_3', B_645, '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_connsp_2('#skF_5', '#skF_3', B_645) | ~m1_subset_1(B_645, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_42, c_4811])).
% 7.15/2.40  tff(c_4802, plain, (![B_645]: (r2_hidden(B_645, '#skF_2'('#skF_3', B_645, '#skF_5')) | ~m1_subset_1('#skF_2'('#skF_3', B_645, '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_connsp_2('#skF_5', '#skF_3', B_645) | ~m1_subset_1(B_645, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_4800, c_22])).
% 7.15/2.40  tff(c_4807, plain, (![B_645]: (r2_hidden(B_645, '#skF_2'('#skF_3', B_645, '#skF_5')) | ~m1_subset_1('#skF_2'('#skF_3', B_645, '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3') | ~m1_connsp_2('#skF_5', '#skF_3', B_645) | ~m1_subset_1(B_645, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_4802])).
% 7.15/2.40  tff(c_4878, plain, (![B_649]: (r2_hidden(B_649, '#skF_2'('#skF_3', B_649, '#skF_5')) | ~m1_subset_1('#skF_2'('#skF_3', B_649, '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_connsp_2('#skF_5', '#skF_3', B_649) | ~m1_subset_1(B_649, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_42, c_4807])).
% 7.15/2.40  tff(c_4886, plain, (![B_650]: (r2_hidden(B_650, '#skF_2'('#skF_3', B_650, '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_650) | ~m1_subset_1(B_650, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_4812, c_4878])).
% 7.15/2.40  tff(c_4671, plain, (![A_624, B_625, C_626]: (v3_pre_topc('#skF_2'(A_624, B_625, C_626), A_624) | ~m1_connsp_2(C_626, A_624, B_625) | ~m1_subset_1(C_626, k1_zfmisc_1(u1_struct_0(A_624))) | ~m1_subset_1(B_625, u1_struct_0(A_624)) | ~l1_pre_topc(A_624) | ~v2_pre_topc(A_624) | v2_struct_0(A_624))), inference(cnfTransformation, [status(thm)], [f_133])).
% 7.15/2.40  tff(c_4676, plain, (![B_625]: (v3_pre_topc('#skF_2'('#skF_3', B_625, '#skF_5'), '#skF_3') | ~m1_connsp_2('#skF_5', '#skF_3', B_625) | ~m1_subset_1(B_625, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_4671])).
% 7.15/2.40  tff(c_4680, plain, (![B_625]: (v3_pre_topc('#skF_2'('#skF_3', B_625, '#skF_5'), '#skF_3') | ~m1_connsp_2('#skF_5', '#skF_3', B_625) | ~m1_subset_1(B_625, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_4676])).
% 7.15/2.40  tff(c_4682, plain, (![B_627]: (v3_pre_topc('#skF_2'('#skF_3', B_627, '#skF_5'), '#skF_3') | ~m1_connsp_2('#skF_5', '#skF_3', B_627) | ~m1_subset_1(B_627, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_42, c_4680])).
% 7.15/2.40  tff(c_3947, plain, (![A_508, B_509]: (r1_tarski(A_508, B_509) | ~m1_subset_1(A_508, k1_zfmisc_1(B_509)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.15/2.40  tff(c_3955, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_3947])).
% 7.15/2.40  tff(c_3969, plain, (![A_518, C_519, B_520]: (r1_tarski(A_518, C_519) | ~r1_tarski(B_520, C_519) | ~r1_tarski(A_518, B_520))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.15/2.40  tff(c_3975, plain, (![A_518]: (r1_tarski(A_518, u1_struct_0('#skF_3')) | ~r1_tarski(A_518, '#skF_5'))), inference(resolution, [status(thm)], [c_3955, c_3969])).
% 7.15/2.40  tff(c_3943, plain, (~v3_pre_topc('#skF_6', '#skF_3')), inference(splitRight, [status(thm)], [c_58])).
% 7.15/2.40  tff(c_56, plain, (![D_68]: (~r2_hidden('#skF_4', D_68) | ~r1_tarski(D_68, '#skF_5') | ~v3_pre_topc(D_68, '#skF_3') | ~m1_subset_1(D_68, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v3_pre_topc('#skF_6', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 7.15/2.40  tff(c_3977, plain, (![D_521]: (~r2_hidden('#skF_4', D_521) | ~r1_tarski(D_521, '#skF_5') | ~v3_pre_topc(D_521, '#skF_3') | ~m1_subset_1(D_521, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_3943, c_56])).
% 7.15/2.40  tff(c_4014, plain, (![A_528]: (~r2_hidden('#skF_4', A_528) | ~r1_tarski(A_528, '#skF_5') | ~v3_pre_topc(A_528, '#skF_3') | ~r1_tarski(A_528, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_12, c_3977])).
% 7.15/2.40  tff(c_4025, plain, (![A_518]: (~r2_hidden('#skF_4', A_518) | ~v3_pre_topc(A_518, '#skF_3') | ~r1_tarski(A_518, '#skF_5'))), inference(resolution, [status(thm)], [c_3975, c_4014])).
% 7.15/2.40  tff(c_4690, plain, (![B_627]: (~r2_hidden('#skF_4', '#skF_2'('#skF_3', B_627, '#skF_5')) | ~r1_tarski('#skF_2'('#skF_3', B_627, '#skF_5'), '#skF_5') | ~m1_connsp_2('#skF_5', '#skF_3', B_627) | ~m1_subset_1(B_627, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_4682, c_4025])).
% 7.15/2.40  tff(c_4890, plain, (~r1_tarski('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_5') | ~m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_4886, c_4690])).
% 7.15/2.40  tff(c_4895, plain, (~r1_tarski('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3942, c_4890])).
% 7.15/2.40  tff(c_4899, plain, (~m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_4515, c_4895])).
% 7.15/2.40  tff(c_4903, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_3942, c_4899])).
% 7.15/2.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.15/2.40  
% 7.15/2.40  Inference rules
% 7.15/2.40  ----------------------
% 7.15/2.40  #Ref     : 0
% 7.15/2.40  #Sup     : 1101
% 7.15/2.40  #Fact    : 0
% 7.15/2.40  #Define  : 0
% 7.15/2.40  #Split   : 34
% 7.15/2.40  #Chain   : 0
% 7.15/2.40  #Close   : 0
% 7.15/2.40  
% 7.15/2.40  Ordering : KBO
% 7.15/2.40  
% 7.15/2.40  Simplification rules
% 7.15/2.40  ----------------------
% 7.15/2.40  #Subsume      : 489
% 7.15/2.40  #Demod        : 514
% 7.15/2.40  #Tautology    : 150
% 7.15/2.40  #SimpNegUnit  : 77
% 7.15/2.40  #BackRed      : 0
% 7.15/2.40  
% 7.15/2.40  #Partial instantiations: 0
% 7.15/2.40  #Strategies tried      : 1
% 7.15/2.40  
% 7.15/2.40  Timing (in seconds)
% 7.15/2.40  ----------------------
% 7.15/2.40  Preprocessing        : 0.33
% 7.15/2.40  Parsing              : 0.18
% 7.15/2.40  CNF conversion       : 0.03
% 7.15/2.40  Main loop            : 1.27
% 7.15/2.40  Inferencing          : 0.41
% 7.15/2.41  Reduction            : 0.39
% 7.15/2.41  Demodulation         : 0.25
% 7.15/2.41  BG Simplification    : 0.04
% 7.15/2.41  Subsumption          : 0.36
% 7.15/2.41  Abstraction          : 0.05
% 7.15/2.41  MUC search           : 0.00
% 7.15/2.41  Cooper               : 0.00
% 7.15/2.41  Total                : 1.66
% 7.15/2.41  Index Insertion      : 0.00
% 7.15/2.41  Index Deletion       : 0.00
% 7.15/2.41  Index Matching       : 0.00
% 7.15/2.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
