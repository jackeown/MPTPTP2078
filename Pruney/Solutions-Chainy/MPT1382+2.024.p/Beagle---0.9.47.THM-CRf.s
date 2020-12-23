%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:10 EST 2020

% Result     : Theorem 3.80s
% Output     : CNFRefutation 4.15s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 219 expanded)
%              Number of leaves         :   27 (  90 expanded)
%              Depth                    :   12
%              Number of atoms          :  228 ( 957 expanded)
%              Number of equality atoms :    0 (   0 expanded)
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

tff(f_29,axiom,(
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

tff(f_48,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

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

tff(f_77,axiom,(
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

tff(f_42,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_101,plain,(
    ! [A_72,B_73] :
      ( v3_pre_topc(k1_tops_1(A_72,B_73),A_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72)
      | ~ v2_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_106,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_101])).

tff(c_110,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_106])).

tff(c_85,plain,(
    ! [A_68,B_69] :
      ( r1_tarski(k1_tops_1(A_68,B_69),B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_90,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_85])).

tff(c_94,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_90])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_37,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_41,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_37])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_26,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_228,plain,(
    ! [B_107,A_108,C_109] :
      ( r2_hidden(B_107,k1_tops_1(A_108,C_109))
      | ~ m1_connsp_2(C_109,A_108,B_107)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ m1_subset_1(B_107,u1_struct_0(A_108))
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108)
      | v2_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_237,plain,(
    ! [B_107,A_108,A_1] :
      ( r2_hidden(B_107,k1_tops_1(A_108,A_1))
      | ~ m1_connsp_2(A_1,A_108,B_107)
      | ~ m1_subset_1(B_107,u1_struct_0(A_108))
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108)
      | v2_struct_0(A_108)
      | ~ r1_tarski(A_1,u1_struct_0(A_108)) ) ),
    inference(resolution,[status(thm)],[c_4,c_228])).

tff(c_111,plain,(
    ! [A_74,B_75] :
      ( m1_subset_1(k1_tops_1(A_74,B_75),k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_24,plain,(
    ! [D_48] :
      ( ~ r1_tarski(D_48,'#skF_3')
      | ~ v3_pre_topc(D_48,'#skF_1')
      | ~ m1_connsp_2(D_48,'#skF_1','#skF_2')
      | ~ m1_subset_1(D_48,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v1_xboole_0(D_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_123,plain,(
    ! [B_75] :
      ( ~ r1_tarski(k1_tops_1('#skF_1',B_75),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_75),'#skF_1')
      | ~ m1_connsp_2(k1_tops_1('#skF_1',B_75),'#skF_1','#skF_2')
      | v1_xboole_0(k1_tops_1('#skF_1',B_75))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_111,c_24])).

tff(c_145,plain,(
    ! [B_83] :
      ( ~ r1_tarski(k1_tops_1('#skF_1',B_83),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_83),'#skF_1')
      | ~ m1_connsp_2(k1_tops_1('#skF_1',B_83),'#skF_1','#skF_2')
      | v1_xboole_0(k1_tops_1('#skF_1',B_83))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_123])).

tff(c_156,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1','#skF_2')
    | v1_xboole_0(k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_145])).

tff(c_163,plain,
    ( ~ m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1','#skF_2')
    | v1_xboole_0(k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_94,c_156])).

tff(c_164,plain,(
    ~ m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k1_tops_1(A_9,B_10),k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_265,plain,(
    ! [B_111,A_112,C_113] :
      ( m1_connsp_2(B_111,A_112,C_113)
      | ~ r2_hidden(C_113,B_111)
      | ~ v3_pre_topc(B_111,A_112)
      | ~ m1_subset_1(C_113,u1_struct_0(A_112))
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112)
      | ~ v2_pre_topc(A_112)
      | v2_struct_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_269,plain,(
    ! [B_111] :
      ( m1_connsp_2(B_111,'#skF_1','#skF_2')
      | ~ r2_hidden('#skF_2',B_111)
      | ~ v3_pre_topc(B_111,'#skF_1')
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_265])).

tff(c_276,plain,(
    ! [B_111] :
      ( m1_connsp_2(B_111,'#skF_1','#skF_2')
      | ~ r2_hidden('#skF_2',B_111)
      | ~ v3_pre_topc(B_111,'#skF_1')
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_269])).

tff(c_278,plain,(
    ! [B_114] :
      ( m1_connsp_2(B_114,'#skF_1','#skF_2')
      | ~ r2_hidden('#skF_2',B_114)
      | ~ v3_pre_topc(B_114,'#skF_1')
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_276])).

tff(c_282,plain,(
    ! [B_10] :
      ( m1_connsp_2(k1_tops_1('#skF_1',B_10),'#skF_1','#skF_2')
      | ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_10))
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_10),'#skF_1')
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_10,c_278])).

tff(c_475,plain,(
    ! [B_135] :
      ( m1_connsp_2(k1_tops_1('#skF_1',B_135),'#skF_1','#skF_2')
      | ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_135))
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_135),'#skF_1')
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_282])).

tff(c_486,plain,
    ( m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1','#skF_2')
    | ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_475])).

tff(c_493,plain,
    ( m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1','#skF_2')
    | ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_486])).

tff(c_494,plain,(
    ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_493])).

tff(c_497,plain,
    ( ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_237,c_494])).

tff(c_503,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_34,c_32,c_30,c_26,c_497])).

tff(c_505,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_503])).

tff(c_506,plain,(
    v1_xboole_0(k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_512,plain,(
    ! [B_144,A_145,C_146] :
      ( r1_tarski(B_144,k1_tops_1(A_145,C_146))
      | ~ r1_tarski(B_144,C_146)
      | ~ v3_pre_topc(B_144,A_145)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_519,plain,(
    ! [B_144] :
      ( r1_tarski(B_144,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(B_144,'#skF_3')
      | ~ v3_pre_topc(B_144,'#skF_1')
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_512])).

tff(c_525,plain,(
    ! [B_147] :
      ( r1_tarski(B_147,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(B_147,'#skF_3')
      | ~ v3_pre_topc(B_147,'#skF_1')
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_519])).

tff(c_529,plain,(
    ! [B_10] :
      ( r1_tarski(k1_tops_1('#skF_1',B_10),k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_10),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_10),'#skF_1')
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_10,c_525])).

tff(c_539,plain,(
    ! [B_10] :
      ( r1_tarski(k1_tops_1('#skF_1',B_10),k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_10),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_10),'#skF_1')
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_529])).

tff(c_578,plain,(
    ! [B_160,A_161,C_162] :
      ( r2_hidden(B_160,k1_tops_1(A_161,C_162))
      | ~ m1_connsp_2(C_162,A_161,B_160)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(u1_struct_0(A_161)))
      | ~ m1_subset_1(B_160,u1_struct_0(A_161))
      | ~ l1_pre_topc(A_161)
      | ~ v2_pre_topc(A_161)
      | v2_struct_0(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_585,plain,(
    ! [B_160] :
      ( r2_hidden(B_160,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_160)
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_578])).

tff(c_590,plain,(
    ! [B_160] :
      ( r2_hidden(B_160,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_160)
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_585])).

tff(c_592,plain,(
    ! [B_163] :
      ( r2_hidden(B_163,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_163)
      | ~ m1_subset_1(B_163,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_590])).

tff(c_60,plain,(
    ! [C_54,B_55,A_56] :
      ( ~ v1_xboole_0(C_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(C_54))
      | ~ r2_hidden(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_65,plain,(
    ! [B_2,A_56,A_1] :
      ( ~ v1_xboole_0(B_2)
      | ~ r2_hidden(A_56,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_60])).

tff(c_614,plain,(
    ! [B_2,B_163] :
      ( ~ v1_xboole_0(B_2)
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),B_2)
      | ~ m1_connsp_2('#skF_3','#skF_1',B_163)
      | ~ m1_subset_1(B_163,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_592,c_65])).

tff(c_679,plain,(
    ! [B_171] :
      ( ~ m1_connsp_2('#skF_3','#skF_1',B_171)
      | ~ m1_subset_1(B_171,u1_struct_0('#skF_1')) ) ),
    inference(splitLeft,[status(thm)],[c_614])).

tff(c_685,plain,(
    ~ m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_679])).

tff(c_690,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_685])).

tff(c_692,plain,(
    ! [B_172] :
      ( ~ v1_xboole_0(B_172)
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),B_172) ) ),
    inference(splitRight,[status(thm)],[c_614])).

tff(c_696,plain,
    ( ~ v1_xboole_0(k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_539,c_692])).

tff(c_715,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_110,c_94,c_506,c_696])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:25:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.80/2.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/2.04  
% 3.80/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/2.04  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.80/2.04  
% 3.80/2.04  %Foreground sorts:
% 3.80/2.04  
% 3.80/2.04  
% 3.80/2.04  %Background operators:
% 3.80/2.04  
% 3.80/2.04  
% 3.80/2.04  %Foreground operators:
% 3.80/2.04  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.80/2.04  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.80/2.04  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.80/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.80/2.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.80/2.04  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.80/2.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.80/2.04  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.80/2.04  tff('#skF_2', type, '#skF_2': $i).
% 3.80/2.04  tff('#skF_3', type, '#skF_3': $i).
% 3.80/2.04  tff('#skF_1', type, '#skF_1': $i).
% 3.80/2.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.80/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.80/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.80/2.04  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.80/2.04  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.80/2.04  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.80/2.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.80/2.04  
% 4.15/2.07  tff(f_143, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(C, A, B) & (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~((m1_connsp_2(D, A, B) & v3_pre_topc(D, A)) & r1_tarski(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_connsp_2)).
% 4.15/2.07  tff(f_56, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 4.15/2.07  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 4.15/2.07  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.15/2.07  tff(f_94, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 4.15/2.07  tff(f_48, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 4.15/2.07  tff(f_113, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 4.15/2.07  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 4.15/2.07  tff(f_42, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 4.15/2.07  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.15/2.07  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.15/2.07  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.15/2.07  tff(c_101, plain, (![A_72, B_73]: (v3_pre_topc(k1_tops_1(A_72, B_73), A_72) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72) | ~v2_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.15/2.07  tff(c_106, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_101])).
% 4.15/2.07  tff(c_110, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_106])).
% 4.15/2.07  tff(c_85, plain, (![A_68, B_69]: (r1_tarski(k1_tops_1(A_68, B_69), B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.15/2.07  tff(c_90, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_85])).
% 4.15/2.07  tff(c_94, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_90])).
% 4.15/2.07  tff(c_36, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.15/2.07  tff(c_37, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~m1_subset_1(A_49, k1_zfmisc_1(B_50)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.15/2.07  tff(c_41, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_37])).
% 4.15/2.07  tff(c_30, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.15/2.07  tff(c_26, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.15/2.07  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.15/2.07  tff(c_228, plain, (![B_107, A_108, C_109]: (r2_hidden(B_107, k1_tops_1(A_108, C_109)) | ~m1_connsp_2(C_109, A_108, B_107) | ~m1_subset_1(C_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~m1_subset_1(B_107, u1_struct_0(A_108)) | ~l1_pre_topc(A_108) | ~v2_pre_topc(A_108) | v2_struct_0(A_108))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.15/2.07  tff(c_237, plain, (![B_107, A_108, A_1]: (r2_hidden(B_107, k1_tops_1(A_108, A_1)) | ~m1_connsp_2(A_1, A_108, B_107) | ~m1_subset_1(B_107, u1_struct_0(A_108)) | ~l1_pre_topc(A_108) | ~v2_pre_topc(A_108) | v2_struct_0(A_108) | ~r1_tarski(A_1, u1_struct_0(A_108)))), inference(resolution, [status(thm)], [c_4, c_228])).
% 4.15/2.07  tff(c_111, plain, (![A_74, B_75]: (m1_subset_1(k1_tops_1(A_74, B_75), k1_zfmisc_1(u1_struct_0(A_74))) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.15/2.07  tff(c_24, plain, (![D_48]: (~r1_tarski(D_48, '#skF_3') | ~v3_pre_topc(D_48, '#skF_1') | ~m1_connsp_2(D_48, '#skF_1', '#skF_2') | ~m1_subset_1(D_48, k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(D_48))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.15/2.07  tff(c_123, plain, (![B_75]: (~r1_tarski(k1_tops_1('#skF_1', B_75), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_75), '#skF_1') | ~m1_connsp_2(k1_tops_1('#skF_1', B_75), '#skF_1', '#skF_2') | v1_xboole_0(k1_tops_1('#skF_1', B_75)) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_111, c_24])).
% 4.15/2.07  tff(c_145, plain, (![B_83]: (~r1_tarski(k1_tops_1('#skF_1', B_83), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_83), '#skF_1') | ~m1_connsp_2(k1_tops_1('#skF_1', B_83), '#skF_1', '#skF_2') | v1_xboole_0(k1_tops_1('#skF_1', B_83)) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_123])).
% 4.15/2.07  tff(c_156, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', '#skF_2') | v1_xboole_0(k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_145])).
% 4.15/2.07  tff(c_163, plain, (~m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', '#skF_2') | v1_xboole_0(k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_94, c_156])).
% 4.15/2.07  tff(c_164, plain, (~m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_163])).
% 4.15/2.07  tff(c_10, plain, (![A_9, B_10]: (m1_subset_1(k1_tops_1(A_9, B_10), k1_zfmisc_1(u1_struct_0(A_9))) | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.15/2.07  tff(c_265, plain, (![B_111, A_112, C_113]: (m1_connsp_2(B_111, A_112, C_113) | ~r2_hidden(C_113, B_111) | ~v3_pre_topc(B_111, A_112) | ~m1_subset_1(C_113, u1_struct_0(A_112)) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112) | ~v2_pre_topc(A_112) | v2_struct_0(A_112))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.15/2.07  tff(c_269, plain, (![B_111]: (m1_connsp_2(B_111, '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', B_111) | ~v3_pre_topc(B_111, '#skF_1') | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_265])).
% 4.15/2.07  tff(c_276, plain, (![B_111]: (m1_connsp_2(B_111, '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', B_111) | ~v3_pre_topc(B_111, '#skF_1') | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_269])).
% 4.15/2.07  tff(c_278, plain, (![B_114]: (m1_connsp_2(B_114, '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', B_114) | ~v3_pre_topc(B_114, '#skF_1') | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_36, c_276])).
% 4.15/2.07  tff(c_282, plain, (![B_10]: (m1_connsp_2(k1_tops_1('#skF_1', B_10), '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_10)) | ~v3_pre_topc(k1_tops_1('#skF_1', B_10), '#skF_1') | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_278])).
% 4.15/2.07  tff(c_475, plain, (![B_135]: (m1_connsp_2(k1_tops_1('#skF_1', B_135), '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_135)) | ~v3_pre_topc(k1_tops_1('#skF_1', B_135), '#skF_1') | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_282])).
% 4.15/2.07  tff(c_486, plain, (m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_28, c_475])).
% 4.15/2.07  tff(c_493, plain, (m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_486])).
% 4.15/2.07  tff(c_494, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_164, c_493])).
% 4.15/2.07  tff(c_497, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_237, c_494])).
% 4.15/2.07  tff(c_503, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_41, c_34, c_32, c_30, c_26, c_497])).
% 4.15/2.07  tff(c_505, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_503])).
% 4.15/2.07  tff(c_506, plain, (v1_xboole_0(k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_163])).
% 4.15/2.07  tff(c_512, plain, (![B_144, A_145, C_146]: (r1_tarski(B_144, k1_tops_1(A_145, C_146)) | ~r1_tarski(B_144, C_146) | ~v3_pre_topc(B_144, A_145) | ~m1_subset_1(C_146, k1_zfmisc_1(u1_struct_0(A_145))) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_pre_topc(A_145))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.15/2.07  tff(c_519, plain, (![B_144]: (r1_tarski(B_144, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(B_144, '#skF_3') | ~v3_pre_topc(B_144, '#skF_1') | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_512])).
% 4.15/2.07  tff(c_525, plain, (![B_147]: (r1_tarski(B_147, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(B_147, '#skF_3') | ~v3_pre_topc(B_147, '#skF_1') | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_519])).
% 4.15/2.07  tff(c_529, plain, (![B_10]: (r1_tarski(k1_tops_1('#skF_1', B_10), k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', B_10), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_10), '#skF_1') | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_525])).
% 4.15/2.07  tff(c_539, plain, (![B_10]: (r1_tarski(k1_tops_1('#skF_1', B_10), k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', B_10), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_10), '#skF_1') | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_529])).
% 4.15/2.07  tff(c_578, plain, (![B_160, A_161, C_162]: (r2_hidden(B_160, k1_tops_1(A_161, C_162)) | ~m1_connsp_2(C_162, A_161, B_160) | ~m1_subset_1(C_162, k1_zfmisc_1(u1_struct_0(A_161))) | ~m1_subset_1(B_160, u1_struct_0(A_161)) | ~l1_pre_topc(A_161) | ~v2_pre_topc(A_161) | v2_struct_0(A_161))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.15/2.07  tff(c_585, plain, (![B_160]: (r2_hidden(B_160, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_160) | ~m1_subset_1(B_160, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_578])).
% 4.15/2.07  tff(c_590, plain, (![B_160]: (r2_hidden(B_160, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_160) | ~m1_subset_1(B_160, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_585])).
% 4.15/2.07  tff(c_592, plain, (![B_163]: (r2_hidden(B_163, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_163) | ~m1_subset_1(B_163, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_36, c_590])).
% 4.15/2.07  tff(c_60, plain, (![C_54, B_55, A_56]: (~v1_xboole_0(C_54) | ~m1_subset_1(B_55, k1_zfmisc_1(C_54)) | ~r2_hidden(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.15/2.07  tff(c_65, plain, (![B_2, A_56, A_1]: (~v1_xboole_0(B_2) | ~r2_hidden(A_56, A_1) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_60])).
% 4.15/2.07  tff(c_614, plain, (![B_2, B_163]: (~v1_xboole_0(B_2) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), B_2) | ~m1_connsp_2('#skF_3', '#skF_1', B_163) | ~m1_subset_1(B_163, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_592, c_65])).
% 4.15/2.07  tff(c_679, plain, (![B_171]: (~m1_connsp_2('#skF_3', '#skF_1', B_171) | ~m1_subset_1(B_171, u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_614])).
% 4.15/2.07  tff(c_685, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_679])).
% 4.15/2.07  tff(c_690, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_685])).
% 4.15/2.07  tff(c_692, plain, (![B_172]: (~v1_xboole_0(B_172) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), B_172))), inference(splitRight, [status(thm)], [c_614])).
% 4.15/2.07  tff(c_696, plain, (~v1_xboole_0(k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_539, c_692])).
% 4.15/2.07  tff(c_715, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_110, c_94, c_506, c_696])).
% 4.15/2.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/2.07  
% 4.15/2.07  Inference rules
% 4.15/2.07  ----------------------
% 4.15/2.07  #Ref     : 0
% 4.15/2.07  #Sup     : 127
% 4.15/2.07  #Fact    : 0
% 4.15/2.07  #Define  : 0
% 4.15/2.07  #Split   : 5
% 4.15/2.07  #Chain   : 0
% 4.15/2.07  #Close   : 0
% 4.15/2.07  
% 4.15/2.07  Ordering : KBO
% 4.15/2.07  
% 4.15/2.07  Simplification rules
% 4.15/2.07  ----------------------
% 4.15/2.07  #Subsume      : 24
% 4.15/2.07  #Demod        : 93
% 4.15/2.07  #Tautology    : 10
% 4.15/2.07  #SimpNegUnit  : 10
% 4.15/2.07  #BackRed      : 0
% 4.15/2.07  
% 4.15/2.07  #Partial instantiations: 0
% 4.15/2.07  #Strategies tried      : 1
% 4.15/2.07  
% 4.15/2.07  Timing (in seconds)
% 4.15/2.07  ----------------------
% 4.15/2.08  Preprocessing        : 0.49
% 4.15/2.08  Parsing              : 0.27
% 4.15/2.08  CNF conversion       : 0.04
% 4.15/2.08  Main loop            : 0.64
% 4.15/2.08  Inferencing          : 0.25
% 4.15/2.08  Reduction            : 0.17
% 4.15/2.08  Demodulation         : 0.12
% 4.15/2.08  BG Simplification    : 0.03
% 4.15/2.08  Subsumption          : 0.13
% 4.15/2.08  Abstraction          : 0.02
% 4.15/2.08  MUC search           : 0.00
% 4.15/2.08  Cooper               : 0.00
% 4.15/2.08  Total                : 1.19
% 4.15/2.08  Index Insertion      : 0.00
% 4.15/2.08  Index Deletion       : 0.00
% 4.15/2.08  Index Matching       : 0.00
% 4.15/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
