%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:09 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 139 expanded)
%              Number of leaves         :   27 (  61 expanded)
%              Depth                    :   12
%              Number of atoms          :  162 ( 557 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   4 average)
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

tff(f_128,negated_conjecture,(
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

tff(f_79,axiom,(
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
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

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

tff(c_26,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_34,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_218,plain,(
    ! [B_82,A_83,C_84] :
      ( r2_hidden(B_82,k1_tops_1(A_83,C_84))
      | ~ m1_connsp_2(C_84,A_83,B_82)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ m1_subset_1(B_82,u1_struct_0(A_83))
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_226,plain,(
    ! [B_82] :
      ( r2_hidden(B_82,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_82)
      | ~ m1_subset_1(B_82,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_218])).

tff(c_231,plain,(
    ! [B_82] :
      ( r2_hidden(B_82,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_82)
      | ~ m1_subset_1(B_82,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_226])).

tff(c_232,plain,(
    ! [B_82] :
      ( r2_hidden(B_82,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_82)
      | ~ m1_subset_1(B_82,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_231])).

tff(c_233,plain,(
    ! [B_85] :
      ( r2_hidden(B_85,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_85)
      | ~ m1_subset_1(B_85,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_231])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_240,plain,(
    ! [B_85] :
      ( ~ v1_xboole_0(k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_85)
      | ~ m1_subset_1(B_85,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_233,c_2])).

tff(c_241,plain,(
    ~ v1_xboole_0(k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_240])).

tff(c_132,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(k1_tops_1(A_70,B_71),B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_140,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_132])).

tff(c_145,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_140])).

tff(c_152,plain,(
    ! [A_72,B_73] :
      ( v3_pre_topc(k1_tops_1(A_72,B_73),A_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72)
      | ~ v2_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_160,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_152])).

tff(c_165,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_160])).

tff(c_56,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(A_50,B_51)
      | ~ m1_subset_1(A_50,k1_zfmisc_1(B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_64,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_56])).

tff(c_66,plain,(
    ! [A_52,C_53,B_54] :
      ( r1_tarski(A_52,C_53)
      | ~ r1_tarski(B_54,C_53)
      | ~ r1_tarski(A_52,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_69,plain,(
    ! [A_52] :
      ( r1_tarski(A_52,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_52,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_64,c_66])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_400,plain,(
    ! [B_112,A_113,C_114] :
      ( m1_connsp_2(B_112,A_113,C_114)
      | ~ r2_hidden(C_114,B_112)
      | ~ v3_pre_topc(B_112,A_113)
      | ~ m1_subset_1(C_114,u1_struct_0(A_113))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113)
      | ~ v2_pre_topc(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_410,plain,(
    ! [B_112] :
      ( m1_connsp_2(B_112,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_112)
      | ~ v3_pre_topc(B_112,'#skF_2')
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_400])).

tff(c_419,plain,(
    ! [B_112] :
      ( m1_connsp_2(B_112,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_112)
      | ~ v3_pre_topc(B_112,'#skF_2')
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_410])).

tff(c_421,plain,(
    ! [B_115] :
      ( m1_connsp_2(B_115,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_115)
      | ~ v3_pre_topc(B_115,'#skF_2')
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_419])).

tff(c_442,plain,(
    ! [A_116] :
      ( m1_connsp_2(A_116,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',A_116)
      | ~ v3_pre_topc(A_116,'#skF_2')
      | ~ r1_tarski(A_116,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_10,c_421])).

tff(c_471,plain,(
    ! [A_117] :
      ( m1_connsp_2(A_117,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',A_117)
      | ~ v3_pre_topc(A_117,'#skF_2')
      | ~ r1_tarski(A_117,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_69,c_442])).

tff(c_44,plain,(
    ! [D_49] :
      ( ~ r1_tarski(D_49,'#skF_4')
      | ~ v3_pre_topc(D_49,'#skF_2')
      | ~ m1_connsp_2(D_49,'#skF_2','#skF_3')
      | ~ m1_subset_1(D_49,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v1_xboole_0(D_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_86,plain,(
    ! [A_63] :
      ( ~ r1_tarski(A_63,'#skF_4')
      | ~ v3_pre_topc(A_63,'#skF_2')
      | ~ m1_connsp_2(A_63,'#skF_2','#skF_3')
      | v1_xboole_0(A_63)
      | ~ r1_tarski(A_63,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_10,c_44])).

tff(c_93,plain,(
    ! [A_52] :
      ( ~ v3_pre_topc(A_52,'#skF_2')
      | ~ m1_connsp_2(A_52,'#skF_2','#skF_3')
      | v1_xboole_0(A_52)
      | ~ r1_tarski(A_52,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_69,c_86])).

tff(c_498,plain,(
    ! [A_120] :
      ( v1_xboole_0(A_120)
      | ~ r2_hidden('#skF_3',A_120)
      | ~ v3_pre_topc(A_120,'#skF_2')
      | ~ r1_tarski(A_120,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_471,c_93])).

tff(c_505,plain,
    ( v1_xboole_0(k1_tops_1('#skF_2','#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_165,c_498])).

tff(c_511,plain,
    ( v1_xboole_0(k1_tops_1('#skF_2','#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_505])).

tff(c_512,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_241,c_511])).

tff(c_515,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_232,c_512])).

tff(c_519,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_515])).

tff(c_522,plain,(
    ! [B_121] :
      ( ~ m1_connsp_2('#skF_4','#skF_2',B_121)
      | ~ m1_subset_1(B_121,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_240])).

tff(c_532,plain,(
    ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_522])).

tff(c_538,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_532])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:53:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.42  
% 2.63/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.42  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.63/1.42  
% 2.63/1.42  %Foreground sorts:
% 2.63/1.42  
% 2.63/1.42  
% 2.63/1.42  %Background operators:
% 2.63/1.42  
% 2.63/1.42  
% 2.63/1.42  %Foreground operators:
% 2.63/1.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.63/1.42  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.63/1.42  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.63/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.63/1.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.63/1.42  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.63/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.42  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.63/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.63/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.63/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.63/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.63/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.42  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.63/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.63/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.63/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.63/1.42  
% 2.63/1.43  tff(f_128, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(C, A, B) & (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~((m1_connsp_2(D, A, B) & v3_pre_topc(D, A)) & r1_tarski(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_connsp_2)).
% 2.63/1.43  tff(f_79, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 2.63/1.43  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.63/1.43  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 2.63/1.43  tff(f_55, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 2.63/1.43  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.63/1.43  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.63/1.43  tff(f_98, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 2.63/1.43  tff(c_26, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.63/1.43  tff(c_30, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.63/1.43  tff(c_36, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.63/1.43  tff(c_34, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.63/1.43  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.63/1.43  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.63/1.43  tff(c_218, plain, (![B_82, A_83, C_84]: (r2_hidden(B_82, k1_tops_1(A_83, C_84)) | ~m1_connsp_2(C_84, A_83, B_82) | ~m1_subset_1(C_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~m1_subset_1(B_82, u1_struct_0(A_83)) | ~l1_pre_topc(A_83) | ~v2_pre_topc(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.63/1.43  tff(c_226, plain, (![B_82]: (r2_hidden(B_82, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_82) | ~m1_subset_1(B_82, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_218])).
% 2.63/1.43  tff(c_231, plain, (![B_82]: (r2_hidden(B_82, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_82) | ~m1_subset_1(B_82, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_226])).
% 2.63/1.43  tff(c_232, plain, (![B_82]: (r2_hidden(B_82, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_82) | ~m1_subset_1(B_82, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_36, c_231])).
% 2.63/1.43  tff(c_233, plain, (![B_85]: (r2_hidden(B_85, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_85) | ~m1_subset_1(B_85, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_36, c_231])).
% 2.63/1.43  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.63/1.43  tff(c_240, plain, (![B_85]: (~v1_xboole_0(k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_85) | ~m1_subset_1(B_85, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_233, c_2])).
% 2.63/1.43  tff(c_241, plain, (~v1_xboole_0(k1_tops_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_240])).
% 2.63/1.43  tff(c_132, plain, (![A_70, B_71]: (r1_tarski(k1_tops_1(A_70, B_71), B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.63/1.43  tff(c_140, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_132])).
% 2.63/1.43  tff(c_145, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_140])).
% 2.63/1.43  tff(c_152, plain, (![A_72, B_73]: (v3_pre_topc(k1_tops_1(A_72, B_73), A_72) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72) | ~v2_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.63/1.43  tff(c_160, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_152])).
% 2.63/1.43  tff(c_165, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_160])).
% 2.63/1.43  tff(c_56, plain, (![A_50, B_51]: (r1_tarski(A_50, B_51) | ~m1_subset_1(A_50, k1_zfmisc_1(B_51)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.63/1.43  tff(c_64, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_56])).
% 2.63/1.43  tff(c_66, plain, (![A_52, C_53, B_54]: (r1_tarski(A_52, C_53) | ~r1_tarski(B_54, C_53) | ~r1_tarski(A_52, B_54))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.63/1.43  tff(c_69, plain, (![A_52]: (r1_tarski(A_52, u1_struct_0('#skF_2')) | ~r1_tarski(A_52, '#skF_4'))), inference(resolution, [status(thm)], [c_64, c_66])).
% 2.63/1.43  tff(c_10, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.63/1.43  tff(c_400, plain, (![B_112, A_113, C_114]: (m1_connsp_2(B_112, A_113, C_114) | ~r2_hidden(C_114, B_112) | ~v3_pre_topc(B_112, A_113) | ~m1_subset_1(C_114, u1_struct_0(A_113)) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_pre_topc(A_113) | ~v2_pre_topc(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.63/1.43  tff(c_410, plain, (![B_112]: (m1_connsp_2(B_112, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_112) | ~v3_pre_topc(B_112, '#skF_2') | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_400])).
% 2.63/1.43  tff(c_419, plain, (![B_112]: (m1_connsp_2(B_112, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_112) | ~v3_pre_topc(B_112, '#skF_2') | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_410])).
% 2.63/1.43  tff(c_421, plain, (![B_115]: (m1_connsp_2(B_115, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_115) | ~v3_pre_topc(B_115, '#skF_2') | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_36, c_419])).
% 2.63/1.43  tff(c_442, plain, (![A_116]: (m1_connsp_2(A_116, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', A_116) | ~v3_pre_topc(A_116, '#skF_2') | ~r1_tarski(A_116, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_10, c_421])).
% 2.63/1.43  tff(c_471, plain, (![A_117]: (m1_connsp_2(A_117, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', A_117) | ~v3_pre_topc(A_117, '#skF_2') | ~r1_tarski(A_117, '#skF_4'))), inference(resolution, [status(thm)], [c_69, c_442])).
% 2.63/1.43  tff(c_44, plain, (![D_49]: (~r1_tarski(D_49, '#skF_4') | ~v3_pre_topc(D_49, '#skF_2') | ~m1_connsp_2(D_49, '#skF_2', '#skF_3') | ~m1_subset_1(D_49, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(D_49))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.63/1.43  tff(c_86, plain, (![A_63]: (~r1_tarski(A_63, '#skF_4') | ~v3_pre_topc(A_63, '#skF_2') | ~m1_connsp_2(A_63, '#skF_2', '#skF_3') | v1_xboole_0(A_63) | ~r1_tarski(A_63, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_10, c_44])).
% 2.63/1.43  tff(c_93, plain, (![A_52]: (~v3_pre_topc(A_52, '#skF_2') | ~m1_connsp_2(A_52, '#skF_2', '#skF_3') | v1_xboole_0(A_52) | ~r1_tarski(A_52, '#skF_4'))), inference(resolution, [status(thm)], [c_69, c_86])).
% 2.63/1.43  tff(c_498, plain, (![A_120]: (v1_xboole_0(A_120) | ~r2_hidden('#skF_3', A_120) | ~v3_pre_topc(A_120, '#skF_2') | ~r1_tarski(A_120, '#skF_4'))), inference(resolution, [status(thm)], [c_471, c_93])).
% 2.63/1.43  tff(c_505, plain, (v1_xboole_0(k1_tops_1('#skF_2', '#skF_4')) | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_165, c_498])).
% 2.63/1.43  tff(c_511, plain, (v1_xboole_0(k1_tops_1('#skF_2', '#skF_4')) | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_505])).
% 2.63/1.43  tff(c_512, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_241, c_511])).
% 2.63/1.43  tff(c_515, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_232, c_512])).
% 2.63/1.43  tff(c_519, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_515])).
% 2.63/1.43  tff(c_522, plain, (![B_121]: (~m1_connsp_2('#skF_4', '#skF_2', B_121) | ~m1_subset_1(B_121, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_240])).
% 2.63/1.43  tff(c_532, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_522])).
% 2.63/1.43  tff(c_538, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_532])).
% 2.63/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.43  
% 2.63/1.43  Inference rules
% 2.63/1.43  ----------------------
% 2.63/1.43  #Ref     : 0
% 2.63/1.43  #Sup     : 103
% 2.63/1.43  #Fact    : 0
% 2.63/1.43  #Define  : 0
% 2.63/1.43  #Split   : 3
% 2.63/1.43  #Chain   : 0
% 2.63/1.43  #Close   : 0
% 2.63/1.43  
% 2.63/1.43  Ordering : KBO
% 2.63/1.43  
% 2.63/1.43  Simplification rules
% 2.63/1.43  ----------------------
% 2.63/1.43  #Subsume      : 16
% 2.63/1.43  #Demod        : 31
% 2.63/1.43  #Tautology    : 6
% 2.63/1.43  #SimpNegUnit  : 5
% 2.63/1.43  #BackRed      : 0
% 2.63/1.43  
% 2.63/1.43  #Partial instantiations: 0
% 2.63/1.43  #Strategies tried      : 1
% 2.63/1.43  
% 2.63/1.44  Timing (in seconds)
% 2.63/1.44  ----------------------
% 2.63/1.44  Preprocessing        : 0.32
% 2.63/1.44  Parsing              : 0.19
% 2.63/1.44  CNF conversion       : 0.02
% 2.63/1.44  Main loop            : 0.32
% 2.63/1.44  Inferencing          : 0.12
% 2.63/1.44  Reduction            : 0.08
% 2.63/1.44  Demodulation         : 0.06
% 2.63/1.44  BG Simplification    : 0.02
% 2.63/1.44  Subsumption          : 0.07
% 2.63/1.44  Abstraction          : 0.01
% 2.63/1.44  MUC search           : 0.00
% 2.63/1.44  Cooper               : 0.00
% 2.63/1.44  Total                : 0.67
% 2.63/1.44  Index Insertion      : 0.00
% 2.63/1.44  Index Deletion       : 0.00
% 2.63/1.44  Index Matching       : 0.00
% 2.63/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
