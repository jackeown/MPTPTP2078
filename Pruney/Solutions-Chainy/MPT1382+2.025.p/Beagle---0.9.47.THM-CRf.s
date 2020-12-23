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
% DateTime   : Thu Dec  3 10:24:10 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :  103 (1222 expanded)
%              Number of leaves         :   27 ( 440 expanded)
%              Depth                    :   27
%              Number of atoms          :  294 (5411 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_connsp_2)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_80,axiom,(
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

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_30,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_111,plain,(
    ! [A_74,B_75] :
      ( v3_pre_topc(k1_tops_1(A_74,B_75),A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_116,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_111])).

tff(c_120,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_116])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_37,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,B_48)
      | ~ m1_subset_1(A_47,k1_zfmisc_1(B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_41,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_37])).

tff(c_26,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_216,plain,(
    ! [B_99,A_100,C_101] :
      ( r2_hidden(B_99,k1_tops_1(A_100,C_101))
      | ~ m1_connsp_2(C_101,A_100,B_99)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ m1_subset_1(B_99,u1_struct_0(A_100))
      | ~ l1_pre_topc(A_100)
      | ~ v2_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_222,plain,(
    ! [B_99,A_100,A_4] :
      ( r2_hidden(B_99,k1_tops_1(A_100,A_4))
      | ~ m1_connsp_2(A_4,A_100,B_99)
      | ~ m1_subset_1(B_99,u1_struct_0(A_100))
      | ~ l1_pre_topc(A_100)
      | ~ v2_pre_topc(A_100)
      | v2_struct_0(A_100)
      | ~ r1_tarski(A_4,u1_struct_0(A_100)) ) ),
    inference(resolution,[status(thm)],[c_6,c_216])).

tff(c_94,plain,(
    ! [A_71,B_72] :
      ( r1_tarski(k1_tops_1(A_71,B_72),B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_99,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_94])).

tff(c_103,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_99])).

tff(c_68,plain,(
    ! [A_55,C_56,B_57] :
      ( r1_tarski(A_55,C_56)
      | ~ r1_tarski(B_57,C_56)
      | ~ r1_tarski(A_55,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_71,plain,(
    ! [A_55] :
      ( r1_tarski(A_55,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_55,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_41,c_68])).

tff(c_330,plain,(
    ! [B_115,A_116,C_117] :
      ( m1_connsp_2(B_115,A_116,C_117)
      | ~ r2_hidden(C_117,B_115)
      | ~ v3_pre_topc(B_115,A_116)
      | ~ m1_subset_1(C_117,u1_struct_0(A_116))
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116)
      | v2_struct_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_334,plain,(
    ! [B_115] :
      ( m1_connsp_2(B_115,'#skF_1','#skF_2')
      | ~ r2_hidden('#skF_2',B_115)
      | ~ v3_pre_topc(B_115,'#skF_1')
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_330])).

tff(c_341,plain,(
    ! [B_115] :
      ( m1_connsp_2(B_115,'#skF_1','#skF_2')
      | ~ r2_hidden('#skF_2',B_115)
      | ~ v3_pre_topc(B_115,'#skF_1')
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_334])).

tff(c_343,plain,(
    ! [B_118] :
      ( m1_connsp_2(B_118,'#skF_1','#skF_2')
      | ~ r2_hidden('#skF_2',B_118)
      | ~ v3_pre_topc(B_118,'#skF_1')
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_341])).

tff(c_354,plain,(
    ! [A_119] :
      ( m1_connsp_2(A_119,'#skF_1','#skF_2')
      | ~ r2_hidden('#skF_2',A_119)
      | ~ v3_pre_topc(A_119,'#skF_1')
      | ~ r1_tarski(A_119,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_6,c_343])).

tff(c_378,plain,(
    ! [A_120] :
      ( m1_connsp_2(A_120,'#skF_1','#skF_2')
      | ~ r2_hidden('#skF_2',A_120)
      | ~ v3_pre_topc(A_120,'#skF_1')
      | ~ r1_tarski(A_120,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_71,c_354])).

tff(c_47,plain,(
    ! [D_51] :
      ( ~ r1_tarski(D_51,'#skF_3')
      | ~ v3_pre_topc(D_51,'#skF_1')
      | ~ m1_connsp_2(D_51,'#skF_1','#skF_2')
      | ~ m1_subset_1(D_51,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v1_xboole_0(D_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_122,plain,(
    ! [A_76] :
      ( ~ r1_tarski(A_76,'#skF_3')
      | ~ v3_pre_topc(A_76,'#skF_1')
      | ~ m1_connsp_2(A_76,'#skF_1','#skF_2')
      | v1_xboole_0(A_76)
      | ~ r1_tarski(A_76,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_6,c_47])).

tff(c_129,plain,(
    ! [A_55] :
      ( ~ v3_pre_topc(A_55,'#skF_1')
      | ~ m1_connsp_2(A_55,'#skF_1','#skF_2')
      | v1_xboole_0(A_55)
      | ~ r1_tarski(A_55,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_71,c_122])).

tff(c_426,plain,(
    ! [A_122] :
      ( v1_xboole_0(A_122)
      | ~ r2_hidden('#skF_2',A_122)
      | ~ v3_pre_topc(A_122,'#skF_1')
      | ~ r1_tarski(A_122,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_378,c_129])).

tff(c_433,plain,
    ( v1_xboole_0(k1_tops_1('#skF_1','#skF_3'))
    | ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_120,c_426])).

tff(c_439,plain,
    ( v1_xboole_0(k1_tops_1('#skF_1','#skF_3'))
    | ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_433])).

tff(c_440,plain,(
    ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_439])).

tff(c_443,plain,
    ( ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_222,c_440])).

tff(c_449,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_34,c_32,c_30,c_26,c_443])).

tff(c_451,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_449])).

tff(c_453,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_439])).

tff(c_20,plain,(
    ! [C_27,A_24,B_25] :
      ( m1_subset_1(C_27,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ m1_connsp_2(C_27,A_24,B_25)
      | ~ m1_subset_1(B_25,u1_struct_0(A_24))
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_384,plain,(
    ! [A_120] :
      ( m1_subset_1(A_120,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ r2_hidden('#skF_2',A_120)
      | ~ v3_pre_topc(A_120,'#skF_1')
      | ~ r1_tarski(A_120,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_378,c_20])).

tff(c_392,plain,(
    ! [A_120] :
      ( m1_subset_1(A_120,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v2_struct_0('#skF_1')
      | ~ r2_hidden('#skF_2',A_120)
      | ~ v3_pre_topc(A_120,'#skF_1')
      | ~ r1_tarski(A_120,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_384])).

tff(c_395,plain,(
    ! [A_121] :
      ( m1_subset_1(A_121,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r2_hidden('#skF_2',A_121)
      | ~ v3_pre_topc(A_121,'#skF_1')
      | ~ r1_tarski(A_121,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_392])).

tff(c_14,plain,(
    ! [A_14,B_16] :
      ( r1_tarski(k1_tops_1(A_14,B_16),B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_404,plain,(
    ! [A_121] :
      ( r1_tarski(k1_tops_1('#skF_1',A_121),A_121)
      | ~ l1_pre_topc('#skF_1')
      | ~ r2_hidden('#skF_2',A_121)
      | ~ v3_pre_topc(A_121,'#skF_1')
      | ~ r1_tarski(A_121,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_395,c_14])).

tff(c_509,plain,(
    ! [A_127] :
      ( r1_tarski(k1_tops_1('#skF_1',A_127),A_127)
      | ~ r2_hidden('#skF_2',A_127)
      | ~ v3_pre_topc(A_127,'#skF_1')
      | ~ r1_tarski(A_127,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_404])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_109,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,'#skF_3')
      | ~ r1_tarski(A_1,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_103,c_2])).

tff(c_537,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_3')),'#skF_3')
    | ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_509,c_109])).

tff(c_552,plain,(
    r1_tarski(k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_120,c_453,c_537])).

tff(c_117,plain,(
    ! [A_74,A_4] :
      ( v3_pre_topc(k1_tops_1(A_74,A_4),A_74)
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74)
      | ~ r1_tarski(A_4,u1_struct_0(A_74)) ) ),
    inference(resolution,[status(thm)],[c_6,c_111])).

tff(c_430,plain,(
    ! [A_4] :
      ( v1_xboole_0(k1_tops_1('#skF_1',A_4))
      | ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_4))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_4),'#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_4,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_117,c_426])).

tff(c_734,plain,(
    ! [A_144] :
      ( v1_xboole_0(k1_tops_1('#skF_1',A_144))
      | ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_144))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_144),'#skF_3')
      | ~ r1_tarski(A_144,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_430])).

tff(c_745,plain,(
    ! [A_4] :
      ( v1_xboole_0(k1_tops_1('#skF_1',A_4))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_4),'#skF_3')
      | ~ m1_connsp_2(A_4,'#skF_1','#skF_2')
      | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ r1_tarski(A_4,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_222,c_734])).

tff(c_758,plain,(
    ! [A_4] :
      ( v1_xboole_0(k1_tops_1('#skF_1',A_4))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_4),'#skF_3')
      | ~ m1_connsp_2(A_4,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1')
      | ~ r1_tarski(A_4,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_745])).

tff(c_763,plain,(
    ! [A_145] :
      ( v1_xboole_0(k1_tops_1('#skF_1',A_145))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_145),'#skF_3')
      | ~ m1_connsp_2(A_145,'#skF_1','#skF_2')
      | ~ r1_tarski(A_145,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_758])).

tff(c_786,plain,
    ( v1_xboole_0(k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1','#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_552,c_763])).

tff(c_818,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_786])).

tff(c_827,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_818])).

tff(c_835,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_827])).

tff(c_837,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_786])).

tff(c_351,plain,(
    ! [A_4] :
      ( m1_connsp_2(A_4,'#skF_1','#skF_2')
      | ~ r2_hidden('#skF_2',A_4)
      | ~ v3_pre_topc(A_4,'#skF_1')
      | ~ r1_tarski(A_4,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_6,c_343])).

tff(c_847,plain,
    ( m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1','#skF_2')
    | ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_837,c_351])).

tff(c_868,plain,(
    m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_453,c_847])).

tff(c_452,plain,(
    v1_xboole_0(k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_439])).

tff(c_875,plain,
    ( m1_subset_1(k1_tops_1('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_868,c_20])).

tff(c_881,plain,
    ( m1_subset_1(k1_tops_1('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_875])).

tff(c_882,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_881])).

tff(c_943,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_3')),k1_tops_1('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_882,c_14])).

tff(c_966,plain,(
    r1_tarski(k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_3')),k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_943])).

tff(c_320,plain,(
    ! [B_112,A_113,A_114] :
      ( r2_hidden(B_112,k1_tops_1(A_113,A_114))
      | ~ m1_connsp_2(A_114,A_113,B_112)
      | ~ m1_subset_1(B_112,u1_struct_0(A_113))
      | ~ l1_pre_topc(A_113)
      | ~ v2_pre_topc(A_113)
      | v2_struct_0(A_113)
      | ~ r1_tarski(A_114,u1_struct_0(A_113)) ) ),
    inference(resolution,[status(thm)],[c_6,c_216])).

tff(c_60,plain,(
    ! [C_52,B_53,A_54] :
      ( ~ v1_xboole_0(C_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(C_52))
      | ~ r2_hidden(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_65,plain,(
    ! [B_5,A_54,A_4] :
      ( ~ v1_xboole_0(B_5)
      | ~ r2_hidden(A_54,A_4)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_60])).

tff(c_329,plain,(
    ! [B_5,A_113,A_114,B_112] :
      ( ~ v1_xboole_0(B_5)
      | ~ r1_tarski(k1_tops_1(A_113,A_114),B_5)
      | ~ m1_connsp_2(A_114,A_113,B_112)
      | ~ m1_subset_1(B_112,u1_struct_0(A_113))
      | ~ l1_pre_topc(A_113)
      | ~ v2_pre_topc(A_113)
      | v2_struct_0(A_113)
      | ~ r1_tarski(A_114,u1_struct_0(A_113)) ) ),
    inference(resolution,[status(thm)],[c_320,c_65])).

tff(c_1081,plain,(
    ! [B_112] :
      ( ~ v1_xboole_0(k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1',B_112)
      | ~ m1_subset_1(B_112,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_966,c_329])).

tff(c_1105,plain,(
    ! [B_112] :
      ( ~ m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1',B_112)
      | ~ m1_subset_1(B_112,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_837,c_34,c_32,c_452,c_1081])).

tff(c_1119,plain,(
    ! [B_155] :
      ( ~ m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1',B_155)
      | ~ m1_subset_1(B_155,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1105])).

tff(c_1122,plain,(
    ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_868,c_1119])).

tff(c_1134,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1122])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:04:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.60  
% 3.20/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.61  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.20/1.61  
% 3.20/1.61  %Foreground sorts:
% 3.20/1.61  
% 3.20/1.61  
% 3.20/1.61  %Background operators:
% 3.20/1.61  
% 3.20/1.61  
% 3.20/1.61  %Foreground operators:
% 3.20/1.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.20/1.61  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.20/1.61  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.20/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.20/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.20/1.61  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.20/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.20/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.20/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.20/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.20/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.61  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.20/1.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.20/1.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.20/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.20/1.61  
% 3.56/1.63  tff(f_143, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(C, A, B) & (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~((m1_connsp_2(D, A, B) & v3_pre_topc(D, A)) & r1_tarski(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_connsp_2)).
% 3.56/1.63  tff(f_56, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.56/1.63  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.56/1.63  tff(f_80, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 3.56/1.63  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 3.56/1.63  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.56/1.63  tff(f_113, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_connsp_2)).
% 3.56/1.63  tff(f_94, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 3.56/1.63  tff(f_48, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.56/1.63  tff(c_30, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.56/1.63  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.56/1.63  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.56/1.63  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.56/1.63  tff(c_111, plain, (![A_74, B_75]: (v3_pre_topc(k1_tops_1(A_74, B_75), A_74) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.56/1.63  tff(c_116, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_111])).
% 3.56/1.63  tff(c_120, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_116])).
% 3.56/1.63  tff(c_36, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.56/1.63  tff(c_37, plain, (![A_47, B_48]: (r1_tarski(A_47, B_48) | ~m1_subset_1(A_47, k1_zfmisc_1(B_48)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.56/1.63  tff(c_41, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_37])).
% 3.56/1.63  tff(c_26, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.56/1.63  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.56/1.63  tff(c_216, plain, (![B_99, A_100, C_101]: (r2_hidden(B_99, k1_tops_1(A_100, C_101)) | ~m1_connsp_2(C_101, A_100, B_99) | ~m1_subset_1(C_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~m1_subset_1(B_99, u1_struct_0(A_100)) | ~l1_pre_topc(A_100) | ~v2_pre_topc(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.56/1.63  tff(c_222, plain, (![B_99, A_100, A_4]: (r2_hidden(B_99, k1_tops_1(A_100, A_4)) | ~m1_connsp_2(A_4, A_100, B_99) | ~m1_subset_1(B_99, u1_struct_0(A_100)) | ~l1_pre_topc(A_100) | ~v2_pre_topc(A_100) | v2_struct_0(A_100) | ~r1_tarski(A_4, u1_struct_0(A_100)))), inference(resolution, [status(thm)], [c_6, c_216])).
% 3.56/1.63  tff(c_94, plain, (![A_71, B_72]: (r1_tarski(k1_tops_1(A_71, B_72), B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.56/1.63  tff(c_99, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_94])).
% 3.56/1.63  tff(c_103, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_99])).
% 3.56/1.63  tff(c_68, plain, (![A_55, C_56, B_57]: (r1_tarski(A_55, C_56) | ~r1_tarski(B_57, C_56) | ~r1_tarski(A_55, B_57))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.56/1.63  tff(c_71, plain, (![A_55]: (r1_tarski(A_55, u1_struct_0('#skF_1')) | ~r1_tarski(A_55, '#skF_3'))), inference(resolution, [status(thm)], [c_41, c_68])).
% 3.56/1.63  tff(c_330, plain, (![B_115, A_116, C_117]: (m1_connsp_2(B_115, A_116, C_117) | ~r2_hidden(C_117, B_115) | ~v3_pre_topc(B_115, A_116) | ~m1_subset_1(C_117, u1_struct_0(A_116)) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116) | ~v2_pre_topc(A_116) | v2_struct_0(A_116))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.56/1.63  tff(c_334, plain, (![B_115]: (m1_connsp_2(B_115, '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', B_115) | ~v3_pre_topc(B_115, '#skF_1') | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_330])).
% 3.56/1.63  tff(c_341, plain, (![B_115]: (m1_connsp_2(B_115, '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', B_115) | ~v3_pre_topc(B_115, '#skF_1') | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_334])).
% 3.56/1.63  tff(c_343, plain, (![B_118]: (m1_connsp_2(B_118, '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', B_118) | ~v3_pre_topc(B_118, '#skF_1') | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_36, c_341])).
% 3.56/1.63  tff(c_354, plain, (![A_119]: (m1_connsp_2(A_119, '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', A_119) | ~v3_pre_topc(A_119, '#skF_1') | ~r1_tarski(A_119, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_343])).
% 3.56/1.63  tff(c_378, plain, (![A_120]: (m1_connsp_2(A_120, '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', A_120) | ~v3_pre_topc(A_120, '#skF_1') | ~r1_tarski(A_120, '#skF_3'))), inference(resolution, [status(thm)], [c_71, c_354])).
% 3.56/1.63  tff(c_47, plain, (![D_51]: (~r1_tarski(D_51, '#skF_3') | ~v3_pre_topc(D_51, '#skF_1') | ~m1_connsp_2(D_51, '#skF_1', '#skF_2') | ~m1_subset_1(D_51, k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(D_51))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.56/1.63  tff(c_122, plain, (![A_76]: (~r1_tarski(A_76, '#skF_3') | ~v3_pre_topc(A_76, '#skF_1') | ~m1_connsp_2(A_76, '#skF_1', '#skF_2') | v1_xboole_0(A_76) | ~r1_tarski(A_76, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_47])).
% 3.56/1.63  tff(c_129, plain, (![A_55]: (~v3_pre_topc(A_55, '#skF_1') | ~m1_connsp_2(A_55, '#skF_1', '#skF_2') | v1_xboole_0(A_55) | ~r1_tarski(A_55, '#skF_3'))), inference(resolution, [status(thm)], [c_71, c_122])).
% 3.56/1.63  tff(c_426, plain, (![A_122]: (v1_xboole_0(A_122) | ~r2_hidden('#skF_2', A_122) | ~v3_pre_topc(A_122, '#skF_1') | ~r1_tarski(A_122, '#skF_3'))), inference(resolution, [status(thm)], [c_378, c_129])).
% 3.56/1.63  tff(c_433, plain, (v1_xboole_0(k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_120, c_426])).
% 3.56/1.63  tff(c_439, plain, (v1_xboole_0(k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_433])).
% 3.56/1.63  tff(c_440, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_439])).
% 3.56/1.63  tff(c_443, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_222, c_440])).
% 3.56/1.63  tff(c_449, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_41, c_34, c_32, c_30, c_26, c_443])).
% 3.56/1.63  tff(c_451, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_449])).
% 3.56/1.63  tff(c_453, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_439])).
% 3.56/1.63  tff(c_20, plain, (![C_27, A_24, B_25]: (m1_subset_1(C_27, k1_zfmisc_1(u1_struct_0(A_24))) | ~m1_connsp_2(C_27, A_24, B_25) | ~m1_subset_1(B_25, u1_struct_0(A_24)) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.56/1.63  tff(c_384, plain, (![A_120]: (m1_subset_1(A_120, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~r2_hidden('#skF_2', A_120) | ~v3_pre_topc(A_120, '#skF_1') | ~r1_tarski(A_120, '#skF_3'))), inference(resolution, [status(thm)], [c_378, c_20])).
% 3.56/1.63  tff(c_392, plain, (![A_120]: (m1_subset_1(A_120, k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1') | ~r2_hidden('#skF_2', A_120) | ~v3_pre_topc(A_120, '#skF_1') | ~r1_tarski(A_120, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_384])).
% 3.56/1.63  tff(c_395, plain, (![A_121]: (m1_subset_1(A_121, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r2_hidden('#skF_2', A_121) | ~v3_pre_topc(A_121, '#skF_1') | ~r1_tarski(A_121, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_36, c_392])).
% 3.56/1.63  tff(c_14, plain, (![A_14, B_16]: (r1_tarski(k1_tops_1(A_14, B_16), B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.56/1.63  tff(c_404, plain, (![A_121]: (r1_tarski(k1_tops_1('#skF_1', A_121), A_121) | ~l1_pre_topc('#skF_1') | ~r2_hidden('#skF_2', A_121) | ~v3_pre_topc(A_121, '#skF_1') | ~r1_tarski(A_121, '#skF_3'))), inference(resolution, [status(thm)], [c_395, c_14])).
% 3.56/1.63  tff(c_509, plain, (![A_127]: (r1_tarski(k1_tops_1('#skF_1', A_127), A_127) | ~r2_hidden('#skF_2', A_127) | ~v3_pre_topc(A_127, '#skF_1') | ~r1_tarski(A_127, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_404])).
% 3.56/1.63  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.56/1.63  tff(c_109, plain, (![A_1]: (r1_tarski(A_1, '#skF_3') | ~r1_tarski(A_1, k1_tops_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_103, c_2])).
% 3.56/1.63  tff(c_537, plain, (r1_tarski(k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_3')), '#skF_3') | ~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_509, c_109])).
% 3.56/1.63  tff(c_552, plain, (r1_tarski(k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_120, c_453, c_537])).
% 3.56/1.63  tff(c_117, plain, (![A_74, A_4]: (v3_pre_topc(k1_tops_1(A_74, A_4), A_74) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74) | ~r1_tarski(A_4, u1_struct_0(A_74)))), inference(resolution, [status(thm)], [c_6, c_111])).
% 3.56/1.63  tff(c_430, plain, (![A_4]: (v1_xboole_0(k1_tops_1('#skF_1', A_4)) | ~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_4)) | ~r1_tarski(k1_tops_1('#skF_1', A_4), '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_4, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_117, c_426])).
% 3.56/1.63  tff(c_734, plain, (![A_144]: (v1_xboole_0(k1_tops_1('#skF_1', A_144)) | ~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_144)) | ~r1_tarski(k1_tops_1('#skF_1', A_144), '#skF_3') | ~r1_tarski(A_144, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_430])).
% 3.56/1.63  tff(c_745, plain, (![A_4]: (v1_xboole_0(k1_tops_1('#skF_1', A_4)) | ~r1_tarski(k1_tops_1('#skF_1', A_4), '#skF_3') | ~m1_connsp_2(A_4, '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~r1_tarski(A_4, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_222, c_734])).
% 3.56/1.63  tff(c_758, plain, (![A_4]: (v1_xboole_0(k1_tops_1('#skF_1', A_4)) | ~r1_tarski(k1_tops_1('#skF_1', A_4), '#skF_3') | ~m1_connsp_2(A_4, '#skF_1', '#skF_2') | v2_struct_0('#skF_1') | ~r1_tarski(A_4, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_745])).
% 3.56/1.63  tff(c_763, plain, (![A_145]: (v1_xboole_0(k1_tops_1('#skF_1', A_145)) | ~r1_tarski(k1_tops_1('#skF_1', A_145), '#skF_3') | ~m1_connsp_2(A_145, '#skF_1', '#skF_2') | ~r1_tarski(A_145, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_36, c_758])).
% 3.56/1.63  tff(c_786, plain, (v1_xboole_0(k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_552, c_763])).
% 3.56/1.63  tff(c_818, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_786])).
% 3.56/1.63  tff(c_827, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_71, c_818])).
% 3.56/1.63  tff(c_835, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_827])).
% 3.56/1.63  tff(c_837, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_786])).
% 3.56/1.63  tff(c_351, plain, (![A_4]: (m1_connsp_2(A_4, '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', A_4) | ~v3_pre_topc(A_4, '#skF_1') | ~r1_tarski(A_4, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_343])).
% 3.56/1.63  tff(c_847, plain, (m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_837, c_351])).
% 3.56/1.63  tff(c_868, plain, (m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_453, c_847])).
% 3.56/1.63  tff(c_452, plain, (v1_xboole_0(k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_439])).
% 3.56/1.63  tff(c_875, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_868, c_20])).
% 3.56/1.63  tff(c_881, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_875])).
% 3.56/1.63  tff(c_882, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_36, c_881])).
% 3.56/1.63  tff(c_943, plain, (r1_tarski(k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_3')), k1_tops_1('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_882, c_14])).
% 3.56/1.63  tff(c_966, plain, (r1_tarski(k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_3')), k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_943])).
% 3.56/1.63  tff(c_320, plain, (![B_112, A_113, A_114]: (r2_hidden(B_112, k1_tops_1(A_113, A_114)) | ~m1_connsp_2(A_114, A_113, B_112) | ~m1_subset_1(B_112, u1_struct_0(A_113)) | ~l1_pre_topc(A_113) | ~v2_pre_topc(A_113) | v2_struct_0(A_113) | ~r1_tarski(A_114, u1_struct_0(A_113)))), inference(resolution, [status(thm)], [c_6, c_216])).
% 3.56/1.63  tff(c_60, plain, (![C_52, B_53, A_54]: (~v1_xboole_0(C_52) | ~m1_subset_1(B_53, k1_zfmisc_1(C_52)) | ~r2_hidden(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.56/1.63  tff(c_65, plain, (![B_5, A_54, A_4]: (~v1_xboole_0(B_5) | ~r2_hidden(A_54, A_4) | ~r1_tarski(A_4, B_5))), inference(resolution, [status(thm)], [c_6, c_60])).
% 3.56/1.63  tff(c_329, plain, (![B_5, A_113, A_114, B_112]: (~v1_xboole_0(B_5) | ~r1_tarski(k1_tops_1(A_113, A_114), B_5) | ~m1_connsp_2(A_114, A_113, B_112) | ~m1_subset_1(B_112, u1_struct_0(A_113)) | ~l1_pre_topc(A_113) | ~v2_pre_topc(A_113) | v2_struct_0(A_113) | ~r1_tarski(A_114, u1_struct_0(A_113)))), inference(resolution, [status(thm)], [c_320, c_65])).
% 3.56/1.63  tff(c_1081, plain, (![B_112]: (~v1_xboole_0(k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', B_112) | ~m1_subset_1(B_112, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_966, c_329])).
% 3.56/1.63  tff(c_1105, plain, (![B_112]: (~m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', B_112) | ~m1_subset_1(B_112, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_837, c_34, c_32, c_452, c_1081])).
% 3.56/1.63  tff(c_1119, plain, (![B_155]: (~m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', B_155) | ~m1_subset_1(B_155, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_36, c_1105])).
% 3.56/1.63  tff(c_1122, plain, (~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_868, c_1119])).
% 3.56/1.63  tff(c_1134, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_1122])).
% 3.56/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.63  
% 3.56/1.63  Inference rules
% 3.56/1.63  ----------------------
% 3.56/1.63  #Ref     : 0
% 3.56/1.63  #Sup     : 218
% 3.56/1.63  #Fact    : 0
% 3.56/1.63  #Define  : 0
% 3.56/1.63  #Split   : 6
% 3.56/1.63  #Chain   : 0
% 3.56/1.63  #Close   : 0
% 3.56/1.63  
% 3.56/1.63  Ordering : KBO
% 3.56/1.63  
% 3.56/1.63  Simplification rules
% 3.56/1.63  ----------------------
% 3.56/1.63  #Subsume      : 54
% 3.56/1.63  #Demod        : 201
% 3.56/1.63  #Tautology    : 38
% 3.56/1.63  #SimpNegUnit  : 29
% 3.56/1.63  #BackRed      : 0
% 3.56/1.63  
% 3.56/1.63  #Partial instantiations: 0
% 3.56/1.63  #Strategies tried      : 1
% 3.56/1.63  
% 3.56/1.63  Timing (in seconds)
% 3.56/1.63  ----------------------
% 3.56/1.63  Preprocessing        : 0.33
% 3.56/1.63  Parsing              : 0.19
% 3.56/1.63  CNF conversion       : 0.02
% 3.56/1.63  Main loop            : 0.46
% 3.56/1.63  Inferencing          : 0.17
% 3.56/1.63  Reduction            : 0.13
% 3.56/1.63  Demodulation         : 0.09
% 3.56/1.63  BG Simplification    : 0.02
% 3.56/1.63  Subsumption          : 0.10
% 3.56/1.63  Abstraction          : 0.02
% 3.56/1.63  MUC search           : 0.00
% 3.56/1.63  Cooper               : 0.00
% 3.56/1.63  Total                : 0.83
% 3.56/1.63  Index Insertion      : 0.00
% 3.56/1.63  Index Deletion       : 0.00
% 3.56/1.63  Index Matching       : 0.00
% 3.56/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
