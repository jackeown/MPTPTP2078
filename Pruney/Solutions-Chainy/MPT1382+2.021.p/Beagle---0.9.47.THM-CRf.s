%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:10 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 235 expanded)
%              Number of leaves         :   29 (  94 expanded)
%              Depth                    :   12
%              Number of atoms          :  195 ( 829 expanded)
%              Number of equality atoms :    2 (   8 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_141,negated_conjecture,(
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

tff(f_78,axiom,(
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

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_111,axiom,(
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

tff(f_46,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_28,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_295,plain,(
    ! [B_92,A_93,C_94] :
      ( r2_hidden(B_92,k1_tops_1(A_93,C_94))
      | ~ m1_connsp_2(C_94,A_93,B_92)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ m1_subset_1(B_92,u1_struct_0(A_93))
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_300,plain,(
    ! [B_92] :
      ( r2_hidden(B_92,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_92)
      | ~ m1_subset_1(B_92,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_295])).

tff(c_307,plain,(
    ! [B_92] :
      ( r2_hidden(B_92,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_92)
      | ~ m1_subset_1(B_92,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_300])).

tff(c_308,plain,(
    ! [B_92] :
      ( r2_hidden(B_92,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_92)
      | ~ m1_subset_1(B_92,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_307])).

tff(c_142,plain,(
    ! [A_70,B_71] :
      ( v3_pre_topc(k1_tops_1(A_70,B_71),A_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_147,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_142])).

tff(c_154,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_147])).

tff(c_120,plain,(
    ! [A_68,B_69] :
      ( r1_tarski(k1_tops_1(A_68,B_69),B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_125,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_120])).

tff(c_132,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_125])).

tff(c_4,plain,(
    ! [A_4] : k2_subset_1(A_4) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_5] : m1_subset_1(k2_subset_1(A_5),k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_39,plain,(
    ! [A_5] : m1_subset_1(A_5,k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_50,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,B_49)
      | ~ m1_subset_1(A_48,k1_zfmisc_1(B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_58,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_39,c_50])).

tff(c_57,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_50])).

tff(c_85,plain,(
    ! [A_54,C_55,B_56] :
      ( r1_tarski(A_54,C_55)
      | ~ r1_tarski(B_56,C_55)
      | ~ r1_tarski(A_54,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_92,plain,(
    ! [A_57] :
      ( r1_tarski(A_57,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_57,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_57,c_85])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_95,plain,(
    ! [A_1,A_57] :
      ( r1_tarski(A_1,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_1,A_57)
      | ~ r1_tarski(A_57,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_92,c_2])).

tff(c_135,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_132,c_95])).

tff(c_140,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_135])).

tff(c_72,plain,(
    ! [A_52,B_53] :
      ( m1_subset_1(A_52,k1_zfmisc_1(B_53))
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    ! [D_45] :
      ( ~ r1_tarski(D_45,'#skF_3')
      | ~ v3_pre_topc(D_45,'#skF_1')
      | ~ m1_connsp_2(D_45,'#skF_1','#skF_2')
      | ~ m1_subset_1(D_45,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v1_xboole_0(D_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_230,plain,(
    ! [A_86] :
      ( ~ r1_tarski(A_86,'#skF_3')
      | ~ v3_pre_topc(A_86,'#skF_1')
      | ~ m1_connsp_2(A_86,'#skF_1','#skF_2')
      | v1_xboole_0(A_86)
      | ~ r1_tarski(A_86,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_72,c_26])).

tff(c_244,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1','#skF_2')
    | v1_xboole_0(k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_140,c_230])).

tff(c_262,plain,
    ( ~ m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1','#skF_2')
    | v1_xboole_0(k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_132,c_244])).

tff(c_269,plain,(
    ~ m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_262])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_443,plain,(
    ! [B_117,A_118,C_119] :
      ( m1_connsp_2(B_117,A_118,C_119)
      | ~ r2_hidden(C_119,B_117)
      | ~ v3_pre_topc(B_117,A_118)
      | ~ m1_subset_1(C_119,u1_struct_0(A_118))
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_pre_topc(A_118)
      | ~ v2_pre_topc(A_118)
      | v2_struct_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_445,plain,(
    ! [B_117] :
      ( m1_connsp_2(B_117,'#skF_1','#skF_2')
      | ~ r2_hidden('#skF_2',B_117)
      | ~ v3_pre_topc(B_117,'#skF_1')
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_443])).

tff(c_448,plain,(
    ! [B_117] :
      ( m1_connsp_2(B_117,'#skF_1','#skF_2')
      | ~ r2_hidden('#skF_2',B_117)
      | ~ v3_pre_topc(B_117,'#skF_1')
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_445])).

tff(c_450,plain,(
    ! [B_120] :
      ( m1_connsp_2(B_120,'#skF_1','#skF_2')
      | ~ r2_hidden('#skF_2',B_120)
      | ~ v3_pre_topc(B_120,'#skF_1')
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_448])).

tff(c_469,plain,(
    ! [A_121] :
      ( m1_connsp_2(A_121,'#skF_1','#skF_2')
      | ~ r2_hidden('#skF_2',A_121)
      | ~ v3_pre_topc(A_121,'#skF_1')
      | ~ r1_tarski(A_121,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_10,c_450])).

tff(c_493,plain,
    ( m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1','#skF_2')
    | ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_140,c_469])).

tff(c_516,plain,
    ( m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1','#skF_2')
    | ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_493])).

tff(c_517,plain,(
    ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_269,c_516])).

tff(c_525,plain,
    ( ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_308,c_517])).

tff(c_529,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_525])).

tff(c_530,plain,(
    v1_xboole_0(k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_651,plain,(
    ! [B_129,A_130,C_131] :
      ( r2_hidden(B_129,k1_tops_1(A_130,C_131))
      | ~ m1_connsp_2(C_131,A_130,B_129)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ m1_subset_1(B_129,u1_struct_0(A_130))
      | ~ l1_pre_topc(A_130)
      | ~ v2_pre_topc(A_130)
      | v2_struct_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_658,plain,(
    ! [B_129] :
      ( r2_hidden(B_129,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_129)
      | ~ m1_subset_1(B_129,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_651])).

tff(c_669,plain,(
    ! [B_129] :
      ( r2_hidden(B_129,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_129)
      | ~ m1_subset_1(B_129,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_658])).

tff(c_672,plain,(
    ! [B_132] :
      ( r2_hidden(B_132,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_132)
      | ~ m1_subset_1(B_132,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_669])).

tff(c_96,plain,(
    ! [C_58,B_59,A_60] :
      ( ~ v1_xboole_0(C_58)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(C_58))
      | ~ r2_hidden(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_105,plain,(
    ! [A_5,A_60] :
      ( ~ v1_xboole_0(A_5)
      | ~ r2_hidden(A_60,A_5) ) ),
    inference(resolution,[status(thm)],[c_39,c_96])).

tff(c_679,plain,(
    ! [B_132] :
      ( ~ v1_xboole_0(k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_132)
      | ~ m1_subset_1(B_132,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_672,c_105])).

tff(c_688,plain,(
    ! [B_133] :
      ( ~ m1_connsp_2('#skF_3','#skF_1',B_133)
      | ~ m1_subset_1(B_133,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_530,c_679])).

tff(c_691,plain,(
    ~ m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_688])).

tff(c_695,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_691])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:13:39 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.07/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.48  
% 3.07/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.48  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.07/1.48  
% 3.07/1.48  %Foreground sorts:
% 3.07/1.48  
% 3.07/1.48  
% 3.07/1.48  %Background operators:
% 3.07/1.48  
% 3.07/1.48  
% 3.07/1.48  %Foreground operators:
% 3.07/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.07/1.48  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.07/1.48  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.07/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.07/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.07/1.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.07/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.07/1.48  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.07/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.07/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.07/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.07/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.07/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.07/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.07/1.48  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.07/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.07/1.48  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.07/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.07/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.07/1.48  
% 3.19/1.50  tff(f_141, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(C, A, B) & (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~((m1_connsp_2(D, A, B) & v3_pre_topc(D, A)) & r1_tarski(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_connsp_2)).
% 3.19/1.50  tff(f_78, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 3.19/1.50  tff(f_54, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.19/1.50  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 3.19/1.50  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.19/1.50  tff(f_35, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.19/1.50  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.19/1.50  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.19/1.50  tff(f_111, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 3.19/1.50  tff(f_46, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.19/1.50  tff(c_28, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.19/1.50  tff(c_32, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.19/1.50  tff(c_38, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.19/1.50  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.19/1.50  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.19/1.50  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.19/1.50  tff(c_295, plain, (![B_92, A_93, C_94]: (r2_hidden(B_92, k1_tops_1(A_93, C_94)) | ~m1_connsp_2(C_94, A_93, B_92) | ~m1_subset_1(C_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~m1_subset_1(B_92, u1_struct_0(A_93)) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.19/1.50  tff(c_300, plain, (![B_92]: (r2_hidden(B_92, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_92) | ~m1_subset_1(B_92, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_295])).
% 3.19/1.50  tff(c_307, plain, (![B_92]: (r2_hidden(B_92, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_92) | ~m1_subset_1(B_92, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_300])).
% 3.19/1.50  tff(c_308, plain, (![B_92]: (r2_hidden(B_92, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_92) | ~m1_subset_1(B_92, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_38, c_307])).
% 3.19/1.50  tff(c_142, plain, (![A_70, B_71]: (v3_pre_topc(k1_tops_1(A_70, B_71), A_70) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.19/1.50  tff(c_147, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_142])).
% 3.19/1.50  tff(c_154, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_147])).
% 3.19/1.50  tff(c_120, plain, (![A_68, B_69]: (r1_tarski(k1_tops_1(A_68, B_69), B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.19/1.50  tff(c_125, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_120])).
% 3.19/1.50  tff(c_132, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_125])).
% 3.19/1.50  tff(c_4, plain, (![A_4]: (k2_subset_1(A_4)=A_4)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.19/1.50  tff(c_6, plain, (![A_5]: (m1_subset_1(k2_subset_1(A_5), k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.19/1.50  tff(c_39, plain, (![A_5]: (m1_subset_1(A_5, k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 3.19/1.50  tff(c_50, plain, (![A_48, B_49]: (r1_tarski(A_48, B_49) | ~m1_subset_1(A_48, k1_zfmisc_1(B_49)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.19/1.50  tff(c_58, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_39, c_50])).
% 3.19/1.50  tff(c_57, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_50])).
% 3.19/1.50  tff(c_85, plain, (![A_54, C_55, B_56]: (r1_tarski(A_54, C_55) | ~r1_tarski(B_56, C_55) | ~r1_tarski(A_54, B_56))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.19/1.50  tff(c_92, plain, (![A_57]: (r1_tarski(A_57, u1_struct_0('#skF_1')) | ~r1_tarski(A_57, '#skF_3'))), inference(resolution, [status(thm)], [c_57, c_85])).
% 3.19/1.50  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.19/1.50  tff(c_95, plain, (![A_1, A_57]: (r1_tarski(A_1, u1_struct_0('#skF_1')) | ~r1_tarski(A_1, A_57) | ~r1_tarski(A_57, '#skF_3'))), inference(resolution, [status(thm)], [c_92, c_2])).
% 3.19/1.50  tff(c_135, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), u1_struct_0('#skF_1')) | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_132, c_95])).
% 3.19/1.50  tff(c_140, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_135])).
% 3.19/1.50  tff(c_72, plain, (![A_52, B_53]: (m1_subset_1(A_52, k1_zfmisc_1(B_53)) | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.19/1.50  tff(c_26, plain, (![D_45]: (~r1_tarski(D_45, '#skF_3') | ~v3_pre_topc(D_45, '#skF_1') | ~m1_connsp_2(D_45, '#skF_1', '#skF_2') | ~m1_subset_1(D_45, k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(D_45))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.19/1.50  tff(c_230, plain, (![A_86]: (~r1_tarski(A_86, '#skF_3') | ~v3_pre_topc(A_86, '#skF_1') | ~m1_connsp_2(A_86, '#skF_1', '#skF_2') | v1_xboole_0(A_86) | ~r1_tarski(A_86, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_72, c_26])).
% 3.19/1.50  tff(c_244, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', '#skF_2') | v1_xboole_0(k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_140, c_230])).
% 3.19/1.50  tff(c_262, plain, (~m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', '#skF_2') | v1_xboole_0(k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_132, c_244])).
% 3.19/1.50  tff(c_269, plain, (~m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_262])).
% 3.19/1.50  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.19/1.50  tff(c_443, plain, (![B_117, A_118, C_119]: (m1_connsp_2(B_117, A_118, C_119) | ~r2_hidden(C_119, B_117) | ~v3_pre_topc(B_117, A_118) | ~m1_subset_1(C_119, u1_struct_0(A_118)) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_pre_topc(A_118) | ~v2_pre_topc(A_118) | v2_struct_0(A_118))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.19/1.50  tff(c_445, plain, (![B_117]: (m1_connsp_2(B_117, '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', B_117) | ~v3_pre_topc(B_117, '#skF_1') | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_443])).
% 3.19/1.50  tff(c_448, plain, (![B_117]: (m1_connsp_2(B_117, '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', B_117) | ~v3_pre_topc(B_117, '#skF_1') | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_445])).
% 3.19/1.50  tff(c_450, plain, (![B_120]: (m1_connsp_2(B_120, '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', B_120) | ~v3_pre_topc(B_120, '#skF_1') | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_38, c_448])).
% 3.19/1.50  tff(c_469, plain, (![A_121]: (m1_connsp_2(A_121, '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', A_121) | ~v3_pre_topc(A_121, '#skF_1') | ~r1_tarski(A_121, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_10, c_450])).
% 3.19/1.50  tff(c_493, plain, (m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_140, c_469])).
% 3.19/1.50  tff(c_516, plain, (m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_493])).
% 3.19/1.50  tff(c_517, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_269, c_516])).
% 3.19/1.50  tff(c_525, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_308, c_517])).
% 3.19/1.50  tff(c_529, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_525])).
% 3.19/1.50  tff(c_530, plain, (v1_xboole_0(k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_262])).
% 3.19/1.50  tff(c_651, plain, (![B_129, A_130, C_131]: (r2_hidden(B_129, k1_tops_1(A_130, C_131)) | ~m1_connsp_2(C_131, A_130, B_129) | ~m1_subset_1(C_131, k1_zfmisc_1(u1_struct_0(A_130))) | ~m1_subset_1(B_129, u1_struct_0(A_130)) | ~l1_pre_topc(A_130) | ~v2_pre_topc(A_130) | v2_struct_0(A_130))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.19/1.50  tff(c_658, plain, (![B_129]: (r2_hidden(B_129, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_129) | ~m1_subset_1(B_129, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_651])).
% 3.19/1.50  tff(c_669, plain, (![B_129]: (r2_hidden(B_129, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_129) | ~m1_subset_1(B_129, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_658])).
% 3.19/1.50  tff(c_672, plain, (![B_132]: (r2_hidden(B_132, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_132) | ~m1_subset_1(B_132, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_38, c_669])).
% 3.19/1.50  tff(c_96, plain, (![C_58, B_59, A_60]: (~v1_xboole_0(C_58) | ~m1_subset_1(B_59, k1_zfmisc_1(C_58)) | ~r2_hidden(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.19/1.50  tff(c_105, plain, (![A_5, A_60]: (~v1_xboole_0(A_5) | ~r2_hidden(A_60, A_5))), inference(resolution, [status(thm)], [c_39, c_96])).
% 3.19/1.50  tff(c_679, plain, (![B_132]: (~v1_xboole_0(k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_132) | ~m1_subset_1(B_132, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_672, c_105])).
% 3.19/1.50  tff(c_688, plain, (![B_133]: (~m1_connsp_2('#skF_3', '#skF_1', B_133) | ~m1_subset_1(B_133, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_530, c_679])).
% 3.19/1.50  tff(c_691, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_688])).
% 3.19/1.50  tff(c_695, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_691])).
% 3.19/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.50  
% 3.19/1.50  Inference rules
% 3.19/1.50  ----------------------
% 3.19/1.50  #Ref     : 0
% 3.19/1.50  #Sup     : 128
% 3.19/1.50  #Fact    : 0
% 3.19/1.50  #Define  : 0
% 3.19/1.50  #Split   : 7
% 3.19/1.50  #Chain   : 0
% 3.19/1.50  #Close   : 0
% 3.19/1.50  
% 3.19/1.50  Ordering : KBO
% 3.19/1.50  
% 3.19/1.50  Simplification rules
% 3.19/1.50  ----------------------
% 3.19/1.50  #Subsume      : 32
% 3.19/1.50  #Demod        : 78
% 3.19/1.50  #Tautology    : 21
% 3.19/1.50  #SimpNegUnit  : 13
% 3.19/1.50  #BackRed      : 0
% 3.19/1.50  
% 3.19/1.50  #Partial instantiations: 0
% 3.19/1.50  #Strategies tried      : 1
% 3.19/1.50  
% 3.19/1.50  Timing (in seconds)
% 3.19/1.50  ----------------------
% 3.19/1.51  Preprocessing        : 0.33
% 3.19/1.51  Parsing              : 0.18
% 3.19/1.51  CNF conversion       : 0.03
% 3.19/1.51  Main loop            : 0.37
% 3.19/1.51  Inferencing          : 0.14
% 3.19/1.51  Reduction            : 0.11
% 3.19/1.51  Demodulation         : 0.07
% 3.19/1.51  BG Simplification    : 0.02
% 3.19/1.51  Subsumption          : 0.08
% 3.19/1.51  Abstraction          : 0.01
% 3.19/1.51  MUC search           : 0.00
% 3.19/1.51  Cooper               : 0.00
% 3.19/1.51  Total                : 0.73
% 3.19/1.51  Index Insertion      : 0.00
% 3.19/1.51  Index Deletion       : 0.00
% 3.19/1.51  Index Matching       : 0.00
% 3.19/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
