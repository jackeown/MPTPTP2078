%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:10 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 3.91s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 354 expanded)
%              Number of leaves         :   27 ( 140 expanded)
%              Depth                    :   15
%              Number of atoms          :  242 (1560 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1

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

tff(f_127,negated_conjecture,(
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

tff(f_61,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B,C] :
          ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,k1_tops_1(A,C))
          <=> ? [D] :
                ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                & v3_pre_topc(D,A)
                & r1_tarski(D,C)
                & r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).

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

tff(f_43,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_97,axiom,(
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

tff(c_36,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_32,plain,(
    m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_40,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_388,plain,(
    ! [B_135,A_136,C_137] :
      ( r2_hidden(B_135,k1_tops_1(A_136,C_137))
      | ~ m1_connsp_2(C_137,A_136,B_135)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ m1_subset_1(B_135,u1_struct_0(A_136))
      | ~ l1_pre_topc(A_136)
      | ~ v2_pre_topc(A_136)
      | v2_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_395,plain,(
    ! [B_135] :
      ( r2_hidden(B_135,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_135)
      | ~ m1_subset_1(B_135,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_388])).

tff(c_400,plain,(
    ! [B_135] :
      ( r2_hidden(B_135,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_135)
      | ~ m1_subset_1(B_135,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_395])).

tff(c_402,plain,(
    ! [B_138] :
      ( r2_hidden(B_138,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_138)
      | ~ m1_subset_1(B_138,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_400])).

tff(c_18,plain,(
    ! [A_11,B_18,C_19] :
      ( r1_tarski('#skF_2'(A_11,B_18,C_19),C_19)
      | ~ r2_hidden(B_18,k1_tops_1(A_11,C_19))
      | ~ m1_subset_1(C_19,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_408,plain,(
    ! [B_138] :
      ( r1_tarski('#skF_2'('#skF_3',B_138,'#skF_5'),'#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_138)
      | ~ m1_subset_1(B_138,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_402,c_18])).

tff(c_425,plain,(
    ! [B_138] :
      ( r1_tarski('#skF_2'('#skF_3',B_138,'#skF_5'),'#skF_5')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_138)
      | ~ m1_subset_1(B_138,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_34,c_408])).

tff(c_43,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_47,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_43])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_397,plain,(
    ! [B_135,A_136,A_6] :
      ( r2_hidden(B_135,k1_tops_1(A_136,A_6))
      | ~ m1_connsp_2(A_6,A_136,B_135)
      | ~ m1_subset_1(B_135,u1_struct_0(A_136))
      | ~ l1_pre_topc(A_136)
      | ~ v2_pre_topc(A_136)
      | v2_struct_0(A_136)
      | ~ r1_tarski(A_6,u1_struct_0(A_136)) ) ),
    inference(resolution,[status(thm)],[c_10,c_388])).

tff(c_66,plain,(
    ! [A_56,B_57] :
      ( r2_hidden('#skF_1'(A_56,B_57),A_56)
      | r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_71,plain,(
    ! [A_56] : r1_tarski(A_56,A_56) ),
    inference(resolution,[status(thm)],[c_66,c_4])).

tff(c_16,plain,(
    ! [B_18,A_11,C_19] :
      ( r2_hidden(B_18,'#skF_2'(A_11,B_18,C_19))
      | ~ r2_hidden(B_18,k1_tops_1(A_11,C_19))
      | ~ m1_subset_1(C_19,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_406,plain,(
    ! [B_138] :
      ( r2_hidden(B_138,'#skF_2'('#skF_3',B_138,'#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_138)
      | ~ m1_subset_1(B_138,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_402,c_16])).

tff(c_429,plain,(
    ! [B_139] :
      ( r2_hidden(B_139,'#skF_2'('#skF_3',B_139,'#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_139)
      | ~ m1_subset_1(B_139,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_34,c_406])).

tff(c_80,plain,(
    ! [C_62,B_63,A_64] :
      ( ~ v1_xboole_0(C_62)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(C_62))
      | ~ r2_hidden(A_64,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_85,plain,(
    ! [B_7,A_64,A_6] :
      ( ~ v1_xboole_0(B_7)
      | ~ r2_hidden(A_64,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_80])).

tff(c_631,plain,(
    ! [B_161,B_162] :
      ( ~ v1_xboole_0(B_161)
      | ~ r1_tarski('#skF_2'('#skF_3',B_162,'#skF_5'),B_161)
      | ~ m1_connsp_2('#skF_5','#skF_3',B_162)
      | ~ m1_subset_1(B_162,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_429,c_85])).

tff(c_665,plain,(
    ! [B_163] :
      ( ~ v1_xboole_0('#skF_2'('#skF_3',B_163,'#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_163)
      | ~ m1_subset_1(B_163,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_71,c_631])).

tff(c_668,plain,
    ( ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_665])).

tff(c_671,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_668])).

tff(c_422,plain,(
    ! [B_138] :
      ( r2_hidden(B_138,'#skF_2'('#skF_3',B_138,'#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_138)
      | ~ m1_subset_1(B_138,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_34,c_406])).

tff(c_301,plain,(
    ! [A_110,B_111,C_112] :
      ( v3_pre_topc('#skF_2'(A_110,B_111,C_112),A_110)
      | ~ r2_hidden(B_111,k1_tops_1(A_110,C_112))
      | ~ m1_subset_1(C_112,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110)
      | ~ v2_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_306,plain,(
    ! [B_111] :
      ( v3_pre_topc('#skF_2'('#skF_3',B_111,'#skF_5'),'#skF_3')
      | ~ r2_hidden(B_111,k1_tops_1('#skF_3','#skF_5'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_301])).

tff(c_310,plain,(
    ! [B_111] :
      ( v3_pre_topc('#skF_2'('#skF_3',B_111,'#skF_5'),'#skF_3')
      | ~ r2_hidden(B_111,k1_tops_1('#skF_3','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_306])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_76,plain,(
    ! [C_59,B_60,A_61] :
      ( r2_hidden(C_59,B_60)
      | ~ r2_hidden(C_59,A_61)
      | ~ r1_tarski(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_122,plain,(
    ! [A_74,B_75,B_76] :
      ( r2_hidden('#skF_1'(A_74,B_75),B_76)
      | ~ r1_tarski(A_74,B_76)
      | r1_tarski(A_74,B_75) ) ),
    inference(resolution,[status(thm)],[c_6,c_76])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_154,plain,(
    ! [A_84,B_85,B_86,B_87] :
      ( r2_hidden('#skF_1'(A_84,B_85),B_86)
      | ~ r1_tarski(B_87,B_86)
      | ~ r1_tarski(A_84,B_87)
      | r1_tarski(A_84,B_85) ) ),
    inference(resolution,[status(thm)],[c_122,c_2])).

tff(c_164,plain,(
    ! [A_88,B_89] :
      ( r2_hidden('#skF_1'(A_88,B_89),u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_88,'#skF_5')
      | r1_tarski(A_88,B_89) ) ),
    inference(resolution,[status(thm)],[c_47,c_154])).

tff(c_175,plain,(
    ! [A_88] :
      ( ~ r1_tarski(A_88,'#skF_5')
      | r1_tarski(A_88,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_164,c_4])).

tff(c_521,plain,(
    ! [B_148,A_149,C_150] :
      ( m1_connsp_2(B_148,A_149,C_150)
      | ~ r2_hidden(C_150,B_148)
      | ~ v3_pre_topc(B_148,A_149)
      | ~ m1_subset_1(C_150,u1_struct_0(A_149))
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_pre_topc(A_149)
      | ~ v2_pre_topc(A_149)
      | v2_struct_0(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_523,plain,(
    ! [B_148] :
      ( m1_connsp_2(B_148,'#skF_3','#skF_4')
      | ~ r2_hidden('#skF_4',B_148)
      | ~ v3_pre_topc(B_148,'#skF_3')
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_521])).

tff(c_526,plain,(
    ! [B_148] :
      ( m1_connsp_2(B_148,'#skF_3','#skF_4')
      | ~ r2_hidden('#skF_4',B_148)
      | ~ v3_pre_topc(B_148,'#skF_3')
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_523])).

tff(c_528,plain,(
    ! [B_151] :
      ( m1_connsp_2(B_151,'#skF_3','#skF_4')
      | ~ r2_hidden('#skF_4',B_151)
      | ~ v3_pre_topc(B_151,'#skF_3')
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_526])).

tff(c_546,plain,(
    ! [A_152] :
      ( m1_connsp_2(A_152,'#skF_3','#skF_4')
      | ~ r2_hidden('#skF_4',A_152)
      | ~ v3_pre_topc(A_152,'#skF_3')
      | ~ r1_tarski(A_152,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_10,c_528])).

tff(c_591,plain,(
    ! [A_155] :
      ( m1_connsp_2(A_155,'#skF_3','#skF_4')
      | ~ r2_hidden('#skF_4',A_155)
      | ~ v3_pre_topc(A_155,'#skF_3')
      | ~ r1_tarski(A_155,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_175,c_546])).

tff(c_176,plain,(
    ! [A_90] :
      ( ~ r1_tarski(A_90,'#skF_5')
      | r1_tarski(A_90,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_164,c_4])).

tff(c_53,plain,(
    ! [D_53] :
      ( ~ r1_tarski(D_53,'#skF_5')
      | ~ v3_pre_topc(D_53,'#skF_3')
      | ~ m1_connsp_2(D_53,'#skF_3','#skF_4')
      | ~ m1_subset_1(D_53,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v1_xboole_0(D_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_61,plain,(
    ! [A_6] :
      ( ~ r1_tarski(A_6,'#skF_5')
      | ~ v3_pre_topc(A_6,'#skF_3')
      | ~ m1_connsp_2(A_6,'#skF_3','#skF_4')
      | v1_xboole_0(A_6)
      | ~ r1_tarski(A_6,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_10,c_53])).

tff(c_189,plain,(
    ! [A_90] :
      ( ~ v3_pre_topc(A_90,'#skF_3')
      | ~ m1_connsp_2(A_90,'#skF_3','#skF_4')
      | v1_xboole_0(A_90)
      | ~ r1_tarski(A_90,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_176,c_61])).

tff(c_600,plain,(
    ! [A_156] :
      ( v1_xboole_0(A_156)
      | ~ r2_hidden('#skF_4',A_156)
      | ~ v3_pre_topc(A_156,'#skF_3')
      | ~ r1_tarski(A_156,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_591,c_189])).

tff(c_1210,plain,(
    ! [B_220] :
      ( v1_xboole_0('#skF_2'('#skF_3',B_220,'#skF_5'))
      | ~ r2_hidden('#skF_4','#skF_2'('#skF_3',B_220,'#skF_5'))
      | ~ r1_tarski('#skF_2'('#skF_3',B_220,'#skF_5'),'#skF_5')
      | ~ r2_hidden(B_220,k1_tops_1('#skF_3','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_310,c_600])).

tff(c_1219,plain,
    ( v1_xboole_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ r1_tarski('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5')
    | ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5'))
    | ~ m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_422,c_1210])).

tff(c_1227,plain,
    ( v1_xboole_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ r1_tarski('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5')
    | ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_1219])).

tff(c_1228,plain,
    ( ~ r1_tarski('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5')
    | ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_671,c_1227])).

tff(c_1229,plain,(
    ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1228])).

tff(c_1235,plain,
    ( ~ m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_397,c_1229])).

tff(c_1242,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_40,c_38,c_36,c_32,c_1235])).

tff(c_1244,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1242])).

tff(c_1245,plain,(
    ~ r1_tarski('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_1228])).

tff(c_1282,plain,
    ( ~ m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_425,c_1245])).

tff(c_1292,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_1282])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:40:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.68/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.68/1.68  
% 3.68/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.68/1.68  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 3.68/1.68  
% 3.68/1.68  %Foreground sorts:
% 3.68/1.68  
% 3.68/1.68  
% 3.68/1.68  %Background operators:
% 3.68/1.68  
% 3.68/1.68  
% 3.68/1.68  %Foreground operators:
% 3.68/1.68  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.68/1.68  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.68/1.68  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.68/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.68/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.68/1.68  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.68/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.68/1.68  tff('#skF_5', type, '#skF_5': $i).
% 3.68/1.68  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.68/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.68/1.68  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.68/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.68/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.68/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.68/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.68/1.68  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.68/1.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.68/1.68  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.68/1.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.68/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.68/1.68  
% 3.91/1.70  tff(f_127, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(C, A, B) & (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~((m1_connsp_2(D, A, B) & v3_pre_topc(D, A)) & r1_tarski(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_connsp_2)).
% 3.91/1.70  tff(f_78, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 3.91/1.70  tff(f_61, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k1_tops_1(A, C)) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_tops_1)).
% 3.91/1.70  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.91/1.70  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.91/1.70  tff(f_43, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.91/1.70  tff(f_97, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 3.91/1.70  tff(c_36, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.91/1.70  tff(c_32, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.91/1.70  tff(c_40, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.91/1.70  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.91/1.70  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.91/1.70  tff(c_42, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.91/1.70  tff(c_388, plain, (![B_135, A_136, C_137]: (r2_hidden(B_135, k1_tops_1(A_136, C_137)) | ~m1_connsp_2(C_137, A_136, B_135) | ~m1_subset_1(C_137, k1_zfmisc_1(u1_struct_0(A_136))) | ~m1_subset_1(B_135, u1_struct_0(A_136)) | ~l1_pre_topc(A_136) | ~v2_pre_topc(A_136) | v2_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.91/1.70  tff(c_395, plain, (![B_135]: (r2_hidden(B_135, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_135) | ~m1_subset_1(B_135, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_388])).
% 3.91/1.70  tff(c_400, plain, (![B_135]: (r2_hidden(B_135, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_135) | ~m1_subset_1(B_135, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_395])).
% 3.91/1.70  tff(c_402, plain, (![B_138]: (r2_hidden(B_138, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_138) | ~m1_subset_1(B_138, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_42, c_400])).
% 3.91/1.70  tff(c_18, plain, (![A_11, B_18, C_19]: (r1_tarski('#skF_2'(A_11, B_18, C_19), C_19) | ~r2_hidden(B_18, k1_tops_1(A_11, C_19)) | ~m1_subset_1(C_19, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.91/1.70  tff(c_408, plain, (![B_138]: (r1_tarski('#skF_2'('#skF_3', B_138, '#skF_5'), '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~m1_connsp_2('#skF_5', '#skF_3', B_138) | ~m1_subset_1(B_138, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_402, c_18])).
% 3.91/1.70  tff(c_425, plain, (![B_138]: (r1_tarski('#skF_2'('#skF_3', B_138, '#skF_5'), '#skF_5') | ~m1_connsp_2('#skF_5', '#skF_3', B_138) | ~m1_subset_1(B_138, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_34, c_408])).
% 3.91/1.70  tff(c_43, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~m1_subset_1(A_49, k1_zfmisc_1(B_50)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.91/1.70  tff(c_47, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_43])).
% 3.91/1.70  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.91/1.70  tff(c_397, plain, (![B_135, A_136, A_6]: (r2_hidden(B_135, k1_tops_1(A_136, A_6)) | ~m1_connsp_2(A_6, A_136, B_135) | ~m1_subset_1(B_135, u1_struct_0(A_136)) | ~l1_pre_topc(A_136) | ~v2_pre_topc(A_136) | v2_struct_0(A_136) | ~r1_tarski(A_6, u1_struct_0(A_136)))), inference(resolution, [status(thm)], [c_10, c_388])).
% 3.91/1.70  tff(c_66, plain, (![A_56, B_57]: (r2_hidden('#skF_1'(A_56, B_57), A_56) | r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.91/1.70  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.91/1.70  tff(c_71, plain, (![A_56]: (r1_tarski(A_56, A_56))), inference(resolution, [status(thm)], [c_66, c_4])).
% 3.91/1.70  tff(c_16, plain, (![B_18, A_11, C_19]: (r2_hidden(B_18, '#skF_2'(A_11, B_18, C_19)) | ~r2_hidden(B_18, k1_tops_1(A_11, C_19)) | ~m1_subset_1(C_19, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.91/1.70  tff(c_406, plain, (![B_138]: (r2_hidden(B_138, '#skF_2'('#skF_3', B_138, '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~m1_connsp_2('#skF_5', '#skF_3', B_138) | ~m1_subset_1(B_138, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_402, c_16])).
% 3.91/1.70  tff(c_429, plain, (![B_139]: (r2_hidden(B_139, '#skF_2'('#skF_3', B_139, '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_139) | ~m1_subset_1(B_139, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_34, c_406])).
% 3.91/1.70  tff(c_80, plain, (![C_62, B_63, A_64]: (~v1_xboole_0(C_62) | ~m1_subset_1(B_63, k1_zfmisc_1(C_62)) | ~r2_hidden(A_64, B_63))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.91/1.70  tff(c_85, plain, (![B_7, A_64, A_6]: (~v1_xboole_0(B_7) | ~r2_hidden(A_64, A_6) | ~r1_tarski(A_6, B_7))), inference(resolution, [status(thm)], [c_10, c_80])).
% 3.91/1.70  tff(c_631, plain, (![B_161, B_162]: (~v1_xboole_0(B_161) | ~r1_tarski('#skF_2'('#skF_3', B_162, '#skF_5'), B_161) | ~m1_connsp_2('#skF_5', '#skF_3', B_162) | ~m1_subset_1(B_162, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_429, c_85])).
% 3.91/1.70  tff(c_665, plain, (![B_163]: (~v1_xboole_0('#skF_2'('#skF_3', B_163, '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_163) | ~m1_subset_1(B_163, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_71, c_631])).
% 3.91/1.70  tff(c_668, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_36, c_665])).
% 3.91/1.70  tff(c_671, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_668])).
% 3.91/1.70  tff(c_422, plain, (![B_138]: (r2_hidden(B_138, '#skF_2'('#skF_3', B_138, '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_138) | ~m1_subset_1(B_138, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_34, c_406])).
% 3.91/1.70  tff(c_301, plain, (![A_110, B_111, C_112]: (v3_pre_topc('#skF_2'(A_110, B_111, C_112), A_110) | ~r2_hidden(B_111, k1_tops_1(A_110, C_112)) | ~m1_subset_1(C_112, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110) | ~v2_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.91/1.70  tff(c_306, plain, (![B_111]: (v3_pre_topc('#skF_2'('#skF_3', B_111, '#skF_5'), '#skF_3') | ~r2_hidden(B_111, k1_tops_1('#skF_3', '#skF_5')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_301])).
% 3.91/1.70  tff(c_310, plain, (![B_111]: (v3_pre_topc('#skF_2'('#skF_3', B_111, '#skF_5'), '#skF_3') | ~r2_hidden(B_111, k1_tops_1('#skF_3', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_306])).
% 3.91/1.70  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.91/1.70  tff(c_76, plain, (![C_59, B_60, A_61]: (r2_hidden(C_59, B_60) | ~r2_hidden(C_59, A_61) | ~r1_tarski(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.91/1.70  tff(c_122, plain, (![A_74, B_75, B_76]: (r2_hidden('#skF_1'(A_74, B_75), B_76) | ~r1_tarski(A_74, B_76) | r1_tarski(A_74, B_75))), inference(resolution, [status(thm)], [c_6, c_76])).
% 3.91/1.70  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.91/1.70  tff(c_154, plain, (![A_84, B_85, B_86, B_87]: (r2_hidden('#skF_1'(A_84, B_85), B_86) | ~r1_tarski(B_87, B_86) | ~r1_tarski(A_84, B_87) | r1_tarski(A_84, B_85))), inference(resolution, [status(thm)], [c_122, c_2])).
% 3.91/1.70  tff(c_164, plain, (![A_88, B_89]: (r2_hidden('#skF_1'(A_88, B_89), u1_struct_0('#skF_3')) | ~r1_tarski(A_88, '#skF_5') | r1_tarski(A_88, B_89))), inference(resolution, [status(thm)], [c_47, c_154])).
% 3.91/1.70  tff(c_175, plain, (![A_88]: (~r1_tarski(A_88, '#skF_5') | r1_tarski(A_88, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_164, c_4])).
% 3.91/1.70  tff(c_521, plain, (![B_148, A_149, C_150]: (m1_connsp_2(B_148, A_149, C_150) | ~r2_hidden(C_150, B_148) | ~v3_pre_topc(B_148, A_149) | ~m1_subset_1(C_150, u1_struct_0(A_149)) | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0(A_149))) | ~l1_pre_topc(A_149) | ~v2_pre_topc(A_149) | v2_struct_0(A_149))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.91/1.70  tff(c_523, plain, (![B_148]: (m1_connsp_2(B_148, '#skF_3', '#skF_4') | ~r2_hidden('#skF_4', B_148) | ~v3_pre_topc(B_148, '#skF_3') | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_521])).
% 3.91/1.70  tff(c_526, plain, (![B_148]: (m1_connsp_2(B_148, '#skF_3', '#skF_4') | ~r2_hidden('#skF_4', B_148) | ~v3_pre_topc(B_148, '#skF_3') | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_523])).
% 3.91/1.70  tff(c_528, plain, (![B_151]: (m1_connsp_2(B_151, '#skF_3', '#skF_4') | ~r2_hidden('#skF_4', B_151) | ~v3_pre_topc(B_151, '#skF_3') | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_526])).
% 3.91/1.70  tff(c_546, plain, (![A_152]: (m1_connsp_2(A_152, '#skF_3', '#skF_4') | ~r2_hidden('#skF_4', A_152) | ~v3_pre_topc(A_152, '#skF_3') | ~r1_tarski(A_152, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_10, c_528])).
% 3.91/1.70  tff(c_591, plain, (![A_155]: (m1_connsp_2(A_155, '#skF_3', '#skF_4') | ~r2_hidden('#skF_4', A_155) | ~v3_pre_topc(A_155, '#skF_3') | ~r1_tarski(A_155, '#skF_5'))), inference(resolution, [status(thm)], [c_175, c_546])).
% 3.91/1.70  tff(c_176, plain, (![A_90]: (~r1_tarski(A_90, '#skF_5') | r1_tarski(A_90, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_164, c_4])).
% 3.91/1.70  tff(c_53, plain, (![D_53]: (~r1_tarski(D_53, '#skF_5') | ~v3_pre_topc(D_53, '#skF_3') | ~m1_connsp_2(D_53, '#skF_3', '#skF_4') | ~m1_subset_1(D_53, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(D_53))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.91/1.70  tff(c_61, plain, (![A_6]: (~r1_tarski(A_6, '#skF_5') | ~v3_pre_topc(A_6, '#skF_3') | ~m1_connsp_2(A_6, '#skF_3', '#skF_4') | v1_xboole_0(A_6) | ~r1_tarski(A_6, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_10, c_53])).
% 3.91/1.70  tff(c_189, plain, (![A_90]: (~v3_pre_topc(A_90, '#skF_3') | ~m1_connsp_2(A_90, '#skF_3', '#skF_4') | v1_xboole_0(A_90) | ~r1_tarski(A_90, '#skF_5'))), inference(resolution, [status(thm)], [c_176, c_61])).
% 3.91/1.70  tff(c_600, plain, (![A_156]: (v1_xboole_0(A_156) | ~r2_hidden('#skF_4', A_156) | ~v3_pre_topc(A_156, '#skF_3') | ~r1_tarski(A_156, '#skF_5'))), inference(resolution, [status(thm)], [c_591, c_189])).
% 3.91/1.70  tff(c_1210, plain, (![B_220]: (v1_xboole_0('#skF_2'('#skF_3', B_220, '#skF_5')) | ~r2_hidden('#skF_4', '#skF_2'('#skF_3', B_220, '#skF_5')) | ~r1_tarski('#skF_2'('#skF_3', B_220, '#skF_5'), '#skF_5') | ~r2_hidden(B_220, k1_tops_1('#skF_3', '#skF_5')))), inference(resolution, [status(thm)], [c_310, c_600])).
% 3.91/1.70  tff(c_1219, plain, (v1_xboole_0('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~r1_tarski('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_5') | ~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_422, c_1210])).
% 3.91/1.70  tff(c_1227, plain, (v1_xboole_0('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~r1_tarski('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_5') | ~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_1219])).
% 3.91/1.70  tff(c_1228, plain, (~r1_tarski('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_5') | ~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_671, c_1227])).
% 3.91/1.70  tff(c_1229, plain, (~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_1228])).
% 3.91/1.70  tff(c_1235, plain, (~m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_397, c_1229])).
% 3.91/1.70  tff(c_1242, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_40, c_38, c_36, c_32, c_1235])).
% 3.91/1.70  tff(c_1244, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_1242])).
% 3.91/1.70  tff(c_1245, plain, (~r1_tarski('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_1228])).
% 3.91/1.70  tff(c_1282, plain, (~m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_425, c_1245])).
% 3.91/1.70  tff(c_1292, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_1282])).
% 3.91/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.70  
% 3.91/1.70  Inference rules
% 3.91/1.70  ----------------------
% 3.91/1.70  #Ref     : 0
% 3.91/1.70  #Sup     : 285
% 3.91/1.70  #Fact    : 0
% 3.91/1.70  #Define  : 0
% 3.91/1.70  #Split   : 11
% 3.91/1.70  #Chain   : 0
% 3.91/1.70  #Close   : 0
% 3.91/1.70  
% 3.91/1.70  Ordering : KBO
% 3.91/1.70  
% 3.91/1.70  Simplification rules
% 3.91/1.70  ----------------------
% 3.91/1.70  #Subsume      : 101
% 3.91/1.70  #Demod        : 118
% 3.91/1.70  #Tautology    : 11
% 3.91/1.70  #SimpNegUnit  : 10
% 3.91/1.70  #BackRed      : 0
% 3.91/1.70  
% 3.91/1.70  #Partial instantiations: 0
% 3.91/1.70  #Strategies tried      : 1
% 3.91/1.70  
% 3.91/1.70  Timing (in seconds)
% 3.91/1.70  ----------------------
% 3.91/1.70  Preprocessing        : 0.32
% 3.91/1.70  Parsing              : 0.18
% 3.91/1.70  CNF conversion       : 0.03
% 3.91/1.71  Main loop            : 0.54
% 3.91/1.71  Inferencing          : 0.19
% 3.91/1.71  Reduction            : 0.15
% 3.91/1.71  Demodulation         : 0.10
% 3.91/1.71  BG Simplification    : 0.02
% 3.91/1.71  Subsumption          : 0.14
% 3.91/1.71  Abstraction          : 0.02
% 3.91/1.71  MUC search           : 0.00
% 3.91/1.71  Cooper               : 0.00
% 3.91/1.71  Total                : 0.90
% 3.91/1.71  Index Insertion      : 0.00
% 3.91/1.71  Index Deletion       : 0.00
% 3.91/1.71  Index Matching       : 0.00
% 3.91/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
