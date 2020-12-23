%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:10 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 348 expanded)
%              Number of leaves         :   27 ( 135 expanded)
%              Depth                    :   16
%              Number of atoms          :  222 (1558 expanded)
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

tff(f_137,negated_conjecture,(
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

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_107,axiom,(
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

tff(f_88,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_36,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,B_46)
      | ~ m1_subset_1(A_45,k1_zfmisc_1(B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_44,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_36])).

tff(c_32,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_24,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_161,plain,(
    ! [B_81,A_82,C_83] :
      ( r2_hidden(B_81,k1_tops_1(A_82,C_83))
      | ~ m1_connsp_2(C_83,A_82,B_81)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ m1_subset_1(B_81,u1_struct_0(A_82))
      | ~ l1_pre_topc(A_82)
      | ~ v2_pre_topc(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_170,plain,(
    ! [B_81,A_82,A_1] :
      ( r2_hidden(B_81,k1_tops_1(A_82,A_1))
      | ~ m1_connsp_2(A_1,A_82,B_81)
      | ~ m1_subset_1(B_81,u1_struct_0(A_82))
      | ~ l1_pre_topc(A_82)
      | ~ v2_pre_topc(A_82)
      | v2_struct_0(A_82)
      | ~ r1_tarski(A_1,u1_struct_0(A_82)) ) ),
    inference(resolution,[status(thm)],[c_4,c_161])).

tff(c_116,plain,(
    ! [A_63,B_64] :
      ( v3_pre_topc(k1_tops_1(A_63,B_64),A_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_123,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_116])).

tff(c_128,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_123])).

tff(c_66,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(k1_tops_1(A_51,B_52),B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_71,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_66])).

tff(c_75,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_71])).

tff(c_90,plain,(
    ! [A_59,B_60] :
      ( m1_subset_1(k1_tops_1(A_59,B_60),k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22,plain,(
    ! [D_42] :
      ( ~ r1_tarski(D_42,'#skF_3')
      | ~ v3_pre_topc(D_42,'#skF_1')
      | ~ m1_connsp_2(D_42,'#skF_1','#skF_2')
      | ~ m1_subset_1(D_42,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v1_xboole_0(D_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_98,plain,(
    ! [B_60] :
      ( ~ r1_tarski(k1_tops_1('#skF_1',B_60),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_60),'#skF_1')
      | ~ m1_connsp_2(k1_tops_1('#skF_1',B_60),'#skF_1','#skF_2')
      | v1_xboole_0(k1_tops_1('#skF_1',B_60))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_90,c_22])).

tff(c_140,plain,(
    ! [B_77] :
      ( ~ r1_tarski(k1_tops_1('#skF_1',B_77),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_77),'#skF_1')
      | ~ m1_connsp_2(k1_tops_1('#skF_1',B_77),'#skF_1','#skF_2')
      | v1_xboole_0(k1_tops_1('#skF_1',B_77))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_98])).

tff(c_151,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1','#skF_2')
    | v1_xboole_0(k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_26,c_140])).

tff(c_158,plain,
    ( ~ m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1','#skF_2')
    | v1_xboole_0(k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_75,c_151])).

tff(c_159,plain,(
    ~ m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k1_tops_1(A_6,B_7),k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_190,plain,(
    ! [B_85,A_86,C_87] :
      ( m1_connsp_2(B_85,A_86,C_87)
      | ~ r2_hidden(C_87,B_85)
      | ~ v3_pre_topc(B_85,A_86)
      | ~ m1_subset_1(C_87,u1_struct_0(A_86))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86)
      | ~ v2_pre_topc(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_192,plain,(
    ! [B_85] :
      ( m1_connsp_2(B_85,'#skF_1','#skF_2')
      | ~ r2_hidden('#skF_2',B_85)
      | ~ v3_pre_topc(B_85,'#skF_1')
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_190])).

tff(c_195,plain,(
    ! [B_85] :
      ( m1_connsp_2(B_85,'#skF_1','#skF_2')
      | ~ r2_hidden('#skF_2',B_85)
      | ~ v3_pre_topc(B_85,'#skF_1')
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_192])).

tff(c_197,plain,(
    ! [B_88] :
      ( m1_connsp_2(B_88,'#skF_1','#skF_2')
      | ~ r2_hidden('#skF_2',B_88)
      | ~ v3_pre_topc(B_88,'#skF_1')
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_195])).

tff(c_201,plain,(
    ! [B_7] :
      ( m1_connsp_2(k1_tops_1('#skF_1',B_7),'#skF_1','#skF_2')
      | ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_7))
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_7),'#skF_1')
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_8,c_197])).

tff(c_263,plain,(
    ! [B_93] :
      ( m1_connsp_2(k1_tops_1('#skF_1',B_93),'#skF_1','#skF_2')
      | ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_93))
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_93),'#skF_1')
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_201])).

tff(c_274,plain,
    ( m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1','#skF_2')
    | ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_263])).

tff(c_281,plain,
    ( m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1','#skF_2')
    | ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_274])).

tff(c_282,plain,(
    ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_159,c_281])).

tff(c_295,plain,
    ( ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_170,c_282])).

tff(c_301,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_32,c_30,c_28,c_24,c_295])).

tff(c_303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_301])).

tff(c_304,plain,(
    v1_xboole_0(k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_305,plain,(
    m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_18,plain,(
    ! [C_23,A_20,B_21] :
      ( m1_subset_1(C_23,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ m1_connsp_2(C_23,A_20,B_21)
      | ~ m1_subset_1(B_21,u1_struct_0(A_20))
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_307,plain,
    ( m1_subset_1(k1_tops_1('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_305,c_18])).

tff(c_310,plain,
    ( m1_subset_1(k1_tops_1('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_307])).

tff(c_311,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_310])).

tff(c_12,plain,(
    ! [A_10,B_12] :
      ( r1_tarski(k1_tops_1(A_10,B_12),B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_318,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_3')),k1_tops_1('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_311,c_12])).

tff(c_333,plain,(
    r1_tarski(k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_3')),k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_318])).

tff(c_346,plain,(
    ! [B_100,A_101,C_102] :
      ( r2_hidden(B_100,k1_tops_1(A_101,C_102))
      | ~ m1_connsp_2(C_102,A_101,B_100)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ m1_subset_1(B_100,u1_struct_0(A_101))
      | ~ l1_pre_topc(A_101)
      | ~ v2_pre_topc(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_348,plain,(
    ! [B_100] :
      ( r2_hidden(B_100,k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_3')))
      | ~ m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1',B_100)
      | ~ m1_subset_1(B_100,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_311,c_346])).

tff(c_358,plain,(
    ! [B_100] :
      ( r2_hidden(B_100,k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_3')))
      | ~ m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1',B_100)
      | ~ m1_subset_1(B_100,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_348])).

tff(c_436,plain,(
    ! [B_109] :
      ( r2_hidden(B_109,k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_3')))
      | ~ m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1',B_109)
      | ~ m1_subset_1(B_109,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_358])).

tff(c_58,plain,(
    ! [C_48,B_49,A_50] :
      ( ~ v1_xboole_0(C_48)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(C_48))
      | ~ r2_hidden(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_63,plain,(
    ! [B_2,A_50,A_1] :
      ( ~ v1_xboole_0(B_2)
      | ~ r2_hidden(A_50,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_58])).

tff(c_450,plain,(
    ! [B_2,B_109] :
      ( ~ v1_xboole_0(B_2)
      | ~ r1_tarski(k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_3')),B_2)
      | ~ m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1',B_109)
      | ~ m1_subset_1(B_109,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_436,c_63])).

tff(c_495,plain,(
    ! [B_115] :
      ( ~ m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1',B_115)
      | ~ m1_subset_1(B_115,u1_struct_0('#skF_1')) ) ),
    inference(splitLeft,[status(thm)],[c_450])).

tff(c_498,plain,(
    ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_305,c_495])).

tff(c_502,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_498])).

tff(c_504,plain,(
    ! [B_116] :
      ( ~ v1_xboole_0(B_116)
      | ~ r1_tarski(k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_3')),B_116) ) ),
    inference(splitRight,[status(thm)],[c_450])).

tff(c_507,plain,(
    ~ v1_xboole_0(k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_333,c_504])).

tff(c_523,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_507])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:42:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.41  
% 2.61/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.41  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.61/1.41  
% 2.61/1.41  %Foreground sorts:
% 2.61/1.41  
% 2.61/1.41  
% 2.61/1.41  %Background operators:
% 2.61/1.41  
% 2.61/1.41  
% 2.61/1.41  %Foreground operators:
% 2.61/1.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.61/1.41  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.61/1.41  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.61/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.61/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.41  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.61/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.61/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.61/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.61/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.61/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.41  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.61/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.61/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.61/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.61/1.41  
% 2.61/1.43  tff(f_137, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(C, A, B) & (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~((m1_connsp_2(D, A, B) & v3_pre_topc(D, A)) & r1_tarski(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_connsp_2)).
% 2.61/1.43  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.61/1.43  tff(f_74, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 2.61/1.43  tff(f_50, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 2.61/1.43  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 2.61/1.43  tff(f_42, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 2.61/1.43  tff(f_107, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 2.61/1.43  tff(f_88, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 2.61/1.43  tff(f_36, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.61/1.43  tff(c_34, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.61/1.43  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.61/1.43  tff(c_36, plain, (![A_45, B_46]: (r1_tarski(A_45, B_46) | ~m1_subset_1(A_45, k1_zfmisc_1(B_46)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.61/1.43  tff(c_44, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_36])).
% 2.61/1.43  tff(c_32, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.61/1.43  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.61/1.43  tff(c_28, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.61/1.43  tff(c_24, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.61/1.43  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.61/1.43  tff(c_161, plain, (![B_81, A_82, C_83]: (r2_hidden(B_81, k1_tops_1(A_82, C_83)) | ~m1_connsp_2(C_83, A_82, B_81) | ~m1_subset_1(C_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~m1_subset_1(B_81, u1_struct_0(A_82)) | ~l1_pre_topc(A_82) | ~v2_pre_topc(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.61/1.43  tff(c_170, plain, (![B_81, A_82, A_1]: (r2_hidden(B_81, k1_tops_1(A_82, A_1)) | ~m1_connsp_2(A_1, A_82, B_81) | ~m1_subset_1(B_81, u1_struct_0(A_82)) | ~l1_pre_topc(A_82) | ~v2_pre_topc(A_82) | v2_struct_0(A_82) | ~r1_tarski(A_1, u1_struct_0(A_82)))), inference(resolution, [status(thm)], [c_4, c_161])).
% 2.61/1.43  tff(c_116, plain, (![A_63, B_64]: (v3_pre_topc(k1_tops_1(A_63, B_64), A_63) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.61/1.43  tff(c_123, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_116])).
% 2.61/1.43  tff(c_128, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_123])).
% 2.61/1.43  tff(c_66, plain, (![A_51, B_52]: (r1_tarski(k1_tops_1(A_51, B_52), B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.61/1.43  tff(c_71, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_66])).
% 2.61/1.43  tff(c_75, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_71])).
% 2.61/1.43  tff(c_90, plain, (![A_59, B_60]: (m1_subset_1(k1_tops_1(A_59, B_60), k1_zfmisc_1(u1_struct_0(A_59))) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.61/1.43  tff(c_22, plain, (![D_42]: (~r1_tarski(D_42, '#skF_3') | ~v3_pre_topc(D_42, '#skF_1') | ~m1_connsp_2(D_42, '#skF_1', '#skF_2') | ~m1_subset_1(D_42, k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(D_42))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.61/1.43  tff(c_98, plain, (![B_60]: (~r1_tarski(k1_tops_1('#skF_1', B_60), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_60), '#skF_1') | ~m1_connsp_2(k1_tops_1('#skF_1', B_60), '#skF_1', '#skF_2') | v1_xboole_0(k1_tops_1('#skF_1', B_60)) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_90, c_22])).
% 2.61/1.43  tff(c_140, plain, (![B_77]: (~r1_tarski(k1_tops_1('#skF_1', B_77), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_77), '#skF_1') | ~m1_connsp_2(k1_tops_1('#skF_1', B_77), '#skF_1', '#skF_2') | v1_xboole_0(k1_tops_1('#skF_1', B_77)) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_98])).
% 2.61/1.43  tff(c_151, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', '#skF_2') | v1_xboole_0(k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_140])).
% 2.61/1.43  tff(c_158, plain, (~m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', '#skF_2') | v1_xboole_0(k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_75, c_151])).
% 2.61/1.43  tff(c_159, plain, (~m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_158])).
% 2.61/1.43  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(k1_tops_1(A_6, B_7), k1_zfmisc_1(u1_struct_0(A_6))) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.61/1.43  tff(c_190, plain, (![B_85, A_86, C_87]: (m1_connsp_2(B_85, A_86, C_87) | ~r2_hidden(C_87, B_85) | ~v3_pre_topc(B_85, A_86) | ~m1_subset_1(C_87, u1_struct_0(A_86)) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86) | ~v2_pre_topc(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.61/1.43  tff(c_192, plain, (![B_85]: (m1_connsp_2(B_85, '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', B_85) | ~v3_pre_topc(B_85, '#skF_1') | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_190])).
% 2.61/1.43  tff(c_195, plain, (![B_85]: (m1_connsp_2(B_85, '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', B_85) | ~v3_pre_topc(B_85, '#skF_1') | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_192])).
% 2.61/1.43  tff(c_197, plain, (![B_88]: (m1_connsp_2(B_88, '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', B_88) | ~v3_pre_topc(B_88, '#skF_1') | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_34, c_195])).
% 2.61/1.43  tff(c_201, plain, (![B_7]: (m1_connsp_2(k1_tops_1('#skF_1', B_7), '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_7)) | ~v3_pre_topc(k1_tops_1('#skF_1', B_7), '#skF_1') | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_197])).
% 2.61/1.43  tff(c_263, plain, (![B_93]: (m1_connsp_2(k1_tops_1('#skF_1', B_93), '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_93)) | ~v3_pre_topc(k1_tops_1('#skF_1', B_93), '#skF_1') | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_201])).
% 2.61/1.43  tff(c_274, plain, (m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_26, c_263])).
% 2.61/1.43  tff(c_281, plain, (m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_274])).
% 2.61/1.43  tff(c_282, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_159, c_281])).
% 2.61/1.43  tff(c_295, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_170, c_282])).
% 2.61/1.43  tff(c_301, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_32, c_30, c_28, c_24, c_295])).
% 2.61/1.43  tff(c_303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_301])).
% 2.61/1.43  tff(c_304, plain, (v1_xboole_0(k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_158])).
% 2.61/1.43  tff(c_305, plain, (m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_158])).
% 2.61/1.43  tff(c_18, plain, (![C_23, A_20, B_21]: (m1_subset_1(C_23, k1_zfmisc_1(u1_struct_0(A_20))) | ~m1_connsp_2(C_23, A_20, B_21) | ~m1_subset_1(B_21, u1_struct_0(A_20)) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.61/1.43  tff(c_307, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_305, c_18])).
% 2.61/1.43  tff(c_310, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_307])).
% 2.61/1.43  tff(c_311, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_34, c_310])).
% 2.61/1.43  tff(c_12, plain, (![A_10, B_12]: (r1_tarski(k1_tops_1(A_10, B_12), B_12) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.61/1.43  tff(c_318, plain, (r1_tarski(k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_3')), k1_tops_1('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_311, c_12])).
% 2.61/1.43  tff(c_333, plain, (r1_tarski(k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_3')), k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_318])).
% 2.61/1.43  tff(c_346, plain, (![B_100, A_101, C_102]: (r2_hidden(B_100, k1_tops_1(A_101, C_102)) | ~m1_connsp_2(C_102, A_101, B_100) | ~m1_subset_1(C_102, k1_zfmisc_1(u1_struct_0(A_101))) | ~m1_subset_1(B_100, u1_struct_0(A_101)) | ~l1_pre_topc(A_101) | ~v2_pre_topc(A_101) | v2_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.61/1.43  tff(c_348, plain, (![B_100]: (r2_hidden(B_100, k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', B_100) | ~m1_subset_1(B_100, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_311, c_346])).
% 2.61/1.43  tff(c_358, plain, (![B_100]: (r2_hidden(B_100, k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', B_100) | ~m1_subset_1(B_100, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_348])).
% 2.61/1.43  tff(c_436, plain, (![B_109]: (r2_hidden(B_109, k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', B_109) | ~m1_subset_1(B_109, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_34, c_358])).
% 2.61/1.43  tff(c_58, plain, (![C_48, B_49, A_50]: (~v1_xboole_0(C_48) | ~m1_subset_1(B_49, k1_zfmisc_1(C_48)) | ~r2_hidden(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.61/1.43  tff(c_63, plain, (![B_2, A_50, A_1]: (~v1_xboole_0(B_2) | ~r2_hidden(A_50, A_1) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_58])).
% 2.61/1.43  tff(c_450, plain, (![B_2, B_109]: (~v1_xboole_0(B_2) | ~r1_tarski(k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_3')), B_2) | ~m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', B_109) | ~m1_subset_1(B_109, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_436, c_63])).
% 2.61/1.43  tff(c_495, plain, (![B_115]: (~m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', B_115) | ~m1_subset_1(B_115, u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_450])).
% 2.61/1.43  tff(c_498, plain, (~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_305, c_495])).
% 2.61/1.43  tff(c_502, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_498])).
% 2.61/1.43  tff(c_504, plain, (![B_116]: (~v1_xboole_0(B_116) | ~r1_tarski(k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_3')), B_116))), inference(splitRight, [status(thm)], [c_450])).
% 2.61/1.43  tff(c_507, plain, (~v1_xboole_0(k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_333, c_504])).
% 2.61/1.43  tff(c_523, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_304, c_507])).
% 2.61/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.43  
% 2.61/1.43  Inference rules
% 2.61/1.43  ----------------------
% 2.61/1.43  #Ref     : 0
% 2.61/1.43  #Sup     : 87
% 2.61/1.43  #Fact    : 0
% 2.61/1.43  #Define  : 0
% 2.61/1.43  #Split   : 6
% 2.61/1.43  #Chain   : 0
% 2.61/1.43  #Close   : 0
% 2.61/1.43  
% 2.61/1.43  Ordering : KBO
% 2.61/1.43  
% 2.61/1.43  Simplification rules
% 2.61/1.43  ----------------------
% 2.61/1.43  #Subsume      : 17
% 2.61/1.43  #Demod        : 84
% 2.61/1.43  #Tautology    : 11
% 2.61/1.43  #SimpNegUnit  : 12
% 2.61/1.43  #BackRed      : 0
% 2.61/1.43  
% 2.61/1.43  #Partial instantiations: 0
% 2.61/1.43  #Strategies tried      : 1
% 2.61/1.43  
% 2.61/1.43  Timing (in seconds)
% 2.61/1.43  ----------------------
% 2.61/1.44  Preprocessing        : 0.29
% 2.61/1.44  Parsing              : 0.17
% 2.61/1.44  CNF conversion       : 0.02
% 2.61/1.44  Main loop            : 0.30
% 2.61/1.44  Inferencing          : 0.12
% 2.61/1.44  Reduction            : 0.09
% 2.61/1.44  Demodulation         : 0.06
% 2.61/1.44  BG Simplification    : 0.02
% 2.61/1.44  Subsumption          : 0.06
% 2.61/1.44  Abstraction          : 0.01
% 2.61/1.44  MUC search           : 0.00
% 2.61/1.44  Cooper               : 0.00
% 2.61/1.44  Total                : 0.64
% 2.61/1.44  Index Insertion      : 0.00
% 2.61/1.44  Index Deletion       : 0.00
% 2.61/1.44  Index Matching       : 0.00
% 2.61/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
