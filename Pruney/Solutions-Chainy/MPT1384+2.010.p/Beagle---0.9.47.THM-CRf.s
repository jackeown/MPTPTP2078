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
% DateTime   : Thu Dec  3 10:24:15 EST 2020

% Result     : Theorem 5.39s
% Output     : CNFRefutation 5.39s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 288 expanded)
%              Number of leaves         :   27 ( 108 expanded)
%              Depth                    :   21
%              Number of atoms          :  347 (1148 expanded)
%              Number of equality atoms :   15 (  38 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_128,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ~ ( r2_hidden(C,B)
                      & ! [D] :
                          ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                         => ~ ( m1_connsp_2(D,A,C)
                              & r1_tarski(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_connsp_2)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_101,axiom,(
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

tff(f_84,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( v3_pre_topc(D,B)
                     => k1_tops_1(B,D) = D )
                    & ( k1_tops_1(A,C) = C
                     => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_38,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_69,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_32,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_30,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_99,plain,(
    ! [A_81,B_82] :
      ( r1_tarski(k1_tops_1(A_81,B_82),B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_101,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_99])).

tff(c_104,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_101])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_107,plain,
    ( k1_tops_1('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_104,c_8])).

tff(c_108,plain,(
    ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_94,plain,(
    ! [A_77,C_78,B_79] :
      ( m1_subset_1(A_77,C_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(C_78))
      | ~ r2_hidden(A_77,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_97,plain,(
    ! [A_77] :
      ( m1_subset_1(A_77,u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_77,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_94])).

tff(c_50,plain,(
    ! [C_64] :
      ( v3_pre_topc('#skF_3','#skF_2')
      | r1_tarski('#skF_5'(C_64),'#skF_3')
      | ~ r2_hidden(C_64,'#skF_3')
      | ~ m1_subset_1(C_64,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_71,plain,(
    ! [C_64] :
      ( r1_tarski('#skF_5'(C_64),'#skF_3')
      | ~ r2_hidden(C_64,'#skF_3')
      | ~ m1_subset_1(C_64,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_50])).

tff(c_90,plain,(
    ! [C_74,B_75,A_76] :
      ( r2_hidden(C_74,B_75)
      | ~ r2_hidden(C_74,A_76)
      | ~ r1_tarski(A_76,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_109,plain,(
    ! [A_83,B_84,B_85] :
      ( r2_hidden('#skF_1'(A_83,B_84),B_85)
      | ~ r1_tarski(A_83,B_85)
      | r1_tarski(A_83,B_84) ) ),
    inference(resolution,[status(thm)],[c_6,c_90])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_119,plain,(
    ! [A_87,B_88,B_89,B_90] :
      ( r2_hidden('#skF_1'(A_87,B_88),B_89)
      | ~ r1_tarski(B_90,B_89)
      | ~ r1_tarski(A_87,B_90)
      | r1_tarski(A_87,B_88) ) ),
    inference(resolution,[status(thm)],[c_109,c_2])).

tff(c_227,plain,(
    ! [A_111,B_112,C_113] :
      ( r2_hidden('#skF_1'(A_111,B_112),'#skF_3')
      | ~ r1_tarski(A_111,'#skF_5'(C_113))
      | r1_tarski(A_111,B_112)
      | ~ r2_hidden(C_113,'#skF_3')
      | ~ m1_subset_1(C_113,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_71,c_119])).

tff(c_263,plain,(
    ! [C_118,B_119] :
      ( r2_hidden('#skF_1'('#skF_5'(C_118),B_119),'#skF_3')
      | r1_tarski('#skF_5'(C_118),B_119)
      | ~ r2_hidden(C_118,'#skF_3')
      | ~ m1_subset_1(C_118,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_12,c_227])).

tff(c_311,plain,(
    ! [C_129,B_130,B_131] :
      ( r2_hidden('#skF_1'('#skF_5'(C_129),B_130),B_131)
      | ~ r1_tarski('#skF_3',B_131)
      | r1_tarski('#skF_5'(C_129),B_130)
      | ~ r2_hidden(C_129,'#skF_3')
      | ~ m1_subset_1(C_129,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_263,c_2])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_324,plain,(
    ! [B_131,C_129] :
      ( ~ r1_tarski('#skF_3',B_131)
      | r1_tarski('#skF_5'(C_129),B_131)
      | ~ r2_hidden(C_129,'#skF_3')
      | ~ m1_subset_1(C_129,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_311,c_4])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_66,plain,(
    ! [C_64] :
      ( v3_pre_topc('#skF_3','#skF_2')
      | m1_subset_1('#skF_5'(C_64),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(C_64,'#skF_3')
      | ~ m1_subset_1(C_64,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_167,plain,(
    ! [C_64] :
      ( m1_subset_1('#skF_5'(C_64),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(C_64,'#skF_3')
      | ~ m1_subset_1(C_64,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_66])).

tff(c_58,plain,(
    ! [C_64] :
      ( v3_pre_topc('#skF_3','#skF_2')
      | m1_connsp_2('#skF_5'(C_64),'#skF_2',C_64)
      | ~ r2_hidden(C_64,'#skF_3')
      | ~ m1_subset_1(C_64,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_165,plain,(
    ! [C_64] :
      ( m1_connsp_2('#skF_5'(C_64),'#skF_2',C_64)
      | ~ r2_hidden(C_64,'#skF_3')
      | ~ m1_subset_1(C_64,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_58])).

tff(c_18,plain,(
    ! [A_14,B_18,C_20] :
      ( r1_tarski(k1_tops_1(A_14,B_18),k1_tops_1(A_14,C_20))
      | ~ r1_tarski(B_18,C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_583,plain,(
    ! [B_174,A_175,C_176] :
      ( r2_hidden(B_174,k1_tops_1(A_175,C_176))
      | ~ m1_connsp_2(C_176,A_175,B_174)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ m1_subset_1(B_174,u1_struct_0(A_175))
      | ~ l1_pre_topc(A_175)
      | ~ v2_pre_topc(A_175)
      | v2_struct_0(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_585,plain,(
    ! [B_174,C_64] :
      ( r2_hidden(B_174,k1_tops_1('#skF_2','#skF_5'(C_64)))
      | ~ m1_connsp_2('#skF_5'(C_64),'#skF_2',B_174)
      | ~ m1_subset_1(B_174,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r2_hidden(C_64,'#skF_3')
      | ~ m1_subset_1(C_64,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_167,c_583])).

tff(c_590,plain,(
    ! [B_174,C_64] :
      ( r2_hidden(B_174,k1_tops_1('#skF_2','#skF_5'(C_64)))
      | ~ m1_connsp_2('#skF_5'(C_64),'#skF_2',B_174)
      | ~ m1_subset_1(B_174,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ r2_hidden(C_64,'#skF_3')
      | ~ m1_subset_1(C_64,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_585])).

tff(c_643,plain,(
    ! [B_181,C_182] :
      ( r2_hidden(B_181,k1_tops_1('#skF_2','#skF_5'(C_182)))
      | ~ m1_connsp_2('#skF_5'(C_182),'#skF_2',B_181)
      | ~ m1_subset_1(B_181,u1_struct_0('#skF_2'))
      | ~ r2_hidden(C_182,'#skF_3')
      | ~ m1_subset_1(C_182,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_590])).

tff(c_823,plain,(
    ! [B_203,B_204,C_205] :
      ( r2_hidden(B_203,B_204)
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_5'(C_205)),B_204)
      | ~ m1_connsp_2('#skF_5'(C_205),'#skF_2',B_203)
      | ~ m1_subset_1(B_203,u1_struct_0('#skF_2'))
      | ~ r2_hidden(C_205,'#skF_3')
      | ~ m1_subset_1(C_205,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_643,c_2])).

tff(c_830,plain,(
    ! [B_203,C_20,C_205] :
      ( r2_hidden(B_203,k1_tops_1('#skF_2',C_20))
      | ~ m1_connsp_2('#skF_5'(C_205),'#skF_2',B_203)
      | ~ m1_subset_1(B_203,u1_struct_0('#skF_2'))
      | ~ r2_hidden(C_205,'#skF_3')
      | ~ m1_subset_1(C_205,u1_struct_0('#skF_2'))
      | ~ r1_tarski('#skF_5'(C_205),C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_5'(C_205),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_823])).

tff(c_1382,plain,(
    ! [B_302,C_303,C_304] :
      ( r2_hidden(B_302,k1_tops_1('#skF_2',C_303))
      | ~ m1_connsp_2('#skF_5'(C_304),'#skF_2',B_302)
      | ~ m1_subset_1(B_302,u1_struct_0('#skF_2'))
      | ~ r2_hidden(C_304,'#skF_3')
      | ~ m1_subset_1(C_304,u1_struct_0('#skF_2'))
      | ~ r1_tarski('#skF_5'(C_304),C_303)
      | ~ m1_subset_1(C_303,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_5'(C_304),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_830])).

tff(c_1396,plain,(
    ! [C_305,C_306] :
      ( r2_hidden(C_305,k1_tops_1('#skF_2',C_306))
      | ~ r1_tarski('#skF_5'(C_305),C_306)
      | ~ m1_subset_1(C_306,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_5'(C_305),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(C_305,'#skF_3')
      | ~ m1_subset_1(C_305,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_165,c_1382])).

tff(c_1403,plain,(
    ! [C_307] :
      ( r2_hidden(C_307,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski('#skF_5'(C_307),'#skF_3')
      | ~ m1_subset_1('#skF_5'(C_307),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(C_307,'#skF_3')
      | ~ m1_subset_1(C_307,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_28,c_1396])).

tff(c_1408,plain,(
    ! [C_308] :
      ( r2_hidden(C_308,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski('#skF_5'(C_308),'#skF_3')
      | ~ r2_hidden(C_308,'#skF_3')
      | ~ m1_subset_1(C_308,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_167,c_1403])).

tff(c_24,plain,(
    ! [C_42,A_36,B_40] :
      ( m1_connsp_2(C_42,A_36,B_40)
      | ~ r2_hidden(B_40,k1_tops_1(A_36,C_42))
      | ~ m1_subset_1(C_42,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ m1_subset_1(B_40,u1_struct_0(A_36))
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1410,plain,(
    ! [C_308] :
      ( m1_connsp_2('#skF_3','#skF_2',C_308)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski('#skF_5'(C_308),'#skF_3')
      | ~ r2_hidden(C_308,'#skF_3')
      | ~ m1_subset_1(C_308,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1408,c_24])).

tff(c_1419,plain,(
    ! [C_308] :
      ( m1_connsp_2('#skF_3','#skF_2',C_308)
      | v2_struct_0('#skF_2')
      | ~ r1_tarski('#skF_5'(C_308),'#skF_3')
      | ~ r2_hidden(C_308,'#skF_3')
      | ~ m1_subset_1(C_308,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_1410])).

tff(c_1423,plain,(
    ! [C_309] :
      ( m1_connsp_2('#skF_3','#skF_2',C_309)
      | ~ r1_tarski('#skF_5'(C_309),'#skF_3')
      | ~ r2_hidden(C_309,'#skF_3')
      | ~ m1_subset_1(C_309,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1419])).

tff(c_1427,plain,(
    ! [C_129] :
      ( m1_connsp_2('#skF_3','#skF_2',C_129)
      | ~ r1_tarski('#skF_3','#skF_3')
      | ~ r2_hidden(C_129,'#skF_3')
      | ~ m1_subset_1(C_129,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_324,c_1423])).

tff(c_1435,plain,(
    ! [C_310] :
      ( m1_connsp_2('#skF_3','#skF_2',C_310)
      | ~ r2_hidden(C_310,'#skF_3')
      | ~ m1_subset_1(C_310,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1427])).

tff(c_1454,plain,(
    ! [A_311] :
      ( m1_connsp_2('#skF_3','#skF_2',A_311)
      | ~ r2_hidden(A_311,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_97,c_1435])).

tff(c_587,plain,(
    ! [B_174] :
      ( r2_hidden(B_174,k1_tops_1('#skF_2','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_2',B_174)
      | ~ m1_subset_1(B_174,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_583])).

tff(c_594,plain,(
    ! [B_174] :
      ( r2_hidden(B_174,k1_tops_1('#skF_2','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_2',B_174)
      | ~ m1_subset_1(B_174,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_587])).

tff(c_596,plain,(
    ! [B_177] :
      ( r2_hidden(B_177,k1_tops_1('#skF_2','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_2',B_177)
      | ~ m1_subset_1(B_177,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_594])).

tff(c_658,plain,(
    ! [A_183] :
      ( r1_tarski(A_183,k1_tops_1('#skF_2','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_2','#skF_1'(A_183,k1_tops_1('#skF_2','#skF_3')))
      | ~ m1_subset_1('#skF_1'(A_183,k1_tops_1('#skF_2','#skF_3')),u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_596,c_4])).

tff(c_672,plain,(
    ! [A_183] :
      ( r1_tarski(A_183,k1_tops_1('#skF_2','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_2','#skF_1'(A_183,k1_tops_1('#skF_2','#skF_3')))
      | ~ r2_hidden('#skF_1'(A_183,k1_tops_1('#skF_2','#skF_3')),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_97,c_658])).

tff(c_1467,plain,(
    ! [A_312] :
      ( r1_tarski(A_312,k1_tops_1('#skF_2','#skF_3'))
      | ~ r2_hidden('#skF_1'(A_312,k1_tops_1('#skF_2','#skF_3')),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1454,c_672])).

tff(c_1499,plain,(
    r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_1467])).

tff(c_1516,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_108,c_1499])).

tff(c_1517,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_20,plain,(
    ! [C_33,A_21,D_35,B_29] :
      ( v3_pre_topc(C_33,A_21)
      | k1_tops_1(A_21,C_33) != C_33
      | ~ m1_subset_1(D_35,k1_zfmisc_1(u1_struct_0(B_29)))
      | ~ m1_subset_1(C_33,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(B_29)
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1832,plain,(
    ! [D_375,B_376] :
      ( ~ m1_subset_1(D_375,k1_zfmisc_1(u1_struct_0(B_376)))
      | ~ l1_pre_topc(B_376) ) ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_1838,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_1832])).

tff(c_1845,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1838])).

tff(c_1847,plain,(
    ! [C_377,A_378] :
      ( v3_pre_topc(C_377,A_378)
      | k1_tops_1(A_378,C_377) != C_377
      | ~ m1_subset_1(C_377,k1_zfmisc_1(u1_struct_0(A_378)))
      | ~ l1_pre_topc(A_378)
      | ~ v2_pre_topc(A_378) ) ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_1853,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | k1_tops_1('#skF_2','#skF_3') != '#skF_3'
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_1847])).

tff(c_1859,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1517,c_1853])).

tff(c_1861,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_1859])).

tff(c_1863,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_36,plain,(
    ! [D_63] :
      ( ~ r1_tarski(D_63,'#skF_3')
      | ~ m1_connsp_2(D_63,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_63,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc('#skF_3','#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2061,plain,(
    ! [D_429] :
      ( ~ r1_tarski(D_429,'#skF_3')
      | ~ m1_connsp_2(D_429,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_429,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1863,c_36])).

tff(c_2064,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_connsp_2('#skF_3','#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_2061])).

tff(c_2067,plain,(
    ~ m1_connsp_2('#skF_3','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2064])).

tff(c_1862,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_40,plain,
    ( m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1864,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_1866,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1863,c_1864])).

tff(c_1867,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_22,plain,(
    ! [B_29,D_35,C_33,A_21] :
      ( k1_tops_1(B_29,D_35) = D_35
      | ~ v3_pre_topc(D_35,B_29)
      | ~ m1_subset_1(D_35,k1_zfmisc_1(u1_struct_0(B_29)))
      | ~ m1_subset_1(C_33,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(B_29)
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2018,plain,(
    ! [C_421,A_422] :
      ( ~ m1_subset_1(C_421,k1_zfmisc_1(u1_struct_0(A_422)))
      | ~ l1_pre_topc(A_422)
      | ~ v2_pre_topc(A_422) ) ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_2021,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_2018])).

tff(c_2025,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_2021])).

tff(c_2027,plain,(
    ! [B_423,D_424] :
      ( k1_tops_1(B_423,D_424) = D_424
      | ~ v3_pre_topc(D_424,B_423)
      | ~ m1_subset_1(D_424,k1_zfmisc_1(u1_struct_0(B_423)))
      | ~ l1_pre_topc(B_423) ) ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_2030,plain,
    ( k1_tops_1('#skF_2','#skF_3') = '#skF_3'
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_2027])).

tff(c_2033,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1863,c_2030])).

tff(c_1915,plain,(
    ! [A_398,B_399] :
      ( r1_tarski(k1_tops_1(A_398,B_399),B_399)
      | ~ m1_subset_1(B_399,k1_zfmisc_1(u1_struct_0(A_398)))
      | ~ l1_pre_topc(A_398) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1917,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_1915])).

tff(c_1920,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1917])).

tff(c_1927,plain,
    ( k1_tops_1('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1920,c_8])).

tff(c_1928,plain,(
    ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1927])).

tff(c_2039,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2033,c_1928])).

tff(c_2043,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2039])).

tff(c_2044,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1927])).

tff(c_2142,plain,(
    ! [C_443,A_444,B_445] :
      ( m1_connsp_2(C_443,A_444,B_445)
      | ~ r2_hidden(B_445,k1_tops_1(A_444,C_443))
      | ~ m1_subset_1(C_443,k1_zfmisc_1(u1_struct_0(A_444)))
      | ~ m1_subset_1(B_445,u1_struct_0(A_444))
      | ~ l1_pre_topc(A_444)
      | ~ v2_pre_topc(A_444)
      | v2_struct_0(A_444) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2144,plain,(
    ! [B_445] :
      ( m1_connsp_2('#skF_3','#skF_2',B_445)
      | ~ r2_hidden(B_445,'#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_445,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2044,c_2142])).

tff(c_2155,plain,(
    ! [B_445] :
      ( m1_connsp_2('#skF_3','#skF_2',B_445)
      | ~ r2_hidden(B_445,'#skF_3')
      | ~ m1_subset_1(B_445,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_2144])).

tff(c_2160,plain,(
    ! [B_446] :
      ( m1_connsp_2('#skF_3','#skF_2',B_446)
      | ~ r2_hidden(B_446,'#skF_3')
      | ~ m1_subset_1(B_446,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_2155])).

tff(c_2166,plain,
    ( m1_connsp_2('#skF_3','#skF_2','#skF_4')
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1867,c_2160])).

tff(c_2170,plain,(
    m1_connsp_2('#skF_3','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1862,c_2166])).

tff(c_2172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2067,c_2170])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:05:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.39/2.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.39/2.04  
% 5.39/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.39/2.04  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.39/2.04  
% 5.39/2.04  %Foreground sorts:
% 5.39/2.04  
% 5.39/2.04  
% 5.39/2.04  %Background operators:
% 5.39/2.04  
% 5.39/2.04  
% 5.39/2.04  %Foreground operators:
% 5.39/2.04  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.39/2.04  tff('#skF_5', type, '#skF_5': $i > $i).
% 5.39/2.04  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 5.39/2.04  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.39/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.39/2.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.39/2.04  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.39/2.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.39/2.04  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.39/2.04  tff('#skF_2', type, '#skF_2': $i).
% 5.39/2.04  tff('#skF_3', type, '#skF_3': $i).
% 5.39/2.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.39/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.39/2.04  tff('#skF_4', type, '#skF_4': $i).
% 5.39/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.39/2.04  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.39/2.04  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.39/2.04  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.39/2.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.39/2.04  
% 5.39/2.06  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.39/2.06  tff(f_128, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(D, A, C) & r1_tarski(D, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_connsp_2)).
% 5.39/2.06  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 5.39/2.06  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.39/2.06  tff(f_44, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 5.39/2.06  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 5.39/2.06  tff(f_101, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 5.39/2.06  tff(f_84, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 5.39/2.06  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.39/2.06  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.39/2.06  tff(c_38, plain, (r2_hidden('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.39/2.06  tff(c_69, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_38])).
% 5.39/2.06  tff(c_32, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.39/2.06  tff(c_30, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.39/2.06  tff(c_99, plain, (![A_81, B_82]: (r1_tarski(k1_tops_1(A_81, B_82), B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.39/2.06  tff(c_101, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_99])).
% 5.39/2.06  tff(c_104, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_101])).
% 5.39/2.06  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.39/2.06  tff(c_107, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_104, c_8])).
% 5.39/2.06  tff(c_108, plain, (~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_107])).
% 5.39/2.06  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.39/2.06  tff(c_94, plain, (![A_77, C_78, B_79]: (m1_subset_1(A_77, C_78) | ~m1_subset_1(B_79, k1_zfmisc_1(C_78)) | ~r2_hidden(A_77, B_79))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.39/2.06  tff(c_97, plain, (![A_77]: (m1_subset_1(A_77, u1_struct_0('#skF_2')) | ~r2_hidden(A_77, '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_94])).
% 5.39/2.06  tff(c_50, plain, (![C_64]: (v3_pre_topc('#skF_3', '#skF_2') | r1_tarski('#skF_5'(C_64), '#skF_3') | ~r2_hidden(C_64, '#skF_3') | ~m1_subset_1(C_64, u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.39/2.06  tff(c_71, plain, (![C_64]: (r1_tarski('#skF_5'(C_64), '#skF_3') | ~r2_hidden(C_64, '#skF_3') | ~m1_subset_1(C_64, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_69, c_50])).
% 5.39/2.06  tff(c_90, plain, (![C_74, B_75, A_76]: (r2_hidden(C_74, B_75) | ~r2_hidden(C_74, A_76) | ~r1_tarski(A_76, B_75))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.39/2.06  tff(c_109, plain, (![A_83, B_84, B_85]: (r2_hidden('#skF_1'(A_83, B_84), B_85) | ~r1_tarski(A_83, B_85) | r1_tarski(A_83, B_84))), inference(resolution, [status(thm)], [c_6, c_90])).
% 5.39/2.06  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.39/2.06  tff(c_119, plain, (![A_87, B_88, B_89, B_90]: (r2_hidden('#skF_1'(A_87, B_88), B_89) | ~r1_tarski(B_90, B_89) | ~r1_tarski(A_87, B_90) | r1_tarski(A_87, B_88))), inference(resolution, [status(thm)], [c_109, c_2])).
% 5.39/2.06  tff(c_227, plain, (![A_111, B_112, C_113]: (r2_hidden('#skF_1'(A_111, B_112), '#skF_3') | ~r1_tarski(A_111, '#skF_5'(C_113)) | r1_tarski(A_111, B_112) | ~r2_hidden(C_113, '#skF_3') | ~m1_subset_1(C_113, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_71, c_119])).
% 5.39/2.06  tff(c_263, plain, (![C_118, B_119]: (r2_hidden('#skF_1'('#skF_5'(C_118), B_119), '#skF_3') | r1_tarski('#skF_5'(C_118), B_119) | ~r2_hidden(C_118, '#skF_3') | ~m1_subset_1(C_118, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_12, c_227])).
% 5.39/2.06  tff(c_311, plain, (![C_129, B_130, B_131]: (r2_hidden('#skF_1'('#skF_5'(C_129), B_130), B_131) | ~r1_tarski('#skF_3', B_131) | r1_tarski('#skF_5'(C_129), B_130) | ~r2_hidden(C_129, '#skF_3') | ~m1_subset_1(C_129, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_263, c_2])).
% 5.39/2.06  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.39/2.06  tff(c_324, plain, (![B_131, C_129]: (~r1_tarski('#skF_3', B_131) | r1_tarski('#skF_5'(C_129), B_131) | ~r2_hidden(C_129, '#skF_3') | ~m1_subset_1(C_129, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_311, c_4])).
% 5.39/2.06  tff(c_34, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.39/2.06  tff(c_66, plain, (![C_64]: (v3_pre_topc('#skF_3', '#skF_2') | m1_subset_1('#skF_5'(C_64), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(C_64, '#skF_3') | ~m1_subset_1(C_64, u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.39/2.06  tff(c_167, plain, (![C_64]: (m1_subset_1('#skF_5'(C_64), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(C_64, '#skF_3') | ~m1_subset_1(C_64, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_69, c_66])).
% 5.39/2.06  tff(c_58, plain, (![C_64]: (v3_pre_topc('#skF_3', '#skF_2') | m1_connsp_2('#skF_5'(C_64), '#skF_2', C_64) | ~r2_hidden(C_64, '#skF_3') | ~m1_subset_1(C_64, u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.39/2.06  tff(c_165, plain, (![C_64]: (m1_connsp_2('#skF_5'(C_64), '#skF_2', C_64) | ~r2_hidden(C_64, '#skF_3') | ~m1_subset_1(C_64, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_69, c_58])).
% 5.39/2.06  tff(c_18, plain, (![A_14, B_18, C_20]: (r1_tarski(k1_tops_1(A_14, B_18), k1_tops_1(A_14, C_20)) | ~r1_tarski(B_18, C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(u1_struct_0(A_14))) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.39/2.06  tff(c_583, plain, (![B_174, A_175, C_176]: (r2_hidden(B_174, k1_tops_1(A_175, C_176)) | ~m1_connsp_2(C_176, A_175, B_174) | ~m1_subset_1(C_176, k1_zfmisc_1(u1_struct_0(A_175))) | ~m1_subset_1(B_174, u1_struct_0(A_175)) | ~l1_pre_topc(A_175) | ~v2_pre_topc(A_175) | v2_struct_0(A_175))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.39/2.06  tff(c_585, plain, (![B_174, C_64]: (r2_hidden(B_174, k1_tops_1('#skF_2', '#skF_5'(C_64))) | ~m1_connsp_2('#skF_5'(C_64), '#skF_2', B_174) | ~m1_subset_1(B_174, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r2_hidden(C_64, '#skF_3') | ~m1_subset_1(C_64, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_167, c_583])).
% 5.39/2.06  tff(c_590, plain, (![B_174, C_64]: (r2_hidden(B_174, k1_tops_1('#skF_2', '#skF_5'(C_64))) | ~m1_connsp_2('#skF_5'(C_64), '#skF_2', B_174) | ~m1_subset_1(B_174, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~r2_hidden(C_64, '#skF_3') | ~m1_subset_1(C_64, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_585])).
% 5.39/2.06  tff(c_643, plain, (![B_181, C_182]: (r2_hidden(B_181, k1_tops_1('#skF_2', '#skF_5'(C_182))) | ~m1_connsp_2('#skF_5'(C_182), '#skF_2', B_181) | ~m1_subset_1(B_181, u1_struct_0('#skF_2')) | ~r2_hidden(C_182, '#skF_3') | ~m1_subset_1(C_182, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_34, c_590])).
% 5.39/2.06  tff(c_823, plain, (![B_203, B_204, C_205]: (r2_hidden(B_203, B_204) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_5'(C_205)), B_204) | ~m1_connsp_2('#skF_5'(C_205), '#skF_2', B_203) | ~m1_subset_1(B_203, u1_struct_0('#skF_2')) | ~r2_hidden(C_205, '#skF_3') | ~m1_subset_1(C_205, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_643, c_2])).
% 5.39/2.06  tff(c_830, plain, (![B_203, C_20, C_205]: (r2_hidden(B_203, k1_tops_1('#skF_2', C_20)) | ~m1_connsp_2('#skF_5'(C_205), '#skF_2', B_203) | ~m1_subset_1(B_203, u1_struct_0('#skF_2')) | ~r2_hidden(C_205, '#skF_3') | ~m1_subset_1(C_205, u1_struct_0('#skF_2')) | ~r1_tarski('#skF_5'(C_205), C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5'(C_205), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_18, c_823])).
% 5.39/2.06  tff(c_1382, plain, (![B_302, C_303, C_304]: (r2_hidden(B_302, k1_tops_1('#skF_2', C_303)) | ~m1_connsp_2('#skF_5'(C_304), '#skF_2', B_302) | ~m1_subset_1(B_302, u1_struct_0('#skF_2')) | ~r2_hidden(C_304, '#skF_3') | ~m1_subset_1(C_304, u1_struct_0('#skF_2')) | ~r1_tarski('#skF_5'(C_304), C_303) | ~m1_subset_1(C_303, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5'(C_304), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_830])).
% 5.39/2.06  tff(c_1396, plain, (![C_305, C_306]: (r2_hidden(C_305, k1_tops_1('#skF_2', C_306)) | ~r1_tarski('#skF_5'(C_305), C_306) | ~m1_subset_1(C_306, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5'(C_305), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(C_305, '#skF_3') | ~m1_subset_1(C_305, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_165, c_1382])).
% 5.39/2.06  tff(c_1403, plain, (![C_307]: (r2_hidden(C_307, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_5'(C_307), '#skF_3') | ~m1_subset_1('#skF_5'(C_307), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(C_307, '#skF_3') | ~m1_subset_1(C_307, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_28, c_1396])).
% 5.39/2.06  tff(c_1408, plain, (![C_308]: (r2_hidden(C_308, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_5'(C_308), '#skF_3') | ~r2_hidden(C_308, '#skF_3') | ~m1_subset_1(C_308, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_167, c_1403])).
% 5.39/2.06  tff(c_24, plain, (![C_42, A_36, B_40]: (m1_connsp_2(C_42, A_36, B_40) | ~r2_hidden(B_40, k1_tops_1(A_36, C_42)) | ~m1_subset_1(C_42, k1_zfmisc_1(u1_struct_0(A_36))) | ~m1_subset_1(B_40, u1_struct_0(A_36)) | ~l1_pre_topc(A_36) | ~v2_pre_topc(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.39/2.06  tff(c_1410, plain, (![C_308]: (m1_connsp_2('#skF_3', '#skF_2', C_308) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski('#skF_5'(C_308), '#skF_3') | ~r2_hidden(C_308, '#skF_3') | ~m1_subset_1(C_308, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1408, c_24])).
% 5.39/2.06  tff(c_1419, plain, (![C_308]: (m1_connsp_2('#skF_3', '#skF_2', C_308) | v2_struct_0('#skF_2') | ~r1_tarski('#skF_5'(C_308), '#skF_3') | ~r2_hidden(C_308, '#skF_3') | ~m1_subset_1(C_308, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_1410])).
% 5.39/2.06  tff(c_1423, plain, (![C_309]: (m1_connsp_2('#skF_3', '#skF_2', C_309) | ~r1_tarski('#skF_5'(C_309), '#skF_3') | ~r2_hidden(C_309, '#skF_3') | ~m1_subset_1(C_309, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_34, c_1419])).
% 5.39/2.06  tff(c_1427, plain, (![C_129]: (m1_connsp_2('#skF_3', '#skF_2', C_129) | ~r1_tarski('#skF_3', '#skF_3') | ~r2_hidden(C_129, '#skF_3') | ~m1_subset_1(C_129, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_324, c_1423])).
% 5.39/2.06  tff(c_1435, plain, (![C_310]: (m1_connsp_2('#skF_3', '#skF_2', C_310) | ~r2_hidden(C_310, '#skF_3') | ~m1_subset_1(C_310, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1427])).
% 5.39/2.06  tff(c_1454, plain, (![A_311]: (m1_connsp_2('#skF_3', '#skF_2', A_311) | ~r2_hidden(A_311, '#skF_3'))), inference(resolution, [status(thm)], [c_97, c_1435])).
% 5.39/2.06  tff(c_587, plain, (![B_174]: (r2_hidden(B_174, k1_tops_1('#skF_2', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_2', B_174) | ~m1_subset_1(B_174, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_583])).
% 5.39/2.06  tff(c_594, plain, (![B_174]: (r2_hidden(B_174, k1_tops_1('#skF_2', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_2', B_174) | ~m1_subset_1(B_174, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_587])).
% 5.39/2.06  tff(c_596, plain, (![B_177]: (r2_hidden(B_177, k1_tops_1('#skF_2', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_2', B_177) | ~m1_subset_1(B_177, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_34, c_594])).
% 5.39/2.06  tff(c_658, plain, (![A_183]: (r1_tarski(A_183, k1_tops_1('#skF_2', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_2', '#skF_1'(A_183, k1_tops_1('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_1'(A_183, k1_tops_1('#skF_2', '#skF_3')), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_596, c_4])).
% 5.39/2.06  tff(c_672, plain, (![A_183]: (r1_tarski(A_183, k1_tops_1('#skF_2', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_2', '#skF_1'(A_183, k1_tops_1('#skF_2', '#skF_3'))) | ~r2_hidden('#skF_1'(A_183, k1_tops_1('#skF_2', '#skF_3')), '#skF_3'))), inference(resolution, [status(thm)], [c_97, c_658])).
% 5.39/2.06  tff(c_1467, plain, (![A_312]: (r1_tarski(A_312, k1_tops_1('#skF_2', '#skF_3')) | ~r2_hidden('#skF_1'(A_312, k1_tops_1('#skF_2', '#skF_3')), '#skF_3'))), inference(resolution, [status(thm)], [c_1454, c_672])).
% 5.39/2.06  tff(c_1499, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_6, c_1467])).
% 5.39/2.06  tff(c_1516, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_108, c_1499])).
% 5.39/2.06  tff(c_1517, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_107])).
% 5.39/2.06  tff(c_20, plain, (![C_33, A_21, D_35, B_29]: (v3_pre_topc(C_33, A_21) | k1_tops_1(A_21, C_33)!=C_33 | ~m1_subset_1(D_35, k1_zfmisc_1(u1_struct_0(B_29))) | ~m1_subset_1(C_33, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(B_29) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.39/2.06  tff(c_1832, plain, (![D_375, B_376]: (~m1_subset_1(D_375, k1_zfmisc_1(u1_struct_0(B_376))) | ~l1_pre_topc(B_376))), inference(splitLeft, [status(thm)], [c_20])).
% 5.39/2.06  tff(c_1838, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_1832])).
% 5.39/2.06  tff(c_1845, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_1838])).
% 5.39/2.06  tff(c_1847, plain, (![C_377, A_378]: (v3_pre_topc(C_377, A_378) | k1_tops_1(A_378, C_377)!=C_377 | ~m1_subset_1(C_377, k1_zfmisc_1(u1_struct_0(A_378))) | ~l1_pre_topc(A_378) | ~v2_pre_topc(A_378))), inference(splitRight, [status(thm)], [c_20])).
% 5.39/2.06  tff(c_1853, plain, (v3_pre_topc('#skF_3', '#skF_2') | k1_tops_1('#skF_2', '#skF_3')!='#skF_3' | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_1847])).
% 5.39/2.06  tff(c_1859, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1517, c_1853])).
% 5.39/2.06  tff(c_1861, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_1859])).
% 5.39/2.06  tff(c_1863, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_38])).
% 5.39/2.06  tff(c_36, plain, (![D_63]: (~r1_tarski(D_63, '#skF_3') | ~m1_connsp_2(D_63, '#skF_2', '#skF_4') | ~m1_subset_1(D_63, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.39/2.06  tff(c_2061, plain, (![D_429]: (~r1_tarski(D_429, '#skF_3') | ~m1_connsp_2(D_429, '#skF_2', '#skF_4') | ~m1_subset_1(D_429, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_1863, c_36])).
% 5.39/2.06  tff(c_2064, plain, (~r1_tarski('#skF_3', '#skF_3') | ~m1_connsp_2('#skF_3', '#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_2061])).
% 5.39/2.06  tff(c_2067, plain, (~m1_connsp_2('#skF_3', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2064])).
% 5.39/2.06  tff(c_1862, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_38])).
% 5.39/2.06  tff(c_40, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.39/2.06  tff(c_1864, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_40])).
% 5.39/2.06  tff(c_1866, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1863, c_1864])).
% 5.39/2.06  tff(c_1867, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_40])).
% 5.39/2.06  tff(c_22, plain, (![B_29, D_35, C_33, A_21]: (k1_tops_1(B_29, D_35)=D_35 | ~v3_pre_topc(D_35, B_29) | ~m1_subset_1(D_35, k1_zfmisc_1(u1_struct_0(B_29))) | ~m1_subset_1(C_33, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(B_29) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.39/2.06  tff(c_2018, plain, (![C_421, A_422]: (~m1_subset_1(C_421, k1_zfmisc_1(u1_struct_0(A_422))) | ~l1_pre_topc(A_422) | ~v2_pre_topc(A_422))), inference(splitLeft, [status(thm)], [c_22])).
% 5.39/2.06  tff(c_2021, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_2018])).
% 5.39/2.06  tff(c_2025, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_2021])).
% 5.39/2.06  tff(c_2027, plain, (![B_423, D_424]: (k1_tops_1(B_423, D_424)=D_424 | ~v3_pre_topc(D_424, B_423) | ~m1_subset_1(D_424, k1_zfmisc_1(u1_struct_0(B_423))) | ~l1_pre_topc(B_423))), inference(splitRight, [status(thm)], [c_22])).
% 5.39/2.06  tff(c_2030, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3' | ~v3_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_2027])).
% 5.39/2.06  tff(c_2033, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1863, c_2030])).
% 5.39/2.06  tff(c_1915, plain, (![A_398, B_399]: (r1_tarski(k1_tops_1(A_398, B_399), B_399) | ~m1_subset_1(B_399, k1_zfmisc_1(u1_struct_0(A_398))) | ~l1_pre_topc(A_398))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.39/2.06  tff(c_1917, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_1915])).
% 5.39/2.06  tff(c_1920, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1917])).
% 5.39/2.06  tff(c_1927, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_1920, c_8])).
% 5.39/2.06  tff(c_1928, plain, (~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1927])).
% 5.39/2.06  tff(c_2039, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2033, c_1928])).
% 5.39/2.06  tff(c_2043, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_2039])).
% 5.39/2.06  tff(c_2044, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_1927])).
% 5.39/2.06  tff(c_2142, plain, (![C_443, A_444, B_445]: (m1_connsp_2(C_443, A_444, B_445) | ~r2_hidden(B_445, k1_tops_1(A_444, C_443)) | ~m1_subset_1(C_443, k1_zfmisc_1(u1_struct_0(A_444))) | ~m1_subset_1(B_445, u1_struct_0(A_444)) | ~l1_pre_topc(A_444) | ~v2_pre_topc(A_444) | v2_struct_0(A_444))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.39/2.06  tff(c_2144, plain, (![B_445]: (m1_connsp_2('#skF_3', '#skF_2', B_445) | ~r2_hidden(B_445, '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_445, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2044, c_2142])).
% 5.39/2.06  tff(c_2155, plain, (![B_445]: (m1_connsp_2('#skF_3', '#skF_2', B_445) | ~r2_hidden(B_445, '#skF_3') | ~m1_subset_1(B_445, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_2144])).
% 5.39/2.06  tff(c_2160, plain, (![B_446]: (m1_connsp_2('#skF_3', '#skF_2', B_446) | ~r2_hidden(B_446, '#skF_3') | ~m1_subset_1(B_446, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_34, c_2155])).
% 5.39/2.06  tff(c_2166, plain, (m1_connsp_2('#skF_3', '#skF_2', '#skF_4') | ~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1867, c_2160])).
% 5.39/2.06  tff(c_2170, plain, (m1_connsp_2('#skF_3', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1862, c_2166])).
% 5.39/2.06  tff(c_2172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2067, c_2170])).
% 5.39/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.39/2.06  
% 5.39/2.06  Inference rules
% 5.39/2.06  ----------------------
% 5.39/2.06  #Ref     : 0
% 5.39/2.06  #Sup     : 443
% 5.39/2.06  #Fact    : 0
% 5.39/2.06  #Define  : 0
% 5.39/2.06  #Split   : 17
% 5.39/2.06  #Chain   : 0
% 5.39/2.06  #Close   : 0
% 5.39/2.06  
% 5.39/2.06  Ordering : KBO
% 5.39/2.06  
% 5.39/2.06  Simplification rules
% 5.39/2.06  ----------------------
% 5.39/2.06  #Subsume      : 184
% 5.39/2.06  #Demod        : 182
% 5.39/2.06  #Tautology    : 76
% 5.39/2.06  #SimpNegUnit  : 22
% 5.39/2.06  #BackRed      : 8
% 5.39/2.06  
% 5.39/2.06  #Partial instantiations: 0
% 5.39/2.06  #Strategies tried      : 1
% 5.39/2.06  
% 5.39/2.06  Timing (in seconds)
% 5.39/2.06  ----------------------
% 5.39/2.06  Preprocessing        : 0.31
% 5.39/2.06  Parsing              : 0.17
% 5.39/2.06  CNF conversion       : 0.03
% 5.39/2.06  Main loop            : 0.94
% 5.39/2.06  Inferencing          : 0.29
% 5.39/2.06  Reduction            : 0.23
% 5.39/2.06  Demodulation         : 0.14
% 5.39/2.06  BG Simplification    : 0.03
% 5.39/2.06  Subsumption          : 0.34
% 5.39/2.06  Abstraction          : 0.03
% 5.39/2.06  MUC search           : 0.00
% 5.39/2.06  Cooper               : 0.00
% 5.39/2.06  Total                : 1.30
% 5.39/2.06  Index Insertion      : 0.00
% 5.39/2.06  Index Deletion       : 0.00
% 5.39/2.06  Index Matching       : 0.00
% 5.39/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
