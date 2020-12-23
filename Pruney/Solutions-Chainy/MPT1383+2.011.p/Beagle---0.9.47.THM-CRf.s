%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:12 EST 2020

% Result     : Theorem 4.90s
% Output     : CNFRefutation 5.29s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 380 expanded)
%              Number of leaves         :   27 ( 144 expanded)
%              Depth                    :   13
%              Number of atoms          :  473 (1580 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
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

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_90,axiom,(
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

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_107,axiom,(
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

tff(c_26,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_48,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | v3_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_53,plain,(
    v3_pre_topc('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_44,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | r1_tarski('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_55,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_40,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | r2_hidden('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_54,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_52,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_34,plain,(
    ! [D_61] :
      ( ~ r2_hidden('#skF_2',D_61)
      | ~ r1_tarski(D_61,'#skF_3')
      | ~ v3_pre_topc(D_61,'#skF_1')
      | ~ m1_subset_1(D_61,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_connsp_2('#skF_3','#skF_1','#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_225,plain,(
    ~ m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_30,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_163,plain,(
    ! [A_86,B_87] :
      ( v3_pre_topc(k1_tops_1(A_86,B_87),A_86)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86)
      | ~ v2_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_170,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_163])).

tff(c_177,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_170])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(k1_tops_1(A_7,B_8),k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_18,plain,(
    ! [B_29,D_35,C_33,A_21] :
      ( k1_tops_1(B_29,D_35) = D_35
      | ~ v3_pre_topc(D_35,B_29)
      | ~ m1_subset_1(D_35,k1_zfmisc_1(u1_struct_0(B_29)))
      | ~ m1_subset_1(C_33,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(B_29)
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_254,plain,(
    ! [C_113,A_114] :
      ( ~ m1_subset_1(C_113,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114)
      | ~ v2_pre_topc(A_114) ) ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_260,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_254])).

tff(c_272,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_260])).

tff(c_274,plain,(
    ! [B_115,D_116] :
      ( k1_tops_1(B_115,D_116) = D_116
      | ~ v3_pre_topc(D_116,B_115)
      | ~ m1_subset_1(D_116,k1_zfmisc_1(u1_struct_0(B_115)))
      | ~ l1_pre_topc(B_115) ) ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_885,plain,(
    ! [A_161,B_162] :
      ( k1_tops_1(A_161,k1_tops_1(A_161,B_162)) = k1_tops_1(A_161,B_162)
      | ~ v3_pre_topc(k1_tops_1(A_161,B_162),A_161)
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0(A_161)))
      | ~ l1_pre_topc(A_161) ) ),
    inference(resolution,[status(thm)],[c_8,c_274])).

tff(c_893,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_3')) = k1_tops_1('#skF_1','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_177,c_885])).

tff(c_900,plain,(
    k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_3')) = k1_tops_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_893])).

tff(c_178,plain,(
    ! [A_88,B_89] :
      ( m1_subset_1(k1_tops_1(A_88,B_89),k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12,plain,(
    ! [A_11,B_13] :
      ( r1_tarski(k1_tops_1(A_11,B_13),B_13)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_194,plain,(
    ! [A_88,B_89] :
      ( r1_tarski(k1_tops_1(A_88,k1_tops_1(A_88,B_89)),k1_tops_1(A_88,B_89))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(resolution,[status(thm)],[c_178,c_12])).

tff(c_966,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),k1_tops_1('#skF_1','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_900,c_194])).

tff(c_1020,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_966])).

tff(c_280,plain,
    ( k1_tops_1('#skF_1','#skF_4') = '#skF_4'
    | ~ v3_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_274])).

tff(c_291,plain,(
    k1_tops_1('#skF_1','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_53,c_280])).

tff(c_14,plain,(
    ! [A_14,B_18,C_20] :
      ( r1_tarski(k1_tops_1(A_14,B_18),k1_tops_1(A_14,C_20))
      | ~ r1_tarski(B_18,C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_302,plain,(
    ! [C_20] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_1',C_20))
      | ~ r1_tarski('#skF_4',C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_14])).

tff(c_436,plain,(
    ! [C_122] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_1',C_122))
      | ~ r1_tarski('#skF_4',C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_66,c_302])).

tff(c_450,plain,
    ( r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_436])).

tff(c_460,plain,(
    r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_450])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_71,plain,(
    ! [C_66,A_67,B_68] :
      ( r2_hidden(C_66,A_67)
      | ~ r2_hidden(C_66,B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_75,plain,(
    ! [A_69] :
      ( r2_hidden('#skF_2',A_69)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_69)) ) ),
    inference(resolution,[status(thm)],[c_54,c_71])).

tff(c_89,plain,(
    ! [B_70] :
      ( r2_hidden('#skF_2',B_70)
      | ~ r1_tarski('#skF_4',B_70) ) ),
    inference(resolution,[status(thm)],[c_6,c_75])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_100,plain,(
    ! [A_73,B_74] :
      ( r2_hidden('#skF_2',A_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73))
      | ~ r1_tarski('#skF_4',B_74) ) ),
    inference(resolution,[status(thm)],[c_89,c_2])).

tff(c_112,plain,(
    ! [B_6,A_5] :
      ( r2_hidden('#skF_2',B_6)
      | ~ r1_tarski('#skF_4',A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_6,c_100])).

tff(c_468,plain,(
    ! [B_6] :
      ( r2_hidden('#skF_2',B_6)
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),B_6) ) ),
    inference(resolution,[status(thm)],[c_460,c_112])).

tff(c_1041,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1020,c_468])).

tff(c_20,plain,(
    ! [C_42,A_36,B_40] :
      ( m1_connsp_2(C_42,A_36,B_40)
      | ~ r2_hidden(B_40,k1_tops_1(A_36,C_42))
      | ~ m1_subset_1(C_42,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ m1_subset_1(B_40,u1_struct_0(A_36))
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1043,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1041,c_20])).

tff(c_1048,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_1043])).

tff(c_1050,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_225,c_1048])).

tff(c_1054,plain,(
    ! [D_163] :
      ( ~ r2_hidden('#skF_2',D_163)
      | ~ r1_tarski(D_163,'#skF_3')
      | ~ v3_pre_topc(D_163,'#skF_1')
      | ~ m1_subset_1(D_163,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1061,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_1054])).

tff(c_1075,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_55,c_54,c_1061])).

tff(c_1076,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_56,plain,(
    ! [A_62,B_63] :
      ( r1_tarski(A_62,B_63)
      | ~ m1_subset_1(A_62,k1_zfmisc_1(B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_60,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_56])).

tff(c_1126,plain,(
    ! [A_176,B_177] :
      ( r1_tarski(k1_tops_1(A_176,B_177),B_177)
      | ~ m1_subset_1(B_177,k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ l1_pre_topc(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1131,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_1126])).

tff(c_1135,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1131])).

tff(c_1493,plain,(
    ! [B_237,A_238,C_239] :
      ( r2_hidden(B_237,k1_tops_1(A_238,C_239))
      | ~ m1_connsp_2(C_239,A_238,B_237)
      | ~ m1_subset_1(C_239,k1_zfmisc_1(u1_struct_0(A_238)))
      | ~ m1_subset_1(B_237,u1_struct_0(A_238))
      | ~ l1_pre_topc(A_238)
      | ~ v2_pre_topc(A_238)
      | v2_struct_0(A_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1500,plain,(
    ! [B_237] :
      ( r2_hidden(B_237,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_237)
      | ~ m1_subset_1(B_237,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_1493])).

tff(c_1505,plain,(
    ! [B_237] :
      ( r2_hidden(B_237,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_237)
      | ~ m1_subset_1(B_237,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_1500])).

tff(c_1643,plain,(
    ! [B_240] :
      ( r2_hidden(B_240,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_240)
      | ~ m1_subset_1(B_240,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1505])).

tff(c_1152,plain,(
    ! [A_184,B_185] :
      ( v3_pre_topc(k1_tops_1(A_184,B_185),A_184)
      | ~ m1_subset_1(B_185,k1_zfmisc_1(u1_struct_0(A_184)))
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1158,plain,(
    ! [A_184,A_5] :
      ( v3_pre_topc(k1_tops_1(A_184,A_5),A_184)
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184)
      | ~ r1_tarski(A_5,u1_struct_0(A_184)) ) ),
    inference(resolution,[status(thm)],[c_6,c_1152])).

tff(c_1188,plain,(
    ! [D_196] :
      ( ~ r2_hidden('#skF_2',D_196)
      | ~ r1_tarski(D_196,'#skF_3')
      | ~ v3_pre_topc(D_196,'#skF_1')
      | ~ m1_subset_1(D_196,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1076,c_34])).

tff(c_1192,plain,(
    ! [B_8] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_8))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_8),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_8),'#skF_1')
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_8,c_1188])).

tff(c_1259,plain,(
    ! [B_208] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_208))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_208),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_208),'#skF_1')
      | ~ m1_subset_1(B_208,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1192])).

tff(c_1287,plain,(
    ! [A_211] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_211))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_211),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',A_211),'#skF_1')
      | ~ r1_tarski(A_211,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_6,c_1259])).

tff(c_1295,plain,(
    ! [A_5] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_5))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_5),'#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_5,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_1158,c_1287])).

tff(c_1304,plain,(
    ! [A_5] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_5))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_5),'#skF_3')
      | ~ r1_tarski(A_5,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_1295])).

tff(c_1647,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1643,c_1304])).

tff(c_1656,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1076,c_60,c_1135,c_1647])).

tff(c_1657,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1660,plain,(
    ! [A_241,B_242] :
      ( r1_tarski(A_241,B_242)
      | ~ m1_subset_1(A_241,k1_zfmisc_1(B_242)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1668,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_1660])).

tff(c_1718,plain,(
    ! [A_254,B_255] :
      ( r1_tarski(k1_tops_1(A_254,B_255),B_255)
      | ~ m1_subset_1(B_255,k1_zfmisc_1(u1_struct_0(A_254)))
      | ~ l1_pre_topc(A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1725,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_1718])).

tff(c_1732,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1725])).

tff(c_2251,plain,(
    ! [B_307,A_308,C_309] :
      ( r2_hidden(B_307,k1_tops_1(A_308,C_309))
      | ~ m1_connsp_2(C_309,A_308,B_307)
      | ~ m1_subset_1(C_309,k1_zfmisc_1(u1_struct_0(A_308)))
      | ~ m1_subset_1(B_307,u1_struct_0(A_308))
      | ~ l1_pre_topc(A_308)
      | ~ v2_pre_topc(A_308)
      | v2_struct_0(A_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2260,plain,(
    ! [B_307] :
      ( r2_hidden(B_307,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_307)
      | ~ m1_subset_1(B_307,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_2251])).

tff(c_2269,plain,(
    ! [B_307] :
      ( r2_hidden(B_307,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_307)
      | ~ m1_subset_1(B_307,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_2260])).

tff(c_2277,plain,(
    ! [B_311] :
      ( r2_hidden(B_311,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_311)
      | ~ m1_subset_1(B_311,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_2269])).

tff(c_1752,plain,(
    ! [A_264,B_265] :
      ( v3_pre_topc(k1_tops_1(A_264,B_265),A_264)
      | ~ m1_subset_1(B_265,k1_zfmisc_1(u1_struct_0(A_264)))
      | ~ l1_pre_topc(A_264)
      | ~ v2_pre_topc(A_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1763,plain,(
    ! [A_264,A_5] :
      ( v3_pre_topc(k1_tops_1(A_264,A_5),A_264)
      | ~ l1_pre_topc(A_264)
      | ~ v2_pre_topc(A_264)
      | ~ r1_tarski(A_5,u1_struct_0(A_264)) ) ),
    inference(resolution,[status(thm)],[c_6,c_1752])).

tff(c_1658,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,(
    ! [D_61] :
      ( ~ r2_hidden('#skF_2',D_61)
      | ~ r1_tarski(D_61,'#skF_3')
      | ~ v3_pre_topc(D_61,'#skF_1')
      | ~ m1_subset_1(D_61,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | r1_tarski('#skF_4','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1771,plain,(
    ! [D_266] :
      ( ~ r2_hidden('#skF_2',D_266)
      | ~ r1_tarski(D_266,'#skF_3')
      | ~ v3_pre_topc(D_266,'#skF_1')
      | ~ m1_subset_1(D_266,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1658,c_42])).

tff(c_1775,plain,(
    ! [B_8] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_8))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_8),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_8),'#skF_1')
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_8,c_1771])).

tff(c_1848,plain,(
    ! [B_280] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_280))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_280),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_280),'#skF_1')
      | ~ m1_subset_1(B_280,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1775])).

tff(c_1878,plain,(
    ! [A_281] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_281))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_281),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',A_281),'#skF_1')
      | ~ r1_tarski(A_281,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_6,c_1848])).

tff(c_1886,plain,(
    ! [A_5] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_5))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_5),'#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_5,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_1763,c_1878])).

tff(c_1898,plain,(
    ! [A_5] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_5))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_5),'#skF_3')
      | ~ r1_tarski(A_5,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_1886])).

tff(c_2281,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2277,c_1898])).

tff(c_2290,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1657,c_1668,c_1732,c_2281])).

tff(c_2291,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_2294,plain,(
    ! [A_312,B_313] :
      ( r1_tarski(A_312,B_313)
      | ~ m1_subset_1(A_312,k1_zfmisc_1(B_313)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2298,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_2294])).

tff(c_2306,plain,(
    ! [A_319,B_320] :
      ( r1_tarski(k1_tops_1(A_319,B_320),B_320)
      | ~ m1_subset_1(B_320,k1_zfmisc_1(u1_struct_0(A_319)))
      | ~ l1_pre_topc(A_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2311,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_2306])).

tff(c_2315,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2311])).

tff(c_2628,plain,(
    ! [B_359,A_360,C_361] :
      ( r2_hidden(B_359,k1_tops_1(A_360,C_361))
      | ~ m1_connsp_2(C_361,A_360,B_359)
      | ~ m1_subset_1(C_361,k1_zfmisc_1(u1_struct_0(A_360)))
      | ~ m1_subset_1(B_359,u1_struct_0(A_360))
      | ~ l1_pre_topc(A_360)
      | ~ v2_pre_topc(A_360)
      | v2_struct_0(A_360) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2635,plain,(
    ! [B_359] :
      ( r2_hidden(B_359,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_359)
      | ~ m1_subset_1(B_359,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_2628])).

tff(c_2640,plain,(
    ! [B_359] :
      ( r2_hidden(B_359,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_359)
      | ~ m1_subset_1(B_359,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_2635])).

tff(c_2642,plain,(
    ! [B_362] :
      ( r2_hidden(B_362,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_362)
      | ~ m1_subset_1(B_362,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_2640])).

tff(c_2318,plain,(
    ! [A_323,B_324] :
      ( v3_pre_topc(k1_tops_1(A_323,B_324),A_323)
      | ~ m1_subset_1(B_324,k1_zfmisc_1(u1_struct_0(A_323)))
      | ~ l1_pre_topc(A_323)
      | ~ v2_pre_topc(A_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2324,plain,(
    ! [A_323,A_5] :
      ( v3_pre_topc(k1_tops_1(A_323,A_5),A_323)
      | ~ l1_pre_topc(A_323)
      | ~ v2_pre_topc(A_323)
      | ~ r1_tarski(A_5,u1_struct_0(A_323)) ) ),
    inference(resolution,[status(thm)],[c_6,c_2318])).

tff(c_2292,plain,(
    ~ r2_hidden('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_38,plain,(
    ! [D_61] :
      ( ~ r2_hidden('#skF_2',D_61)
      | ~ r1_tarski(D_61,'#skF_3')
      | ~ v3_pre_topc(D_61,'#skF_1')
      | ~ m1_subset_1(D_61,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | r2_hidden('#skF_2','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2345,plain,(
    ! [D_335] :
      ( ~ r2_hidden('#skF_2',D_335)
      | ~ r1_tarski(D_335,'#skF_3')
      | ~ v3_pre_topc(D_335,'#skF_1')
      | ~ m1_subset_1(D_335,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2292,c_38])).

tff(c_2349,plain,(
    ! [B_8] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_8))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_8),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_8),'#skF_1')
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_8,c_2345])).

tff(c_2383,plain,(
    ! [B_340] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_340))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_340),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_340),'#skF_1')
      | ~ m1_subset_1(B_340,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2349])).

tff(c_2402,plain,(
    ! [A_341] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_341))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_341),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',A_341),'#skF_1')
      | ~ r1_tarski(A_341,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_6,c_2383])).

tff(c_2410,plain,(
    ! [A_5] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_5))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_5),'#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_5,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_2324,c_2402])).

tff(c_2419,plain,(
    ! [A_5] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_5))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_5),'#skF_3')
      | ~ r1_tarski(A_5,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_2410])).

tff(c_2646,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2642,c_2419])).

tff(c_2655,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2291,c_2298,c_2315,c_2646])).

tff(c_2656,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2661,plain,(
    ! [A_365,B_366] :
      ( r1_tarski(A_365,B_366)
      | ~ m1_subset_1(A_365,k1_zfmisc_1(B_366)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2669,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_2661])).

tff(c_2672,plain,(
    ! [A_370,B_371] :
      ( r1_tarski(k1_tops_1(A_370,B_371),B_371)
      | ~ m1_subset_1(B_371,k1_zfmisc_1(u1_struct_0(A_370)))
      | ~ l1_pre_topc(A_370) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2677,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_2672])).

tff(c_2681,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2677])).

tff(c_3699,plain,(
    ! [B_475,A_476,C_477] :
      ( r2_hidden(B_475,k1_tops_1(A_476,C_477))
      | ~ m1_connsp_2(C_477,A_476,B_475)
      | ~ m1_subset_1(C_477,k1_zfmisc_1(u1_struct_0(A_476)))
      | ~ m1_subset_1(B_475,u1_struct_0(A_476))
      | ~ l1_pre_topc(A_476)
      | ~ v2_pre_topc(A_476)
      | v2_struct_0(A_476) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_3706,plain,(
    ! [B_475] :
      ( r2_hidden(B_475,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_475)
      | ~ m1_subset_1(B_475,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_3699])).

tff(c_3711,plain,(
    ! [B_475] :
      ( r2_hidden(B_475,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_475)
      | ~ m1_subset_1(B_475,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_3706])).

tff(c_3713,plain,(
    ! [B_478] :
      ( r2_hidden(B_478,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_478)
      | ~ m1_subset_1(B_478,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_3711])).

tff(c_2684,plain,(
    ! [A_374,B_375] :
      ( v3_pre_topc(k1_tops_1(A_374,B_375),A_374)
      | ~ m1_subset_1(B_375,k1_zfmisc_1(u1_struct_0(A_374)))
      | ~ l1_pre_topc(A_374)
      | ~ v2_pre_topc(A_374) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2690,plain,(
    ! [A_374,A_5] :
      ( v3_pre_topc(k1_tops_1(A_374,A_5),A_374)
      | ~ l1_pre_topc(A_374)
      | ~ v2_pre_topc(A_374)
      | ~ r1_tarski(A_5,u1_struct_0(A_374)) ) ),
    inference(resolution,[status(thm)],[c_6,c_2684])).

tff(c_2657,plain,(
    ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,(
    ! [D_61] :
      ( ~ r2_hidden('#skF_2',D_61)
      | ~ r1_tarski(D_61,'#skF_3')
      | ~ v3_pre_topc(D_61,'#skF_1')
      | ~ m1_subset_1(D_61,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v3_pre_topc('#skF_4','#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_3277,plain,(
    ! [D_429] :
      ( ~ r2_hidden('#skF_2',D_429)
      | ~ r1_tarski(D_429,'#skF_3')
      | ~ v3_pre_topc(D_429,'#skF_1')
      | ~ m1_subset_1(D_429,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2657,c_46])).

tff(c_3281,plain,(
    ! [B_8] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_8))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_8),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_8),'#skF_1')
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_8,c_3277])).

tff(c_3401,plain,(
    ! [B_455] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_455))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_455),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_455),'#skF_1')
      | ~ m1_subset_1(B_455,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_3281])).

tff(c_3429,plain,(
    ! [A_458] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_458))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_458),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',A_458),'#skF_1')
      | ~ r1_tarski(A_458,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_6,c_3401])).

tff(c_3437,plain,(
    ! [A_5] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_5))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_5),'#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_5,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_2690,c_3429])).

tff(c_3446,plain,(
    ! [A_5] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_5))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_5),'#skF_3')
      | ~ r1_tarski(A_5,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_3437])).

tff(c_3717,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_3713,c_3446])).

tff(c_3726,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2656,c_2669,c_2681,c_3717])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n009.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 09:40:56 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.90/1.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.29/1.93  
% 5.29/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.29/1.93  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.29/1.93  
% 5.29/1.93  %Foreground sorts:
% 5.29/1.93  
% 5.29/1.93  
% 5.29/1.93  %Background operators:
% 5.29/1.93  
% 5.29/1.93  
% 5.29/1.93  %Foreground operators:
% 5.29/1.93  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.29/1.93  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 5.29/1.93  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.29/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.29/1.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.29/1.93  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.29/1.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.29/1.93  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.29/1.93  tff('#skF_2', type, '#skF_2': $i).
% 5.29/1.93  tff('#skF_3', type, '#skF_3': $i).
% 5.29/1.93  tff('#skF_1', type, '#skF_1': $i).
% 5.29/1.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.29/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.29/1.93  tff('#skF_4', type, '#skF_4': $i).
% 5.29/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.29/1.93  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.29/1.93  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.29/1.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.29/1.93  
% 5.29/1.96  tff(f_132, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_connsp_2)).
% 5.29/1.96  tff(f_50, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 5.29/1.96  tff(f_42, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 5.29/1.96  tff(f_90, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 5.29/1.96  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 5.29/1.96  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 5.29/1.96  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.29/1.96  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 5.29/1.96  tff(f_107, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 5.29/1.96  tff(c_26, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.29/1.96  tff(c_48, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | v3_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.29/1.96  tff(c_53, plain, (v3_pre_topc('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_48])).
% 5.29/1.96  tff(c_44, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | r1_tarski('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.29/1.96  tff(c_55, plain, (r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 5.29/1.96  tff(c_40, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | r2_hidden('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.29/1.96  tff(c_54, plain, (r2_hidden('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_40])).
% 5.29/1.96  tff(c_52, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.29/1.96  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_52])).
% 5.29/1.96  tff(c_32, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.29/1.96  tff(c_34, plain, (![D_61]: (~r2_hidden('#skF_2', D_61) | ~r1_tarski(D_61, '#skF_3') | ~v3_pre_topc(D_61, '#skF_1') | ~m1_subset_1(D_61, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_connsp_2('#skF_3', '#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.29/1.96  tff(c_225, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_34])).
% 5.29/1.96  tff(c_30, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.29/1.96  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.29/1.96  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.29/1.96  tff(c_163, plain, (![A_86, B_87]: (v3_pre_topc(k1_tops_1(A_86, B_87), A_86) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86) | ~v2_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.29/1.96  tff(c_170, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_163])).
% 5.29/1.96  tff(c_177, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_170])).
% 5.29/1.96  tff(c_8, plain, (![A_7, B_8]: (m1_subset_1(k1_tops_1(A_7, B_8), k1_zfmisc_1(u1_struct_0(A_7))) | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0(A_7))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.29/1.96  tff(c_18, plain, (![B_29, D_35, C_33, A_21]: (k1_tops_1(B_29, D_35)=D_35 | ~v3_pre_topc(D_35, B_29) | ~m1_subset_1(D_35, k1_zfmisc_1(u1_struct_0(B_29))) | ~m1_subset_1(C_33, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(B_29) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.29/1.96  tff(c_254, plain, (![C_113, A_114]: (~m1_subset_1(C_113, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114) | ~v2_pre_topc(A_114))), inference(splitLeft, [status(thm)], [c_18])).
% 5.29/1.96  tff(c_260, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_254])).
% 5.29/1.96  tff(c_272, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_260])).
% 5.29/1.96  tff(c_274, plain, (![B_115, D_116]: (k1_tops_1(B_115, D_116)=D_116 | ~v3_pre_topc(D_116, B_115) | ~m1_subset_1(D_116, k1_zfmisc_1(u1_struct_0(B_115))) | ~l1_pre_topc(B_115))), inference(splitRight, [status(thm)], [c_18])).
% 5.29/1.96  tff(c_885, plain, (![A_161, B_162]: (k1_tops_1(A_161, k1_tops_1(A_161, B_162))=k1_tops_1(A_161, B_162) | ~v3_pre_topc(k1_tops_1(A_161, B_162), A_161) | ~m1_subset_1(B_162, k1_zfmisc_1(u1_struct_0(A_161))) | ~l1_pre_topc(A_161))), inference(resolution, [status(thm)], [c_8, c_274])).
% 5.29/1.96  tff(c_893, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_3'))=k1_tops_1('#skF_1', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_177, c_885])).
% 5.29/1.96  tff(c_900, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_3'))=k1_tops_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_893])).
% 5.29/1.96  tff(c_178, plain, (![A_88, B_89]: (m1_subset_1(k1_tops_1(A_88, B_89), k1_zfmisc_1(u1_struct_0(A_88))) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.29/1.96  tff(c_12, plain, (![A_11, B_13]: (r1_tarski(k1_tops_1(A_11, B_13), B_13) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.29/1.96  tff(c_194, plain, (![A_88, B_89]: (r1_tarski(k1_tops_1(A_88, k1_tops_1(A_88, B_89)), k1_tops_1(A_88, B_89)) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(resolution, [status(thm)], [c_178, c_12])).
% 5.29/1.96  tff(c_966, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), k1_tops_1('#skF_1', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_900, c_194])).
% 5.29/1.96  tff(c_1020, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_966])).
% 5.29/1.96  tff(c_280, plain, (k1_tops_1('#skF_1', '#skF_4')='#skF_4' | ~v3_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_274])).
% 5.29/1.96  tff(c_291, plain, (k1_tops_1('#skF_1', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_53, c_280])).
% 5.29/1.96  tff(c_14, plain, (![A_14, B_18, C_20]: (r1_tarski(k1_tops_1(A_14, B_18), k1_tops_1(A_14, C_20)) | ~r1_tarski(B_18, C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(u1_struct_0(A_14))) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.29/1.96  tff(c_302, plain, (![C_20]: (r1_tarski('#skF_4', k1_tops_1('#skF_1', C_20)) | ~r1_tarski('#skF_4', C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_291, c_14])).
% 5.29/1.96  tff(c_436, plain, (![C_122]: (r1_tarski('#skF_4', k1_tops_1('#skF_1', C_122)) | ~r1_tarski('#skF_4', C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_66, c_302])).
% 5.29/1.96  tff(c_450, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_436])).
% 5.29/1.96  tff(c_460, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_450])).
% 5.29/1.96  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.29/1.96  tff(c_71, plain, (![C_66, A_67, B_68]: (r2_hidden(C_66, A_67) | ~r2_hidden(C_66, B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.29/1.96  tff(c_75, plain, (![A_69]: (r2_hidden('#skF_2', A_69) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_69)))), inference(resolution, [status(thm)], [c_54, c_71])).
% 5.29/1.96  tff(c_89, plain, (![B_70]: (r2_hidden('#skF_2', B_70) | ~r1_tarski('#skF_4', B_70))), inference(resolution, [status(thm)], [c_6, c_75])).
% 5.29/1.96  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.29/1.96  tff(c_100, plain, (![A_73, B_74]: (r2_hidden('#skF_2', A_73) | ~m1_subset_1(B_74, k1_zfmisc_1(A_73)) | ~r1_tarski('#skF_4', B_74))), inference(resolution, [status(thm)], [c_89, c_2])).
% 5.29/1.96  tff(c_112, plain, (![B_6, A_5]: (r2_hidden('#skF_2', B_6) | ~r1_tarski('#skF_4', A_5) | ~r1_tarski(A_5, B_6))), inference(resolution, [status(thm)], [c_6, c_100])).
% 5.29/1.96  tff(c_468, plain, (![B_6]: (r2_hidden('#skF_2', B_6) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), B_6))), inference(resolution, [status(thm)], [c_460, c_112])).
% 5.29/1.96  tff(c_1041, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_1020, c_468])).
% 5.29/1.96  tff(c_20, plain, (![C_42, A_36, B_40]: (m1_connsp_2(C_42, A_36, B_40) | ~r2_hidden(B_40, k1_tops_1(A_36, C_42)) | ~m1_subset_1(C_42, k1_zfmisc_1(u1_struct_0(A_36))) | ~m1_subset_1(B_40, u1_struct_0(A_36)) | ~l1_pre_topc(A_36) | ~v2_pre_topc(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.29/1.96  tff(c_1043, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1041, c_20])).
% 5.29/1.96  tff(c_1048, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_1043])).
% 5.29/1.96  tff(c_1050, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_225, c_1048])).
% 5.29/1.96  tff(c_1054, plain, (![D_163]: (~r2_hidden('#skF_2', D_163) | ~r1_tarski(D_163, '#skF_3') | ~v3_pre_topc(D_163, '#skF_1') | ~m1_subset_1(D_163, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_34])).
% 5.29/1.96  tff(c_1061, plain, (~r2_hidden('#skF_2', '#skF_4') | ~r1_tarski('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_1054])).
% 5.29/1.96  tff(c_1075, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_53, c_55, c_54, c_1061])).
% 5.29/1.96  tff(c_1076, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 5.29/1.96  tff(c_56, plain, (![A_62, B_63]: (r1_tarski(A_62, B_63) | ~m1_subset_1(A_62, k1_zfmisc_1(B_63)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.29/1.96  tff(c_60, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_56])).
% 5.29/1.96  tff(c_1126, plain, (![A_176, B_177]: (r1_tarski(k1_tops_1(A_176, B_177), B_177) | ~m1_subset_1(B_177, k1_zfmisc_1(u1_struct_0(A_176))) | ~l1_pre_topc(A_176))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.29/1.96  tff(c_1131, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_1126])).
% 5.29/1.96  tff(c_1135, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1131])).
% 5.29/1.96  tff(c_1493, plain, (![B_237, A_238, C_239]: (r2_hidden(B_237, k1_tops_1(A_238, C_239)) | ~m1_connsp_2(C_239, A_238, B_237) | ~m1_subset_1(C_239, k1_zfmisc_1(u1_struct_0(A_238))) | ~m1_subset_1(B_237, u1_struct_0(A_238)) | ~l1_pre_topc(A_238) | ~v2_pre_topc(A_238) | v2_struct_0(A_238))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.29/1.96  tff(c_1500, plain, (![B_237]: (r2_hidden(B_237, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_237) | ~m1_subset_1(B_237, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_1493])).
% 5.29/1.96  tff(c_1505, plain, (![B_237]: (r2_hidden(B_237, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_237) | ~m1_subset_1(B_237, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_1500])).
% 5.29/1.96  tff(c_1643, plain, (![B_240]: (r2_hidden(B_240, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_240) | ~m1_subset_1(B_240, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_32, c_1505])).
% 5.29/1.96  tff(c_1152, plain, (![A_184, B_185]: (v3_pre_topc(k1_tops_1(A_184, B_185), A_184) | ~m1_subset_1(B_185, k1_zfmisc_1(u1_struct_0(A_184))) | ~l1_pre_topc(A_184) | ~v2_pre_topc(A_184))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.29/1.96  tff(c_1158, plain, (![A_184, A_5]: (v3_pre_topc(k1_tops_1(A_184, A_5), A_184) | ~l1_pre_topc(A_184) | ~v2_pre_topc(A_184) | ~r1_tarski(A_5, u1_struct_0(A_184)))), inference(resolution, [status(thm)], [c_6, c_1152])).
% 5.29/1.96  tff(c_1188, plain, (![D_196]: (~r2_hidden('#skF_2', D_196) | ~r1_tarski(D_196, '#skF_3') | ~v3_pre_topc(D_196, '#skF_1') | ~m1_subset_1(D_196, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_1076, c_34])).
% 5.29/1.96  tff(c_1192, plain, (![B_8]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_8)) | ~r1_tarski(k1_tops_1('#skF_1', B_8), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_8), '#skF_1') | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_1188])).
% 5.29/1.96  tff(c_1259, plain, (![B_208]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_208)) | ~r1_tarski(k1_tops_1('#skF_1', B_208), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_208), '#skF_1') | ~m1_subset_1(B_208, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1192])).
% 5.29/1.96  tff(c_1287, plain, (![A_211]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_211)) | ~r1_tarski(k1_tops_1('#skF_1', A_211), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', A_211), '#skF_1') | ~r1_tarski(A_211, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_1259])).
% 5.29/1.96  tff(c_1295, plain, (![A_5]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_5)) | ~r1_tarski(k1_tops_1('#skF_1', A_5), '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_5, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_1158, c_1287])).
% 5.29/1.96  tff(c_1304, plain, (![A_5]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_5)) | ~r1_tarski(k1_tops_1('#skF_1', A_5), '#skF_3') | ~r1_tarski(A_5, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_1295])).
% 5.29/1.96  tff(c_1647, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1')) | ~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_1643, c_1304])).
% 5.29/1.96  tff(c_1656, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_1076, c_60, c_1135, c_1647])).
% 5.29/1.96  tff(c_1657, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 5.29/1.96  tff(c_1660, plain, (![A_241, B_242]: (r1_tarski(A_241, B_242) | ~m1_subset_1(A_241, k1_zfmisc_1(B_242)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.29/1.96  tff(c_1668, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_1660])).
% 5.29/1.96  tff(c_1718, plain, (![A_254, B_255]: (r1_tarski(k1_tops_1(A_254, B_255), B_255) | ~m1_subset_1(B_255, k1_zfmisc_1(u1_struct_0(A_254))) | ~l1_pre_topc(A_254))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.29/1.96  tff(c_1725, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_1718])).
% 5.29/1.96  tff(c_1732, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1725])).
% 5.29/1.96  tff(c_2251, plain, (![B_307, A_308, C_309]: (r2_hidden(B_307, k1_tops_1(A_308, C_309)) | ~m1_connsp_2(C_309, A_308, B_307) | ~m1_subset_1(C_309, k1_zfmisc_1(u1_struct_0(A_308))) | ~m1_subset_1(B_307, u1_struct_0(A_308)) | ~l1_pre_topc(A_308) | ~v2_pre_topc(A_308) | v2_struct_0(A_308))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.29/1.96  tff(c_2260, plain, (![B_307]: (r2_hidden(B_307, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_307) | ~m1_subset_1(B_307, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_2251])).
% 5.29/1.96  tff(c_2269, plain, (![B_307]: (r2_hidden(B_307, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_307) | ~m1_subset_1(B_307, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_2260])).
% 5.29/1.96  tff(c_2277, plain, (![B_311]: (r2_hidden(B_311, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_311) | ~m1_subset_1(B_311, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_32, c_2269])).
% 5.29/1.96  tff(c_1752, plain, (![A_264, B_265]: (v3_pre_topc(k1_tops_1(A_264, B_265), A_264) | ~m1_subset_1(B_265, k1_zfmisc_1(u1_struct_0(A_264))) | ~l1_pre_topc(A_264) | ~v2_pre_topc(A_264))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.29/1.96  tff(c_1763, plain, (![A_264, A_5]: (v3_pre_topc(k1_tops_1(A_264, A_5), A_264) | ~l1_pre_topc(A_264) | ~v2_pre_topc(A_264) | ~r1_tarski(A_5, u1_struct_0(A_264)))), inference(resolution, [status(thm)], [c_6, c_1752])).
% 5.29/1.96  tff(c_1658, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 5.29/1.96  tff(c_42, plain, (![D_61]: (~r2_hidden('#skF_2', D_61) | ~r1_tarski(D_61, '#skF_3') | ~v3_pre_topc(D_61, '#skF_1') | ~m1_subset_1(D_61, k1_zfmisc_1(u1_struct_0('#skF_1'))) | r1_tarski('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.29/1.96  tff(c_1771, plain, (![D_266]: (~r2_hidden('#skF_2', D_266) | ~r1_tarski(D_266, '#skF_3') | ~v3_pre_topc(D_266, '#skF_1') | ~m1_subset_1(D_266, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_1658, c_42])).
% 5.29/1.96  tff(c_1775, plain, (![B_8]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_8)) | ~r1_tarski(k1_tops_1('#skF_1', B_8), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_8), '#skF_1') | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_1771])).
% 5.29/1.96  tff(c_1848, plain, (![B_280]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_280)) | ~r1_tarski(k1_tops_1('#skF_1', B_280), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_280), '#skF_1') | ~m1_subset_1(B_280, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1775])).
% 5.29/1.96  tff(c_1878, plain, (![A_281]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_281)) | ~r1_tarski(k1_tops_1('#skF_1', A_281), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', A_281), '#skF_1') | ~r1_tarski(A_281, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_1848])).
% 5.29/1.96  tff(c_1886, plain, (![A_5]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_5)) | ~r1_tarski(k1_tops_1('#skF_1', A_5), '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_5, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_1763, c_1878])).
% 5.29/1.96  tff(c_1898, plain, (![A_5]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_5)) | ~r1_tarski(k1_tops_1('#skF_1', A_5), '#skF_3') | ~r1_tarski(A_5, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_1886])).
% 5.29/1.96  tff(c_2281, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1')) | ~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_2277, c_1898])).
% 5.29/1.96  tff(c_2290, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_1657, c_1668, c_1732, c_2281])).
% 5.29/1.96  tff(c_2291, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 5.29/1.96  tff(c_2294, plain, (![A_312, B_313]: (r1_tarski(A_312, B_313) | ~m1_subset_1(A_312, k1_zfmisc_1(B_313)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.29/1.96  tff(c_2298, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_2294])).
% 5.29/1.96  tff(c_2306, plain, (![A_319, B_320]: (r1_tarski(k1_tops_1(A_319, B_320), B_320) | ~m1_subset_1(B_320, k1_zfmisc_1(u1_struct_0(A_319))) | ~l1_pre_topc(A_319))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.29/1.96  tff(c_2311, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_2306])).
% 5.29/1.96  tff(c_2315, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2311])).
% 5.29/1.96  tff(c_2628, plain, (![B_359, A_360, C_361]: (r2_hidden(B_359, k1_tops_1(A_360, C_361)) | ~m1_connsp_2(C_361, A_360, B_359) | ~m1_subset_1(C_361, k1_zfmisc_1(u1_struct_0(A_360))) | ~m1_subset_1(B_359, u1_struct_0(A_360)) | ~l1_pre_topc(A_360) | ~v2_pre_topc(A_360) | v2_struct_0(A_360))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.29/1.96  tff(c_2635, plain, (![B_359]: (r2_hidden(B_359, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_359) | ~m1_subset_1(B_359, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_2628])).
% 5.29/1.96  tff(c_2640, plain, (![B_359]: (r2_hidden(B_359, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_359) | ~m1_subset_1(B_359, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_2635])).
% 5.29/1.96  tff(c_2642, plain, (![B_362]: (r2_hidden(B_362, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_362) | ~m1_subset_1(B_362, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_32, c_2640])).
% 5.29/1.96  tff(c_2318, plain, (![A_323, B_324]: (v3_pre_topc(k1_tops_1(A_323, B_324), A_323) | ~m1_subset_1(B_324, k1_zfmisc_1(u1_struct_0(A_323))) | ~l1_pre_topc(A_323) | ~v2_pre_topc(A_323))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.29/1.96  tff(c_2324, plain, (![A_323, A_5]: (v3_pre_topc(k1_tops_1(A_323, A_5), A_323) | ~l1_pre_topc(A_323) | ~v2_pre_topc(A_323) | ~r1_tarski(A_5, u1_struct_0(A_323)))), inference(resolution, [status(thm)], [c_6, c_2318])).
% 5.29/1.96  tff(c_2292, plain, (~r2_hidden('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_40])).
% 5.29/1.96  tff(c_38, plain, (![D_61]: (~r2_hidden('#skF_2', D_61) | ~r1_tarski(D_61, '#skF_3') | ~v3_pre_topc(D_61, '#skF_1') | ~m1_subset_1(D_61, k1_zfmisc_1(u1_struct_0('#skF_1'))) | r2_hidden('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.29/1.96  tff(c_2345, plain, (![D_335]: (~r2_hidden('#skF_2', D_335) | ~r1_tarski(D_335, '#skF_3') | ~v3_pre_topc(D_335, '#skF_1') | ~m1_subset_1(D_335, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_2292, c_38])).
% 5.29/1.96  tff(c_2349, plain, (![B_8]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_8)) | ~r1_tarski(k1_tops_1('#skF_1', B_8), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_8), '#skF_1') | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_2345])).
% 5.29/1.96  tff(c_2383, plain, (![B_340]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_340)) | ~r1_tarski(k1_tops_1('#skF_1', B_340), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_340), '#skF_1') | ~m1_subset_1(B_340, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2349])).
% 5.29/1.96  tff(c_2402, plain, (![A_341]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_341)) | ~r1_tarski(k1_tops_1('#skF_1', A_341), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', A_341), '#skF_1') | ~r1_tarski(A_341, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_2383])).
% 5.29/1.96  tff(c_2410, plain, (![A_5]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_5)) | ~r1_tarski(k1_tops_1('#skF_1', A_5), '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_5, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_2324, c_2402])).
% 5.29/1.96  tff(c_2419, plain, (![A_5]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_5)) | ~r1_tarski(k1_tops_1('#skF_1', A_5), '#skF_3') | ~r1_tarski(A_5, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_2410])).
% 5.29/1.96  tff(c_2646, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1')) | ~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_2642, c_2419])).
% 5.29/1.96  tff(c_2655, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_2291, c_2298, c_2315, c_2646])).
% 5.29/1.96  tff(c_2656, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 5.29/1.96  tff(c_2661, plain, (![A_365, B_366]: (r1_tarski(A_365, B_366) | ~m1_subset_1(A_365, k1_zfmisc_1(B_366)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.29/1.96  tff(c_2669, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_2661])).
% 5.29/1.96  tff(c_2672, plain, (![A_370, B_371]: (r1_tarski(k1_tops_1(A_370, B_371), B_371) | ~m1_subset_1(B_371, k1_zfmisc_1(u1_struct_0(A_370))) | ~l1_pre_topc(A_370))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.29/1.96  tff(c_2677, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_2672])).
% 5.29/1.96  tff(c_2681, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2677])).
% 5.29/1.96  tff(c_3699, plain, (![B_475, A_476, C_477]: (r2_hidden(B_475, k1_tops_1(A_476, C_477)) | ~m1_connsp_2(C_477, A_476, B_475) | ~m1_subset_1(C_477, k1_zfmisc_1(u1_struct_0(A_476))) | ~m1_subset_1(B_475, u1_struct_0(A_476)) | ~l1_pre_topc(A_476) | ~v2_pre_topc(A_476) | v2_struct_0(A_476))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.29/1.96  tff(c_3706, plain, (![B_475]: (r2_hidden(B_475, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_475) | ~m1_subset_1(B_475, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_3699])).
% 5.29/1.96  tff(c_3711, plain, (![B_475]: (r2_hidden(B_475, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_475) | ~m1_subset_1(B_475, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_3706])).
% 5.29/1.96  tff(c_3713, plain, (![B_478]: (r2_hidden(B_478, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_478) | ~m1_subset_1(B_478, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_32, c_3711])).
% 5.29/1.96  tff(c_2684, plain, (![A_374, B_375]: (v3_pre_topc(k1_tops_1(A_374, B_375), A_374) | ~m1_subset_1(B_375, k1_zfmisc_1(u1_struct_0(A_374))) | ~l1_pre_topc(A_374) | ~v2_pre_topc(A_374))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.29/1.96  tff(c_2690, plain, (![A_374, A_5]: (v3_pre_topc(k1_tops_1(A_374, A_5), A_374) | ~l1_pre_topc(A_374) | ~v2_pre_topc(A_374) | ~r1_tarski(A_5, u1_struct_0(A_374)))), inference(resolution, [status(thm)], [c_6, c_2684])).
% 5.29/1.96  tff(c_2657, plain, (~v3_pre_topc('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 5.29/1.96  tff(c_46, plain, (![D_61]: (~r2_hidden('#skF_2', D_61) | ~r1_tarski(D_61, '#skF_3') | ~v3_pre_topc(D_61, '#skF_1') | ~m1_subset_1(D_61, k1_zfmisc_1(u1_struct_0('#skF_1'))) | v3_pre_topc('#skF_4', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.29/1.96  tff(c_3277, plain, (![D_429]: (~r2_hidden('#skF_2', D_429) | ~r1_tarski(D_429, '#skF_3') | ~v3_pre_topc(D_429, '#skF_1') | ~m1_subset_1(D_429, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_2657, c_46])).
% 5.29/1.96  tff(c_3281, plain, (![B_8]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_8)) | ~r1_tarski(k1_tops_1('#skF_1', B_8), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_8), '#skF_1') | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_3277])).
% 5.29/1.96  tff(c_3401, plain, (![B_455]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_455)) | ~r1_tarski(k1_tops_1('#skF_1', B_455), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_455), '#skF_1') | ~m1_subset_1(B_455, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_3281])).
% 5.29/1.96  tff(c_3429, plain, (![A_458]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_458)) | ~r1_tarski(k1_tops_1('#skF_1', A_458), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', A_458), '#skF_1') | ~r1_tarski(A_458, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_3401])).
% 5.29/1.96  tff(c_3437, plain, (![A_5]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_5)) | ~r1_tarski(k1_tops_1('#skF_1', A_5), '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_5, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_2690, c_3429])).
% 5.29/1.96  tff(c_3446, plain, (![A_5]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_5)) | ~r1_tarski(k1_tops_1('#skF_1', A_5), '#skF_3') | ~r1_tarski(A_5, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_3437])).
% 5.29/1.96  tff(c_3717, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1')) | ~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_3713, c_3446])).
% 5.29/1.96  tff(c_3726, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_2656, c_2669, c_2681, c_3717])).
% 5.29/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.29/1.96  
% 5.29/1.96  Inference rules
% 5.29/1.96  ----------------------
% 5.29/1.96  #Ref     : 0
% 5.29/1.96  #Sup     : 686
% 5.29/1.96  #Fact    : 0
% 5.29/1.96  #Define  : 0
% 5.29/1.96  #Split   : 34
% 5.29/1.96  #Chain   : 0
% 5.29/1.96  #Close   : 0
% 5.29/1.96  
% 5.29/1.96  Ordering : KBO
% 5.29/1.96  
% 5.29/1.96  Simplification rules
% 5.29/1.96  ----------------------
% 5.29/1.96  #Subsume      : 243
% 5.29/1.96  #Demod        : 852
% 5.29/1.96  #Tautology    : 171
% 5.29/1.96  #SimpNegUnit  : 40
% 5.29/1.96  #BackRed      : 5
% 5.29/1.96  
% 5.29/1.96  #Partial instantiations: 0
% 5.29/1.96  #Strategies tried      : 1
% 5.29/1.96  
% 5.29/1.96  Timing (in seconds)
% 5.29/1.96  ----------------------
% 5.29/1.96  Preprocessing        : 0.31
% 5.29/1.96  Parsing              : 0.17
% 5.29/1.96  CNF conversion       : 0.02
% 5.29/1.96  Main loop            : 0.87
% 5.29/1.96  Inferencing          : 0.33
% 5.29/1.96  Reduction            : 0.26
% 5.29/1.96  Demodulation         : 0.18
% 5.29/1.96  BG Simplification    : 0.03
% 5.29/1.96  Subsumption          : 0.18
% 5.29/1.96  Abstraction          : 0.03
% 5.29/1.96  MUC search           : 0.00
% 5.29/1.97  Cooper               : 0.00
% 5.29/1.97  Total                : 1.24
% 5.29/1.97  Index Insertion      : 0.00
% 5.29/1.97  Index Deletion       : 0.00
% 5.29/1.97  Index Matching       : 0.00
% 5.29/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
