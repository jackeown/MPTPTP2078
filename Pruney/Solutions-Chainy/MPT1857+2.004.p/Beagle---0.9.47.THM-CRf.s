%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:09 EST 2020

% Result     : Theorem 5.02s
% Output     : CNFRefutation 5.27s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 339 expanded)
%              Number of leaves         :   25 ( 124 expanded)
%              Depth                    :   21
%              Number of atoms          :  283 (1216 expanded)
%              Number of equality atoms :   36 ( 350 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                        & C = D
                        & v2_tex_2(C,A) )
                     => v2_tex_2(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tex_2)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( r1_tarski(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_34,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(c_24,plain,(
    ~ v2_tex_2('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_32,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_28,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_26,plain,(
    v2_tex_2('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_40,plain,(
    v2_tex_2('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26])).

tff(c_36,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_103,plain,(
    ! [A_62,B_63] :
      ( r1_tarski('#skF_2'(A_62,B_63),B_63)
      | v2_tex_2(B_63,A_62)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_105,plain,
    ( r1_tarski('#skF_2'('#skF_4','#skF_6'),'#skF_6')
    | v2_tex_2('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_103])).

tff(c_110,plain,
    ( r1_tarski('#skF_2'('#skF_4','#skF_6'),'#skF_6')
    | v2_tex_2('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_105])).

tff(c_111,plain,(
    r1_tarski('#skF_2'('#skF_4','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_110])).

tff(c_16,plain,(
    ! [A_11,B_25] :
      ( m1_subset_1('#skF_2'(A_11,B_25),k1_zfmisc_1(u1_struct_0(A_11)))
      | v2_tex_2(B_25,A_11)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6,plain,(
    ! [A_4] :
      ( m1_subset_1(u1_pre_topc(A_4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_4))))
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_30,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_54,plain,(
    ! [C_48,A_49,D_50,B_51] :
      ( C_48 = A_49
      | g1_pre_topc(C_48,D_50) != g1_pre_topc(A_49,B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(k1_zfmisc_1(A_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_98,plain,(
    ! [A_60,B_61] :
      ( u1_struct_0('#skF_3') = A_60
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(A_60,B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k1_zfmisc_1(A_60))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_54])).

tff(c_102,plain,(
    ! [A_4] :
      ( u1_struct_0(A_4) = u1_struct_0('#skF_3')
      | g1_pre_topc(u1_struct_0(A_4),u1_pre_topc(A_4)) != g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
      | ~ l1_pre_topc(A_4) ) ),
    inference(resolution,[status(thm)],[c_6,c_98])).

tff(c_122,plain,
    ( u1_struct_0('#skF_3') = u1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_102])).

tff(c_124,plain,(
    u1_struct_0('#skF_3') = u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_122])).

tff(c_238,plain,(
    ! [A_75,B_76,C_77] :
      ( v3_pre_topc('#skF_1'(A_75,B_76,C_77),A_75)
      | ~ r1_tarski(C_77,B_76)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ v2_tex_2(B_76,A_75)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_242,plain,(
    ! [B_76,C_77] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_76,C_77),'#skF_3')
      | ~ r1_tarski(C_77,B_76)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_76,'#skF_3')
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_238])).

tff(c_551,plain,(
    ! [B_105,C_106] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_105,C_106),'#skF_3')
      | ~ r1_tarski(C_106,B_105)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_105,'#skF_3')
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_124,c_242])).

tff(c_559,plain,(
    ! [B_105,B_25] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_105,'#skF_2'('#skF_4',B_25)),'#skF_3')
      | ~ r1_tarski('#skF_2'('#skF_4',B_25),B_105)
      | ~ v2_tex_2(B_105,'#skF_3')
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_25,'#skF_4')
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_551])).

tff(c_568,plain,(
    ! [B_105,B_25] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_105,'#skF_2'('#skF_4',B_25)),'#skF_3')
      | ~ r1_tarski('#skF_2'('#skF_4',B_25),B_105)
      | ~ v2_tex_2(B_105,'#skF_3')
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_25,'#skF_4')
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_559])).

tff(c_344,plain,(
    ! [A_84,B_85,C_86] :
      ( m1_subset_1('#skF_1'(A_84,B_85,C_86),k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ r1_tarski(C_86,B_85)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ v2_tex_2(B_85,A_84)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_372,plain,(
    ! [B_85,C_86] :
      ( m1_subset_1('#skF_1'('#skF_3',B_85,C_86),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(C_86,B_85)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_85,'#skF_3')
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_344])).

tff(c_643,plain,(
    ! [B_123,C_124] :
      ( m1_subset_1('#skF_1'('#skF_3',B_123,C_124),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(C_124,B_123)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_123,'#skF_3')
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_124,c_124,c_372])).

tff(c_149,plain,
    ( m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_6])).

tff(c_159,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_149])).

tff(c_135,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_3')) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_30])).

tff(c_8,plain,(
    ! [D_10,B_6,C_9,A_5] :
      ( D_10 = B_6
      | g1_pre_topc(C_9,D_10) != g1_pre_topc(A_5,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(k1_zfmisc_1(A_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_187,plain,(
    ! [D_10,C_9] :
      ( u1_pre_topc('#skF_3') = D_10
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(C_9,D_10)
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_8])).

tff(c_195,plain,(
    ! [D_10,C_9] :
      ( u1_pre_topc('#skF_3') = D_10
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(C_9,D_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_187])).

tff(c_201,plain,(
    u1_pre_topc('#skF_3') = u1_pre_topc('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_195])).

tff(c_4,plain,(
    ! [B_3,A_1] :
      ( r2_hidden(B_3,u1_pre_topc(A_1))
      | ~ v3_pre_topc(B_3,A_1)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_143,plain,(
    ! [B_3] :
      ( r2_hidden(B_3,u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc(B_3,'#skF_3')
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_4])).

tff(c_155,plain,(
    ! [B_3] :
      ( r2_hidden(B_3,u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc(B_3,'#skF_3')
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_143])).

tff(c_265,plain,(
    ! [B_3] :
      ( r2_hidden(B_3,u1_pre_topc('#skF_4'))
      | ~ v3_pre_topc(B_3,'#skF_3')
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_155])).

tff(c_815,plain,(
    ! [B_156,C_157] :
      ( r2_hidden('#skF_1'('#skF_3',B_156,C_157),u1_pre_topc('#skF_4'))
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_156,C_157),'#skF_3')
      | ~ r1_tarski(C_157,B_156)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_156,'#skF_3')
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_643,c_265])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v3_pre_topc(B_3,A_1)
      | ~ r2_hidden(B_3,u1_pre_topc(A_1))
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_685,plain,(
    ! [B_123,C_124] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_123,C_124),'#skF_4')
      | ~ r2_hidden('#skF_1'('#skF_3',B_123,C_124),u1_pre_topc('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(C_124,B_123)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_123,'#skF_3')
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_643,c_2])).

tff(c_711,plain,(
    ! [B_123,C_124] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_123,C_124),'#skF_4')
      | ~ r2_hidden('#skF_1'('#skF_3',B_123,C_124),u1_pre_topc('#skF_4'))
      | ~ r1_tarski(C_124,B_123)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_123,'#skF_3')
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_685])).

tff(c_820,plain,(
    ! [B_158,C_159] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_158,C_159),'#skF_4')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_158,C_159),'#skF_3')
      | ~ r1_tarski(C_159,B_158)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_158,'#skF_3')
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_815,c_711])).

tff(c_1090,plain,(
    ! [B_207,B_208] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_207,'#skF_2'('#skF_4',B_208)),'#skF_4')
      | ~ m1_subset_1('#skF_2'('#skF_4',B_208),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski('#skF_2'('#skF_4',B_208),B_207)
      | ~ v2_tex_2(B_207,'#skF_3')
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_208,'#skF_4')
      | ~ m1_subset_1(B_208,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_568,c_820])).

tff(c_1093,plain,(
    ! [B_207,B_25] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_207,'#skF_2'('#skF_4',B_25)),'#skF_4')
      | ~ r1_tarski('#skF_2'('#skF_4',B_25),B_207)
      | ~ v2_tex_2(B_207,'#skF_3')
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_25,'#skF_4')
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_1090])).

tff(c_1096,plain,(
    ! [B_207,B_25] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_207,'#skF_2'('#skF_4',B_25)),'#skF_4')
      | ~ r1_tarski('#skF_2'('#skF_4',B_25),B_207)
      | ~ v2_tex_2(B_207,'#skF_3')
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_25,'#skF_4')
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1093])).

tff(c_390,plain,(
    ! [B_85,C_86] :
      ( m1_subset_1('#skF_1'('#skF_3',B_85,C_86),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(C_86,B_85)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_85,'#skF_3')
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_124,c_124,c_372])).

tff(c_595,plain,(
    ! [A_108,B_109,C_110] :
      ( k9_subset_1(u1_struct_0(A_108),B_109,'#skF_1'(A_108,B_109,C_110)) = C_110
      | ~ r1_tarski(C_110,B_109)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ v2_tex_2(B_109,A_108)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_603,plain,(
    ! [B_109,C_110] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_109,'#skF_1'('#skF_3',B_109,C_110)) = C_110
      | ~ r1_tarski(C_110,B_109)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_109,'#skF_3')
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_595])).

tff(c_712,plain,(
    ! [B_125,C_126] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_125,'#skF_1'('#skF_3',B_125,C_126)) = C_126
      | ~ r1_tarski(C_126,B_125)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_125,'#skF_3')
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_124,c_124,c_603])).

tff(c_722,plain,(
    ! [B_125,B_25] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_125,'#skF_1'('#skF_3',B_125,'#skF_2'('#skF_4',B_25))) = '#skF_2'('#skF_4',B_25)
      | ~ r1_tarski('#skF_2'('#skF_4',B_25),B_125)
      | ~ v2_tex_2(B_125,'#skF_3')
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_25,'#skF_4')
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_712])).

tff(c_1033,plain,(
    ! [B_194,B_195] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_194,'#skF_1'('#skF_3',B_194,'#skF_2'('#skF_4',B_195))) = '#skF_2'('#skF_4',B_195)
      | ~ r1_tarski('#skF_2'('#skF_4',B_195),B_194)
      | ~ v2_tex_2(B_194,'#skF_3')
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_195,'#skF_4')
      | ~ m1_subset_1(B_195,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_722])).

tff(c_12,plain,(
    ! [A_11,B_25,D_35] :
      ( k9_subset_1(u1_struct_0(A_11),B_25,D_35) != '#skF_2'(A_11,B_25)
      | ~ v3_pre_topc(D_35,A_11)
      | ~ m1_subset_1(D_35,k1_zfmisc_1(u1_struct_0(A_11)))
      | v2_tex_2(B_25,A_11)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1040,plain,(
    ! [B_195,B_194] :
      ( '#skF_2'('#skF_4',B_195) != '#skF_2'('#skF_4',B_194)
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_194,'#skF_2'('#skF_4',B_195)),'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_194,'#skF_2'('#skF_4',B_195)),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_194,'#skF_4')
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski('#skF_2'('#skF_4',B_195),B_194)
      | ~ v2_tex_2(B_194,'#skF_3')
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_195,'#skF_4')
      | ~ m1_subset_1(B_195,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1033,c_12])).

tff(c_1536,plain,(
    ! [B_330,B_329] :
      ( '#skF_2'('#skF_4',B_330) != '#skF_2'('#skF_4',B_329)
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_330,'#skF_2'('#skF_4',B_329)),'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_330,'#skF_2'('#skF_4',B_329)),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_330,'#skF_4')
      | ~ r1_tarski('#skF_2'('#skF_4',B_329),B_330)
      | ~ v2_tex_2(B_330,'#skF_3')
      | ~ m1_subset_1(B_330,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_329,'#skF_4')
      | ~ m1_subset_1(B_329,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1040])).

tff(c_1542,plain,(
    ! [B_332,B_331] :
      ( '#skF_2'('#skF_4',B_332) != '#skF_2'('#skF_4',B_331)
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_331,'#skF_2'('#skF_4',B_332)),'#skF_4')
      | v2_tex_2(B_331,'#skF_4')
      | v2_tex_2(B_332,'#skF_4')
      | ~ m1_subset_1(B_332,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski('#skF_2'('#skF_4',B_332),B_331)
      | ~ m1_subset_1('#skF_2'('#skF_4',B_332),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_331,'#skF_3')
      | ~ m1_subset_1(B_331,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_390,c_1536])).

tff(c_1553,plain,(
    ! [B_336,B_335] :
      ( '#skF_2'('#skF_4',B_336) != '#skF_2'('#skF_4',B_335)
      | v2_tex_2(B_336,'#skF_4')
      | ~ m1_subset_1('#skF_2'('#skF_4',B_335),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski('#skF_2'('#skF_4',B_335),B_336)
      | ~ v2_tex_2(B_336,'#skF_3')
      | ~ m1_subset_1(B_336,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_335,'#skF_4')
      | ~ m1_subset_1(B_335,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_1096,c_1542])).

tff(c_1556,plain,(
    ! [B_336,B_25] :
      ( '#skF_2'('#skF_4',B_336) != '#skF_2'('#skF_4',B_25)
      | v2_tex_2(B_336,'#skF_4')
      | ~ r1_tarski('#skF_2'('#skF_4',B_25),B_336)
      | ~ v2_tex_2(B_336,'#skF_3')
      | ~ m1_subset_1(B_336,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_25,'#skF_4')
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_1553])).

tff(c_1560,plain,(
    ! [B_338,B_337] :
      ( '#skF_2'('#skF_4',B_338) != '#skF_2'('#skF_4',B_337)
      | v2_tex_2(B_337,'#skF_4')
      | ~ r1_tarski('#skF_2'('#skF_4',B_338),B_337)
      | ~ v2_tex_2(B_337,'#skF_3')
      | ~ m1_subset_1(B_337,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_338,'#skF_4')
      | ~ m1_subset_1(B_338,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1556])).

tff(c_1572,plain,
    ( ~ v2_tex_2('#skF_6','#skF_3')
    | v2_tex_2('#skF_6','#skF_4')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_111,c_1560])).

tff(c_1583,plain,(
    v2_tex_2('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_40,c_1572])).

tff(c_1585,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_1583])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:51:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.02/1.98  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.27/1.98  
% 5.27/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.27/1.99  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 5.27/1.99  
% 5.27/1.99  %Foreground sorts:
% 5.27/1.99  
% 5.27/1.99  
% 5.27/1.99  %Background operators:
% 5.27/1.99  
% 5.27/1.99  
% 5.27/1.99  %Foreground operators:
% 5.27/1.99  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.27/1.99  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 5.27/1.99  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.27/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.27/1.99  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 5.27/1.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.27/1.99  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.27/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.27/1.99  tff('#skF_5', type, '#skF_5': $i).
% 5.27/1.99  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 5.27/1.99  tff('#skF_6', type, '#skF_6': $i).
% 5.27/1.99  tff('#skF_3', type, '#skF_3': $i).
% 5.27/1.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.27/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.27/1.99  tff('#skF_4', type, '#skF_4': $i).
% 5.27/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.27/1.99  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.27/1.99  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.27/1.99  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 5.27/1.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.27/1.99  
% 5.27/2.00  tff(f_88, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (C = D)) & v2_tex_2(C, A)) => v2_tex_2(D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_tex_2)).
% 5.27/2.00  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 5.27/2.00  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 5.27/2.00  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 5.27/2.00  tff(f_34, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 5.27/2.00  tff(c_24, plain, (~v2_tex_2('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.27/2.00  tff(c_32, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.27/2.00  tff(c_28, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.27/2.00  tff(c_26, plain, (v2_tex_2('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.27/2.00  tff(c_40, plain, (v2_tex_2('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26])).
% 5.27/2.00  tff(c_36, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.27/2.00  tff(c_103, plain, (![A_62, B_63]: (r1_tarski('#skF_2'(A_62, B_63), B_63) | v2_tex_2(B_63, A_62) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.27/2.00  tff(c_105, plain, (r1_tarski('#skF_2'('#skF_4', '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_32, c_103])).
% 5.27/2.00  tff(c_110, plain, (r1_tarski('#skF_2'('#skF_4', '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_105])).
% 5.27/2.00  tff(c_111, plain, (r1_tarski('#skF_2'('#skF_4', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_24, c_110])).
% 5.27/2.00  tff(c_16, plain, (![A_11, B_25]: (m1_subset_1('#skF_2'(A_11, B_25), k1_zfmisc_1(u1_struct_0(A_11))) | v2_tex_2(B_25, A_11) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.27/2.00  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.27/2.00  tff(c_6, plain, (![A_4]: (m1_subset_1(u1_pre_topc(A_4), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_4)))) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.27/2.00  tff(c_30, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.27/2.00  tff(c_54, plain, (![C_48, A_49, D_50, B_51]: (C_48=A_49 | g1_pre_topc(C_48, D_50)!=g1_pre_topc(A_49, B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(k1_zfmisc_1(A_49))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.27/2.00  tff(c_98, plain, (![A_60, B_61]: (u1_struct_0('#skF_3')=A_60 | g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))!=g1_pre_topc(A_60, B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(k1_zfmisc_1(A_60))))), inference(superposition, [status(thm), theory('equality')], [c_30, c_54])).
% 5.27/2.00  tff(c_102, plain, (![A_4]: (u1_struct_0(A_4)=u1_struct_0('#skF_3') | g1_pre_topc(u1_struct_0(A_4), u1_pre_topc(A_4))!=g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')) | ~l1_pre_topc(A_4))), inference(resolution, [status(thm)], [c_6, c_98])).
% 5.27/2.00  tff(c_122, plain, (u1_struct_0('#skF_3')=u1_struct_0('#skF_4') | ~l1_pre_topc('#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_102])).
% 5.27/2.00  tff(c_124, plain, (u1_struct_0('#skF_3')=u1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_122])).
% 5.27/2.00  tff(c_238, plain, (![A_75, B_76, C_77]: (v3_pre_topc('#skF_1'(A_75, B_76, C_77), A_75) | ~r1_tarski(C_77, B_76) | ~m1_subset_1(C_77, k1_zfmisc_1(u1_struct_0(A_75))) | ~v2_tex_2(B_76, A_75) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.27/2.00  tff(c_242, plain, (![B_76, C_77]: (v3_pre_topc('#skF_1'('#skF_3', B_76, C_77), '#skF_3') | ~r1_tarski(C_77, B_76) | ~m1_subset_1(C_77, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_76, '#skF_3') | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_124, c_238])).
% 5.27/2.00  tff(c_551, plain, (![B_105, C_106]: (v3_pre_topc('#skF_1'('#skF_3', B_105, C_106), '#skF_3') | ~r1_tarski(C_106, B_105) | ~m1_subset_1(C_106, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_105, '#skF_3') | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_124, c_242])).
% 5.27/2.00  tff(c_559, plain, (![B_105, B_25]: (v3_pre_topc('#skF_1'('#skF_3', B_105, '#skF_2'('#skF_4', B_25)), '#skF_3') | ~r1_tarski('#skF_2'('#skF_4', B_25), B_105) | ~v2_tex_2(B_105, '#skF_3') | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_25, '#skF_4') | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_16, c_551])).
% 5.27/2.00  tff(c_568, plain, (![B_105, B_25]: (v3_pre_topc('#skF_1'('#skF_3', B_105, '#skF_2'('#skF_4', B_25)), '#skF_3') | ~r1_tarski('#skF_2'('#skF_4', B_25), B_105) | ~v2_tex_2(B_105, '#skF_3') | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_25, '#skF_4') | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_559])).
% 5.27/2.00  tff(c_344, plain, (![A_84, B_85, C_86]: (m1_subset_1('#skF_1'(A_84, B_85, C_86), k1_zfmisc_1(u1_struct_0(A_84))) | ~r1_tarski(C_86, B_85) | ~m1_subset_1(C_86, k1_zfmisc_1(u1_struct_0(A_84))) | ~v2_tex_2(B_85, A_84) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.27/2.00  tff(c_372, plain, (![B_85, C_86]: (m1_subset_1('#skF_1'('#skF_3', B_85, C_86), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(C_86, B_85) | ~m1_subset_1(C_86, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_85, '#skF_3') | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_124, c_344])).
% 5.27/2.00  tff(c_643, plain, (![B_123, C_124]: (m1_subset_1('#skF_1'('#skF_3', B_123, C_124), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(C_124, B_123) | ~m1_subset_1(C_124, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_123, '#skF_3') | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_124, c_124, c_372])).
% 5.27/2.00  tff(c_149, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_124, c_6])).
% 5.27/2.00  tff(c_159, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_149])).
% 5.27/2.00  tff(c_135, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_3'))=g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_30])).
% 5.27/2.00  tff(c_8, plain, (![D_10, B_6, C_9, A_5]: (D_10=B_6 | g1_pre_topc(C_9, D_10)!=g1_pre_topc(A_5, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(k1_zfmisc_1(A_5))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.27/2.00  tff(c_187, plain, (![D_10, C_9]: (u1_pre_topc('#skF_3')=D_10 | g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))!=g1_pre_topc(C_9, D_10) | ~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))))), inference(superposition, [status(thm), theory('equality')], [c_135, c_8])).
% 5.27/2.00  tff(c_195, plain, (![D_10, C_9]: (u1_pre_topc('#skF_3')=D_10 | g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))!=g1_pre_topc(C_9, D_10))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_187])).
% 5.27/2.00  tff(c_201, plain, (u1_pre_topc('#skF_3')=u1_pre_topc('#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_195])).
% 5.27/2.00  tff(c_4, plain, (![B_3, A_1]: (r2_hidden(B_3, u1_pre_topc(A_1)) | ~v3_pre_topc(B_3, A_1) | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.27/2.00  tff(c_143, plain, (![B_3]: (r2_hidden(B_3, u1_pre_topc('#skF_3')) | ~v3_pre_topc(B_3, '#skF_3') | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_124, c_4])).
% 5.27/2.00  tff(c_155, plain, (![B_3]: (r2_hidden(B_3, u1_pre_topc('#skF_3')) | ~v3_pre_topc(B_3, '#skF_3') | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_143])).
% 5.27/2.00  tff(c_265, plain, (![B_3]: (r2_hidden(B_3, u1_pre_topc('#skF_4')) | ~v3_pre_topc(B_3, '#skF_3') | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_201, c_155])).
% 5.27/2.00  tff(c_815, plain, (![B_156, C_157]: (r2_hidden('#skF_1'('#skF_3', B_156, C_157), u1_pre_topc('#skF_4')) | ~v3_pre_topc('#skF_1'('#skF_3', B_156, C_157), '#skF_3') | ~r1_tarski(C_157, B_156) | ~m1_subset_1(C_157, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_156, '#skF_3') | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_643, c_265])).
% 5.27/2.00  tff(c_2, plain, (![B_3, A_1]: (v3_pre_topc(B_3, A_1) | ~r2_hidden(B_3, u1_pre_topc(A_1)) | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.27/2.00  tff(c_685, plain, (![B_123, C_124]: (v3_pre_topc('#skF_1'('#skF_3', B_123, C_124), '#skF_4') | ~r2_hidden('#skF_1'('#skF_3', B_123, C_124), u1_pre_topc('#skF_4')) | ~l1_pre_topc('#skF_4') | ~r1_tarski(C_124, B_123) | ~m1_subset_1(C_124, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_123, '#skF_3') | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_643, c_2])).
% 5.27/2.00  tff(c_711, plain, (![B_123, C_124]: (v3_pre_topc('#skF_1'('#skF_3', B_123, C_124), '#skF_4') | ~r2_hidden('#skF_1'('#skF_3', B_123, C_124), u1_pre_topc('#skF_4')) | ~r1_tarski(C_124, B_123) | ~m1_subset_1(C_124, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_123, '#skF_3') | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_685])).
% 5.27/2.00  tff(c_820, plain, (![B_158, C_159]: (v3_pre_topc('#skF_1'('#skF_3', B_158, C_159), '#skF_4') | ~v3_pre_topc('#skF_1'('#skF_3', B_158, C_159), '#skF_3') | ~r1_tarski(C_159, B_158) | ~m1_subset_1(C_159, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_158, '#skF_3') | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_815, c_711])).
% 5.27/2.00  tff(c_1090, plain, (![B_207, B_208]: (v3_pre_topc('#skF_1'('#skF_3', B_207, '#skF_2'('#skF_4', B_208)), '#skF_4') | ~m1_subset_1('#skF_2'('#skF_4', B_208), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski('#skF_2'('#skF_4', B_208), B_207) | ~v2_tex_2(B_207, '#skF_3') | ~m1_subset_1(B_207, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_208, '#skF_4') | ~m1_subset_1(B_208, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_568, c_820])).
% 5.27/2.00  tff(c_1093, plain, (![B_207, B_25]: (v3_pre_topc('#skF_1'('#skF_3', B_207, '#skF_2'('#skF_4', B_25)), '#skF_4') | ~r1_tarski('#skF_2'('#skF_4', B_25), B_207) | ~v2_tex_2(B_207, '#skF_3') | ~m1_subset_1(B_207, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_25, '#skF_4') | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_16, c_1090])).
% 5.27/2.00  tff(c_1096, plain, (![B_207, B_25]: (v3_pre_topc('#skF_1'('#skF_3', B_207, '#skF_2'('#skF_4', B_25)), '#skF_4') | ~r1_tarski('#skF_2'('#skF_4', B_25), B_207) | ~v2_tex_2(B_207, '#skF_3') | ~m1_subset_1(B_207, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_25, '#skF_4') | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1093])).
% 5.27/2.00  tff(c_390, plain, (![B_85, C_86]: (m1_subset_1('#skF_1'('#skF_3', B_85, C_86), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(C_86, B_85) | ~m1_subset_1(C_86, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_85, '#skF_3') | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_124, c_124, c_372])).
% 5.27/2.00  tff(c_595, plain, (![A_108, B_109, C_110]: (k9_subset_1(u1_struct_0(A_108), B_109, '#skF_1'(A_108, B_109, C_110))=C_110 | ~r1_tarski(C_110, B_109) | ~m1_subset_1(C_110, k1_zfmisc_1(u1_struct_0(A_108))) | ~v2_tex_2(B_109, A_108) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.27/2.00  tff(c_603, plain, (![B_109, C_110]: (k9_subset_1(u1_struct_0('#skF_3'), B_109, '#skF_1'('#skF_3', B_109, C_110))=C_110 | ~r1_tarski(C_110, B_109) | ~m1_subset_1(C_110, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_109, '#skF_3') | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_124, c_595])).
% 5.27/2.00  tff(c_712, plain, (![B_125, C_126]: (k9_subset_1(u1_struct_0('#skF_4'), B_125, '#skF_1'('#skF_3', B_125, C_126))=C_126 | ~r1_tarski(C_126, B_125) | ~m1_subset_1(C_126, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_125, '#skF_3') | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_124, c_124, c_603])).
% 5.27/2.00  tff(c_722, plain, (![B_125, B_25]: (k9_subset_1(u1_struct_0('#skF_4'), B_125, '#skF_1'('#skF_3', B_125, '#skF_2'('#skF_4', B_25)))='#skF_2'('#skF_4', B_25) | ~r1_tarski('#skF_2'('#skF_4', B_25), B_125) | ~v2_tex_2(B_125, '#skF_3') | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_25, '#skF_4') | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_16, c_712])).
% 5.27/2.00  tff(c_1033, plain, (![B_194, B_195]: (k9_subset_1(u1_struct_0('#skF_4'), B_194, '#skF_1'('#skF_3', B_194, '#skF_2'('#skF_4', B_195)))='#skF_2'('#skF_4', B_195) | ~r1_tarski('#skF_2'('#skF_4', B_195), B_194) | ~v2_tex_2(B_194, '#skF_3') | ~m1_subset_1(B_194, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_195, '#skF_4') | ~m1_subset_1(B_195, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_722])).
% 5.27/2.00  tff(c_12, plain, (![A_11, B_25, D_35]: (k9_subset_1(u1_struct_0(A_11), B_25, D_35)!='#skF_2'(A_11, B_25) | ~v3_pre_topc(D_35, A_11) | ~m1_subset_1(D_35, k1_zfmisc_1(u1_struct_0(A_11))) | v2_tex_2(B_25, A_11) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.27/2.00  tff(c_1040, plain, (![B_195, B_194]: ('#skF_2'('#skF_4', B_195)!='#skF_2'('#skF_4', B_194) | ~v3_pre_topc('#skF_1'('#skF_3', B_194, '#skF_2'('#skF_4', B_195)), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_3', B_194, '#skF_2'('#skF_4', B_195)), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_194, '#skF_4') | ~m1_subset_1(B_194, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~r1_tarski('#skF_2'('#skF_4', B_195), B_194) | ~v2_tex_2(B_194, '#skF_3') | ~m1_subset_1(B_194, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_195, '#skF_4') | ~m1_subset_1(B_195, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_1033, c_12])).
% 5.27/2.00  tff(c_1536, plain, (![B_330, B_329]: ('#skF_2'('#skF_4', B_330)!='#skF_2'('#skF_4', B_329) | ~v3_pre_topc('#skF_1'('#skF_3', B_330, '#skF_2'('#skF_4', B_329)), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_3', B_330, '#skF_2'('#skF_4', B_329)), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_330, '#skF_4') | ~r1_tarski('#skF_2'('#skF_4', B_329), B_330) | ~v2_tex_2(B_330, '#skF_3') | ~m1_subset_1(B_330, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_329, '#skF_4') | ~m1_subset_1(B_329, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1040])).
% 5.27/2.00  tff(c_1542, plain, (![B_332, B_331]: ('#skF_2'('#skF_4', B_332)!='#skF_2'('#skF_4', B_331) | ~v3_pre_topc('#skF_1'('#skF_3', B_331, '#skF_2'('#skF_4', B_332)), '#skF_4') | v2_tex_2(B_331, '#skF_4') | v2_tex_2(B_332, '#skF_4') | ~m1_subset_1(B_332, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski('#skF_2'('#skF_4', B_332), B_331) | ~m1_subset_1('#skF_2'('#skF_4', B_332), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_331, '#skF_3') | ~m1_subset_1(B_331, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_390, c_1536])).
% 5.27/2.00  tff(c_1553, plain, (![B_336, B_335]: ('#skF_2'('#skF_4', B_336)!='#skF_2'('#skF_4', B_335) | v2_tex_2(B_336, '#skF_4') | ~m1_subset_1('#skF_2'('#skF_4', B_335), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski('#skF_2'('#skF_4', B_335), B_336) | ~v2_tex_2(B_336, '#skF_3') | ~m1_subset_1(B_336, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_335, '#skF_4') | ~m1_subset_1(B_335, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_1096, c_1542])).
% 5.27/2.00  tff(c_1556, plain, (![B_336, B_25]: ('#skF_2'('#skF_4', B_336)!='#skF_2'('#skF_4', B_25) | v2_tex_2(B_336, '#skF_4') | ~r1_tarski('#skF_2'('#skF_4', B_25), B_336) | ~v2_tex_2(B_336, '#skF_3') | ~m1_subset_1(B_336, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_25, '#skF_4') | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_16, c_1553])).
% 5.27/2.00  tff(c_1560, plain, (![B_338, B_337]: ('#skF_2'('#skF_4', B_338)!='#skF_2'('#skF_4', B_337) | v2_tex_2(B_337, '#skF_4') | ~r1_tarski('#skF_2'('#skF_4', B_338), B_337) | ~v2_tex_2(B_337, '#skF_3') | ~m1_subset_1(B_337, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_338, '#skF_4') | ~m1_subset_1(B_338, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1556])).
% 5.27/2.00  tff(c_1572, plain, (~v2_tex_2('#skF_6', '#skF_3') | v2_tex_2('#skF_6', '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_111, c_1560])).
% 5.27/2.00  tff(c_1583, plain, (v2_tex_2('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_40, c_1572])).
% 5.27/2.00  tff(c_1585, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_1583])).
% 5.27/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.27/2.00  
% 5.27/2.00  Inference rules
% 5.27/2.01  ----------------------
% 5.27/2.01  #Ref     : 6
% 5.27/2.01  #Sup     : 302
% 5.27/2.01  #Fact    : 0
% 5.27/2.01  #Define  : 0
% 5.27/2.01  #Split   : 5
% 5.27/2.01  #Chain   : 0
% 5.27/2.01  #Close   : 0
% 5.27/2.01  
% 5.27/2.01  Ordering : KBO
% 5.27/2.01  
% 5.27/2.01  Simplification rules
% 5.27/2.01  ----------------------
% 5.27/2.01  #Subsume      : 55
% 5.27/2.01  #Demod        : 182
% 5.27/2.01  #Tautology    : 100
% 5.27/2.01  #SimpNegUnit  : 10
% 5.27/2.01  #BackRed      : 7
% 5.27/2.01  
% 5.27/2.01  #Partial instantiations: 0
% 5.27/2.01  #Strategies tried      : 1
% 5.27/2.01  
% 5.27/2.01  Timing (in seconds)
% 5.27/2.01  ----------------------
% 5.27/2.01  Preprocessing        : 0.32
% 5.27/2.01  Parsing              : 0.17
% 5.27/2.01  CNF conversion       : 0.02
% 5.27/2.01  Main loop            : 0.92
% 5.27/2.01  Inferencing          : 0.39
% 5.27/2.01  Reduction            : 0.23
% 5.27/2.01  Demodulation         : 0.15
% 5.27/2.01  BG Simplification    : 0.03
% 5.27/2.01  Subsumption          : 0.22
% 5.27/2.01  Abstraction          : 0.03
% 5.27/2.01  MUC search           : 0.00
% 5.27/2.01  Cooper               : 0.00
% 5.27/2.01  Total                : 1.27
% 5.27/2.01  Index Insertion      : 0.00
% 5.27/2.01  Index Deletion       : 0.00
% 5.27/2.01  Index Matching       : 0.00
% 5.27/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
