%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1857+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:33 EST 2020

% Result     : Theorem 5.45s
% Output     : CNFRefutation 5.45s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 622 expanded)
%              Number of leaves         :   25 ( 211 expanded)
%              Depth                    :   23
%              Number of atoms          :  287 (2048 expanded)
%              Number of equality atoms :   36 ( 700 expanded)
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

tff(f_87,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tex_2)).

tff(f_54,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(c_24,plain,(
    ~ v2_tex_2('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_32,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_28,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_26,plain,(
    v2_tex_2('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_40,plain,(
    v2_tex_2('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26])).

tff(c_36,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_103,plain,(
    ! [A_62,B_63] :
      ( r1_tarski('#skF_2'(A_62,B_63),B_63)
      | v2_tex_2(B_63,A_62)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

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

tff(c_10,plain,(
    ! [A_4,B_18] :
      ( m1_subset_1('#skF_2'(A_4,B_18),k1_zfmisc_1(u1_struct_0(A_4)))
      | v2_tex_2(B_18,A_4)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_18,plain,(
    ! [A_29] :
      ( m1_subset_1(u1_pre_topc(A_29),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_29))))
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_30,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_54,plain,(
    ! [D_48,B_49,C_50,A_51] :
      ( D_48 = B_49
      | g1_pre_topc(C_50,D_48) != g1_pre_topc(A_51,B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k1_zfmisc_1(A_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_98,plain,(
    ! [B_60,A_61] :
      ( u1_pre_topc('#skF_3') = B_60
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(A_61,B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k1_zfmisc_1(A_61))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_54])).

tff(c_102,plain,(
    ! [A_29] :
      ( u1_pre_topc(A_29) = u1_pre_topc('#skF_3')
      | g1_pre_topc(u1_struct_0(A_29),u1_pre_topc(A_29)) != g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_18,c_98])).

tff(c_122,plain,
    ( u1_pre_topc('#skF_3') = u1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_102])).

tff(c_124,plain,(
    u1_pre_topc('#skF_3') = u1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_122])).

tff(c_140,plain,
    ( m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_18])).

tff(c_144,plain,(
    m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_140])).

tff(c_136,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_4')) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_30])).

tff(c_22,plain,(
    ! [C_34,A_30,D_35,B_31] :
      ( C_34 = A_30
      | g1_pre_topc(C_34,D_35) != g1_pre_topc(A_30,B_31)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(k1_zfmisc_1(A_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_167,plain,(
    ! [C_34,D_35] :
      ( u1_struct_0('#skF_3') = C_34
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(C_34,D_35)
      | ~ m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_22])).

tff(c_175,plain,(
    ! [C_34,D_35] :
      ( u1_struct_0('#skF_3') = C_34
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(C_34,D_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_167])).

tff(c_181,plain,(
    u1_struct_0('#skF_3') = u1_struct_0('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_175])).

tff(c_234,plain,(
    ! [A_75,B_76,C_77] :
      ( v3_pre_topc('#skF_1'(A_75,B_76,C_77),A_75)
      | ~ r1_tarski(C_77,B_76)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ v2_tex_2(B_76,A_75)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_236,plain,(
    ! [B_76,C_77] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_76,C_77),'#skF_3')
      | ~ r1_tarski(C_77,B_76)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_76,'#skF_3')
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_234])).

tff(c_545,plain,(
    ! [B_105,C_106] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_105,C_106),'#skF_3')
      | ~ r1_tarski(C_106,B_105)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_105,'#skF_3')
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_181,c_236])).

tff(c_553,plain,(
    ! [B_105,B_18] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_105,'#skF_2'('#skF_4',B_18)),'#skF_3')
      | ~ r1_tarski('#skF_2'('#skF_4',B_18),B_105)
      | ~ v2_tex_2(B_105,'#skF_3')
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_18,'#skF_4')
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10,c_545])).

tff(c_827,plain,(
    ! [B_149,B_150] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_149,'#skF_2'('#skF_4',B_150)),'#skF_3')
      | ~ r1_tarski('#skF_2'('#skF_4',B_150),B_149)
      | ~ v2_tex_2(B_149,'#skF_3')
      | ~ m1_subset_1(B_149,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_150,'#skF_4')
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_553])).

tff(c_338,plain,(
    ! [A_84,B_85,C_86] :
      ( m1_subset_1('#skF_1'(A_84,B_85,C_86),k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ r1_tarski(C_86,B_85)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ v2_tex_2(B_85,A_84)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4,plain,(
    ! [B_3,A_1] :
      ( r2_hidden(B_3,u1_pre_topc(A_1))
      | ~ v3_pre_topc(B_3,A_1)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_776,plain,(
    ! [A_134,B_135,C_136] :
      ( r2_hidden('#skF_1'(A_134,B_135,C_136),u1_pre_topc(A_134))
      | ~ v3_pre_topc('#skF_1'(A_134,B_135,C_136),A_134)
      | ~ r1_tarski(C_136,B_135)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ v2_tex_2(B_135,A_134)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ l1_pre_topc(A_134) ) ),
    inference(resolution,[status(thm)],[c_338,c_4])).

tff(c_779,plain,(
    ! [B_135,C_136] :
      ( r2_hidden('#skF_1'('#skF_3',B_135,C_136),u1_pre_topc('#skF_4'))
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_135,C_136),'#skF_3')
      | ~ r1_tarski(C_136,B_135)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_135,'#skF_3')
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_776])).

tff(c_781,plain,(
    ! [B_135,C_136] :
      ( r2_hidden('#skF_1'('#skF_3',B_135,C_136),u1_pre_topc('#skF_4'))
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_135,C_136),'#skF_3')
      | ~ r1_tarski(C_136,B_135)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_135,'#skF_3')
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_181,c_181,c_779])).

tff(c_366,plain,(
    ! [B_85,C_86] :
      ( m1_subset_1('#skF_1'('#skF_3',B_85,C_86),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(C_86,B_85)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_85,'#skF_3')
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_338])).

tff(c_637,plain,(
    ! [B_123,C_124] :
      ( m1_subset_1('#skF_1'('#skF_3',B_123,C_124),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(C_124,B_123)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_123,'#skF_3')
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_181,c_181,c_366])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v3_pre_topc(B_3,A_1)
      | ~ r2_hidden(B_3,u1_pre_topc(A_1))
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_679,plain,(
    ! [B_123,C_124] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_123,C_124),'#skF_4')
      | ~ r2_hidden('#skF_1'('#skF_3',B_123,C_124),u1_pre_topc('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(C_124,B_123)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_123,'#skF_3')
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_637,c_2])).

tff(c_800,plain,(
    ! [B_145,C_146] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_145,C_146),'#skF_4')
      | ~ r2_hidden('#skF_1'('#skF_3',B_145,C_146),u1_pre_topc('#skF_4'))
      | ~ r1_tarski(C_146,B_145)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_145,'#skF_3')
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_679])).

tff(c_804,plain,(
    ! [B_135,C_136] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_135,C_136),'#skF_4')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_135,C_136),'#skF_3')
      | ~ r1_tarski(C_136,B_135)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_135,'#skF_3')
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_781,c_800])).

tff(c_1084,plain,(
    ! [B_207,B_208] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_207,'#skF_2'('#skF_4',B_208)),'#skF_4')
      | ~ m1_subset_1('#skF_2'('#skF_4',B_208),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski('#skF_2'('#skF_4',B_208),B_207)
      | ~ v2_tex_2(B_207,'#skF_3')
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_208,'#skF_4')
      | ~ m1_subset_1(B_208,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_827,c_804])).

tff(c_1087,plain,(
    ! [B_207,B_18] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_207,'#skF_2'('#skF_4',B_18)),'#skF_4')
      | ~ r1_tarski('#skF_2'('#skF_4',B_18),B_207)
      | ~ v2_tex_2(B_207,'#skF_3')
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_18,'#skF_4')
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10,c_1084])).

tff(c_1090,plain,(
    ! [B_207,B_18] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_207,'#skF_2'('#skF_4',B_18)),'#skF_4')
      | ~ r1_tarski('#skF_2'('#skF_4',B_18),B_207)
      | ~ v2_tex_2(B_207,'#skF_3')
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_18,'#skF_4')
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1087])).

tff(c_384,plain,(
    ! [B_85,C_86] :
      ( m1_subset_1('#skF_1'('#skF_3',B_85,C_86),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(C_86,B_85)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_85,'#skF_3')
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_181,c_181,c_366])).

tff(c_589,plain,(
    ! [A_108,B_109,C_110] :
      ( k9_subset_1(u1_struct_0(A_108),B_109,'#skF_1'(A_108,B_109,C_110)) = C_110
      | ~ r1_tarski(C_110,B_109)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ v2_tex_2(B_109,A_108)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_595,plain,(
    ! [B_109,C_110] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_109,'#skF_1'('#skF_3',B_109,C_110)) = C_110
      | ~ r1_tarski(C_110,B_109)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_109,'#skF_3')
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_589])).

tff(c_706,plain,(
    ! [B_125,C_126] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_125,'#skF_1'('#skF_3',B_125,C_126)) = C_126
      | ~ r1_tarski(C_126,B_125)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_125,'#skF_3')
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_181,c_181,c_595])).

tff(c_716,plain,(
    ! [B_125,B_18] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_125,'#skF_1'('#skF_3',B_125,'#skF_2'('#skF_4',B_18))) = '#skF_2'('#skF_4',B_18)
      | ~ r1_tarski('#skF_2'('#skF_4',B_18),B_125)
      | ~ v2_tex_2(B_125,'#skF_3')
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_18,'#skF_4')
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10,c_706])).

tff(c_1027,plain,(
    ! [B_194,B_195] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_194,'#skF_1'('#skF_3',B_194,'#skF_2'('#skF_4',B_195))) = '#skF_2'('#skF_4',B_195)
      | ~ r1_tarski('#skF_2'('#skF_4',B_195),B_194)
      | ~ v2_tex_2(B_194,'#skF_3')
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_195,'#skF_4')
      | ~ m1_subset_1(B_195,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_716])).

tff(c_6,plain,(
    ! [A_4,B_18,D_28] :
      ( k9_subset_1(u1_struct_0(A_4),B_18,D_28) != '#skF_2'(A_4,B_18)
      | ~ v3_pre_topc(D_28,A_4)
      | ~ m1_subset_1(D_28,k1_zfmisc_1(u1_struct_0(A_4)))
      | v2_tex_2(B_18,A_4)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1034,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_1027,c_6])).

tff(c_1530,plain,(
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
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1034])).

tff(c_1536,plain,(
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
    inference(resolution,[status(thm)],[c_384,c_1530])).

tff(c_1547,plain,(
    ! [B_336,B_335] :
      ( '#skF_2'('#skF_4',B_336) != '#skF_2'('#skF_4',B_335)
      | v2_tex_2(B_335,'#skF_4')
      | ~ m1_subset_1('#skF_2'('#skF_4',B_336),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski('#skF_2'('#skF_4',B_336),B_335)
      | ~ v2_tex_2(B_335,'#skF_3')
      | ~ m1_subset_1(B_335,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_336,'#skF_4')
      | ~ m1_subset_1(B_336,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_1090,c_1536])).

tff(c_1550,plain,(
    ! [B_335,B_18] :
      ( '#skF_2'('#skF_4',B_335) != '#skF_2'('#skF_4',B_18)
      | v2_tex_2(B_335,'#skF_4')
      | ~ r1_tarski('#skF_2'('#skF_4',B_18),B_335)
      | ~ v2_tex_2(B_335,'#skF_3')
      | ~ m1_subset_1(B_335,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_18,'#skF_4')
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10,c_1547])).

tff(c_1554,plain,(
    ! [B_338,B_337] :
      ( '#skF_2'('#skF_4',B_338) != '#skF_2'('#skF_4',B_337)
      | v2_tex_2(B_337,'#skF_4')
      | ~ r1_tarski('#skF_2'('#skF_4',B_338),B_337)
      | ~ v2_tex_2(B_337,'#skF_3')
      | ~ m1_subset_1(B_337,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_338,'#skF_4')
      | ~ m1_subset_1(B_338,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1550])).

tff(c_1566,plain,
    ( ~ v2_tex_2('#skF_6','#skF_3')
    | v2_tex_2('#skF_6','#skF_4')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_111,c_1554])).

tff(c_1577,plain,(
    v2_tex_2('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_40,c_1566])).

tff(c_1579,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_1577])).

%------------------------------------------------------------------------------
