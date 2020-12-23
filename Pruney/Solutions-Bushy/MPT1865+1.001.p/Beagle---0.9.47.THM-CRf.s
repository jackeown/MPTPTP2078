%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1865+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:34 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   60 (  94 expanded)
%              Number of leaves         :   25 (  45 expanded)
%              Depth                    :   14
%              Number of atoms          :  143 ( 300 expanded)
%              Number of equality atoms :   17 (  33 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tex_2(B,A)
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ~ ( r2_hidden(C,B)
                      & ! [D] :
                          ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                         => ~ ( v4_pre_topc(D,A)
                              & k9_subset_1(u1_struct_0(A),B,D) = k1_tarski(C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tex_2)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
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
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).

tff(c_28,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_18,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(k1_tarski(A_28),B_29)
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_64,plain,(
    ! [C_58,B_59,A_60] :
      ( ~ v1_xboole_0(C_58)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(C_58))
      | ~ r2_hidden(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_70,plain,(
    ! [A_60] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_60,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_64])).

tff(c_71,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_14,plain,(
    ! [A_26,B_27] :
      ( r2_hidden(A_26,B_27)
      | v1_xboole_0(B_27)
      | ~ m1_subset_1(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_36,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_32,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_22,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(A_30,k1_zfmisc_1(B_31))
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_191,plain,(
    ! [A_95,B_96,C_97] :
      ( v4_pre_topc('#skF_1'(A_95,B_96,C_97),A_95)
      | ~ r1_tarski(C_97,B_96)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ v2_tex_2(B_96,A_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_226,plain,(
    ! [A_101,B_102,A_103] :
      ( v4_pre_topc('#skF_1'(A_101,B_102,A_103),A_101)
      | ~ r1_tarski(A_103,B_102)
      | ~ v2_tex_2(B_102,A_101)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101)
      | ~ r1_tarski(A_103,u1_struct_0(A_101)) ) ),
    inference(resolution,[status(thm)],[c_22,c_191])).

tff(c_233,plain,(
    ! [A_103] :
      ( v4_pre_topc('#skF_1'('#skF_3','#skF_4',A_103),'#skF_3')
      | ~ r1_tarski(A_103,'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_103,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_34,c_226])).

tff(c_238,plain,(
    ! [A_103] :
      ( v4_pre_topc('#skF_1'('#skF_3','#skF_4',A_103),'#skF_3')
      | ~ r1_tarski(A_103,'#skF_4')
      | ~ r1_tarski(A_103,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_233])).

tff(c_300,plain,(
    ! [A_122,B_123,C_124] :
      ( k9_subset_1(u1_struct_0(A_122),B_123,'#skF_1'(A_122,B_123,C_124)) = C_124
      | ~ r1_tarski(C_124,B_123)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ v2_tex_2(B_123,A_122)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_356,plain,(
    ! [A_127,B_128,A_129] :
      ( k9_subset_1(u1_struct_0(A_127),B_128,'#skF_1'(A_127,B_128,A_129)) = A_129
      | ~ r1_tarski(A_129,B_128)
      | ~ v2_tex_2(B_128,A_127)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127)
      | ~ r1_tarski(A_129,u1_struct_0(A_127)) ) ),
    inference(resolution,[status(thm)],[c_22,c_300])).

tff(c_365,plain,(
    ! [A_129] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3','#skF_4',A_129)) = A_129
      | ~ r1_tarski(A_129,'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_129,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_34,c_356])).

tff(c_377,plain,(
    ! [A_134] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3','#skF_4',A_134)) = A_134
      | ~ r1_tarski(A_134,'#skF_4')
      | ~ r1_tarski(A_134,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_365])).

tff(c_246,plain,(
    ! [A_113,B_114,C_115] :
      ( m1_subset_1('#skF_1'(A_113,B_114,C_115),k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ r1_tarski(C_115,B_114)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ v2_tex_2(B_114,A_113)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    ! [D_46] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',D_46) != k1_tarski('#skF_5')
      | ~ v4_pre_topc(D_46,'#skF_3')
      | ~ m1_subset_1(D_46,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_268,plain,(
    ! [B_114,C_115] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_114,C_115)) != k1_tarski('#skF_5')
      | ~ v4_pre_topc('#skF_1'('#skF_3',B_114,C_115),'#skF_3')
      | ~ r1_tarski(C_115,B_114)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_114,'#skF_3')
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_246,c_26])).

tff(c_285,plain,(
    ! [B_114,C_115] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_114,C_115)) != k1_tarski('#skF_5')
      | ~ v4_pre_topc('#skF_1'('#skF_3',B_114,C_115),'#skF_3')
      | ~ r1_tarski(C_115,B_114)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_114,'#skF_3')
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_268])).

tff(c_386,plain,(
    ! [A_134] :
      ( k1_tarski('#skF_5') != A_134
      | ~ v4_pre_topc('#skF_1'('#skF_3','#skF_4',A_134),'#skF_3')
      | ~ r1_tarski(A_134,'#skF_4')
      | ~ m1_subset_1(A_134,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_134,'#skF_4')
      | ~ r1_tarski(A_134,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_285])).

tff(c_407,plain,(
    ! [A_135] :
      ( k1_tarski('#skF_5') != A_135
      | ~ v4_pre_topc('#skF_1'('#skF_3','#skF_4',A_135),'#skF_3')
      | ~ m1_subset_1(A_135,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_135,'#skF_4')
      | ~ r1_tarski(A_135,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_386])).

tff(c_434,plain,(
    ! [A_136] :
      ( k1_tarski('#skF_5') != A_136
      | ~ v4_pre_topc('#skF_1'('#skF_3','#skF_4',A_136),'#skF_3')
      | ~ r1_tarski(A_136,'#skF_4')
      | ~ r1_tarski(A_136,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_22,c_407])).

tff(c_454,plain,(
    ! [A_137] :
      ( k1_tarski('#skF_5') != A_137
      | ~ r1_tarski(A_137,'#skF_4')
      | ~ r1_tarski(A_137,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_238,c_434])).

tff(c_483,plain,(
    ! [A_138] :
      ( k1_tarski(A_138) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_138),'#skF_4')
      | ~ r2_hidden(A_138,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_18,c_454])).

tff(c_487,plain,(
    ! [A_26] :
      ( k1_tarski(A_26) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_26),'#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_26,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_14,c_483])).

tff(c_491,plain,(
    ! [A_139] :
      ( k1_tarski(A_139) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_139),'#skF_4')
      | ~ m1_subset_1(A_139,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_487])).

tff(c_497,plain,(
    ! [A_140] :
      ( k1_tarski(A_140) != k1_tarski('#skF_5')
      | ~ m1_subset_1(A_140,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_140,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_491])).

tff(c_500,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_497])).

tff(c_504,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_500])).

tff(c_505,plain,(
    ! [A_60] : ~ r2_hidden(A_60,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_508,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_505,c_28])).

%------------------------------------------------------------------------------
