%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:59 EST 2020

% Result     : Theorem 6.72s
% Output     : CNFRefutation 6.84s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 136 expanded)
%              Number of leaves         :   39 (  62 expanded)
%              Depth                    :   20
%              Number of atoms          :  186 ( 305 expanded)
%              Number of equality atoms :   18 (  26 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_130,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_114,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_46,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_40,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_51,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_42,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_77,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_54,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_28,plain,(
    ! [A_23] :
      ( l1_struct_0(A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_56,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_48,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_131,plain,(
    ! [A_65,B_66] :
      ( ~ r2_hidden('#skF_2'(A_65,B_66),B_66)
      | r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_136,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_131])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_149,plain,(
    ! [C_70,B_71,A_72] :
      ( r2_hidden(C_70,B_71)
      | ~ r2_hidden(C_70,A_72)
      | ~ r1_tarski(A_72,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_186,plain,(
    ! [A_79,B_80] :
      ( r2_hidden('#skF_1'(A_79),B_80)
      | ~ r1_tarski(A_79,B_80)
      | v1_xboole_0(A_79) ) ),
    inference(resolution,[status(thm)],[c_4,c_149])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,B_19)
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_196,plain,(
    ! [A_79,B_80] :
      ( m1_subset_1('#skF_1'(A_79),B_80)
      | ~ r1_tarski(A_79,B_80)
      | v1_xboole_0(A_79) ) ),
    inference(resolution,[status(thm)],[c_186,c_24])).

tff(c_155,plain,(
    ! [A_1,B_71] :
      ( r2_hidden('#skF_1'(A_1),B_71)
      | ~ r1_tarski(A_1,B_71)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_149])).

tff(c_90,plain,(
    ! [A_52,B_53] :
      ( m1_subset_1(A_52,B_53)
      | ~ r2_hidden(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_94,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_90])).

tff(c_247,plain,(
    ! [A_90,B_91] :
      ( k6_domain_1(A_90,B_91) = k1_tarski(B_91)
      | ~ m1_subset_1(B_91,A_90)
      | v1_xboole_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_267,plain,(
    ! [A_1] :
      ( k6_domain_1(A_1,'#skF_1'(A_1)) = k1_tarski('#skF_1'(A_1))
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_94,c_247])).

tff(c_376,plain,(
    ! [A_106,B_107] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_106),B_107),A_106)
      | ~ m1_subset_1(B_107,u1_struct_0(A_106))
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2505,plain,(
    ! [A_368] :
      ( v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_368))),A_368)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_368)),u1_struct_0(A_368))
      | ~ l1_pre_topc(A_368)
      | ~ v2_pre_topc(A_368)
      | v2_struct_0(A_368)
      | v1_xboole_0(u1_struct_0(A_368)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_376])).

tff(c_52,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_97,plain,(
    ! [A_56,B_57] :
      ( r2_hidden('#skF_2'(A_56,B_57),A_56)
      | r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_107,plain,(
    ! [A_60,B_61] :
      ( ~ v1_xboole_0(A_60)
      | r1_tarski(A_60,B_61) ) ),
    inference(resolution,[status(thm)],[c_97,c_2])).

tff(c_16,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_113,plain,(
    ! [A_62] :
      ( k1_xboole_0 = A_62
      | ~ v1_xboole_0(A_62) ) ),
    inference(resolution,[status(thm)],[c_107,c_16])).

tff(c_117,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_52,c_113])).

tff(c_12,plain,(
    ! [A_10] : k2_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_72,plain,(
    ! [A_47,B_48] : k2_xboole_0(k1_tarski(A_47),B_48) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_76,plain,(
    ! [A_47] : k1_tarski(A_47) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_72])).

tff(c_120,plain,(
    ! [A_47] : k1_tarski(A_47) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_76])).

tff(c_22,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k1_tarski(A_16),k1_zfmisc_1(B_17))
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_20,plain,(
    ! [A_15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_122,plain,(
    ! [A_15] : m1_subset_1('#skF_5',k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_20])).

tff(c_14,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_124,plain,(
    ! [A_11] : r1_tarski('#skF_5',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_14])).

tff(c_885,plain,(
    ! [C_165,B_166,A_167] :
      ( C_165 = B_166
      | ~ r1_tarski(B_166,C_165)
      | ~ v2_tex_2(C_165,A_167)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ v3_tex_2(B_166,A_167)
      | ~ m1_subset_1(B_166,k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ l1_pre_topc(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_889,plain,(
    ! [A_11,A_167] :
      ( A_11 = '#skF_5'
      | ~ v2_tex_2(A_11,A_167)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ v3_tex_2('#skF_5',A_167)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ l1_pre_topc(A_167) ) ),
    inference(resolution,[status(thm)],[c_124,c_885])).

tff(c_1190,plain,(
    ! [A_206,A_207] :
      ( A_206 = '#skF_5'
      | ~ v2_tex_2(A_206,A_207)
      | ~ m1_subset_1(A_206,k1_zfmisc_1(u1_struct_0(A_207)))
      | ~ v3_tex_2('#skF_5',A_207)
      | ~ l1_pre_topc(A_207) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_889])).

tff(c_1245,plain,(
    ! [A_16,A_207] :
      ( k1_tarski(A_16) = '#skF_5'
      | ~ v2_tex_2(k1_tarski(A_16),A_207)
      | ~ v3_tex_2('#skF_5',A_207)
      | ~ l1_pre_topc(A_207)
      | ~ r2_hidden(A_16,u1_struct_0(A_207)) ) ),
    inference(resolution,[status(thm)],[c_22,c_1190])).

tff(c_1266,plain,(
    ! [A_16,A_207] :
      ( ~ v2_tex_2(k1_tarski(A_16),A_207)
      | ~ v3_tex_2('#skF_5',A_207)
      | ~ l1_pre_topc(A_207)
      | ~ r2_hidden(A_16,u1_struct_0(A_207)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_1245])).

tff(c_4172,plain,(
    ! [A_558] :
      ( ~ v3_tex_2('#skF_5',A_558)
      | ~ r2_hidden('#skF_1'(u1_struct_0(A_558)),u1_struct_0(A_558))
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_558)),u1_struct_0(A_558))
      | ~ l1_pre_topc(A_558)
      | ~ v2_pre_topc(A_558)
      | v2_struct_0(A_558)
      | v1_xboole_0(u1_struct_0(A_558)) ) ),
    inference(resolution,[status(thm)],[c_2505,c_1266])).

tff(c_4175,plain,(
    ! [A_558] :
      ( ~ v3_tex_2('#skF_5',A_558)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_558)),u1_struct_0(A_558))
      | ~ l1_pre_topc(A_558)
      | ~ v2_pre_topc(A_558)
      | v2_struct_0(A_558)
      | ~ r1_tarski(u1_struct_0(A_558),u1_struct_0(A_558))
      | v1_xboole_0(u1_struct_0(A_558)) ) ),
    inference(resolution,[status(thm)],[c_155,c_4172])).

tff(c_4183,plain,(
    ! [A_559] :
      ( ~ v3_tex_2('#skF_5',A_559)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_559)),u1_struct_0(A_559))
      | ~ l1_pre_topc(A_559)
      | ~ v2_pre_topc(A_559)
      | v2_struct_0(A_559)
      | v1_xboole_0(u1_struct_0(A_559)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_4175])).

tff(c_4190,plain,(
    ! [A_559] :
      ( ~ v3_tex_2('#skF_5',A_559)
      | ~ l1_pre_topc(A_559)
      | ~ v2_pre_topc(A_559)
      | v2_struct_0(A_559)
      | ~ r1_tarski(u1_struct_0(A_559),u1_struct_0(A_559))
      | v1_xboole_0(u1_struct_0(A_559)) ) ),
    inference(resolution,[status(thm)],[c_196,c_4183])).

tff(c_4199,plain,(
    ! [A_560] :
      ( ~ v3_tex_2('#skF_5',A_560)
      | ~ l1_pre_topc(A_560)
      | ~ v2_pre_topc(A_560)
      | v2_struct_0(A_560)
      | v1_xboole_0(u1_struct_0(A_560)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_4190])).

tff(c_30,plain,(
    ! [A_24] :
      ( ~ v1_xboole_0(u1_struct_0(A_24))
      | ~ l1_struct_0(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4209,plain,(
    ! [A_563] :
      ( ~ l1_struct_0(A_563)
      | ~ v3_tex_2('#skF_5',A_563)
      | ~ l1_pre_topc(A_563)
      | ~ v2_pre_topc(A_563)
      | v2_struct_0(A_563) ) ),
    inference(resolution,[status(thm)],[c_4199,c_30])).

tff(c_4215,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_4209])).

tff(c_4219,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4215])).

tff(c_4220,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4219])).

tff(c_4223,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_4220])).

tff(c_4227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4223])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:58:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.72/2.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.72/2.52  
% 6.72/2.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.72/2.53  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 6.72/2.53  
% 6.72/2.53  %Foreground sorts:
% 6.72/2.53  
% 6.72/2.53  
% 6.72/2.53  %Background operators:
% 6.72/2.53  
% 6.72/2.53  
% 6.72/2.53  %Foreground operators:
% 6.72/2.53  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.72/2.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.72/2.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.72/2.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.72/2.53  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.72/2.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.72/2.53  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.72/2.53  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.72/2.53  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 6.72/2.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.72/2.53  tff('#skF_5', type, '#skF_5': $i).
% 6.72/2.53  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 6.72/2.53  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 6.72/2.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.72/2.53  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.72/2.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.72/2.53  tff('#skF_4', type, '#skF_4': $i).
% 6.72/2.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.72/2.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.72/2.53  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.72/2.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.72/2.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.72/2.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.72/2.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.72/2.53  
% 6.84/2.54  tff(f_130, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 6.84/2.54  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.84/2.54  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.84/2.54  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.84/2.54  tff(f_59, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 6.84/2.54  tff(f_84, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 6.84/2.54  tff(f_114, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 6.84/2.54  tff(f_46, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 6.84/2.54  tff(f_40, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 6.84/2.54  tff(f_49, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 6.84/2.54  tff(f_55, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 6.84/2.54  tff(f_51, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 6.84/2.54  tff(f_42, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.84/2.54  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 6.84/2.54  tff(f_77, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 6.84/2.54  tff(c_54, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.84/2.54  tff(c_28, plain, (![A_23]: (l1_struct_0(A_23) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.84/2.54  tff(c_58, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.84/2.54  tff(c_56, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.84/2.54  tff(c_48, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.84/2.54  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.84/2.54  tff(c_131, plain, (![A_65, B_66]: (~r2_hidden('#skF_2'(A_65, B_66), B_66) | r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.84/2.54  tff(c_136, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_131])).
% 6.84/2.54  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.84/2.54  tff(c_149, plain, (![C_70, B_71, A_72]: (r2_hidden(C_70, B_71) | ~r2_hidden(C_70, A_72) | ~r1_tarski(A_72, B_71))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.84/2.54  tff(c_186, plain, (![A_79, B_80]: (r2_hidden('#skF_1'(A_79), B_80) | ~r1_tarski(A_79, B_80) | v1_xboole_0(A_79))), inference(resolution, [status(thm)], [c_4, c_149])).
% 6.84/2.54  tff(c_24, plain, (![A_18, B_19]: (m1_subset_1(A_18, B_19) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.84/2.54  tff(c_196, plain, (![A_79, B_80]: (m1_subset_1('#skF_1'(A_79), B_80) | ~r1_tarski(A_79, B_80) | v1_xboole_0(A_79))), inference(resolution, [status(thm)], [c_186, c_24])).
% 6.84/2.54  tff(c_155, plain, (![A_1, B_71]: (r2_hidden('#skF_1'(A_1), B_71) | ~r1_tarski(A_1, B_71) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_149])).
% 6.84/2.54  tff(c_90, plain, (![A_52, B_53]: (m1_subset_1(A_52, B_53) | ~r2_hidden(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.84/2.54  tff(c_94, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_90])).
% 6.84/2.54  tff(c_247, plain, (![A_90, B_91]: (k6_domain_1(A_90, B_91)=k1_tarski(B_91) | ~m1_subset_1(B_91, A_90) | v1_xboole_0(A_90))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.84/2.54  tff(c_267, plain, (![A_1]: (k6_domain_1(A_1, '#skF_1'(A_1))=k1_tarski('#skF_1'(A_1)) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_94, c_247])).
% 6.84/2.54  tff(c_376, plain, (![A_106, B_107]: (v2_tex_2(k6_domain_1(u1_struct_0(A_106), B_107), A_106) | ~m1_subset_1(B_107, u1_struct_0(A_106)) | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.84/2.54  tff(c_2505, plain, (![A_368]: (v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_368))), A_368) | ~m1_subset_1('#skF_1'(u1_struct_0(A_368)), u1_struct_0(A_368)) | ~l1_pre_topc(A_368) | ~v2_pre_topc(A_368) | v2_struct_0(A_368) | v1_xboole_0(u1_struct_0(A_368)))), inference(superposition, [status(thm), theory('equality')], [c_267, c_376])).
% 6.84/2.54  tff(c_52, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.84/2.54  tff(c_97, plain, (![A_56, B_57]: (r2_hidden('#skF_2'(A_56, B_57), A_56) | r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.84/2.54  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.84/2.54  tff(c_107, plain, (![A_60, B_61]: (~v1_xboole_0(A_60) | r1_tarski(A_60, B_61))), inference(resolution, [status(thm)], [c_97, c_2])).
% 6.84/2.54  tff(c_16, plain, (![A_12]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.84/2.54  tff(c_113, plain, (![A_62]: (k1_xboole_0=A_62 | ~v1_xboole_0(A_62))), inference(resolution, [status(thm)], [c_107, c_16])).
% 6.84/2.54  tff(c_117, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_52, c_113])).
% 6.84/2.54  tff(c_12, plain, (![A_10]: (k2_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.84/2.54  tff(c_72, plain, (![A_47, B_48]: (k2_xboole_0(k1_tarski(A_47), B_48)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.84/2.54  tff(c_76, plain, (![A_47]: (k1_tarski(A_47)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_72])).
% 6.84/2.54  tff(c_120, plain, (![A_47]: (k1_tarski(A_47)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_117, c_76])).
% 6.84/2.54  tff(c_22, plain, (![A_16, B_17]: (m1_subset_1(k1_tarski(A_16), k1_zfmisc_1(B_17)) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.84/2.54  tff(c_20, plain, (![A_15]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.84/2.54  tff(c_122, plain, (![A_15]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_20])).
% 6.84/2.54  tff(c_14, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.84/2.54  tff(c_124, plain, (![A_11]: (r1_tarski('#skF_5', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_14])).
% 6.84/2.54  tff(c_885, plain, (![C_165, B_166, A_167]: (C_165=B_166 | ~r1_tarski(B_166, C_165) | ~v2_tex_2(C_165, A_167) | ~m1_subset_1(C_165, k1_zfmisc_1(u1_struct_0(A_167))) | ~v3_tex_2(B_166, A_167) | ~m1_subset_1(B_166, k1_zfmisc_1(u1_struct_0(A_167))) | ~l1_pre_topc(A_167))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.84/2.54  tff(c_889, plain, (![A_11, A_167]: (A_11='#skF_5' | ~v2_tex_2(A_11, A_167) | ~m1_subset_1(A_11, k1_zfmisc_1(u1_struct_0(A_167))) | ~v3_tex_2('#skF_5', A_167) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_167))) | ~l1_pre_topc(A_167))), inference(resolution, [status(thm)], [c_124, c_885])).
% 6.84/2.54  tff(c_1190, plain, (![A_206, A_207]: (A_206='#skF_5' | ~v2_tex_2(A_206, A_207) | ~m1_subset_1(A_206, k1_zfmisc_1(u1_struct_0(A_207))) | ~v3_tex_2('#skF_5', A_207) | ~l1_pre_topc(A_207))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_889])).
% 6.84/2.54  tff(c_1245, plain, (![A_16, A_207]: (k1_tarski(A_16)='#skF_5' | ~v2_tex_2(k1_tarski(A_16), A_207) | ~v3_tex_2('#skF_5', A_207) | ~l1_pre_topc(A_207) | ~r2_hidden(A_16, u1_struct_0(A_207)))), inference(resolution, [status(thm)], [c_22, c_1190])).
% 6.84/2.54  tff(c_1266, plain, (![A_16, A_207]: (~v2_tex_2(k1_tarski(A_16), A_207) | ~v3_tex_2('#skF_5', A_207) | ~l1_pre_topc(A_207) | ~r2_hidden(A_16, u1_struct_0(A_207)))), inference(negUnitSimplification, [status(thm)], [c_120, c_1245])).
% 6.84/2.54  tff(c_4172, plain, (![A_558]: (~v3_tex_2('#skF_5', A_558) | ~r2_hidden('#skF_1'(u1_struct_0(A_558)), u1_struct_0(A_558)) | ~m1_subset_1('#skF_1'(u1_struct_0(A_558)), u1_struct_0(A_558)) | ~l1_pre_topc(A_558) | ~v2_pre_topc(A_558) | v2_struct_0(A_558) | v1_xboole_0(u1_struct_0(A_558)))), inference(resolution, [status(thm)], [c_2505, c_1266])).
% 6.84/2.54  tff(c_4175, plain, (![A_558]: (~v3_tex_2('#skF_5', A_558) | ~m1_subset_1('#skF_1'(u1_struct_0(A_558)), u1_struct_0(A_558)) | ~l1_pre_topc(A_558) | ~v2_pre_topc(A_558) | v2_struct_0(A_558) | ~r1_tarski(u1_struct_0(A_558), u1_struct_0(A_558)) | v1_xboole_0(u1_struct_0(A_558)))), inference(resolution, [status(thm)], [c_155, c_4172])).
% 6.84/2.54  tff(c_4183, plain, (![A_559]: (~v3_tex_2('#skF_5', A_559) | ~m1_subset_1('#skF_1'(u1_struct_0(A_559)), u1_struct_0(A_559)) | ~l1_pre_topc(A_559) | ~v2_pre_topc(A_559) | v2_struct_0(A_559) | v1_xboole_0(u1_struct_0(A_559)))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_4175])).
% 6.84/2.54  tff(c_4190, plain, (![A_559]: (~v3_tex_2('#skF_5', A_559) | ~l1_pre_topc(A_559) | ~v2_pre_topc(A_559) | v2_struct_0(A_559) | ~r1_tarski(u1_struct_0(A_559), u1_struct_0(A_559)) | v1_xboole_0(u1_struct_0(A_559)))), inference(resolution, [status(thm)], [c_196, c_4183])).
% 6.84/2.54  tff(c_4199, plain, (![A_560]: (~v3_tex_2('#skF_5', A_560) | ~l1_pre_topc(A_560) | ~v2_pre_topc(A_560) | v2_struct_0(A_560) | v1_xboole_0(u1_struct_0(A_560)))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_4190])).
% 6.84/2.54  tff(c_30, plain, (![A_24]: (~v1_xboole_0(u1_struct_0(A_24)) | ~l1_struct_0(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.84/2.54  tff(c_4209, plain, (![A_563]: (~l1_struct_0(A_563) | ~v3_tex_2('#skF_5', A_563) | ~l1_pre_topc(A_563) | ~v2_pre_topc(A_563) | v2_struct_0(A_563))), inference(resolution, [status(thm)], [c_4199, c_30])).
% 6.84/2.54  tff(c_4215, plain, (~l1_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_4209])).
% 6.84/2.54  tff(c_4219, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_4215])).
% 6.84/2.54  tff(c_4220, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_58, c_4219])).
% 6.84/2.54  tff(c_4223, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_28, c_4220])).
% 6.84/2.54  tff(c_4227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_4223])).
% 6.84/2.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.84/2.54  
% 6.84/2.54  Inference rules
% 6.84/2.54  ----------------------
% 6.84/2.54  #Ref     : 0
% 6.84/2.54  #Sup     : 912
% 6.84/2.54  #Fact    : 0
% 6.84/2.54  #Define  : 0
% 6.84/2.54  #Split   : 1
% 6.84/2.54  #Chain   : 0
% 6.84/2.54  #Close   : 0
% 6.84/2.54  
% 6.84/2.54  Ordering : KBO
% 6.84/2.54  
% 6.84/2.55  Simplification rules
% 6.84/2.55  ----------------------
% 6.84/2.55  #Subsume      : 77
% 6.84/2.55  #Demod        : 71
% 6.84/2.55  #Tautology    : 189
% 6.84/2.55  #SimpNegUnit  : 16
% 6.84/2.55  #BackRed      : 20
% 6.84/2.55  
% 6.84/2.55  #Partial instantiations: 0
% 6.84/2.55  #Strategies tried      : 1
% 6.84/2.55  
% 6.84/2.55  Timing (in seconds)
% 6.84/2.55  ----------------------
% 6.84/2.55  Preprocessing        : 0.33
% 6.84/2.55  Parsing              : 0.17
% 6.84/2.55  CNF conversion       : 0.03
% 6.84/2.55  Main loop            : 1.40
% 6.84/2.55  Inferencing          : 0.47
% 6.84/2.55  Reduction            : 0.33
% 6.84/2.55  Demodulation         : 0.22
% 6.84/2.55  BG Simplification    : 0.06
% 6.84/2.55  Subsumption          : 0.42
% 6.84/2.55  Abstraction          : 0.07
% 6.84/2.55  MUC search           : 0.00
% 6.84/2.55  Cooper               : 0.00
% 6.84/2.55  Total                : 1.77
% 6.84/2.55  Index Insertion      : 0.00
% 6.84/2.55  Index Deletion       : 0.00
% 6.84/2.55  Index Matching       : 0.00
% 6.84/2.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
