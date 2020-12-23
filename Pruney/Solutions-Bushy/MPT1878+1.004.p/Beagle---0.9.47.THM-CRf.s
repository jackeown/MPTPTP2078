%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1878+1.004 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:37 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 107 expanded)
%              Number of leaves         :   34 (  51 expanded)
%              Depth                    :   17
%              Number of atoms          :  145 ( 228 expanded)
%              Number of equality atoms :   14 (  26 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_56,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_91,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_99,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_72,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
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

tff(f_67,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_64,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_44,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_16,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_46,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_38,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_42,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_18,plain,(
    ! [A_14] : m1_subset_1('#skF_2'(A_14),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_103,plain,(
    ! [A_43,B_44] :
      ( k6_domain_1(A_43,B_44) = k1_tarski(B_44)
      | ~ m1_subset_1(B_44,A_43)
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_115,plain,(
    ! [A_14] :
      ( k6_domain_1(A_14,'#skF_2'(A_14)) = k1_tarski('#skF_2'(A_14))
      | v1_xboole_0(A_14) ) ),
    inference(resolution,[status(thm)],[c_18,c_103])).

tff(c_321,plain,(
    ! [A_65,B_66] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_65),B_66),A_65)
      | ~ m1_subset_1(B_66,u1_struct_0(A_65))
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_325,plain,(
    ! [A_65] :
      ( v2_tex_2(k1_tarski('#skF_2'(u1_struct_0(A_65))),A_65)
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_65)),u1_struct_0(A_65))
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65)
      | v1_xboole_0(u1_struct_0(A_65)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_321])).

tff(c_327,plain,(
    ! [A_65] :
      ( v2_tex_2(k1_tarski('#skF_2'(u1_struct_0(A_65))),A_65)
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65)
      | v1_xboole_0(u1_struct_0(A_65)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_325])).

tff(c_140,plain,(
    ! [A_49,B_50] :
      ( m1_subset_1(k6_domain_1(A_49,B_50),k1_zfmisc_1(A_49))
      | ~ m1_subset_1(B_50,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_152,plain,(
    ! [A_14] :
      ( m1_subset_1(k1_tarski('#skF_2'(A_14)),k1_zfmisc_1(A_14))
      | ~ m1_subset_1('#skF_2'(A_14),A_14)
      | v1_xboole_0(A_14)
      | v1_xboole_0(A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_140])).

tff(c_158,plain,(
    ! [A_14] :
      ( m1_subset_1(k1_tarski('#skF_2'(A_14)),k1_zfmisc_1(A_14))
      | v1_xboole_0(A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_152])).

tff(c_51,plain,(
    ! [A_31] :
      ( k1_xboole_0 = A_31
      | ~ v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_59,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_42,c_51])).

tff(c_24,plain,(
    ! [A_18] : v1_xboole_0('#skF_3'(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_58,plain,(
    ! [A_18] : '#skF_3'(A_18) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_51])).

tff(c_65,plain,(
    ! [A_18] : '#skF_3'(A_18) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_58])).

tff(c_26,plain,(
    ! [A_18] : m1_subset_1('#skF_3'(A_18),k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_83,plain,(
    ! [A_18] : m1_subset_1('#skF_5',k1_zfmisc_1(A_18)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_26])).

tff(c_88,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,B_41)
      | ~ m1_subset_1(A_40,k1_zfmisc_1(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_100,plain,(
    ! [A_18] : r1_tarski('#skF_5',A_18) ),
    inference(resolution,[status(thm)],[c_83,c_88])).

tff(c_639,plain,(
    ! [C_101,B_102,A_103] :
      ( C_101 = B_102
      | ~ r1_tarski(B_102,C_101)
      | ~ v2_tex_2(C_101,A_103)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ v3_tex_2(B_102,A_103)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_655,plain,(
    ! [A_18,A_103] :
      ( A_18 = '#skF_5'
      | ~ v2_tex_2(A_18,A_103)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ v3_tex_2('#skF_5',A_103)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(resolution,[status(thm)],[c_100,c_639])).

tff(c_666,plain,(
    ! [A_104,A_105] :
      ( A_104 = '#skF_5'
      | ~ v2_tex_2(A_104,A_105)
      | ~ m1_subset_1(A_104,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ v3_tex_2('#skF_5',A_105)
      | ~ l1_pre_topc(A_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_655])).

tff(c_724,plain,(
    ! [A_109] :
      ( k1_tarski('#skF_2'(u1_struct_0(A_109))) = '#skF_5'
      | ~ v2_tex_2(k1_tarski('#skF_2'(u1_struct_0(A_109))),A_109)
      | ~ v3_tex_2('#skF_5',A_109)
      | ~ l1_pre_topc(A_109)
      | v1_xboole_0(u1_struct_0(A_109)) ) ),
    inference(resolution,[status(thm)],[c_158,c_666])).

tff(c_736,plain,(
    ! [A_112] :
      ( k1_tarski('#skF_2'(u1_struct_0(A_112))) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_112)
      | ~ l1_pre_topc(A_112)
      | ~ v2_pre_topc(A_112)
      | v2_struct_0(A_112)
      | v1_xboole_0(u1_struct_0(A_112)) ) ),
    inference(resolution,[status(thm)],[c_327,c_724])).

tff(c_22,plain,(
    ! [A_17] : ~ v1_xboole_0(k1_tarski(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_774,plain,(
    ! [A_112] :
      ( ~ v1_xboole_0('#skF_5')
      | ~ v3_tex_2('#skF_5',A_112)
      | ~ l1_pre_topc(A_112)
      | ~ v2_pre_topc(A_112)
      | v2_struct_0(A_112)
      | v1_xboole_0(u1_struct_0(A_112)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_736,c_22])).

tff(c_788,plain,(
    ! [A_113] :
      ( ~ v3_tex_2('#skF_5',A_113)
      | ~ l1_pre_topc(A_113)
      | ~ v2_pre_topc(A_113)
      | v2_struct_0(A_113)
      | v1_xboole_0(u1_struct_0(A_113)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_774])).

tff(c_20,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0(u1_struct_0(A_16))
      | ~ l1_struct_0(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_797,plain,(
    ! [A_114] :
      ( ~ l1_struct_0(A_114)
      | ~ v3_tex_2('#skF_5',A_114)
      | ~ l1_pre_topc(A_114)
      | ~ v2_pre_topc(A_114)
      | v2_struct_0(A_114) ) ),
    inference(resolution,[status(thm)],[c_788,c_20])).

tff(c_803,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_797])).

tff(c_807,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_803])).

tff(c_808,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_807])).

tff(c_811,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_808])).

tff(c_815,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_811])).

%------------------------------------------------------------------------------
