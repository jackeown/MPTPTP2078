%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1878+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:36 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   76 (  97 expanded)
%              Number of leaves         :   37 (  49 expanded)
%              Depth                    :   17
%              Number of atoms          :  150 ( 216 expanded)
%              Number of equality atoms :   16 (  21 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_121,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_101,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_105,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_76,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_89,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_48,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_71,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_48,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_20,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_50,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_42,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_46,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_109,plain,(
    ! [A_45] :
      ( v1_xboole_0(A_45)
      | r2_hidden('#skF_1'(A_45),A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_34,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(A_24,B_25)
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_116,plain,(
    ! [A_45] :
      ( m1_subset_1('#skF_1'(A_45),A_45)
      | v1_xboole_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_109,c_34])).

tff(c_38,plain,(
    ! [A_27,B_29] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_27),B_29),A_27)
      | ~ m1_subset_1(B_29,u1_struct_0(A_27))
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k6_domain_1(A_15,B_16),k1_zfmisc_1(A_15))
      | ~ m1_subset_1(B_16,A_15)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_56,plain,(
    ! [A_35] :
      ( k1_xboole_0 = A_35
      | ~ v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_68,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_56])).

tff(c_28,plain,(
    ! [A_20] : v1_xboole_0('#skF_3'(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_66,plain,(
    ! [A_20] : '#skF_3'(A_20) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_56])).

tff(c_87,plain,(
    ! [A_20] : '#skF_3'(A_20) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66])).

tff(c_30,plain,(
    ! [A_20] : m1_subset_1('#skF_3'(A_20),k1_zfmisc_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_104,plain,(
    ! [A_20] : m1_subset_1('#skF_5',k1_zfmisc_1(A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_30])).

tff(c_36,plain,(
    ! [A_26] : r1_tarski(k1_xboole_0,A_26) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_76,plain,(
    ! [A_26] : r1_tarski('#skF_5',A_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_36])).

tff(c_373,plain,(
    ! [C_81,B_82,A_83] :
      ( C_81 = B_82
      | ~ r1_tarski(B_82,C_81)
      | ~ v2_tex_2(C_81,A_83)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ v3_tex_2(B_82,A_83)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_375,plain,(
    ! [A_26,A_83] :
      ( A_26 = '#skF_5'
      | ~ v2_tex_2(A_26,A_83)
      | ~ m1_subset_1(A_26,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ v3_tex_2('#skF_5',A_83)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(resolution,[status(thm)],[c_76,c_373])).

tff(c_379,plain,(
    ! [A_84,A_85] :
      ( A_84 = '#skF_5'
      | ~ v2_tex_2(A_84,A_85)
      | ~ m1_subset_1(A_84,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ v3_tex_2('#skF_5',A_85)
      | ~ l1_pre_topc(A_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_375])).

tff(c_427,plain,(
    ! [A_88,B_89] :
      ( k6_domain_1(u1_struct_0(A_88),B_89) = '#skF_5'
      | ~ v2_tex_2(k6_domain_1(u1_struct_0(A_88),B_89),A_88)
      | ~ v3_tex_2('#skF_5',A_88)
      | ~ l1_pre_topc(A_88)
      | ~ m1_subset_1(B_89,u1_struct_0(A_88))
      | v1_xboole_0(u1_struct_0(A_88)) ) ),
    inference(resolution,[status(thm)],[c_18,c_379])).

tff(c_436,plain,(
    ! [A_90,B_91] :
      ( k6_domain_1(u1_struct_0(A_90),B_91) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_90)
      | v1_xboole_0(u1_struct_0(A_90))
      | ~ m1_subset_1(B_91,u1_struct_0(A_90))
      | ~ l1_pre_topc(A_90)
      | ~ v2_pre_topc(A_90)
      | v2_struct_0(A_90) ) ),
    inference(resolution,[status(thm)],[c_38,c_427])).

tff(c_457,plain,(
    ! [A_94] :
      ( k6_domain_1(u1_struct_0(A_94),'#skF_1'(u1_struct_0(A_94))) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_94)
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94)
      | v2_struct_0(A_94)
      | v1_xboole_0(u1_struct_0(A_94)) ) ),
    inference(resolution,[status(thm)],[c_116,c_436])).

tff(c_120,plain,(
    ! [A_48,B_49] :
      ( k6_domain_1(A_48,B_49) = k1_tarski(B_49)
      | ~ m1_subset_1(B_49,A_48)
      | v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_127,plain,(
    ! [A_45] :
      ( k6_domain_1(A_45,'#skF_1'(A_45)) = k1_tarski('#skF_1'(A_45))
      | v1_xboole_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_116,c_120])).

tff(c_488,plain,(
    ! [A_95] :
      ( k1_tarski('#skF_1'(u1_struct_0(A_95))) = '#skF_5'
      | v1_xboole_0(u1_struct_0(A_95))
      | ~ v3_tex_2('#skF_5',A_95)
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95)
      | v2_struct_0(A_95)
      | v1_xboole_0(u1_struct_0(A_95)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_457,c_127])).

tff(c_26,plain,(
    ! [A_19] : ~ v1_xboole_0(k1_tarski(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_505,plain,(
    ! [A_95] :
      ( ~ v1_xboole_0('#skF_5')
      | v1_xboole_0(u1_struct_0(A_95))
      | ~ v3_tex_2('#skF_5',A_95)
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95)
      | v2_struct_0(A_95)
      | v1_xboole_0(u1_struct_0(A_95)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_488,c_26])).

tff(c_514,plain,(
    ! [A_96] :
      ( ~ v3_tex_2('#skF_5',A_96)
      | ~ l1_pre_topc(A_96)
      | ~ v2_pre_topc(A_96)
      | v2_struct_0(A_96)
      | v1_xboole_0(u1_struct_0(A_96)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_505])).

tff(c_24,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(u1_struct_0(A_18))
      | ~ l1_struct_0(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_523,plain,(
    ! [A_97] :
      ( ~ l1_struct_0(A_97)
      | ~ v3_tex_2('#skF_5',A_97)
      | ~ l1_pre_topc(A_97)
      | ~ v2_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(resolution,[status(thm)],[c_514,c_24])).

tff(c_529,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_523])).

tff(c_533,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_529])).

tff(c_534,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_533])).

tff(c_537,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_534])).

tff(c_541,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_537])).

%------------------------------------------------------------------------------
