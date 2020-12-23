%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:00 EST 2020

% Result     : Theorem 4.27s
% Output     : CNFRefutation 4.27s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 115 expanded)
%              Number of leaves         :   41 (  56 expanded)
%              Depth                    :   18
%              Number of atoms          :  202 ( 302 expanded)
%              Number of equality atoms :   21 (  30 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff(f_139,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_42,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v3_pre_topc(B,A)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_tops_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_123,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_111,axiom,(
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

tff(f_76,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_54,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_18,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_56,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_48,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_52,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_69,plain,(
    ! [A_38] :
      ( k1_xboole_0 = A_38
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_73,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_52,c_69])).

tff(c_8,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_75,plain,(
    ! [A_6] : k2_xboole_0(A_6,'#skF_5') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_8])).

tff(c_12,plain,(
    ! [A_8,B_9] : k2_xboole_0(k1_tarski(A_8),B_9) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_102,plain,(
    ! [A_44,B_45] : k2_xboole_0(k1_tarski(A_44),B_45) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_12])).

tff(c_106,plain,(
    ! [A_44] : k1_tarski(A_44) != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_102])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_160,plain,(
    ! [A_65] :
      ( m1_subset_1('#skF_2'(A_65),k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_16,plain,(
    ! [A_11,C_13,B_12] :
      ( m1_subset_1(A_11,C_13)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(C_13))
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_210,plain,(
    ! [A_75,A_76] :
      ( m1_subset_1(A_75,u1_struct_0(A_76))
      | ~ r2_hidden(A_75,'#skF_2'(A_76))
      | ~ l1_pre_topc(A_76)
      | ~ v2_pre_topc(A_76)
      | v2_struct_0(A_76) ) ),
    inference(resolution,[status(thm)],[c_160,c_16])).

tff(c_215,plain,(
    ! [A_76] :
      ( m1_subset_1('#skF_1'('#skF_2'(A_76)),u1_struct_0(A_76))
      | ~ l1_pre_topc(A_76)
      | ~ v2_pre_topc(A_76)
      | v2_struct_0(A_76)
      | v1_xboole_0('#skF_2'(A_76)) ) ),
    inference(resolution,[status(thm)],[c_4,c_210])).

tff(c_46,plain,(
    ! [A_32,B_34] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_32),B_34),A_32)
      | ~ m1_subset_1(B_34,u1_struct_0(A_32))
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_22,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k6_domain_1(A_16,B_17),k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_17,A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_14,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_83,plain,(
    ! [A_10] : m1_subset_1('#skF_5',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_14])).

tff(c_10,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_76,plain,(
    ! [A_7] : r1_tarski('#skF_5',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_10])).

tff(c_504,plain,(
    ! [C_105,B_106,A_107] :
      ( C_105 = B_106
      | ~ r1_tarski(B_106,C_105)
      | ~ v2_tex_2(C_105,A_107)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ v3_tex_2(B_106,A_107)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_506,plain,(
    ! [A_7,A_107] :
      ( A_7 = '#skF_5'
      | ~ v2_tex_2(A_7,A_107)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ v3_tex_2('#skF_5',A_107)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(resolution,[status(thm)],[c_76,c_504])).

tff(c_510,plain,(
    ! [A_108,A_109] :
      ( A_108 = '#skF_5'
      | ~ v2_tex_2(A_108,A_109)
      | ~ m1_subset_1(A_108,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ v3_tex_2('#skF_5',A_109)
      | ~ l1_pre_topc(A_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_506])).

tff(c_724,plain,(
    ! [A_130,B_131] :
      ( k6_domain_1(u1_struct_0(A_130),B_131) = '#skF_5'
      | ~ v2_tex_2(k6_domain_1(u1_struct_0(A_130),B_131),A_130)
      | ~ v3_tex_2('#skF_5',A_130)
      | ~ l1_pre_topc(A_130)
      | ~ m1_subset_1(B_131,u1_struct_0(A_130))
      | v1_xboole_0(u1_struct_0(A_130)) ) ),
    inference(resolution,[status(thm)],[c_22,c_510])).

tff(c_736,plain,(
    ! [A_132,B_133] :
      ( k6_domain_1(u1_struct_0(A_132),B_133) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_132)
      | v1_xboole_0(u1_struct_0(A_132))
      | ~ m1_subset_1(B_133,u1_struct_0(A_132))
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132)
      | v2_struct_0(A_132) ) ),
    inference(resolution,[status(thm)],[c_46,c_724])).

tff(c_746,plain,(
    ! [A_134] :
      ( k6_domain_1(u1_struct_0(A_134),'#skF_1'('#skF_2'(A_134))) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_134)
      | v1_xboole_0(u1_struct_0(A_134))
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134)
      | v2_struct_0(A_134)
      | v1_xboole_0('#skF_2'(A_134)) ) ),
    inference(resolution,[status(thm)],[c_215,c_736])).

tff(c_242,plain,(
    ! [A_83] :
      ( m1_subset_1('#skF_1'('#skF_2'(A_83)),u1_struct_0(A_83))
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83)
      | v2_struct_0(A_83)
      | v1_xboole_0('#skF_2'(A_83)) ) ),
    inference(resolution,[status(thm)],[c_4,c_210])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( k6_domain_1(A_18,B_19) = k1_tarski(B_19)
      | ~ m1_subset_1(B_19,A_18)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_246,plain,(
    ! [A_83] :
      ( k6_domain_1(u1_struct_0(A_83),'#skF_1'('#skF_2'(A_83))) = k1_tarski('#skF_1'('#skF_2'(A_83)))
      | v1_xboole_0(u1_struct_0(A_83))
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83)
      | v2_struct_0(A_83)
      | v1_xboole_0('#skF_2'(A_83)) ) ),
    inference(resolution,[status(thm)],[c_242,c_24])).

tff(c_755,plain,(
    ! [A_134] :
      ( k1_tarski('#skF_1'('#skF_2'(A_134))) = '#skF_5'
      | v1_xboole_0(u1_struct_0(A_134))
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134)
      | v2_struct_0(A_134)
      | v1_xboole_0('#skF_2'(A_134))
      | ~ v3_tex_2('#skF_5',A_134)
      | v1_xboole_0(u1_struct_0(A_134))
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134)
      | v2_struct_0(A_134)
      | v1_xboole_0('#skF_2'(A_134)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_746,c_246])).

tff(c_784,plain,(
    ! [A_134] :
      ( v1_xboole_0(u1_struct_0(A_134))
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134)
      | v2_struct_0(A_134)
      | v1_xboole_0('#skF_2'(A_134))
      | ~ v3_tex_2('#skF_5',A_134)
      | v1_xboole_0(u1_struct_0(A_134))
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134)
      | v2_struct_0(A_134)
      | v1_xboole_0('#skF_2'(A_134)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_755])).

tff(c_1454,plain,(
    ! [A_177] :
      ( ~ v3_tex_2('#skF_5',A_177)
      | ~ l1_pre_topc(A_177)
      | ~ v2_pre_topc(A_177)
      | v2_struct_0(A_177)
      | v1_xboole_0('#skF_2'(A_177))
      | v1_xboole_0(u1_struct_0(A_177)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_784])).

tff(c_20,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0(u1_struct_0(A_15))
      | ~ l1_struct_0(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1463,plain,(
    ! [A_178] :
      ( ~ l1_struct_0(A_178)
      | ~ v3_tex_2('#skF_5',A_178)
      | ~ l1_pre_topc(A_178)
      | ~ v2_pre_topc(A_178)
      | v2_struct_0(A_178)
      | v1_xboole_0('#skF_2'(A_178)) ) ),
    inference(resolution,[status(thm)],[c_1454,c_20])).

tff(c_30,plain,(
    ! [A_20] :
      ( ~ v1_xboole_0('#skF_2'(A_20))
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1472,plain,(
    ! [A_179] :
      ( ~ l1_struct_0(A_179)
      | ~ v3_tex_2('#skF_5',A_179)
      | ~ l1_pre_topc(A_179)
      | ~ v2_pre_topc(A_179)
      | v2_struct_0(A_179) ) ),
    inference(resolution,[status(thm)],[c_1463,c_30])).

tff(c_1478,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_1472])).

tff(c_1482,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1478])).

tff(c_1483,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1482])).

tff(c_1498,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_1483])).

tff(c_1502,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1498])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:46:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.27/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.27/1.72  
% 4.27/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.27/1.73  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4
% 4.27/1.73  
% 4.27/1.73  %Foreground sorts:
% 4.27/1.73  
% 4.27/1.73  
% 4.27/1.73  %Background operators:
% 4.27/1.73  
% 4.27/1.73  
% 4.27/1.73  %Foreground operators:
% 4.27/1.73  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.27/1.73  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.27/1.73  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.27/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.27/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.27/1.73  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.27/1.73  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.27/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.27/1.73  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.27/1.73  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.27/1.73  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.27/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.27/1.73  tff('#skF_5', type, '#skF_5': $i).
% 4.27/1.73  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.27/1.73  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.27/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.27/1.73  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.27/1.73  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.27/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.27/1.73  tff('#skF_4', type, '#skF_4': $i).
% 4.27/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.27/1.73  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.27/1.73  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.27/1.73  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.27/1.73  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.27/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.27/1.73  
% 4.27/1.74  tff(f_139, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 4.27/1.74  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.27/1.74  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.27/1.74  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.27/1.74  tff(f_42, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 4.27/1.74  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.27/1.74  tff(f_93, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: (((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v3_pre_topc(B, A)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_tops_1)).
% 4.27/1.74  tff(f_50, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 4.27/1.74  tff(f_123, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 4.27/1.74  tff(f_69, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 4.27/1.74  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.27/1.74  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.27/1.74  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 4.27/1.74  tff(f_76, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.27/1.74  tff(f_62, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.27/1.74  tff(c_54, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.27/1.74  tff(c_18, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.27/1.74  tff(c_58, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.27/1.74  tff(c_56, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.27/1.74  tff(c_48, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.27/1.74  tff(c_52, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.27/1.74  tff(c_69, plain, (![A_38]: (k1_xboole_0=A_38 | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.27/1.74  tff(c_73, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_52, c_69])).
% 4.27/1.74  tff(c_8, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.27/1.74  tff(c_75, plain, (![A_6]: (k2_xboole_0(A_6, '#skF_5')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_73, c_8])).
% 4.27/1.74  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(k1_tarski(A_8), B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.27/1.74  tff(c_102, plain, (![A_44, B_45]: (k2_xboole_0(k1_tarski(A_44), B_45)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_12])).
% 4.27/1.74  tff(c_106, plain, (![A_44]: (k1_tarski(A_44)!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_75, c_102])).
% 4.27/1.74  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.27/1.74  tff(c_160, plain, (![A_65]: (m1_subset_1('#skF_2'(A_65), k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.27/1.74  tff(c_16, plain, (![A_11, C_13, B_12]: (m1_subset_1(A_11, C_13) | ~m1_subset_1(B_12, k1_zfmisc_1(C_13)) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.27/1.74  tff(c_210, plain, (![A_75, A_76]: (m1_subset_1(A_75, u1_struct_0(A_76)) | ~r2_hidden(A_75, '#skF_2'(A_76)) | ~l1_pre_topc(A_76) | ~v2_pre_topc(A_76) | v2_struct_0(A_76))), inference(resolution, [status(thm)], [c_160, c_16])).
% 4.27/1.74  tff(c_215, plain, (![A_76]: (m1_subset_1('#skF_1'('#skF_2'(A_76)), u1_struct_0(A_76)) | ~l1_pre_topc(A_76) | ~v2_pre_topc(A_76) | v2_struct_0(A_76) | v1_xboole_0('#skF_2'(A_76)))), inference(resolution, [status(thm)], [c_4, c_210])).
% 4.27/1.74  tff(c_46, plain, (![A_32, B_34]: (v2_tex_2(k6_domain_1(u1_struct_0(A_32), B_34), A_32) | ~m1_subset_1(B_34, u1_struct_0(A_32)) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.27/1.74  tff(c_22, plain, (![A_16, B_17]: (m1_subset_1(k6_domain_1(A_16, B_17), k1_zfmisc_1(A_16)) | ~m1_subset_1(B_17, A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.27/1.74  tff(c_14, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.27/1.74  tff(c_83, plain, (![A_10]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_14])).
% 4.27/1.74  tff(c_10, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.27/1.74  tff(c_76, plain, (![A_7]: (r1_tarski('#skF_5', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_10])).
% 4.27/1.74  tff(c_504, plain, (![C_105, B_106, A_107]: (C_105=B_106 | ~r1_tarski(B_106, C_105) | ~v2_tex_2(C_105, A_107) | ~m1_subset_1(C_105, k1_zfmisc_1(u1_struct_0(A_107))) | ~v3_tex_2(B_106, A_107) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.27/1.74  tff(c_506, plain, (![A_7, A_107]: (A_7='#skF_5' | ~v2_tex_2(A_7, A_107) | ~m1_subset_1(A_7, k1_zfmisc_1(u1_struct_0(A_107))) | ~v3_tex_2('#skF_5', A_107) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(resolution, [status(thm)], [c_76, c_504])).
% 4.27/1.74  tff(c_510, plain, (![A_108, A_109]: (A_108='#skF_5' | ~v2_tex_2(A_108, A_109) | ~m1_subset_1(A_108, k1_zfmisc_1(u1_struct_0(A_109))) | ~v3_tex_2('#skF_5', A_109) | ~l1_pre_topc(A_109))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_506])).
% 4.27/1.74  tff(c_724, plain, (![A_130, B_131]: (k6_domain_1(u1_struct_0(A_130), B_131)='#skF_5' | ~v2_tex_2(k6_domain_1(u1_struct_0(A_130), B_131), A_130) | ~v3_tex_2('#skF_5', A_130) | ~l1_pre_topc(A_130) | ~m1_subset_1(B_131, u1_struct_0(A_130)) | v1_xboole_0(u1_struct_0(A_130)))), inference(resolution, [status(thm)], [c_22, c_510])).
% 4.27/1.74  tff(c_736, plain, (![A_132, B_133]: (k6_domain_1(u1_struct_0(A_132), B_133)='#skF_5' | ~v3_tex_2('#skF_5', A_132) | v1_xboole_0(u1_struct_0(A_132)) | ~m1_subset_1(B_133, u1_struct_0(A_132)) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132) | v2_struct_0(A_132))), inference(resolution, [status(thm)], [c_46, c_724])).
% 4.27/1.74  tff(c_746, plain, (![A_134]: (k6_domain_1(u1_struct_0(A_134), '#skF_1'('#skF_2'(A_134)))='#skF_5' | ~v3_tex_2('#skF_5', A_134) | v1_xboole_0(u1_struct_0(A_134)) | ~l1_pre_topc(A_134) | ~v2_pre_topc(A_134) | v2_struct_0(A_134) | v1_xboole_0('#skF_2'(A_134)))), inference(resolution, [status(thm)], [c_215, c_736])).
% 4.27/1.74  tff(c_242, plain, (![A_83]: (m1_subset_1('#skF_1'('#skF_2'(A_83)), u1_struct_0(A_83)) | ~l1_pre_topc(A_83) | ~v2_pre_topc(A_83) | v2_struct_0(A_83) | v1_xboole_0('#skF_2'(A_83)))), inference(resolution, [status(thm)], [c_4, c_210])).
% 4.27/1.74  tff(c_24, plain, (![A_18, B_19]: (k6_domain_1(A_18, B_19)=k1_tarski(B_19) | ~m1_subset_1(B_19, A_18) | v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.27/1.74  tff(c_246, plain, (![A_83]: (k6_domain_1(u1_struct_0(A_83), '#skF_1'('#skF_2'(A_83)))=k1_tarski('#skF_1'('#skF_2'(A_83))) | v1_xboole_0(u1_struct_0(A_83)) | ~l1_pre_topc(A_83) | ~v2_pre_topc(A_83) | v2_struct_0(A_83) | v1_xboole_0('#skF_2'(A_83)))), inference(resolution, [status(thm)], [c_242, c_24])).
% 4.27/1.74  tff(c_755, plain, (![A_134]: (k1_tarski('#skF_1'('#skF_2'(A_134)))='#skF_5' | v1_xboole_0(u1_struct_0(A_134)) | ~l1_pre_topc(A_134) | ~v2_pre_topc(A_134) | v2_struct_0(A_134) | v1_xboole_0('#skF_2'(A_134)) | ~v3_tex_2('#skF_5', A_134) | v1_xboole_0(u1_struct_0(A_134)) | ~l1_pre_topc(A_134) | ~v2_pre_topc(A_134) | v2_struct_0(A_134) | v1_xboole_0('#skF_2'(A_134)))), inference(superposition, [status(thm), theory('equality')], [c_746, c_246])).
% 4.27/1.74  tff(c_784, plain, (![A_134]: (v1_xboole_0(u1_struct_0(A_134)) | ~l1_pre_topc(A_134) | ~v2_pre_topc(A_134) | v2_struct_0(A_134) | v1_xboole_0('#skF_2'(A_134)) | ~v3_tex_2('#skF_5', A_134) | v1_xboole_0(u1_struct_0(A_134)) | ~l1_pre_topc(A_134) | ~v2_pre_topc(A_134) | v2_struct_0(A_134) | v1_xboole_0('#skF_2'(A_134)))), inference(negUnitSimplification, [status(thm)], [c_106, c_755])).
% 4.27/1.74  tff(c_1454, plain, (![A_177]: (~v3_tex_2('#skF_5', A_177) | ~l1_pre_topc(A_177) | ~v2_pre_topc(A_177) | v2_struct_0(A_177) | v1_xboole_0('#skF_2'(A_177)) | v1_xboole_0(u1_struct_0(A_177)))), inference(factorization, [status(thm), theory('equality')], [c_784])).
% 4.27/1.74  tff(c_20, plain, (![A_15]: (~v1_xboole_0(u1_struct_0(A_15)) | ~l1_struct_0(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.27/1.74  tff(c_1463, plain, (![A_178]: (~l1_struct_0(A_178) | ~v3_tex_2('#skF_5', A_178) | ~l1_pre_topc(A_178) | ~v2_pre_topc(A_178) | v2_struct_0(A_178) | v1_xboole_0('#skF_2'(A_178)))), inference(resolution, [status(thm)], [c_1454, c_20])).
% 4.27/1.74  tff(c_30, plain, (![A_20]: (~v1_xboole_0('#skF_2'(A_20)) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.27/1.74  tff(c_1472, plain, (![A_179]: (~l1_struct_0(A_179) | ~v3_tex_2('#skF_5', A_179) | ~l1_pre_topc(A_179) | ~v2_pre_topc(A_179) | v2_struct_0(A_179))), inference(resolution, [status(thm)], [c_1463, c_30])).
% 4.27/1.74  tff(c_1478, plain, (~l1_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_1472])).
% 4.27/1.74  tff(c_1482, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1478])).
% 4.27/1.74  tff(c_1483, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_58, c_1482])).
% 4.27/1.74  tff(c_1498, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_18, c_1483])).
% 4.27/1.74  tff(c_1502, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_1498])).
% 4.27/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.27/1.74  
% 4.27/1.74  Inference rules
% 4.27/1.74  ----------------------
% 4.27/1.74  #Ref     : 0
% 4.27/1.74  #Sup     : 352
% 4.27/1.74  #Fact    : 2
% 4.27/1.74  #Define  : 0
% 4.27/1.74  #Split   : 4
% 4.27/1.74  #Chain   : 0
% 4.27/1.74  #Close   : 0
% 4.27/1.74  
% 4.27/1.74  Ordering : KBO
% 4.27/1.74  
% 4.27/1.74  Simplification rules
% 4.27/1.74  ----------------------
% 4.27/1.74  #Subsume      : 45
% 4.27/1.74  #Demod        : 93
% 4.27/1.74  #Tautology    : 74
% 4.27/1.74  #SimpNegUnit  : 10
% 4.27/1.74  #BackRed      : 11
% 4.27/1.74  
% 4.27/1.74  #Partial instantiations: 0
% 4.27/1.74  #Strategies tried      : 1
% 4.27/1.74  
% 4.27/1.74  Timing (in seconds)
% 4.27/1.74  ----------------------
% 4.27/1.75  Preprocessing        : 0.32
% 4.27/1.75  Parsing              : 0.17
% 4.27/1.75  CNF conversion       : 0.02
% 4.27/1.75  Main loop            : 0.66
% 4.27/1.75  Inferencing          : 0.24
% 4.27/1.75  Reduction            : 0.20
% 4.27/1.75  Demodulation         : 0.14
% 4.27/1.75  BG Simplification    : 0.03
% 4.27/1.75  Subsumption          : 0.15
% 4.27/1.75  Abstraction          : 0.03
% 4.27/1.75  MUC search           : 0.00
% 4.27/1.75  Cooper               : 0.00
% 4.27/1.75  Total                : 1.02
% 4.27/1.75  Index Insertion      : 0.00
% 4.27/1.75  Index Deletion       : 0.00
% 4.27/1.75  Index Matching       : 0.00
% 4.27/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
