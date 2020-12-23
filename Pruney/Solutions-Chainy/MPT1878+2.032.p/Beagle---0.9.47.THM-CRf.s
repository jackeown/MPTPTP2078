%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:01 EST 2020

% Result     : Theorem 7.56s
% Output     : CNFRefutation 7.56s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 155 expanded)
%              Number of leaves         :   40 (  70 expanded)
%              Depth                    :   19
%              Number of atoms          :  213 ( 430 expanded)
%              Number of equality atoms :   38 (  73 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k3_mcart_1 > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_144,negated_conjecture,(
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
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_38,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_128,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_116,axiom,(
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

tff(f_53,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_56,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_54,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_52,plain,(
    v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_48,plain,(
    v3_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_82,plain,(
    ! [A_59] :
      ( r2_hidden('#skF_2'(A_59),A_59)
      | k1_xboole_0 = A_59 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_87,plain,(
    ! [A_60] :
      ( ~ v1_xboole_0(A_60)
      | k1_xboole_0 = A_60 ) ),
    inference(resolution,[status(thm)],[c_82,c_2])).

tff(c_91,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_52,c_87])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_71,plain,(
    ! [A_55,B_56] : k2_xboole_0(k1_tarski(A_55),B_56) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_75,plain,(
    ! [A_55] : k1_tarski(A_55) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_71])).

tff(c_95,plain,(
    ! [A_55] : k1_tarski(A_55) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_75])).

tff(c_18,plain,(
    ! [A_16] :
      ( r2_hidden('#skF_2'(A_16),A_16)
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_94,plain,(
    ! [A_16] :
      ( r2_hidden('#skF_2'(A_16),A_16)
      | A_16 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_18])).

tff(c_213,plain,(
    ! [A_101] :
      ( m1_subset_1('#skF_3'(A_101),k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101)
      | ~ v2_pre_topc(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_14,plain,(
    ! [A_10,C_12,B_11] :
      ( m1_subset_1(A_10,C_12)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(C_12))
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_308,plain,(
    ! [A_121,A_122] :
      ( m1_subset_1(A_121,u1_struct_0(A_122))
      | ~ r2_hidden(A_121,'#skF_3'(A_122))
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122)
      | v2_struct_0(A_122) ) ),
    inference(resolution,[status(thm)],[c_213,c_14])).

tff(c_542,plain,(
    ! [A_147] :
      ( m1_subset_1('#skF_2'('#skF_3'(A_147)),u1_struct_0(A_147))
      | ~ l1_pre_topc(A_147)
      | ~ v2_pre_topc(A_147)
      | v2_struct_0(A_147)
      | '#skF_3'(A_147) = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_94,c_308])).

tff(c_32,plain,(
    ! [A_34,B_35] :
      ( k6_domain_1(A_34,B_35) = k1_tarski(B_35)
      | ~ m1_subset_1(B_35,A_34)
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_546,plain,(
    ! [A_147] :
      ( k6_domain_1(u1_struct_0(A_147),'#skF_2'('#skF_3'(A_147))) = k1_tarski('#skF_2'('#skF_3'(A_147)))
      | v1_xboole_0(u1_struct_0(A_147))
      | ~ l1_pre_topc(A_147)
      | ~ v2_pre_topc(A_147)
      | v2_struct_0(A_147)
      | '#skF_3'(A_147) = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_542,c_32])).

tff(c_317,plain,(
    ! [A_122] :
      ( m1_subset_1('#skF_2'('#skF_3'(A_122)),u1_struct_0(A_122))
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122)
      | v2_struct_0(A_122)
      | '#skF_3'(A_122) = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_94,c_308])).

tff(c_46,plain,(
    ! [A_46,B_48] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_46),B_48),A_46)
      | ~ m1_subset_1(B_48,u1_struct_0(A_46))
      | ~ l1_pre_topc(A_46)
      | ~ v2_pre_topc(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_30,plain,(
    ! [A_32,B_33] :
      ( m1_subset_1(k6_domain_1(A_32,B_33),k1_zfmisc_1(A_32))
      | ~ m1_subset_1(B_33,A_32)
      | v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_12,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_97,plain,(
    ! [A_9] : m1_subset_1('#skF_6',k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_12])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_99,plain,(
    ! [A_6] : r1_tarski('#skF_6',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_8])).

tff(c_465,plain,(
    ! [C_139,B_140,A_141] :
      ( C_139 = B_140
      | ~ r1_tarski(B_140,C_139)
      | ~ v2_tex_2(C_139,A_141)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ v3_tex_2(B_140,A_141)
      | ~ m1_subset_1(B_140,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_467,plain,(
    ! [A_6,A_141] :
      ( A_6 = '#skF_6'
      | ~ v2_tex_2(A_6,A_141)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ v3_tex_2('#skF_6',A_141)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141) ) ),
    inference(resolution,[status(thm)],[c_99,c_465])).

tff(c_547,plain,(
    ! [A_148,A_149] :
      ( A_148 = '#skF_6'
      | ~ v2_tex_2(A_148,A_149)
      | ~ m1_subset_1(A_148,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ v3_tex_2('#skF_6',A_149)
      | ~ l1_pre_topc(A_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_467])).

tff(c_1648,plain,(
    ! [A_220,B_221] :
      ( k6_domain_1(u1_struct_0(A_220),B_221) = '#skF_6'
      | ~ v2_tex_2(k6_domain_1(u1_struct_0(A_220),B_221),A_220)
      | ~ v3_tex_2('#skF_6',A_220)
      | ~ l1_pre_topc(A_220)
      | ~ m1_subset_1(B_221,u1_struct_0(A_220))
      | v1_xboole_0(u1_struct_0(A_220)) ) ),
    inference(resolution,[status(thm)],[c_30,c_547])).

tff(c_1667,plain,(
    ! [A_222,B_223] :
      ( k6_domain_1(u1_struct_0(A_222),B_223) = '#skF_6'
      | ~ v3_tex_2('#skF_6',A_222)
      | v1_xboole_0(u1_struct_0(A_222))
      | ~ m1_subset_1(B_223,u1_struct_0(A_222))
      | ~ l1_pre_topc(A_222)
      | ~ v2_pre_topc(A_222)
      | v2_struct_0(A_222) ) ),
    inference(resolution,[status(thm)],[c_46,c_1648])).

tff(c_1686,plain,(
    ! [A_224] :
      ( k6_domain_1(u1_struct_0(A_224),'#skF_2'('#skF_3'(A_224))) = '#skF_6'
      | ~ v3_tex_2('#skF_6',A_224)
      | v1_xboole_0(u1_struct_0(A_224))
      | ~ l1_pre_topc(A_224)
      | ~ v2_pre_topc(A_224)
      | v2_struct_0(A_224)
      | '#skF_3'(A_224) = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_317,c_1667])).

tff(c_1731,plain,(
    ! [A_147] :
      ( k1_tarski('#skF_2'('#skF_3'(A_147))) = '#skF_6'
      | ~ v3_tex_2('#skF_6',A_147)
      | v1_xboole_0(u1_struct_0(A_147))
      | ~ l1_pre_topc(A_147)
      | ~ v2_pre_topc(A_147)
      | v2_struct_0(A_147)
      | '#skF_3'(A_147) = '#skF_6'
      | v1_xboole_0(u1_struct_0(A_147))
      | ~ l1_pre_topc(A_147)
      | ~ v2_pre_topc(A_147)
      | v2_struct_0(A_147)
      | '#skF_3'(A_147) = '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_546,c_1686])).

tff(c_1736,plain,(
    ! [A_147] :
      ( ~ v3_tex_2('#skF_6',A_147)
      | v1_xboole_0(u1_struct_0(A_147))
      | ~ l1_pre_topc(A_147)
      | ~ v2_pre_topc(A_147)
      | v2_struct_0(A_147)
      | '#skF_3'(A_147) = '#skF_6'
      | v1_xboole_0(u1_struct_0(A_147))
      | ~ l1_pre_topc(A_147)
      | ~ v2_pre_topc(A_147)
      | v2_struct_0(A_147)
      | '#skF_3'(A_147) = '#skF_6' ) ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_1731])).

tff(c_4967,plain,(
    ! [A_362] :
      ( ~ v3_tex_2('#skF_6',A_362)
      | ~ l1_pre_topc(A_362)
      | ~ v2_pre_topc(A_362)
      | v2_struct_0(A_362)
      | '#skF_3'(A_362) = '#skF_6'
      | v1_xboole_0(u1_struct_0(A_362)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_1736])).

tff(c_16,plain,(
    ! [C_15,B_14,A_13] :
      ( ~ v1_xboole_0(C_15)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(C_15))
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_275,plain,(
    ! [A_114,A_115] :
      ( ~ v1_xboole_0(u1_struct_0(A_114))
      | ~ r2_hidden(A_115,'#skF_3'(A_114))
      | ~ l1_pre_topc(A_114)
      | ~ v2_pre_topc(A_114)
      | v2_struct_0(A_114) ) ),
    inference(resolution,[status(thm)],[c_213,c_16])).

tff(c_284,plain,(
    ! [A_114] :
      ( ~ v1_xboole_0(u1_struct_0(A_114))
      | ~ l1_pre_topc(A_114)
      | ~ v2_pre_topc(A_114)
      | v2_struct_0(A_114)
      | '#skF_3'(A_114) = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_94,c_275])).

tff(c_4988,plain,(
    ! [A_363] :
      ( ~ v3_tex_2('#skF_6',A_363)
      | ~ l1_pre_topc(A_363)
      | ~ v2_pre_topc(A_363)
      | v2_struct_0(A_363)
      | '#skF_3'(A_363) = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_4967,c_284])).

tff(c_4994,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | '#skF_3'('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_48,c_4988])).

tff(c_4998,plain,
    ( v2_struct_0('#skF_5')
    | '#skF_3'('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4994])).

tff(c_4999,plain,(
    '#skF_3'('#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4998])).

tff(c_26,plain,(
    ! [A_30] :
      ( ~ v1_xboole_0('#skF_3'(A_30))
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_5087,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4999,c_26])).

tff(c_5178,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_5087])).

tff(c_5180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_5178])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:51:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.56/2.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.56/2.62  
% 7.56/2.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.56/2.63  %$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k3_mcart_1 > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 7.56/2.63  
% 7.56/2.63  %Foreground sorts:
% 7.56/2.63  
% 7.56/2.63  
% 7.56/2.63  %Background operators:
% 7.56/2.63  
% 7.56/2.63  
% 7.56/2.63  %Foreground operators:
% 7.56/2.63  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.56/2.63  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.56/2.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.56/2.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.56/2.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.56/2.63  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.56/2.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.56/2.63  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 7.56/2.63  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.56/2.63  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 7.56/2.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.56/2.63  tff('#skF_5', type, '#skF_5': $i).
% 7.56/2.63  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 7.56/2.63  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 7.56/2.63  tff('#skF_6', type, '#skF_6': $i).
% 7.56/2.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.56/2.63  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 7.56/2.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.56/2.63  tff('#skF_3', type, '#skF_3': $i > $i).
% 7.56/2.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.56/2.63  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.56/2.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.56/2.63  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.56/2.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.56/2.63  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.56/2.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.56/2.63  
% 7.56/2.64  tff(f_144, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 7.56/2.64  tff(f_69, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 7.56/2.64  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.56/2.64  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 7.56/2.64  tff(f_38, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 7.56/2.64  tff(f_84, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc7_pre_topc)).
% 7.56/2.64  tff(f_46, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 7.56/2.64  tff(f_98, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 7.56/2.64  tff(f_128, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 7.56/2.64  tff(f_91, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 7.56/2.64  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 7.56/2.64  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.56/2.64  tff(f_116, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 7.56/2.64  tff(f_53, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 7.56/2.64  tff(c_58, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.56/2.64  tff(c_56, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.56/2.64  tff(c_54, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.56/2.64  tff(c_52, plain, (v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.56/2.64  tff(c_48, plain, (v3_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.56/2.64  tff(c_82, plain, (![A_59]: (r2_hidden('#skF_2'(A_59), A_59) | k1_xboole_0=A_59)), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.56/2.64  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.56/2.64  tff(c_87, plain, (![A_60]: (~v1_xboole_0(A_60) | k1_xboole_0=A_60)), inference(resolution, [status(thm)], [c_82, c_2])).
% 7.56/2.64  tff(c_91, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_52, c_87])).
% 7.56/2.64  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.56/2.64  tff(c_71, plain, (![A_55, B_56]: (k2_xboole_0(k1_tarski(A_55), B_56)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.56/2.64  tff(c_75, plain, (![A_55]: (k1_tarski(A_55)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_71])).
% 7.56/2.64  tff(c_95, plain, (![A_55]: (k1_tarski(A_55)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_75])).
% 7.56/2.64  tff(c_18, plain, (![A_16]: (r2_hidden('#skF_2'(A_16), A_16) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.56/2.64  tff(c_94, plain, (![A_16]: (r2_hidden('#skF_2'(A_16), A_16) | A_16='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_18])).
% 7.56/2.64  tff(c_213, plain, (![A_101]: (m1_subset_1('#skF_3'(A_101), k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101) | ~v2_pre_topc(A_101) | v2_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.56/2.64  tff(c_14, plain, (![A_10, C_12, B_11]: (m1_subset_1(A_10, C_12) | ~m1_subset_1(B_11, k1_zfmisc_1(C_12)) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.56/2.64  tff(c_308, plain, (![A_121, A_122]: (m1_subset_1(A_121, u1_struct_0(A_122)) | ~r2_hidden(A_121, '#skF_3'(A_122)) | ~l1_pre_topc(A_122) | ~v2_pre_topc(A_122) | v2_struct_0(A_122))), inference(resolution, [status(thm)], [c_213, c_14])).
% 7.56/2.64  tff(c_542, plain, (![A_147]: (m1_subset_1('#skF_2'('#skF_3'(A_147)), u1_struct_0(A_147)) | ~l1_pre_topc(A_147) | ~v2_pre_topc(A_147) | v2_struct_0(A_147) | '#skF_3'(A_147)='#skF_6')), inference(resolution, [status(thm)], [c_94, c_308])).
% 7.56/2.64  tff(c_32, plain, (![A_34, B_35]: (k6_domain_1(A_34, B_35)=k1_tarski(B_35) | ~m1_subset_1(B_35, A_34) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.56/2.64  tff(c_546, plain, (![A_147]: (k6_domain_1(u1_struct_0(A_147), '#skF_2'('#skF_3'(A_147)))=k1_tarski('#skF_2'('#skF_3'(A_147))) | v1_xboole_0(u1_struct_0(A_147)) | ~l1_pre_topc(A_147) | ~v2_pre_topc(A_147) | v2_struct_0(A_147) | '#skF_3'(A_147)='#skF_6')), inference(resolution, [status(thm)], [c_542, c_32])).
% 7.56/2.64  tff(c_317, plain, (![A_122]: (m1_subset_1('#skF_2'('#skF_3'(A_122)), u1_struct_0(A_122)) | ~l1_pre_topc(A_122) | ~v2_pre_topc(A_122) | v2_struct_0(A_122) | '#skF_3'(A_122)='#skF_6')), inference(resolution, [status(thm)], [c_94, c_308])).
% 7.56/2.64  tff(c_46, plain, (![A_46, B_48]: (v2_tex_2(k6_domain_1(u1_struct_0(A_46), B_48), A_46) | ~m1_subset_1(B_48, u1_struct_0(A_46)) | ~l1_pre_topc(A_46) | ~v2_pre_topc(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.56/2.64  tff(c_30, plain, (![A_32, B_33]: (m1_subset_1(k6_domain_1(A_32, B_33), k1_zfmisc_1(A_32)) | ~m1_subset_1(B_33, A_32) | v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.56/2.64  tff(c_12, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.56/2.64  tff(c_97, plain, (![A_9]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_12])).
% 7.56/2.64  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.56/2.64  tff(c_99, plain, (![A_6]: (r1_tarski('#skF_6', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_8])).
% 7.56/2.64  tff(c_465, plain, (![C_139, B_140, A_141]: (C_139=B_140 | ~r1_tarski(B_140, C_139) | ~v2_tex_2(C_139, A_141) | ~m1_subset_1(C_139, k1_zfmisc_1(u1_struct_0(A_141))) | ~v3_tex_2(B_140, A_141) | ~m1_subset_1(B_140, k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_pre_topc(A_141))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.56/2.64  tff(c_467, plain, (![A_6, A_141]: (A_6='#skF_6' | ~v2_tex_2(A_6, A_141) | ~m1_subset_1(A_6, k1_zfmisc_1(u1_struct_0(A_141))) | ~v3_tex_2('#skF_6', A_141) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_pre_topc(A_141))), inference(resolution, [status(thm)], [c_99, c_465])).
% 7.56/2.64  tff(c_547, plain, (![A_148, A_149]: (A_148='#skF_6' | ~v2_tex_2(A_148, A_149) | ~m1_subset_1(A_148, k1_zfmisc_1(u1_struct_0(A_149))) | ~v3_tex_2('#skF_6', A_149) | ~l1_pre_topc(A_149))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_467])).
% 7.56/2.64  tff(c_1648, plain, (![A_220, B_221]: (k6_domain_1(u1_struct_0(A_220), B_221)='#skF_6' | ~v2_tex_2(k6_domain_1(u1_struct_0(A_220), B_221), A_220) | ~v3_tex_2('#skF_6', A_220) | ~l1_pre_topc(A_220) | ~m1_subset_1(B_221, u1_struct_0(A_220)) | v1_xboole_0(u1_struct_0(A_220)))), inference(resolution, [status(thm)], [c_30, c_547])).
% 7.56/2.64  tff(c_1667, plain, (![A_222, B_223]: (k6_domain_1(u1_struct_0(A_222), B_223)='#skF_6' | ~v3_tex_2('#skF_6', A_222) | v1_xboole_0(u1_struct_0(A_222)) | ~m1_subset_1(B_223, u1_struct_0(A_222)) | ~l1_pre_topc(A_222) | ~v2_pre_topc(A_222) | v2_struct_0(A_222))), inference(resolution, [status(thm)], [c_46, c_1648])).
% 7.56/2.64  tff(c_1686, plain, (![A_224]: (k6_domain_1(u1_struct_0(A_224), '#skF_2'('#skF_3'(A_224)))='#skF_6' | ~v3_tex_2('#skF_6', A_224) | v1_xboole_0(u1_struct_0(A_224)) | ~l1_pre_topc(A_224) | ~v2_pre_topc(A_224) | v2_struct_0(A_224) | '#skF_3'(A_224)='#skF_6')), inference(resolution, [status(thm)], [c_317, c_1667])).
% 7.56/2.64  tff(c_1731, plain, (![A_147]: (k1_tarski('#skF_2'('#skF_3'(A_147)))='#skF_6' | ~v3_tex_2('#skF_6', A_147) | v1_xboole_0(u1_struct_0(A_147)) | ~l1_pre_topc(A_147) | ~v2_pre_topc(A_147) | v2_struct_0(A_147) | '#skF_3'(A_147)='#skF_6' | v1_xboole_0(u1_struct_0(A_147)) | ~l1_pre_topc(A_147) | ~v2_pre_topc(A_147) | v2_struct_0(A_147) | '#skF_3'(A_147)='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_546, c_1686])).
% 7.56/2.64  tff(c_1736, plain, (![A_147]: (~v3_tex_2('#skF_6', A_147) | v1_xboole_0(u1_struct_0(A_147)) | ~l1_pre_topc(A_147) | ~v2_pre_topc(A_147) | v2_struct_0(A_147) | '#skF_3'(A_147)='#skF_6' | v1_xboole_0(u1_struct_0(A_147)) | ~l1_pre_topc(A_147) | ~v2_pre_topc(A_147) | v2_struct_0(A_147) | '#skF_3'(A_147)='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_95, c_1731])).
% 7.56/2.64  tff(c_4967, plain, (![A_362]: (~v3_tex_2('#skF_6', A_362) | ~l1_pre_topc(A_362) | ~v2_pre_topc(A_362) | v2_struct_0(A_362) | '#skF_3'(A_362)='#skF_6' | v1_xboole_0(u1_struct_0(A_362)))), inference(factorization, [status(thm), theory('equality')], [c_1736])).
% 7.56/2.64  tff(c_16, plain, (![C_15, B_14, A_13]: (~v1_xboole_0(C_15) | ~m1_subset_1(B_14, k1_zfmisc_1(C_15)) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.56/2.64  tff(c_275, plain, (![A_114, A_115]: (~v1_xboole_0(u1_struct_0(A_114)) | ~r2_hidden(A_115, '#skF_3'(A_114)) | ~l1_pre_topc(A_114) | ~v2_pre_topc(A_114) | v2_struct_0(A_114))), inference(resolution, [status(thm)], [c_213, c_16])).
% 7.56/2.64  tff(c_284, plain, (![A_114]: (~v1_xboole_0(u1_struct_0(A_114)) | ~l1_pre_topc(A_114) | ~v2_pre_topc(A_114) | v2_struct_0(A_114) | '#skF_3'(A_114)='#skF_6')), inference(resolution, [status(thm)], [c_94, c_275])).
% 7.56/2.64  tff(c_4988, plain, (![A_363]: (~v3_tex_2('#skF_6', A_363) | ~l1_pre_topc(A_363) | ~v2_pre_topc(A_363) | v2_struct_0(A_363) | '#skF_3'(A_363)='#skF_6')), inference(resolution, [status(thm)], [c_4967, c_284])).
% 7.56/2.64  tff(c_4994, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | '#skF_3'('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_48, c_4988])).
% 7.56/2.64  tff(c_4998, plain, (v2_struct_0('#skF_5') | '#skF_3'('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_4994])).
% 7.56/2.64  tff(c_4999, plain, ('#skF_3'('#skF_5')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_58, c_4998])).
% 7.56/2.64  tff(c_26, plain, (![A_30]: (~v1_xboole_0('#skF_3'(A_30)) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.56/2.64  tff(c_5087, plain, (~v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4999, c_26])).
% 7.56/2.64  tff(c_5178, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_5087])).
% 7.56/2.64  tff(c_5180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_5178])).
% 7.56/2.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.56/2.64  
% 7.56/2.64  Inference rules
% 7.56/2.64  ----------------------
% 7.56/2.64  #Ref     : 0
% 7.56/2.64  #Sup     : 1298
% 7.56/2.64  #Fact    : 2
% 7.56/2.64  #Define  : 0
% 7.56/2.64  #Split   : 5
% 7.56/2.64  #Chain   : 0
% 7.56/2.64  #Close   : 0
% 7.56/2.64  
% 7.56/2.64  Ordering : KBO
% 7.56/2.64  
% 7.56/2.64  Simplification rules
% 7.56/2.64  ----------------------
% 7.56/2.64  #Subsume      : 257
% 7.56/2.64  #Demod        : 494
% 7.56/2.64  #Tautology    : 296
% 7.56/2.64  #SimpNegUnit  : 70
% 7.56/2.64  #BackRed      : 18
% 7.56/2.64  
% 7.56/2.64  #Partial instantiations: 0
% 7.56/2.64  #Strategies tried      : 1
% 7.56/2.64  
% 7.56/2.64  Timing (in seconds)
% 7.56/2.64  ----------------------
% 7.56/2.65  Preprocessing        : 0.34
% 7.56/2.65  Parsing              : 0.19
% 7.56/2.65  CNF conversion       : 0.02
% 7.56/2.65  Main loop            : 1.53
% 7.56/2.65  Inferencing          : 0.48
% 7.56/2.65  Reduction            : 0.46
% 7.56/2.65  Demodulation         : 0.30
% 7.56/2.65  BG Simplification    : 0.06
% 7.56/2.65  Subsumption          : 0.43
% 7.56/2.65  Abstraction          : 0.07
% 7.56/2.65  MUC search           : 0.00
% 7.56/2.65  Cooper               : 0.00
% 7.56/2.65  Total                : 1.91
% 7.56/2.65  Index Insertion      : 0.00
% 7.56/2.65  Index Deletion       : 0.00
% 7.56/2.65  Index Matching       : 0.00
% 7.80/2.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
