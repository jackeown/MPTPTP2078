%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:00 EST 2020

% Result     : Theorem 4.43s
% Output     : CNFRefutation 4.60s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 114 expanded)
%              Number of leaves         :   40 (  55 expanded)
%              Depth                    :   18
%              Number of atoms          :  201 ( 299 expanded)
%              Number of equality atoms :   21 (  30 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4

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

tff(f_137,negated_conjecture,(
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

tff(f_77,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_121,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_84,axiom,(
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

tff(f_109,axiom,(
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

tff(f_91,axiom,(
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

tff(c_52,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_18,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_54,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_46,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_50,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_58,plain,(
    ! [A_37] :
      ( k1_xboole_0 = A_37
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_62,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_58])).

tff(c_8,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_70,plain,(
    ! [A_6] : k2_xboole_0(A_6,'#skF_5') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_8])).

tff(c_12,plain,(
    ! [A_8,B_9] : k2_xboole_0(k1_tarski(A_8),B_9) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_92,plain,(
    ! [A_45,B_46] : k2_xboole_0(k1_tarski(A_45),B_46) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_12])).

tff(c_96,plain,(
    ! [A_45] : k1_tarski(A_45) != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_92])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_148,plain,(
    ! [A_63] :
      ( m1_subset_1('#skF_2'(A_63),k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_16,plain,(
    ! [A_11,C_13,B_12] :
      ( m1_subset_1(A_11,C_13)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(C_13))
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_197,plain,(
    ! [A_71,A_72] :
      ( m1_subset_1(A_71,u1_struct_0(A_72))
      | ~ r2_hidden(A_71,'#skF_2'(A_72))
      | ~ l1_pre_topc(A_72)
      | ~ v2_pre_topc(A_72)
      | v2_struct_0(A_72) ) ),
    inference(resolution,[status(thm)],[c_148,c_16])).

tff(c_202,plain,(
    ! [A_72] :
      ( m1_subset_1('#skF_1'('#skF_2'(A_72)),u1_struct_0(A_72))
      | ~ l1_pre_topc(A_72)
      | ~ v2_pre_topc(A_72)
      | v2_struct_0(A_72)
      | v1_xboole_0('#skF_2'(A_72)) ) ),
    inference(resolution,[status(thm)],[c_4,c_197])).

tff(c_44,plain,(
    ! [A_32,B_34] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_32),B_34),A_32)
      | ~ m1_subset_1(B_34,u1_struct_0(A_32))
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_28,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k6_domain_1(A_18,B_19),k1_zfmisc_1(A_18))
      | ~ m1_subset_1(B_19,A_18)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_14,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_81,plain,(
    ! [A_10] : m1_subset_1('#skF_5',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_14])).

tff(c_10,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_64,plain,(
    ! [A_7] : r1_tarski('#skF_5',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_10])).

tff(c_452,plain,(
    ! [C_98,B_99,A_100] :
      ( C_98 = B_99
      | ~ r1_tarski(B_99,C_98)
      | ~ v2_tex_2(C_98,A_100)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ v3_tex_2(B_99,A_100)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_454,plain,(
    ! [A_7,A_100] :
      ( A_7 = '#skF_5'
      | ~ v2_tex_2(A_7,A_100)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ v3_tex_2('#skF_5',A_100)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(resolution,[status(thm)],[c_64,c_452])).

tff(c_458,plain,(
    ! [A_101,A_102] :
      ( A_101 = '#skF_5'
      | ~ v2_tex_2(A_101,A_102)
      | ~ m1_subset_1(A_101,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ v3_tex_2('#skF_5',A_102)
      | ~ l1_pre_topc(A_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_454])).

tff(c_726,plain,(
    ! [A_128,B_129] :
      ( k6_domain_1(u1_struct_0(A_128),B_129) = '#skF_5'
      | ~ v2_tex_2(k6_domain_1(u1_struct_0(A_128),B_129),A_128)
      | ~ v3_tex_2('#skF_5',A_128)
      | ~ l1_pre_topc(A_128)
      | ~ m1_subset_1(B_129,u1_struct_0(A_128))
      | v1_xboole_0(u1_struct_0(A_128)) ) ),
    inference(resolution,[status(thm)],[c_28,c_458])).

tff(c_738,plain,(
    ! [A_130,B_131] :
      ( k6_domain_1(u1_struct_0(A_130),B_131) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_130)
      | v1_xboole_0(u1_struct_0(A_130))
      | ~ m1_subset_1(B_131,u1_struct_0(A_130))
      | ~ l1_pre_topc(A_130)
      | ~ v2_pre_topc(A_130)
      | v2_struct_0(A_130) ) ),
    inference(resolution,[status(thm)],[c_44,c_726])).

tff(c_748,plain,(
    ! [A_132] :
      ( k6_domain_1(u1_struct_0(A_132),'#skF_1'('#skF_2'(A_132))) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_132)
      | v1_xboole_0(u1_struct_0(A_132))
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132)
      | v2_struct_0(A_132)
      | v1_xboole_0('#skF_2'(A_132)) ) ),
    inference(resolution,[status(thm)],[c_202,c_738])).

tff(c_254,plain,(
    ! [A_83] :
      ( m1_subset_1('#skF_1'('#skF_2'(A_83)),u1_struct_0(A_83))
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83)
      | v2_struct_0(A_83)
      | v1_xboole_0('#skF_2'(A_83)) ) ),
    inference(resolution,[status(thm)],[c_4,c_197])).

tff(c_30,plain,(
    ! [A_20,B_21] :
      ( k6_domain_1(A_20,B_21) = k1_tarski(B_21)
      | ~ m1_subset_1(B_21,A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_258,plain,(
    ! [A_83] :
      ( k6_domain_1(u1_struct_0(A_83),'#skF_1'('#skF_2'(A_83))) = k1_tarski('#skF_1'('#skF_2'(A_83)))
      | v1_xboole_0(u1_struct_0(A_83))
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83)
      | v2_struct_0(A_83)
      | v1_xboole_0('#skF_2'(A_83)) ) ),
    inference(resolution,[status(thm)],[c_254,c_30])).

tff(c_757,plain,(
    ! [A_132] :
      ( k1_tarski('#skF_1'('#skF_2'(A_132))) = '#skF_5'
      | v1_xboole_0(u1_struct_0(A_132))
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132)
      | v2_struct_0(A_132)
      | v1_xboole_0('#skF_2'(A_132))
      | ~ v3_tex_2('#skF_5',A_132)
      | v1_xboole_0(u1_struct_0(A_132))
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132)
      | v2_struct_0(A_132)
      | v1_xboole_0('#skF_2'(A_132)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_748,c_258])).

tff(c_786,plain,(
    ! [A_132] :
      ( v1_xboole_0(u1_struct_0(A_132))
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132)
      | v2_struct_0(A_132)
      | v1_xboole_0('#skF_2'(A_132))
      | ~ v3_tex_2('#skF_5',A_132)
      | v1_xboole_0(u1_struct_0(A_132))
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132)
      | v2_struct_0(A_132)
      | v1_xboole_0('#skF_2'(A_132)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_757])).

tff(c_1487,plain,(
    ! [A_176] :
      ( ~ v3_tex_2('#skF_5',A_176)
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176)
      | v2_struct_0(A_176)
      | v1_xboole_0('#skF_2'(A_176))
      | v1_xboole_0(u1_struct_0(A_176)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_786])).

tff(c_20,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0(u1_struct_0(A_15))
      | ~ l1_struct_0(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1496,plain,(
    ! [A_177] :
      ( ~ l1_struct_0(A_177)
      | ~ v3_tex_2('#skF_5',A_177)
      | ~ l1_pre_topc(A_177)
      | ~ v2_pre_topc(A_177)
      | v2_struct_0(A_177)
      | v1_xboole_0('#skF_2'(A_177)) ) ),
    inference(resolution,[status(thm)],[c_1487,c_20])).

tff(c_24,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0('#skF_2'(A_16))
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1505,plain,(
    ! [A_178] :
      ( ~ l1_struct_0(A_178)
      | ~ v3_tex_2('#skF_5',A_178)
      | ~ l1_pre_topc(A_178)
      | ~ v2_pre_topc(A_178)
      | v2_struct_0(A_178) ) ),
    inference(resolution,[status(thm)],[c_1496,c_24])).

tff(c_1511,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_1505])).

tff(c_1515,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1511])).

tff(c_1516,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1515])).

tff(c_1519,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_1516])).

tff(c_1523,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1519])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:32:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.43/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.60/1.83  
% 4.60/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.60/1.84  %$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4
% 4.60/1.84  
% 4.60/1.84  %Foreground sorts:
% 4.60/1.84  
% 4.60/1.84  
% 4.60/1.84  %Background operators:
% 4.60/1.84  
% 4.60/1.84  
% 4.60/1.84  %Foreground operators:
% 4.60/1.84  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.60/1.84  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.60/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.60/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.60/1.84  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.60/1.84  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.60/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.60/1.84  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.60/1.84  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.60/1.84  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.60/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.60/1.84  tff('#skF_5', type, '#skF_5': $i).
% 4.60/1.84  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.60/1.84  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.60/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.60/1.84  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.60/1.84  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.60/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.60/1.84  tff('#skF_4', type, '#skF_4': $i).
% 4.60/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.60/1.84  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.60/1.84  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.60/1.84  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.60/1.84  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.60/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.60/1.84  
% 4.60/1.85  tff(f_137, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 4.60/1.85  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.60/1.85  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.60/1.85  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.60/1.85  tff(f_42, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 4.60/1.85  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.60/1.85  tff(f_77, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc7_pre_topc)).
% 4.60/1.85  tff(f_50, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 4.60/1.85  tff(f_121, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 4.60/1.85  tff(f_84, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 4.60/1.85  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.60/1.85  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.60/1.85  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 4.60/1.85  tff(f_91, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.60/1.85  tff(f_62, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.60/1.85  tff(c_52, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.60/1.85  tff(c_18, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.60/1.85  tff(c_56, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.60/1.85  tff(c_54, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.60/1.85  tff(c_46, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.60/1.85  tff(c_50, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.60/1.85  tff(c_58, plain, (![A_37]: (k1_xboole_0=A_37 | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.60/1.85  tff(c_62, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_50, c_58])).
% 4.60/1.85  tff(c_8, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.60/1.85  tff(c_70, plain, (![A_6]: (k2_xboole_0(A_6, '#skF_5')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_8])).
% 4.60/1.85  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(k1_tarski(A_8), B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.60/1.85  tff(c_92, plain, (![A_45, B_46]: (k2_xboole_0(k1_tarski(A_45), B_46)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_12])).
% 4.60/1.85  tff(c_96, plain, (![A_45]: (k1_tarski(A_45)!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_70, c_92])).
% 4.60/1.85  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.60/1.85  tff(c_148, plain, (![A_63]: (m1_subset_1('#skF_2'(A_63), k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.60/1.85  tff(c_16, plain, (![A_11, C_13, B_12]: (m1_subset_1(A_11, C_13) | ~m1_subset_1(B_12, k1_zfmisc_1(C_13)) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.60/1.85  tff(c_197, plain, (![A_71, A_72]: (m1_subset_1(A_71, u1_struct_0(A_72)) | ~r2_hidden(A_71, '#skF_2'(A_72)) | ~l1_pre_topc(A_72) | ~v2_pre_topc(A_72) | v2_struct_0(A_72))), inference(resolution, [status(thm)], [c_148, c_16])).
% 4.60/1.85  tff(c_202, plain, (![A_72]: (m1_subset_1('#skF_1'('#skF_2'(A_72)), u1_struct_0(A_72)) | ~l1_pre_topc(A_72) | ~v2_pre_topc(A_72) | v2_struct_0(A_72) | v1_xboole_0('#skF_2'(A_72)))), inference(resolution, [status(thm)], [c_4, c_197])).
% 4.60/1.85  tff(c_44, plain, (![A_32, B_34]: (v2_tex_2(k6_domain_1(u1_struct_0(A_32), B_34), A_32) | ~m1_subset_1(B_34, u1_struct_0(A_32)) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.60/1.85  tff(c_28, plain, (![A_18, B_19]: (m1_subset_1(k6_domain_1(A_18, B_19), k1_zfmisc_1(A_18)) | ~m1_subset_1(B_19, A_18) | v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.60/1.85  tff(c_14, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.60/1.85  tff(c_81, plain, (![A_10]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_14])).
% 4.60/1.85  tff(c_10, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.60/1.85  tff(c_64, plain, (![A_7]: (r1_tarski('#skF_5', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_10])).
% 4.60/1.85  tff(c_452, plain, (![C_98, B_99, A_100]: (C_98=B_99 | ~r1_tarski(B_99, C_98) | ~v2_tex_2(C_98, A_100) | ~m1_subset_1(C_98, k1_zfmisc_1(u1_struct_0(A_100))) | ~v3_tex_2(B_99, A_100) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.60/1.85  tff(c_454, plain, (![A_7, A_100]: (A_7='#skF_5' | ~v2_tex_2(A_7, A_100) | ~m1_subset_1(A_7, k1_zfmisc_1(u1_struct_0(A_100))) | ~v3_tex_2('#skF_5', A_100) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(resolution, [status(thm)], [c_64, c_452])).
% 4.60/1.85  tff(c_458, plain, (![A_101, A_102]: (A_101='#skF_5' | ~v2_tex_2(A_101, A_102) | ~m1_subset_1(A_101, k1_zfmisc_1(u1_struct_0(A_102))) | ~v3_tex_2('#skF_5', A_102) | ~l1_pre_topc(A_102))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_454])).
% 4.60/1.85  tff(c_726, plain, (![A_128, B_129]: (k6_domain_1(u1_struct_0(A_128), B_129)='#skF_5' | ~v2_tex_2(k6_domain_1(u1_struct_0(A_128), B_129), A_128) | ~v3_tex_2('#skF_5', A_128) | ~l1_pre_topc(A_128) | ~m1_subset_1(B_129, u1_struct_0(A_128)) | v1_xboole_0(u1_struct_0(A_128)))), inference(resolution, [status(thm)], [c_28, c_458])).
% 4.60/1.85  tff(c_738, plain, (![A_130, B_131]: (k6_domain_1(u1_struct_0(A_130), B_131)='#skF_5' | ~v3_tex_2('#skF_5', A_130) | v1_xboole_0(u1_struct_0(A_130)) | ~m1_subset_1(B_131, u1_struct_0(A_130)) | ~l1_pre_topc(A_130) | ~v2_pre_topc(A_130) | v2_struct_0(A_130))), inference(resolution, [status(thm)], [c_44, c_726])).
% 4.60/1.85  tff(c_748, plain, (![A_132]: (k6_domain_1(u1_struct_0(A_132), '#skF_1'('#skF_2'(A_132)))='#skF_5' | ~v3_tex_2('#skF_5', A_132) | v1_xboole_0(u1_struct_0(A_132)) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132) | v2_struct_0(A_132) | v1_xboole_0('#skF_2'(A_132)))), inference(resolution, [status(thm)], [c_202, c_738])).
% 4.60/1.85  tff(c_254, plain, (![A_83]: (m1_subset_1('#skF_1'('#skF_2'(A_83)), u1_struct_0(A_83)) | ~l1_pre_topc(A_83) | ~v2_pre_topc(A_83) | v2_struct_0(A_83) | v1_xboole_0('#skF_2'(A_83)))), inference(resolution, [status(thm)], [c_4, c_197])).
% 4.60/1.85  tff(c_30, plain, (![A_20, B_21]: (k6_domain_1(A_20, B_21)=k1_tarski(B_21) | ~m1_subset_1(B_21, A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.60/1.85  tff(c_258, plain, (![A_83]: (k6_domain_1(u1_struct_0(A_83), '#skF_1'('#skF_2'(A_83)))=k1_tarski('#skF_1'('#skF_2'(A_83))) | v1_xboole_0(u1_struct_0(A_83)) | ~l1_pre_topc(A_83) | ~v2_pre_topc(A_83) | v2_struct_0(A_83) | v1_xboole_0('#skF_2'(A_83)))), inference(resolution, [status(thm)], [c_254, c_30])).
% 4.60/1.85  tff(c_757, plain, (![A_132]: (k1_tarski('#skF_1'('#skF_2'(A_132)))='#skF_5' | v1_xboole_0(u1_struct_0(A_132)) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132) | v2_struct_0(A_132) | v1_xboole_0('#skF_2'(A_132)) | ~v3_tex_2('#skF_5', A_132) | v1_xboole_0(u1_struct_0(A_132)) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132) | v2_struct_0(A_132) | v1_xboole_0('#skF_2'(A_132)))), inference(superposition, [status(thm), theory('equality')], [c_748, c_258])).
% 4.60/1.85  tff(c_786, plain, (![A_132]: (v1_xboole_0(u1_struct_0(A_132)) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132) | v2_struct_0(A_132) | v1_xboole_0('#skF_2'(A_132)) | ~v3_tex_2('#skF_5', A_132) | v1_xboole_0(u1_struct_0(A_132)) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132) | v2_struct_0(A_132) | v1_xboole_0('#skF_2'(A_132)))), inference(negUnitSimplification, [status(thm)], [c_96, c_757])).
% 4.60/1.85  tff(c_1487, plain, (![A_176]: (~v3_tex_2('#skF_5', A_176) | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176) | v2_struct_0(A_176) | v1_xboole_0('#skF_2'(A_176)) | v1_xboole_0(u1_struct_0(A_176)))), inference(factorization, [status(thm), theory('equality')], [c_786])).
% 4.60/1.85  tff(c_20, plain, (![A_15]: (~v1_xboole_0(u1_struct_0(A_15)) | ~l1_struct_0(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.60/1.85  tff(c_1496, plain, (![A_177]: (~l1_struct_0(A_177) | ~v3_tex_2('#skF_5', A_177) | ~l1_pre_topc(A_177) | ~v2_pre_topc(A_177) | v2_struct_0(A_177) | v1_xboole_0('#skF_2'(A_177)))), inference(resolution, [status(thm)], [c_1487, c_20])).
% 4.60/1.85  tff(c_24, plain, (![A_16]: (~v1_xboole_0('#skF_2'(A_16)) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.60/1.85  tff(c_1505, plain, (![A_178]: (~l1_struct_0(A_178) | ~v3_tex_2('#skF_5', A_178) | ~l1_pre_topc(A_178) | ~v2_pre_topc(A_178) | v2_struct_0(A_178))), inference(resolution, [status(thm)], [c_1496, c_24])).
% 4.60/1.85  tff(c_1511, plain, (~l1_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_46, c_1505])).
% 4.60/1.85  tff(c_1515, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1511])).
% 4.60/1.85  tff(c_1516, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_56, c_1515])).
% 4.60/1.85  tff(c_1519, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_18, c_1516])).
% 4.60/1.85  tff(c_1523, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_1519])).
% 4.60/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.60/1.85  
% 4.60/1.85  Inference rules
% 4.60/1.85  ----------------------
% 4.60/1.85  #Ref     : 0
% 4.60/1.85  #Sup     : 362
% 4.60/1.85  #Fact    : 2
% 4.60/1.85  #Define  : 0
% 4.60/1.85  #Split   : 4
% 4.60/1.85  #Chain   : 0
% 4.60/1.85  #Close   : 0
% 4.60/1.85  
% 4.60/1.85  Ordering : KBO
% 4.60/1.85  
% 4.60/1.85  Simplification rules
% 4.60/1.85  ----------------------
% 4.60/1.85  #Subsume      : 45
% 4.60/1.85  #Demod        : 92
% 4.60/1.85  #Tautology    : 74
% 4.60/1.85  #SimpNegUnit  : 10
% 4.60/1.85  #BackRed      : 10
% 4.60/1.85  
% 4.60/1.85  #Partial instantiations: 0
% 4.60/1.85  #Strategies tried      : 1
% 4.60/1.85  
% 4.60/1.85  Timing (in seconds)
% 4.60/1.85  ----------------------
% 4.60/1.86  Preprocessing        : 0.34
% 4.60/1.86  Parsing              : 0.19
% 4.60/1.86  CNF conversion       : 0.02
% 4.60/1.86  Main loop            : 0.66
% 4.60/1.86  Inferencing          : 0.23
% 4.60/1.86  Reduction            : 0.19
% 4.60/1.86  Demodulation         : 0.12
% 4.60/1.86  BG Simplification    : 0.04
% 4.60/1.86  Subsumption          : 0.15
% 4.60/1.86  Abstraction          : 0.03
% 4.60/1.86  MUC search           : 0.00
% 4.60/1.86  Cooper               : 0.00
% 4.60/1.86  Total                : 1.04
% 4.60/1.86  Index Insertion      : 0.00
% 4.60/1.86  Index Deletion       : 0.00
% 4.60/1.86  Index Matching       : 0.00
% 4.60/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
