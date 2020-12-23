%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:57 EST 2020

% Result     : Theorem 5.13s
% Output     : CNFRefutation 5.13s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 110 expanded)
%              Number of leaves         :   38 (  53 expanded)
%              Depth                    :   16
%              Number of atoms          :  196 ( 297 expanded)
%              Number of equality atoms :   21 (  30 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4

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

tff(f_132,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

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

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_116,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_79,axiom,(
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

tff(f_104,axiom,(
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

tff(f_86,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_52,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_50,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_44,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_48,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_65,plain,(
    ! [A_39] :
      ( k1_xboole_0 = A_39
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_69,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_48,c_65])).

tff(c_8,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_71,plain,(
    ! [A_6] : k2_xboole_0(A_6,'#skF_5') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_8])).

tff(c_12,plain,(
    ! [A_8,B_9] : k2_xboole_0(k1_tarski(A_8),B_9) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_97,plain,(
    ! [A_44,B_45] : k2_xboole_0(k1_tarski(A_44),B_45) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_12])).

tff(c_101,plain,(
    ! [A_44] : k1_tarski(A_44) != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_97])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_163,plain,(
    ! [A_65] :
      ( m1_subset_1('#skF_2'(A_65),k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_18,plain,(
    ! [A_14,C_16,B_15] :
      ( m1_subset_1(A_14,C_16)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(C_16))
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_221,plain,(
    ! [A_74,A_75] :
      ( m1_subset_1(A_74,u1_struct_0(A_75))
      | ~ r2_hidden(A_74,'#skF_2'(A_75))
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75)
      | v2_struct_0(A_75) ) ),
    inference(resolution,[status(thm)],[c_163,c_18])).

tff(c_226,plain,(
    ! [A_75] :
      ( m1_subset_1('#skF_1'('#skF_2'(A_75)),u1_struct_0(A_75))
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75)
      | v2_struct_0(A_75)
      | v1_xboole_0('#skF_2'(A_75)) ) ),
    inference(resolution,[status(thm)],[c_4,c_221])).

tff(c_42,plain,(
    ! [A_33,B_35] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_33),B_35),A_33)
      | ~ m1_subset_1(B_35,u1_struct_0(A_33))
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_26,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k6_domain_1(A_19,B_20),k1_zfmisc_1(A_19))
      | ~ m1_subset_1(B_20,A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_14,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_78,plain,(
    ! [A_10] : m1_subset_1('#skF_5',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_14])).

tff(c_10,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_72,plain,(
    ! [A_7] : r1_tarski('#skF_5',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_10])).

tff(c_445,plain,(
    ! [C_97,B_98,A_99] :
      ( C_97 = B_98
      | ~ r1_tarski(B_98,C_97)
      | ~ v2_tex_2(C_97,A_99)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ v3_tex_2(B_98,A_99)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_447,plain,(
    ! [A_7,A_99] :
      ( A_7 = '#skF_5'
      | ~ v2_tex_2(A_7,A_99)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ v3_tex_2('#skF_5',A_99)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99) ) ),
    inference(resolution,[status(thm)],[c_72,c_445])).

tff(c_451,plain,(
    ! [A_100,A_101] :
      ( A_100 = '#skF_5'
      | ~ v2_tex_2(A_100,A_101)
      | ~ m1_subset_1(A_100,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ v3_tex_2('#skF_5',A_101)
      | ~ l1_pre_topc(A_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_447])).

tff(c_957,plain,(
    ! [A_141,B_142] :
      ( k6_domain_1(u1_struct_0(A_141),B_142) = '#skF_5'
      | ~ v2_tex_2(k6_domain_1(u1_struct_0(A_141),B_142),A_141)
      | ~ v3_tex_2('#skF_5',A_141)
      | ~ l1_pre_topc(A_141)
      | ~ m1_subset_1(B_142,u1_struct_0(A_141))
      | v1_xboole_0(u1_struct_0(A_141)) ) ),
    inference(resolution,[status(thm)],[c_26,c_451])).

tff(c_969,plain,(
    ! [A_143,B_144] :
      ( k6_domain_1(u1_struct_0(A_143),B_144) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_143)
      | v1_xboole_0(u1_struct_0(A_143))
      | ~ m1_subset_1(B_144,u1_struct_0(A_143))
      | ~ l1_pre_topc(A_143)
      | ~ v2_pre_topc(A_143)
      | v2_struct_0(A_143) ) ),
    inference(resolution,[status(thm)],[c_42,c_957])).

tff(c_979,plain,(
    ! [A_145] :
      ( k6_domain_1(u1_struct_0(A_145),'#skF_1'('#skF_2'(A_145))) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_145)
      | v1_xboole_0(u1_struct_0(A_145))
      | ~ l1_pre_topc(A_145)
      | ~ v2_pre_topc(A_145)
      | v2_struct_0(A_145)
      | v1_xboole_0('#skF_2'(A_145)) ) ),
    inference(resolution,[status(thm)],[c_226,c_969])).

tff(c_254,plain,(
    ! [A_84] :
      ( m1_subset_1('#skF_1'('#skF_2'(A_84)),u1_struct_0(A_84))
      | ~ l1_pre_topc(A_84)
      | ~ v2_pre_topc(A_84)
      | v2_struct_0(A_84)
      | v1_xboole_0('#skF_2'(A_84)) ) ),
    inference(resolution,[status(thm)],[c_4,c_221])).

tff(c_28,plain,(
    ! [A_21,B_22] :
      ( k6_domain_1(A_21,B_22) = k1_tarski(B_22)
      | ~ m1_subset_1(B_22,A_21)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_258,plain,(
    ! [A_84] :
      ( k6_domain_1(u1_struct_0(A_84),'#skF_1'('#skF_2'(A_84))) = k1_tarski('#skF_1'('#skF_2'(A_84)))
      | v1_xboole_0(u1_struct_0(A_84))
      | ~ l1_pre_topc(A_84)
      | ~ v2_pre_topc(A_84)
      | v2_struct_0(A_84)
      | v1_xboole_0('#skF_2'(A_84)) ) ),
    inference(resolution,[status(thm)],[c_254,c_28])).

tff(c_988,plain,(
    ! [A_145] :
      ( k1_tarski('#skF_1'('#skF_2'(A_145))) = '#skF_5'
      | v1_xboole_0(u1_struct_0(A_145))
      | ~ l1_pre_topc(A_145)
      | ~ v2_pre_topc(A_145)
      | v2_struct_0(A_145)
      | v1_xboole_0('#skF_2'(A_145))
      | ~ v3_tex_2('#skF_5',A_145)
      | v1_xboole_0(u1_struct_0(A_145))
      | ~ l1_pre_topc(A_145)
      | ~ v2_pre_topc(A_145)
      | v2_struct_0(A_145)
      | v1_xboole_0('#skF_2'(A_145)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_979,c_258])).

tff(c_1017,plain,(
    ! [A_145] :
      ( v1_xboole_0(u1_struct_0(A_145))
      | ~ l1_pre_topc(A_145)
      | ~ v2_pre_topc(A_145)
      | v2_struct_0(A_145)
      | v1_xboole_0('#skF_2'(A_145))
      | ~ v3_tex_2('#skF_5',A_145)
      | v1_xboole_0(u1_struct_0(A_145))
      | ~ l1_pre_topc(A_145)
      | ~ v2_pre_topc(A_145)
      | v2_struct_0(A_145)
      | v1_xboole_0('#skF_2'(A_145)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_988])).

tff(c_1899,plain,(
    ! [A_191] :
      ( ~ v3_tex_2('#skF_5',A_191)
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191)
      | v1_xboole_0('#skF_2'(A_191))
      | v1_xboole_0(u1_struct_0(A_191)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_1017])).

tff(c_16,plain,(
    ! [B_13,A_11] :
      ( v1_xboole_0(B_13)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_11))
      | ~ v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_174,plain,(
    ! [A_65] :
      ( v1_xboole_0('#skF_2'(A_65))
      | ~ v1_xboole_0(u1_struct_0(A_65))
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_163,c_16])).

tff(c_1912,plain,(
    ! [A_192] :
      ( ~ v3_tex_2('#skF_5',A_192)
      | ~ l1_pre_topc(A_192)
      | ~ v2_pre_topc(A_192)
      | v2_struct_0(A_192)
      | v1_xboole_0('#skF_2'(A_192)) ) ),
    inference(resolution,[status(thm)],[c_1899,c_174])).

tff(c_22,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0('#skF_2'(A_17))
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1939,plain,(
    ! [A_195] :
      ( ~ v3_tex_2('#skF_5',A_195)
      | ~ l1_pre_topc(A_195)
      | ~ v2_pre_topc(A_195)
      | v2_struct_0(A_195) ) ),
    inference(resolution,[status(thm)],[c_1912,c_22])).

tff(c_1945,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_1939])).

tff(c_1949,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1945])).

tff(c_1951,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1949])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:55:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.13/1.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.13/1.96  
% 5.13/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.13/1.96  %$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4
% 5.13/1.96  
% 5.13/1.96  %Foreground sorts:
% 5.13/1.96  
% 5.13/1.96  
% 5.13/1.96  %Background operators:
% 5.13/1.96  
% 5.13/1.96  
% 5.13/1.96  %Foreground operators:
% 5.13/1.96  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.13/1.96  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.13/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.13/1.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.13/1.96  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.13/1.96  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.13/1.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.13/1.96  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.13/1.96  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.13/1.96  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 5.13/1.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.13/1.96  tff('#skF_5', type, '#skF_5': $i).
% 5.13/1.96  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 5.13/1.96  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 5.13/1.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.13/1.96  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.13/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.13/1.96  tff('#skF_4', type, '#skF_4': $i).
% 5.13/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.13/1.96  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.13/1.96  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.13/1.96  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.13/1.96  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.13/1.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.13/1.96  
% 5.13/1.98  tff(f_132, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 5.13/1.98  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.13/1.98  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 5.13/1.98  tff(f_42, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 5.13/1.98  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.13/1.98  tff(f_72, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc7_pre_topc)).
% 5.13/1.98  tff(f_57, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 5.13/1.98  tff(f_116, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 5.13/1.98  tff(f_79, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 5.13/1.98  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 5.13/1.98  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.13/1.98  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 5.13/1.98  tff(f_86, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 5.13/1.98  tff(f_51, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 5.13/1.98  tff(c_54, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.13/1.98  tff(c_52, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.13/1.98  tff(c_50, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.13/1.98  tff(c_44, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.13/1.98  tff(c_48, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.13/1.98  tff(c_65, plain, (![A_39]: (k1_xboole_0=A_39 | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.13/1.98  tff(c_69, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_48, c_65])).
% 5.13/1.98  tff(c_8, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.13/1.98  tff(c_71, plain, (![A_6]: (k2_xboole_0(A_6, '#skF_5')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_69, c_8])).
% 5.13/1.98  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(k1_tarski(A_8), B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.13/1.98  tff(c_97, plain, (![A_44, B_45]: (k2_xboole_0(k1_tarski(A_44), B_45)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_12])).
% 5.13/1.98  tff(c_101, plain, (![A_44]: (k1_tarski(A_44)!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_71, c_97])).
% 5.13/1.98  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.13/1.98  tff(c_163, plain, (![A_65]: (m1_subset_1('#skF_2'(A_65), k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.13/1.98  tff(c_18, plain, (![A_14, C_16, B_15]: (m1_subset_1(A_14, C_16) | ~m1_subset_1(B_15, k1_zfmisc_1(C_16)) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.13/1.98  tff(c_221, plain, (![A_74, A_75]: (m1_subset_1(A_74, u1_struct_0(A_75)) | ~r2_hidden(A_74, '#skF_2'(A_75)) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75))), inference(resolution, [status(thm)], [c_163, c_18])).
% 5.13/1.98  tff(c_226, plain, (![A_75]: (m1_subset_1('#skF_1'('#skF_2'(A_75)), u1_struct_0(A_75)) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75) | v1_xboole_0('#skF_2'(A_75)))), inference(resolution, [status(thm)], [c_4, c_221])).
% 5.13/1.98  tff(c_42, plain, (![A_33, B_35]: (v2_tex_2(k6_domain_1(u1_struct_0(A_33), B_35), A_33) | ~m1_subset_1(B_35, u1_struct_0(A_33)) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.13/1.98  tff(c_26, plain, (![A_19, B_20]: (m1_subset_1(k6_domain_1(A_19, B_20), k1_zfmisc_1(A_19)) | ~m1_subset_1(B_20, A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.13/1.98  tff(c_14, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.13/1.98  tff(c_78, plain, (![A_10]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_14])).
% 5.13/1.98  tff(c_10, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.13/1.98  tff(c_72, plain, (![A_7]: (r1_tarski('#skF_5', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_10])).
% 5.13/1.98  tff(c_445, plain, (![C_97, B_98, A_99]: (C_97=B_98 | ~r1_tarski(B_98, C_97) | ~v2_tex_2(C_97, A_99) | ~m1_subset_1(C_97, k1_zfmisc_1(u1_struct_0(A_99))) | ~v3_tex_2(B_98, A_99) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.13/1.98  tff(c_447, plain, (![A_7, A_99]: (A_7='#skF_5' | ~v2_tex_2(A_7, A_99) | ~m1_subset_1(A_7, k1_zfmisc_1(u1_struct_0(A_99))) | ~v3_tex_2('#skF_5', A_99) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99))), inference(resolution, [status(thm)], [c_72, c_445])).
% 5.13/1.98  tff(c_451, plain, (![A_100, A_101]: (A_100='#skF_5' | ~v2_tex_2(A_100, A_101) | ~m1_subset_1(A_100, k1_zfmisc_1(u1_struct_0(A_101))) | ~v3_tex_2('#skF_5', A_101) | ~l1_pre_topc(A_101))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_447])).
% 5.13/1.98  tff(c_957, plain, (![A_141, B_142]: (k6_domain_1(u1_struct_0(A_141), B_142)='#skF_5' | ~v2_tex_2(k6_domain_1(u1_struct_0(A_141), B_142), A_141) | ~v3_tex_2('#skF_5', A_141) | ~l1_pre_topc(A_141) | ~m1_subset_1(B_142, u1_struct_0(A_141)) | v1_xboole_0(u1_struct_0(A_141)))), inference(resolution, [status(thm)], [c_26, c_451])).
% 5.13/1.98  tff(c_969, plain, (![A_143, B_144]: (k6_domain_1(u1_struct_0(A_143), B_144)='#skF_5' | ~v3_tex_2('#skF_5', A_143) | v1_xboole_0(u1_struct_0(A_143)) | ~m1_subset_1(B_144, u1_struct_0(A_143)) | ~l1_pre_topc(A_143) | ~v2_pre_topc(A_143) | v2_struct_0(A_143))), inference(resolution, [status(thm)], [c_42, c_957])).
% 5.13/1.98  tff(c_979, plain, (![A_145]: (k6_domain_1(u1_struct_0(A_145), '#skF_1'('#skF_2'(A_145)))='#skF_5' | ~v3_tex_2('#skF_5', A_145) | v1_xboole_0(u1_struct_0(A_145)) | ~l1_pre_topc(A_145) | ~v2_pre_topc(A_145) | v2_struct_0(A_145) | v1_xboole_0('#skF_2'(A_145)))), inference(resolution, [status(thm)], [c_226, c_969])).
% 5.13/1.98  tff(c_254, plain, (![A_84]: (m1_subset_1('#skF_1'('#skF_2'(A_84)), u1_struct_0(A_84)) | ~l1_pre_topc(A_84) | ~v2_pre_topc(A_84) | v2_struct_0(A_84) | v1_xboole_0('#skF_2'(A_84)))), inference(resolution, [status(thm)], [c_4, c_221])).
% 5.13/1.98  tff(c_28, plain, (![A_21, B_22]: (k6_domain_1(A_21, B_22)=k1_tarski(B_22) | ~m1_subset_1(B_22, A_21) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.13/1.98  tff(c_258, plain, (![A_84]: (k6_domain_1(u1_struct_0(A_84), '#skF_1'('#skF_2'(A_84)))=k1_tarski('#skF_1'('#skF_2'(A_84))) | v1_xboole_0(u1_struct_0(A_84)) | ~l1_pre_topc(A_84) | ~v2_pre_topc(A_84) | v2_struct_0(A_84) | v1_xboole_0('#skF_2'(A_84)))), inference(resolution, [status(thm)], [c_254, c_28])).
% 5.13/1.98  tff(c_988, plain, (![A_145]: (k1_tarski('#skF_1'('#skF_2'(A_145)))='#skF_5' | v1_xboole_0(u1_struct_0(A_145)) | ~l1_pre_topc(A_145) | ~v2_pre_topc(A_145) | v2_struct_0(A_145) | v1_xboole_0('#skF_2'(A_145)) | ~v3_tex_2('#skF_5', A_145) | v1_xboole_0(u1_struct_0(A_145)) | ~l1_pre_topc(A_145) | ~v2_pre_topc(A_145) | v2_struct_0(A_145) | v1_xboole_0('#skF_2'(A_145)))), inference(superposition, [status(thm), theory('equality')], [c_979, c_258])).
% 5.13/1.98  tff(c_1017, plain, (![A_145]: (v1_xboole_0(u1_struct_0(A_145)) | ~l1_pre_topc(A_145) | ~v2_pre_topc(A_145) | v2_struct_0(A_145) | v1_xboole_0('#skF_2'(A_145)) | ~v3_tex_2('#skF_5', A_145) | v1_xboole_0(u1_struct_0(A_145)) | ~l1_pre_topc(A_145) | ~v2_pre_topc(A_145) | v2_struct_0(A_145) | v1_xboole_0('#skF_2'(A_145)))), inference(negUnitSimplification, [status(thm)], [c_101, c_988])).
% 5.13/1.98  tff(c_1899, plain, (![A_191]: (~v3_tex_2('#skF_5', A_191) | ~l1_pre_topc(A_191) | ~v2_pre_topc(A_191) | v2_struct_0(A_191) | v1_xboole_0('#skF_2'(A_191)) | v1_xboole_0(u1_struct_0(A_191)))), inference(factorization, [status(thm), theory('equality')], [c_1017])).
% 5.13/1.98  tff(c_16, plain, (![B_13, A_11]: (v1_xboole_0(B_13) | ~m1_subset_1(B_13, k1_zfmisc_1(A_11)) | ~v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.13/1.98  tff(c_174, plain, (![A_65]: (v1_xboole_0('#skF_2'(A_65)) | ~v1_xboole_0(u1_struct_0(A_65)) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65))), inference(resolution, [status(thm)], [c_163, c_16])).
% 5.13/1.98  tff(c_1912, plain, (![A_192]: (~v3_tex_2('#skF_5', A_192) | ~l1_pre_topc(A_192) | ~v2_pre_topc(A_192) | v2_struct_0(A_192) | v1_xboole_0('#skF_2'(A_192)))), inference(resolution, [status(thm)], [c_1899, c_174])).
% 5.13/1.98  tff(c_22, plain, (![A_17]: (~v1_xboole_0('#skF_2'(A_17)) | ~l1_pre_topc(A_17) | ~v2_pre_topc(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.13/1.98  tff(c_1939, plain, (![A_195]: (~v3_tex_2('#skF_5', A_195) | ~l1_pre_topc(A_195) | ~v2_pre_topc(A_195) | v2_struct_0(A_195))), inference(resolution, [status(thm)], [c_1912, c_22])).
% 5.13/1.98  tff(c_1945, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_1939])).
% 5.13/1.98  tff(c_1949, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1945])).
% 5.13/1.98  tff(c_1951, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_1949])).
% 5.13/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.13/1.98  
% 5.13/1.98  Inference rules
% 5.13/1.98  ----------------------
% 5.13/1.98  #Ref     : 0
% 5.13/1.98  #Sup     : 466
% 5.13/1.98  #Fact    : 2
% 5.13/1.98  #Define  : 0
% 5.13/1.98  #Split   : 4
% 5.13/1.98  #Chain   : 0
% 5.13/1.98  #Close   : 0
% 5.13/1.98  
% 5.13/1.98  Ordering : KBO
% 5.13/1.98  
% 5.13/1.98  Simplification rules
% 5.13/1.98  ----------------------
% 5.13/1.98  #Subsume      : 71
% 5.13/1.98  #Demod        : 127
% 5.13/1.98  #Tautology    : 123
% 5.13/1.98  #SimpNegUnit  : 11
% 5.13/1.98  #BackRed      : 9
% 5.13/1.98  
% 5.13/1.98  #Partial instantiations: 0
% 5.13/1.98  #Strategies tried      : 1
% 5.13/1.98  
% 5.13/1.98  Timing (in seconds)
% 5.13/1.98  ----------------------
% 5.13/1.98  Preprocessing        : 0.34
% 5.13/1.98  Parsing              : 0.18
% 5.13/1.98  CNF conversion       : 0.02
% 5.13/1.98  Main loop            : 0.86
% 5.13/1.98  Inferencing          : 0.29
% 5.13/1.98  Reduction            : 0.24
% 5.13/1.98  Demodulation         : 0.16
% 5.13/1.98  BG Simplification    : 0.04
% 5.13/1.98  Subsumption          : 0.22
% 5.13/1.98  Abstraction          : 0.04
% 5.13/1.98  MUC search           : 0.00
% 5.13/1.98  Cooper               : 0.00
% 5.13/1.98  Total                : 1.24
% 5.13/1.98  Index Insertion      : 0.00
% 5.13/1.98  Index Deletion       : 0.00
% 5.13/1.98  Index Matching       : 0.00
% 5.13/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
