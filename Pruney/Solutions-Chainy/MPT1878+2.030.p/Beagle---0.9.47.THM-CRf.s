%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:01 EST 2020

% Result     : Theorem 20.73s
% Output     : CNFRefutation 20.73s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 116 expanded)
%              Number of leaves         :   38 (  55 expanded)
%              Depth                    :   16
%              Number of atoms          :  204 ( 311 expanded)
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

tff(f_51,axiom,(
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

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

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
    ! [A_40] :
      ( k1_xboole_0 = A_40
      | ~ v1_xboole_0(A_40) ) ),
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
    ! [A_45,B_46] : k2_xboole_0(k1_tarski(A_45),B_46) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_12])).

tff(c_101,plain,(
    ! [A_45] : k1_tarski(A_45) != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_97])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_179,plain,(
    ! [A_71] :
      ( m1_subset_1('#skF_2'(A_71),k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_18,plain,(
    ! [A_15,C_17,B_16] :
      ( m1_subset_1(A_15,C_17)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(C_17))
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_301,plain,(
    ! [A_89,A_90] :
      ( m1_subset_1(A_89,u1_struct_0(A_90))
      | ~ r2_hidden(A_89,'#skF_2'(A_90))
      | ~ l1_pre_topc(A_90)
      | ~ v2_pre_topc(A_90)
      | v2_struct_0(A_90) ) ),
    inference(resolution,[status(thm)],[c_179,c_18])).

tff(c_311,plain,(
    ! [A_90] :
      ( m1_subset_1('#skF_1'('#skF_2'(A_90)),u1_struct_0(A_90))
      | ~ l1_pre_topc(A_90)
      | ~ v2_pre_topc(A_90)
      | v2_struct_0(A_90)
      | v1_xboole_0('#skF_2'(A_90)) ) ),
    inference(resolution,[status(thm)],[c_4,c_301])).

tff(c_42,plain,(
    ! [A_34,B_36] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_34),B_36),A_34)
      | ~ m1_subset_1(B_36,u1_struct_0(A_34))
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k6_domain_1(A_20,B_21),k1_zfmisc_1(A_20))
      | ~ m1_subset_1(B_21,A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_16,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_78,plain,(
    ! [A_14] : m1_subset_1('#skF_5',k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_16])).

tff(c_10,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_72,plain,(
    ! [A_7] : r1_tarski('#skF_5',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_10])).

tff(c_579,plain,(
    ! [C_113,B_114,A_115] :
      ( C_113 = B_114
      | ~ r1_tarski(B_114,C_113)
      | ~ v2_tex_2(C_113,A_115)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ v3_tex_2(B_114,A_115)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_581,plain,(
    ! [A_7,A_115] :
      ( A_7 = '#skF_5'
      | ~ v2_tex_2(A_7,A_115)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ v3_tex_2('#skF_5',A_115)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(resolution,[status(thm)],[c_72,c_579])).

tff(c_828,plain,(
    ! [A_130,A_131] :
      ( A_130 = '#skF_5'
      | ~ v2_tex_2(A_130,A_131)
      | ~ m1_subset_1(A_130,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ v3_tex_2('#skF_5',A_131)
      | ~ l1_pre_topc(A_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_581])).

tff(c_8829,plain,(
    ! [A_371,B_372] :
      ( k6_domain_1(u1_struct_0(A_371),B_372) = '#skF_5'
      | ~ v2_tex_2(k6_domain_1(u1_struct_0(A_371),B_372),A_371)
      | ~ v3_tex_2('#skF_5',A_371)
      | ~ l1_pre_topc(A_371)
      | ~ m1_subset_1(B_372,u1_struct_0(A_371))
      | v1_xboole_0(u1_struct_0(A_371)) ) ),
    inference(resolution,[status(thm)],[c_26,c_828])).

tff(c_8841,plain,(
    ! [A_373,B_374] :
      ( k6_domain_1(u1_struct_0(A_373),B_374) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_373)
      | v1_xboole_0(u1_struct_0(A_373))
      | ~ m1_subset_1(B_374,u1_struct_0(A_373))
      | ~ l1_pre_topc(A_373)
      | ~ v2_pre_topc(A_373)
      | v2_struct_0(A_373) ) ),
    inference(resolution,[status(thm)],[c_42,c_8829])).

tff(c_8873,plain,(
    ! [A_375] :
      ( k6_domain_1(u1_struct_0(A_375),'#skF_1'('#skF_2'(A_375))) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_375)
      | v1_xboole_0(u1_struct_0(A_375))
      | ~ l1_pre_topc(A_375)
      | ~ v2_pre_topc(A_375)
      | v2_struct_0(A_375)
      | v1_xboole_0('#skF_2'(A_375)) ) ),
    inference(resolution,[status(thm)],[c_311,c_8841])).

tff(c_437,plain,(
    ! [A_104] :
      ( m1_subset_1('#skF_1'('#skF_2'(A_104)),u1_struct_0(A_104))
      | ~ l1_pre_topc(A_104)
      | ~ v2_pre_topc(A_104)
      | v2_struct_0(A_104)
      | v1_xboole_0('#skF_2'(A_104)) ) ),
    inference(resolution,[status(thm)],[c_4,c_301])).

tff(c_28,plain,(
    ! [A_22,B_23] :
      ( k6_domain_1(A_22,B_23) = k1_tarski(B_23)
      | ~ m1_subset_1(B_23,A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_441,plain,(
    ! [A_104] :
      ( k6_domain_1(u1_struct_0(A_104),'#skF_1'('#skF_2'(A_104))) = k1_tarski('#skF_1'('#skF_2'(A_104)))
      | v1_xboole_0(u1_struct_0(A_104))
      | ~ l1_pre_topc(A_104)
      | ~ v2_pre_topc(A_104)
      | v2_struct_0(A_104)
      | v1_xboole_0('#skF_2'(A_104)) ) ),
    inference(resolution,[status(thm)],[c_437,c_28])).

tff(c_8887,plain,(
    ! [A_375] :
      ( k1_tarski('#skF_1'('#skF_2'(A_375))) = '#skF_5'
      | v1_xboole_0(u1_struct_0(A_375))
      | ~ l1_pre_topc(A_375)
      | ~ v2_pre_topc(A_375)
      | v2_struct_0(A_375)
      | v1_xboole_0('#skF_2'(A_375))
      | ~ v3_tex_2('#skF_5',A_375)
      | v1_xboole_0(u1_struct_0(A_375))
      | ~ l1_pre_topc(A_375)
      | ~ v2_pre_topc(A_375)
      | v2_struct_0(A_375)
      | v1_xboole_0('#skF_2'(A_375)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8873,c_441])).

tff(c_8937,plain,(
    ! [A_375] :
      ( v1_xboole_0(u1_struct_0(A_375))
      | ~ l1_pre_topc(A_375)
      | ~ v2_pre_topc(A_375)
      | v2_struct_0(A_375)
      | v1_xboole_0('#skF_2'(A_375))
      | ~ v3_tex_2('#skF_5',A_375)
      | v1_xboole_0(u1_struct_0(A_375))
      | ~ l1_pre_topc(A_375)
      | ~ v2_pre_topc(A_375)
      | v2_struct_0(A_375)
      | v1_xboole_0('#skF_2'(A_375)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_8887])).

tff(c_59070,plain,(
    ! [A_906] :
      ( ~ v3_tex_2('#skF_5',A_906)
      | ~ l1_pre_topc(A_906)
      | ~ v2_pre_topc(A_906)
      | v2_struct_0(A_906)
      | v1_xboole_0('#skF_2'(A_906))
      | v1_xboole_0(u1_struct_0(A_906)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_8937])).

tff(c_110,plain,(
    ! [C_52,A_53,B_54] :
      ( r2_hidden(C_52,A_53)
      | ~ r2_hidden(C_52,B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_157,plain,(
    ! [A_67,A_68] :
      ( r2_hidden('#skF_1'(A_67),A_68)
      | ~ m1_subset_1(A_67,k1_zfmisc_1(A_68))
      | v1_xboole_0(A_67) ) ),
    inference(resolution,[status(thm)],[c_4,c_110])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_168,plain,(
    ! [A_68,A_67] :
      ( ~ v1_xboole_0(A_68)
      | ~ m1_subset_1(A_67,k1_zfmisc_1(A_68))
      | v1_xboole_0(A_67) ) ),
    inference(resolution,[status(thm)],[c_157,c_2])).

tff(c_188,plain,(
    ! [A_71] :
      ( ~ v1_xboole_0(u1_struct_0(A_71))
      | v1_xboole_0('#skF_2'(A_71))
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(resolution,[status(thm)],[c_179,c_168])).

tff(c_59092,plain,(
    ! [A_907] :
      ( ~ v3_tex_2('#skF_5',A_907)
      | ~ l1_pre_topc(A_907)
      | ~ v2_pre_topc(A_907)
      | v2_struct_0(A_907)
      | v1_xboole_0('#skF_2'(A_907)) ) ),
    inference(resolution,[status(thm)],[c_59070,c_188])).

tff(c_22,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0('#skF_2'(A_18))
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_59105,plain,(
    ! [A_908] :
      ( ~ v3_tex_2('#skF_5',A_908)
      | ~ l1_pre_topc(A_908)
      | ~ v2_pre_topc(A_908)
      | v2_struct_0(A_908) ) ),
    inference(resolution,[status(thm)],[c_59092,c_22])).

tff(c_59111,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_59105])).

tff(c_59115,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_59111])).

tff(c_59117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_59115])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:30:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.73/12.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.73/12.46  
% 20.73/12.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.73/12.46  %$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4
% 20.73/12.46  
% 20.73/12.46  %Foreground sorts:
% 20.73/12.46  
% 20.73/12.46  
% 20.73/12.46  %Background operators:
% 20.73/12.46  
% 20.73/12.46  
% 20.73/12.46  %Foreground operators:
% 20.73/12.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 20.73/12.46  tff('#skF_2', type, '#skF_2': $i > $i).
% 20.73/12.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.73/12.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 20.73/12.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 20.73/12.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 20.73/12.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 20.73/12.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 20.73/12.46  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 20.73/12.46  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 20.73/12.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.73/12.46  tff('#skF_5', type, '#skF_5': $i).
% 20.73/12.46  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 20.73/12.46  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 20.73/12.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 20.73/12.46  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 20.73/12.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.73/12.46  tff('#skF_4', type, '#skF_4': $i).
% 20.73/12.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.73/12.46  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 20.73/12.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 20.73/12.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 20.73/12.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 20.73/12.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 20.73/12.46  
% 20.73/12.48  tff(f_132, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 20.73/12.48  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 20.73/12.48  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 20.73/12.48  tff(f_42, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 20.73/12.48  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 20.73/12.48  tff(f_72, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc7_pre_topc)).
% 20.73/12.48  tff(f_57, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 20.73/12.48  tff(f_116, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 20.73/12.48  tff(f_79, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 20.73/12.48  tff(f_51, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 20.73/12.48  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 20.73/12.48  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 20.73/12.48  tff(f_86, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 20.73/12.48  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 20.73/12.48  tff(c_54, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 20.73/12.48  tff(c_52, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 20.73/12.48  tff(c_50, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 20.73/12.48  tff(c_44, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 20.73/12.48  tff(c_48, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 20.73/12.48  tff(c_65, plain, (![A_40]: (k1_xboole_0=A_40 | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_35])).
% 20.73/12.48  tff(c_69, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_48, c_65])).
% 20.73/12.48  tff(c_8, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 20.73/12.48  tff(c_71, plain, (![A_6]: (k2_xboole_0(A_6, '#skF_5')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_69, c_8])).
% 20.73/12.48  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(k1_tarski(A_8), B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 20.73/12.48  tff(c_97, plain, (![A_45, B_46]: (k2_xboole_0(k1_tarski(A_45), B_46)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_12])).
% 20.73/12.48  tff(c_101, plain, (![A_45]: (k1_tarski(A_45)!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_71, c_97])).
% 20.73/12.48  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 20.73/12.48  tff(c_179, plain, (![A_71]: (m1_subset_1('#skF_2'(A_71), k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71) | ~v2_pre_topc(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_72])).
% 20.73/12.48  tff(c_18, plain, (![A_15, C_17, B_16]: (m1_subset_1(A_15, C_17) | ~m1_subset_1(B_16, k1_zfmisc_1(C_17)) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 20.73/12.48  tff(c_301, plain, (![A_89, A_90]: (m1_subset_1(A_89, u1_struct_0(A_90)) | ~r2_hidden(A_89, '#skF_2'(A_90)) | ~l1_pre_topc(A_90) | ~v2_pre_topc(A_90) | v2_struct_0(A_90))), inference(resolution, [status(thm)], [c_179, c_18])).
% 20.73/12.48  tff(c_311, plain, (![A_90]: (m1_subset_1('#skF_1'('#skF_2'(A_90)), u1_struct_0(A_90)) | ~l1_pre_topc(A_90) | ~v2_pre_topc(A_90) | v2_struct_0(A_90) | v1_xboole_0('#skF_2'(A_90)))), inference(resolution, [status(thm)], [c_4, c_301])).
% 20.73/12.48  tff(c_42, plain, (![A_34, B_36]: (v2_tex_2(k6_domain_1(u1_struct_0(A_34), B_36), A_34) | ~m1_subset_1(B_36, u1_struct_0(A_34)) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_116])).
% 20.73/12.48  tff(c_26, plain, (![A_20, B_21]: (m1_subset_1(k6_domain_1(A_20, B_21), k1_zfmisc_1(A_20)) | ~m1_subset_1(B_21, A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_79])).
% 20.73/12.48  tff(c_16, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 20.73/12.48  tff(c_78, plain, (![A_14]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_16])).
% 20.73/12.48  tff(c_10, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 20.73/12.48  tff(c_72, plain, (![A_7]: (r1_tarski('#skF_5', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_10])).
% 20.73/12.48  tff(c_579, plain, (![C_113, B_114, A_115]: (C_113=B_114 | ~r1_tarski(B_114, C_113) | ~v2_tex_2(C_113, A_115) | ~m1_subset_1(C_113, k1_zfmisc_1(u1_struct_0(A_115))) | ~v3_tex_2(B_114, A_115) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_104])).
% 20.73/12.48  tff(c_581, plain, (![A_7, A_115]: (A_7='#skF_5' | ~v2_tex_2(A_7, A_115) | ~m1_subset_1(A_7, k1_zfmisc_1(u1_struct_0(A_115))) | ~v3_tex_2('#skF_5', A_115) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(resolution, [status(thm)], [c_72, c_579])).
% 20.73/12.48  tff(c_828, plain, (![A_130, A_131]: (A_130='#skF_5' | ~v2_tex_2(A_130, A_131) | ~m1_subset_1(A_130, k1_zfmisc_1(u1_struct_0(A_131))) | ~v3_tex_2('#skF_5', A_131) | ~l1_pre_topc(A_131))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_581])).
% 20.73/12.48  tff(c_8829, plain, (![A_371, B_372]: (k6_domain_1(u1_struct_0(A_371), B_372)='#skF_5' | ~v2_tex_2(k6_domain_1(u1_struct_0(A_371), B_372), A_371) | ~v3_tex_2('#skF_5', A_371) | ~l1_pre_topc(A_371) | ~m1_subset_1(B_372, u1_struct_0(A_371)) | v1_xboole_0(u1_struct_0(A_371)))), inference(resolution, [status(thm)], [c_26, c_828])).
% 20.73/12.48  tff(c_8841, plain, (![A_373, B_374]: (k6_domain_1(u1_struct_0(A_373), B_374)='#skF_5' | ~v3_tex_2('#skF_5', A_373) | v1_xboole_0(u1_struct_0(A_373)) | ~m1_subset_1(B_374, u1_struct_0(A_373)) | ~l1_pre_topc(A_373) | ~v2_pre_topc(A_373) | v2_struct_0(A_373))), inference(resolution, [status(thm)], [c_42, c_8829])).
% 20.73/12.48  tff(c_8873, plain, (![A_375]: (k6_domain_1(u1_struct_0(A_375), '#skF_1'('#skF_2'(A_375)))='#skF_5' | ~v3_tex_2('#skF_5', A_375) | v1_xboole_0(u1_struct_0(A_375)) | ~l1_pre_topc(A_375) | ~v2_pre_topc(A_375) | v2_struct_0(A_375) | v1_xboole_0('#skF_2'(A_375)))), inference(resolution, [status(thm)], [c_311, c_8841])).
% 20.73/12.48  tff(c_437, plain, (![A_104]: (m1_subset_1('#skF_1'('#skF_2'(A_104)), u1_struct_0(A_104)) | ~l1_pre_topc(A_104) | ~v2_pre_topc(A_104) | v2_struct_0(A_104) | v1_xboole_0('#skF_2'(A_104)))), inference(resolution, [status(thm)], [c_4, c_301])).
% 20.73/12.48  tff(c_28, plain, (![A_22, B_23]: (k6_domain_1(A_22, B_23)=k1_tarski(B_23) | ~m1_subset_1(B_23, A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_86])).
% 20.73/12.48  tff(c_441, plain, (![A_104]: (k6_domain_1(u1_struct_0(A_104), '#skF_1'('#skF_2'(A_104)))=k1_tarski('#skF_1'('#skF_2'(A_104))) | v1_xboole_0(u1_struct_0(A_104)) | ~l1_pre_topc(A_104) | ~v2_pre_topc(A_104) | v2_struct_0(A_104) | v1_xboole_0('#skF_2'(A_104)))), inference(resolution, [status(thm)], [c_437, c_28])).
% 20.73/12.48  tff(c_8887, plain, (![A_375]: (k1_tarski('#skF_1'('#skF_2'(A_375)))='#skF_5' | v1_xboole_0(u1_struct_0(A_375)) | ~l1_pre_topc(A_375) | ~v2_pre_topc(A_375) | v2_struct_0(A_375) | v1_xboole_0('#skF_2'(A_375)) | ~v3_tex_2('#skF_5', A_375) | v1_xboole_0(u1_struct_0(A_375)) | ~l1_pre_topc(A_375) | ~v2_pre_topc(A_375) | v2_struct_0(A_375) | v1_xboole_0('#skF_2'(A_375)))), inference(superposition, [status(thm), theory('equality')], [c_8873, c_441])).
% 20.73/12.48  tff(c_8937, plain, (![A_375]: (v1_xboole_0(u1_struct_0(A_375)) | ~l1_pre_topc(A_375) | ~v2_pre_topc(A_375) | v2_struct_0(A_375) | v1_xboole_0('#skF_2'(A_375)) | ~v3_tex_2('#skF_5', A_375) | v1_xboole_0(u1_struct_0(A_375)) | ~l1_pre_topc(A_375) | ~v2_pre_topc(A_375) | v2_struct_0(A_375) | v1_xboole_0('#skF_2'(A_375)))), inference(negUnitSimplification, [status(thm)], [c_101, c_8887])).
% 20.73/12.48  tff(c_59070, plain, (![A_906]: (~v3_tex_2('#skF_5', A_906) | ~l1_pre_topc(A_906) | ~v2_pre_topc(A_906) | v2_struct_0(A_906) | v1_xboole_0('#skF_2'(A_906)) | v1_xboole_0(u1_struct_0(A_906)))), inference(factorization, [status(thm), theory('equality')], [c_8937])).
% 20.73/12.48  tff(c_110, plain, (![C_52, A_53, B_54]: (r2_hidden(C_52, A_53) | ~r2_hidden(C_52, B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 20.73/12.48  tff(c_157, plain, (![A_67, A_68]: (r2_hidden('#skF_1'(A_67), A_68) | ~m1_subset_1(A_67, k1_zfmisc_1(A_68)) | v1_xboole_0(A_67))), inference(resolution, [status(thm)], [c_4, c_110])).
% 20.73/12.48  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 20.73/12.48  tff(c_168, plain, (![A_68, A_67]: (~v1_xboole_0(A_68) | ~m1_subset_1(A_67, k1_zfmisc_1(A_68)) | v1_xboole_0(A_67))), inference(resolution, [status(thm)], [c_157, c_2])).
% 20.73/12.48  tff(c_188, plain, (![A_71]: (~v1_xboole_0(u1_struct_0(A_71)) | v1_xboole_0('#skF_2'(A_71)) | ~l1_pre_topc(A_71) | ~v2_pre_topc(A_71) | v2_struct_0(A_71))), inference(resolution, [status(thm)], [c_179, c_168])).
% 20.73/12.48  tff(c_59092, plain, (![A_907]: (~v3_tex_2('#skF_5', A_907) | ~l1_pre_topc(A_907) | ~v2_pre_topc(A_907) | v2_struct_0(A_907) | v1_xboole_0('#skF_2'(A_907)))), inference(resolution, [status(thm)], [c_59070, c_188])).
% 20.73/12.48  tff(c_22, plain, (![A_18]: (~v1_xboole_0('#skF_2'(A_18)) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_72])).
% 20.73/12.48  tff(c_59105, plain, (![A_908]: (~v3_tex_2('#skF_5', A_908) | ~l1_pre_topc(A_908) | ~v2_pre_topc(A_908) | v2_struct_0(A_908))), inference(resolution, [status(thm)], [c_59092, c_22])).
% 20.73/12.48  tff(c_59111, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_59105])).
% 20.73/12.48  tff(c_59115, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_59111])).
% 20.73/12.48  tff(c_59117, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_59115])).
% 20.73/12.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.73/12.48  
% 20.73/12.48  Inference rules
% 20.73/12.48  ----------------------
% 20.73/12.48  #Ref     : 0
% 20.73/12.48  #Sup     : 16306
% 20.73/12.48  #Fact    : 6
% 20.73/12.48  #Define  : 0
% 20.73/12.48  #Split   : 15
% 20.73/12.48  #Chain   : 0
% 20.73/12.48  #Close   : 0
% 20.73/12.48  
% 20.73/12.48  Ordering : KBO
% 20.73/12.48  
% 20.73/12.48  Simplification rules
% 20.73/12.48  ----------------------
% 20.73/12.48  #Subsume      : 7431
% 20.73/12.48  #Demod        : 21175
% 20.73/12.48  #Tautology    : 4814
% 20.73/12.48  #SimpNegUnit  : 495
% 20.73/12.48  #BackRed      : 30
% 20.73/12.48  
% 20.73/12.48  #Partial instantiations: 0
% 20.73/12.48  #Strategies tried      : 1
% 20.73/12.48  
% 20.73/12.48  Timing (in seconds)
% 20.73/12.48  ----------------------
% 20.73/12.48  Preprocessing        : 0.33
% 20.73/12.48  Parsing              : 0.18
% 20.73/12.48  CNF conversion       : 0.02
% 20.73/12.48  Main loop            : 11.33
% 20.73/12.48  Inferencing          : 1.71
% 20.73/12.48  Reduction            : 2.76
% 20.73/12.48  Demodulation         : 1.93
% 20.73/12.48  BG Simplification    : 0.19
% 20.73/12.48  Subsumption          : 6.19
% 20.73/12.48  Abstraction          : 0.38
% 20.73/12.48  MUC search           : 0.00
% 20.73/12.48  Cooper               : 0.00
% 20.73/12.48  Total                : 11.69
% 20.73/12.48  Index Insertion      : 0.00
% 20.73/12.48  Index Deletion       : 0.00
% 20.73/12.48  Index Matching       : 0.00
% 20.73/12.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
