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
% DateTime   : Thu Dec  3 10:30:22 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 413 expanded)
%              Number of leaves         :   38 ( 150 expanded)
%              Depth                    :   18
%              Number of atoms          :  215 (1275 expanded)
%              Number of equality atoms :   25 ( 211 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_171,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r1_xboole_0(k2_pre_topc(A,k6_domain_1(u1_struct_0(A),B)),k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C)))
                  | k2_pre_topc(A,k6_domain_1(u1_struct_0(A),B)) = k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tex_2)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_132,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_xboole_0(B,C)
                  & v3_pre_topc(B,A) )
               => r1_xboole_0(B,k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_tsep_1)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_116,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(f_151,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(B,k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C)))
               => k2_pre_topc(A,k6_domain_1(u1_struct_0(A),B)) = k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tex_2)).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_14,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_74,plain,(
    ! [A_57,B_58] :
      ( k6_domain_1(A_57,B_58) = k1_tarski(B_58)
      | ~ m1_subset_1(B_58,A_57)
      | v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_81,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_74])).

tff(c_83,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_16,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(u1_struct_0(A_12))
      | ~ l1_struct_0(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_86,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_83,c_16])).

tff(c_89,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_86])).

tff(c_92,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_89])).

tff(c_96,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_92])).

tff(c_98,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_82,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_74])).

tff(c_105,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_82])).

tff(c_97,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_40,plain,(
    k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5')) != k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_100,plain,(
    k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')) != k2_pre_topc('#skF_3',k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_40])).

tff(c_143,plain,(
    k2_pre_topc('#skF_3',k1_tarski('#skF_5')) != k2_pre_topc('#skF_3',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_100])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r1_xboole_0(k1_tarski(A_7),B_8)
      | r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_69,plain,(
    ! [A_53,B_54,C_55] :
      ( ~ r1_xboole_0(A_53,B_54)
      | ~ r2_hidden(C_55,B_54)
      | ~ r2_hidden(C_55,A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_111,plain,(
    ! [C_60,B_61,A_62] :
      ( ~ r2_hidden(C_60,B_61)
      | ~ r2_hidden(C_60,k1_tarski(A_62))
      | r2_hidden(A_62,B_61) ) ),
    inference(resolution,[status(thm)],[c_10,c_69])).

tff(c_150,plain,(
    ! [A_66,B_67,A_68] :
      ( ~ r2_hidden('#skF_1'(A_66,B_67),k1_tarski(A_68))
      | r2_hidden(A_68,A_66)
      | r1_xboole_0(A_66,B_67) ) ),
    inference(resolution,[status(thm)],[c_6,c_111])).

tff(c_159,plain,(
    ! [A_68,A_1] :
      ( r2_hidden(A_68,A_1)
      | r1_xboole_0(A_1,k1_tarski(A_68)) ) ),
    inference(resolution,[status(thm)],[c_4,c_150])).

tff(c_52,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_118,plain,(
    ! [A_63,B_64] :
      ( m1_subset_1(k6_domain_1(A_63,B_64),k1_zfmisc_1(A_63))
      | ~ m1_subset_1(B_64,A_63)
      | v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_124,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_118])).

tff(c_130,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_124])).

tff(c_131,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_130])).

tff(c_389,plain,(
    ! [A_109,B_110] :
      ( k2_pre_topc(A_109,k2_pre_topc(A_109,B_110)) = k2_pre_topc(A_109,B_110)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_397,plain,
    ( k2_pre_topc('#skF_3',k2_pre_topc('#skF_3',k1_tarski('#skF_4'))) = k2_pre_topc('#skF_3',k1_tarski('#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_131,c_389])).

tff(c_408,plain,(
    k2_pre_topc('#skF_3',k2_pre_topc('#skF_3',k1_tarski('#skF_4'))) = k2_pre_topc('#skF_3',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_397])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k2_pre_topc(A_9,B_10),k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_127,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_118])).

tff(c_133,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_127])).

tff(c_134,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_133])).

tff(c_515,plain,(
    ! [B_118,A_119,C_120] :
      ( r1_xboole_0(B_118,k2_pre_topc(A_119,C_120))
      | ~ v3_pre_topc(B_118,A_119)
      | ~ r1_xboole_0(B_118,C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_521,plain,(
    ! [B_118] :
      ( r1_xboole_0(B_118,k2_pre_topc('#skF_3',k1_tarski('#skF_5')))
      | ~ v3_pre_topc(B_118,'#skF_3')
      | ~ r1_xboole_0(B_118,k1_tarski('#skF_5'))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_134,c_515])).

tff(c_566,plain,(
    ! [B_123] :
      ( r1_xboole_0(B_123,k2_pre_topc('#skF_3',k1_tarski('#skF_5')))
      | ~ v3_pre_topc(B_123,'#skF_3')
      | ~ r1_xboole_0(B_123,k1_tarski('#skF_5'))
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_521])).

tff(c_42,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')),k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_99,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')),k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_42])).

tff(c_144,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_99])).

tff(c_572,plain,
    ( ~ v3_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),'#skF_3')
    | ~ r1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_tarski('#skF_5'))
    | ~ m1_subset_1(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_566,c_144])).

tff(c_578,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_572])).

tff(c_581,plain,
    ( ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_578])).

tff(c_585,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_131,c_581])).

tff(c_587,plain,(
    m1_subset_1(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_572])).

tff(c_20,plain,(
    ! [B_17,A_15] :
      ( v4_pre_topc(B_17,A_15)
      | k2_pre_topc(A_15,B_17) != B_17
      | ~ v2_pre_topc(A_15)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_595,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),'#skF_3')
    | k2_pre_topc('#skF_3',k2_pre_topc('#skF_3',k1_tarski('#skF_4'))) != k2_pre_topc('#skF_3',k1_tarski('#skF_4'))
    | ~ v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_587,c_20])).

tff(c_612,plain,(
    v4_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_52,c_408,c_595])).

tff(c_50,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_28,plain,(
    ! [B_25,A_22] :
      ( v3_pre_topc(B_25,A_22)
      | ~ v4_pre_topc(B_25,A_22)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ v3_tdlat_3(A_22)
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_592,plain,
    ( v3_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),'#skF_3')
    | ~ v4_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),'#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_587,c_28])).

tff(c_609,plain,
    ( v3_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),'#skF_3')
    | ~ v4_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_50,c_592])).

tff(c_622,plain,(
    v3_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_609])).

tff(c_586,plain,
    ( ~ r1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_tarski('#skF_5'))
    | ~ v3_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_572])).

tff(c_624,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_586])).

tff(c_632,plain,(
    r2_hidden('#skF_5',k2_pre_topc('#skF_3',k1_tarski('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_159,c_624])).

tff(c_633,plain,(
    ! [A_125,C_126,B_127] :
      ( k2_pre_topc(A_125,k6_domain_1(u1_struct_0(A_125),C_126)) = k2_pre_topc(A_125,k6_domain_1(u1_struct_0(A_125),B_127))
      | ~ r2_hidden(B_127,k2_pre_topc(A_125,k6_domain_1(u1_struct_0(A_125),C_126)))
      | ~ m1_subset_1(C_126,u1_struct_0(A_125))
      | ~ m1_subset_1(B_127,u1_struct_0(A_125))
      | ~ l1_pre_topc(A_125)
      | ~ v3_tdlat_3(A_125)
      | ~ v2_pre_topc(A_125)
      | v2_struct_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_636,plain,(
    ! [B_127] :
      ( k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),B_127)) = k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))
      | ~ r2_hidden(B_127,k2_pre_topc('#skF_3',k1_tarski('#skF_4')))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_127,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_633])).

tff(c_649,plain,(
    ! [B_127] :
      ( k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),B_127)) = k2_pre_topc('#skF_3',k1_tarski('#skF_4'))
      | ~ r2_hidden(B_127,k2_pre_topc('#skF_3',k1_tarski('#skF_4')))
      | ~ m1_subset_1(B_127,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_105,c_636])).

tff(c_718,plain,(
    ! [B_131] :
      ( k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),B_131)) = k2_pre_topc('#skF_3',k1_tarski('#skF_4'))
      | ~ r2_hidden(B_131,k2_pre_topc('#skF_3',k1_tarski('#skF_4')))
      | ~ m1_subset_1(B_131,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_649])).

tff(c_721,plain,
    ( k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5')) = k2_pre_topc('#skF_3',k1_tarski('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_632,c_718])).

tff(c_732,plain,(
    k2_pre_topc('#skF_3',k1_tarski('#skF_5')) = k2_pre_topc('#skF_3',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_97,c_721])).

tff(c_734,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_732])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:58:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.46  
% 3.13/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.46  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 3.13/1.46  
% 3.13/1.46  %Foreground sorts:
% 3.13/1.46  
% 3.13/1.46  
% 3.13/1.46  %Background operators:
% 3.13/1.46  
% 3.13/1.46  
% 3.13/1.46  %Foreground operators:
% 3.13/1.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.13/1.46  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.13/1.46  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.13/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.13/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.13/1.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.13/1.46  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.13/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.13/1.46  tff('#skF_5', type, '#skF_5': $i).
% 3.13/1.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.13/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.13/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.13/1.46  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.13/1.46  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.13/1.46  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.13/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.46  tff('#skF_4', type, '#skF_4': $i).
% 3.13/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.46  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.13/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.13/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.13/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.13/1.46  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.13/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.13/1.46  
% 3.13/1.48  tff(f_171, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_xboole_0(k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)), k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) | (k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tex_2)).
% 3.13/1.48  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.13/1.48  tff(f_103, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.13/1.48  tff(f_68, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.13/1.48  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.13/1.48  tff(f_50, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.13/1.48  tff(f_96, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.13/1.48  tff(f_74, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k2_pre_topc(A, k2_pre_topc(A, B)) = k2_pre_topc(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 3.13/1.48  tff(f_56, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 3.13/1.48  tff(f_132, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_xboole_0(B, C) & v3_pre_topc(B, A)) => r1_xboole_0(B, k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_tsep_1)).
% 3.13/1.48  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.13/1.48  tff(f_116, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tdlat_3)).
% 3.13/1.48  tff(f_151, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) => (k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tex_2)).
% 3.13/1.48  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.13/1.48  tff(c_14, plain, (![A_11]: (l1_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.13/1.48  tff(c_54, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.13/1.48  tff(c_44, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.13/1.48  tff(c_74, plain, (![A_57, B_58]: (k6_domain_1(A_57, B_58)=k1_tarski(B_58) | ~m1_subset_1(B_58, A_57) | v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.13/1.48  tff(c_81, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_74])).
% 3.13/1.48  tff(c_83, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_81])).
% 3.13/1.48  tff(c_16, plain, (![A_12]: (~v1_xboole_0(u1_struct_0(A_12)) | ~l1_struct_0(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.13/1.48  tff(c_86, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_83, c_16])).
% 3.13/1.48  tff(c_89, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_86])).
% 3.13/1.48  tff(c_92, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14, c_89])).
% 3.13/1.48  tff(c_96, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_92])).
% 3.13/1.48  tff(c_98, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_81])).
% 3.13/1.48  tff(c_46, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.13/1.48  tff(c_82, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_74])).
% 3.13/1.48  tff(c_105, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_98, c_82])).
% 3.13/1.48  tff(c_97, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_81])).
% 3.13/1.48  tff(c_40, plain, (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5'))!=k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.13/1.48  tff(c_100, plain, (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'))!=k2_pre_topc('#skF_3', k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_40])).
% 3.13/1.48  tff(c_143, plain, (k2_pre_topc('#skF_3', k1_tarski('#skF_5'))!=k2_pre_topc('#skF_3', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_100])).
% 3.13/1.48  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.13/1.48  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.13/1.48  tff(c_10, plain, (![A_7, B_8]: (r1_xboole_0(k1_tarski(A_7), B_8) | r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.13/1.48  tff(c_69, plain, (![A_53, B_54, C_55]: (~r1_xboole_0(A_53, B_54) | ~r2_hidden(C_55, B_54) | ~r2_hidden(C_55, A_53))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.13/1.48  tff(c_111, plain, (![C_60, B_61, A_62]: (~r2_hidden(C_60, B_61) | ~r2_hidden(C_60, k1_tarski(A_62)) | r2_hidden(A_62, B_61))), inference(resolution, [status(thm)], [c_10, c_69])).
% 3.13/1.48  tff(c_150, plain, (![A_66, B_67, A_68]: (~r2_hidden('#skF_1'(A_66, B_67), k1_tarski(A_68)) | r2_hidden(A_68, A_66) | r1_xboole_0(A_66, B_67))), inference(resolution, [status(thm)], [c_6, c_111])).
% 3.13/1.48  tff(c_159, plain, (![A_68, A_1]: (r2_hidden(A_68, A_1) | r1_xboole_0(A_1, k1_tarski(A_68)))), inference(resolution, [status(thm)], [c_4, c_150])).
% 3.13/1.48  tff(c_52, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.13/1.48  tff(c_118, plain, (![A_63, B_64]: (m1_subset_1(k6_domain_1(A_63, B_64), k1_zfmisc_1(A_63)) | ~m1_subset_1(B_64, A_63) | v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.13/1.48  tff(c_124, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_105, c_118])).
% 3.13/1.48  tff(c_130, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_124])).
% 3.13/1.48  tff(c_131, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_98, c_130])).
% 3.13/1.48  tff(c_389, plain, (![A_109, B_110]: (k2_pre_topc(A_109, k2_pre_topc(A_109, B_110))=k2_pre_topc(A_109, B_110) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.13/1.48  tff(c_397, plain, (k2_pre_topc('#skF_3', k2_pre_topc('#skF_3', k1_tarski('#skF_4')))=k2_pre_topc('#skF_3', k1_tarski('#skF_4')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_131, c_389])).
% 3.13/1.48  tff(c_408, plain, (k2_pre_topc('#skF_3', k2_pre_topc('#skF_3', k1_tarski('#skF_4')))=k2_pre_topc('#skF_3', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_397])).
% 3.13/1.48  tff(c_12, plain, (![A_9, B_10]: (m1_subset_1(k2_pre_topc(A_9, B_10), k1_zfmisc_1(u1_struct_0(A_9))) | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.13/1.48  tff(c_127, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_97, c_118])).
% 3.13/1.48  tff(c_133, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_127])).
% 3.13/1.48  tff(c_134, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_98, c_133])).
% 3.13/1.48  tff(c_515, plain, (![B_118, A_119, C_120]: (r1_xboole_0(B_118, k2_pre_topc(A_119, C_120)) | ~v3_pre_topc(B_118, A_119) | ~r1_xboole_0(B_118, C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(u1_struct_0(A_119))) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119) | ~v2_pre_topc(A_119))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.13/1.48  tff(c_521, plain, (![B_118]: (r1_xboole_0(B_118, k2_pre_topc('#skF_3', k1_tarski('#skF_5'))) | ~v3_pre_topc(B_118, '#skF_3') | ~r1_xboole_0(B_118, k1_tarski('#skF_5')) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_134, c_515])).
% 3.13/1.48  tff(c_566, plain, (![B_123]: (r1_xboole_0(B_123, k2_pre_topc('#skF_3', k1_tarski('#skF_5'))) | ~v3_pre_topc(B_123, '#skF_3') | ~r1_xboole_0(B_123, k1_tarski('#skF_5')) | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_521])).
% 3.13/1.48  tff(c_42, plain, (~r1_xboole_0(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')), k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.13/1.48  tff(c_99, plain, (~r1_xboole_0(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')), k2_pre_topc('#skF_3', k1_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_42])).
% 3.13/1.48  tff(c_144, plain, (~r1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k2_pre_topc('#skF_3', k1_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_99])).
% 3.13/1.48  tff(c_572, plain, (~v3_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), '#skF_3') | ~r1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_tarski('#skF_5')) | ~m1_subset_1(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_566, c_144])).
% 3.13/1.48  tff(c_578, plain, (~m1_subset_1(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_572])).
% 3.13/1.48  tff(c_581, plain, (~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_12, c_578])).
% 3.13/1.48  tff(c_585, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_131, c_581])).
% 3.13/1.48  tff(c_587, plain, (m1_subset_1(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_572])).
% 3.13/1.48  tff(c_20, plain, (![B_17, A_15]: (v4_pre_topc(B_17, A_15) | k2_pre_topc(A_15, B_17)!=B_17 | ~v2_pre_topc(A_15) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.13/1.48  tff(c_595, plain, (v4_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), '#skF_3') | k2_pre_topc('#skF_3', k2_pre_topc('#skF_3', k1_tarski('#skF_4')))!=k2_pre_topc('#skF_3', k1_tarski('#skF_4')) | ~v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_587, c_20])).
% 3.13/1.48  tff(c_612, plain, (v4_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_52, c_408, c_595])).
% 3.13/1.48  tff(c_50, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.13/1.48  tff(c_28, plain, (![B_25, A_22]: (v3_pre_topc(B_25, A_22) | ~v4_pre_topc(B_25, A_22) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_22))) | ~v3_tdlat_3(A_22) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.13/1.48  tff(c_592, plain, (v3_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), '#skF_3') | ~v4_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), '#skF_3') | ~v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_587, c_28])).
% 3.13/1.48  tff(c_609, plain, (v3_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), '#skF_3') | ~v4_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_50, c_592])).
% 3.13/1.48  tff(c_622, plain, (v3_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_612, c_609])).
% 3.13/1.48  tff(c_586, plain, (~r1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_tarski('#skF_5')) | ~v3_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), '#skF_3')), inference(splitRight, [status(thm)], [c_572])).
% 3.13/1.48  tff(c_624, plain, (~r1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_622, c_586])).
% 3.13/1.48  tff(c_632, plain, (r2_hidden('#skF_5', k2_pre_topc('#skF_3', k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_159, c_624])).
% 3.13/1.48  tff(c_633, plain, (![A_125, C_126, B_127]: (k2_pre_topc(A_125, k6_domain_1(u1_struct_0(A_125), C_126))=k2_pre_topc(A_125, k6_domain_1(u1_struct_0(A_125), B_127)) | ~r2_hidden(B_127, k2_pre_topc(A_125, k6_domain_1(u1_struct_0(A_125), C_126))) | ~m1_subset_1(C_126, u1_struct_0(A_125)) | ~m1_subset_1(B_127, u1_struct_0(A_125)) | ~l1_pre_topc(A_125) | ~v3_tdlat_3(A_125) | ~v2_pre_topc(A_125) | v2_struct_0(A_125))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.13/1.48  tff(c_636, plain, (![B_127]: (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), B_127))=k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')) | ~r2_hidden(B_127, k2_pre_topc('#skF_3', k1_tarski('#skF_4'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1(B_127, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_105, c_633])).
% 3.13/1.48  tff(c_649, plain, (![B_127]: (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), B_127))=k2_pre_topc('#skF_3', k1_tarski('#skF_4')) | ~r2_hidden(B_127, k2_pre_topc('#skF_3', k1_tarski('#skF_4'))) | ~m1_subset_1(B_127, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_105, c_636])).
% 3.13/1.48  tff(c_718, plain, (![B_131]: (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), B_131))=k2_pre_topc('#skF_3', k1_tarski('#skF_4')) | ~r2_hidden(B_131, k2_pre_topc('#skF_3', k1_tarski('#skF_4'))) | ~m1_subset_1(B_131, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_54, c_649])).
% 3.13/1.48  tff(c_721, plain, (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5'))=k2_pre_topc('#skF_3', k1_tarski('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_632, c_718])).
% 3.13/1.48  tff(c_732, plain, (k2_pre_topc('#skF_3', k1_tarski('#skF_5'))=k2_pre_topc('#skF_3', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_97, c_721])).
% 3.13/1.48  tff(c_734, plain, $false, inference(negUnitSimplification, [status(thm)], [c_143, c_732])).
% 3.13/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.48  
% 3.13/1.48  Inference rules
% 3.13/1.48  ----------------------
% 3.13/1.48  #Ref     : 0
% 3.13/1.48  #Sup     : 149
% 3.13/1.48  #Fact    : 0
% 3.13/1.48  #Define  : 0
% 3.13/1.48  #Split   : 5
% 3.13/1.48  #Chain   : 0
% 3.13/1.48  #Close   : 0
% 3.13/1.48  
% 3.13/1.48  Ordering : KBO
% 3.13/1.48  
% 3.13/1.48  Simplification rules
% 3.13/1.48  ----------------------
% 3.13/1.48  #Subsume      : 40
% 3.13/1.48  #Demod        : 68
% 3.13/1.48  #Tautology    : 35
% 3.13/1.48  #SimpNegUnit  : 11
% 3.13/1.48  #BackRed      : 2
% 3.13/1.48  
% 3.13/1.48  #Partial instantiations: 0
% 3.13/1.48  #Strategies tried      : 1
% 3.13/1.48  
% 3.13/1.48  Timing (in seconds)
% 3.13/1.48  ----------------------
% 3.13/1.48  Preprocessing        : 0.34
% 3.13/1.48  Parsing              : 0.18
% 3.13/1.48  CNF conversion       : 0.02
% 3.13/1.48  Main loop            : 0.35
% 3.13/1.48  Inferencing          : 0.13
% 3.13/1.48  Reduction            : 0.10
% 3.13/1.48  Demodulation         : 0.06
% 3.13/1.48  BG Simplification    : 0.02
% 3.13/1.48  Subsumption          : 0.07
% 3.13/1.48  Abstraction          : 0.02
% 3.13/1.48  MUC search           : 0.00
% 3.13/1.48  Cooper               : 0.00
% 3.13/1.48  Total                : 0.74
% 3.13/1.48  Index Insertion      : 0.00
% 3.13/1.48  Index Deletion       : 0.00
% 3.13/1.48  Index Matching       : 0.00
% 3.13/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
