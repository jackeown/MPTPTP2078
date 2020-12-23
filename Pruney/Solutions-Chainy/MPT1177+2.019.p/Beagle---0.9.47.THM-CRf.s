%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:57 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 276 expanded)
%              Number of leaves         :   38 ( 118 expanded)
%              Depth                    :   10
%              Number of atoms          :  297 (1178 expanded)
%              Number of equality atoms :   26 (  43 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_xboole_0 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k1_orders_1,type,(
    k1_orders_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(m1_orders_2,type,(
    m1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_216,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
           => ! [C] :
                ( m2_orders_2(C,A,B)
               => ! [D] :
                    ( m2_orders_2(D,A,B)
                   => ( r2_xboole_0(C,D)
                    <=> m1_orders_2(C,A,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_orders_2)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ! [C] :
          ( m2_orders_2(C,A,B)
         => ( v6_orders_2(C,A)
            & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_119,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_orders_2(C,A,B)
             => r1_tarski(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).

tff(f_144,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ~ ( B != k1_xboole_0
                  & m1_orders_2(B,A,C)
                  & m1_orders_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_orders_2)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_163,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( m2_orders_2(C,A,B)
             => r2_hidden(k1_funct_1(B,u1_struct_0(A)),C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_orders_2)).

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_52,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_191,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( m2_orders_2(C,A,B)
             => ! [D] :
                  ( m2_orders_2(D,A,B)
                 => ( C != D
                   => ( m1_orders_2(C,A,D)
                    <=> ~ m1_orders_2(D,A,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_orders_2)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_60,plain,
    ( ~ m1_orders_2('#skF_3','#skF_1','#skF_4')
    | ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_119,plain,(
    ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_44,plain,(
    m2_orders_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_56,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_54,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_52,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_50,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_48,plain,(
    m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_486,plain,(
    ! [C_129,A_130,B_131] :
      ( m1_subset_1(C_129,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ m2_orders_2(C_129,A_130,B_131)
      | ~ m1_orders_1(B_131,k1_orders_1(u1_struct_0(A_130)))
      | ~ l1_orders_2(A_130)
      | ~ v5_orders_2(A_130)
      | ~ v4_orders_2(A_130)
      | ~ v3_orders_2(A_130)
      | v2_struct_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_488,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_486])).

tff(c_491,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_488])).

tff(c_492,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_491])).

tff(c_238,plain,(
    ! [A_96,B_97] :
      ( r2_xboole_0(A_96,B_97)
      | B_97 = A_96
      | ~ r1_tarski(A_96,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_252,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_238,c_119])).

tff(c_259,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_252])).

tff(c_66,plain,
    ( r2_xboole_0('#skF_3','#skF_4')
    | m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_120,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_309,plain,(
    ! [C_102,B_103,A_104] :
      ( r1_tarski(C_102,B_103)
      | ~ m1_orders_2(C_102,A_104,B_103)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_orders_2(A_104)
      | ~ v5_orders_2(A_104)
      | ~ v4_orders_2(A_104)
      | ~ v3_orders_2(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_311,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_120,c_309])).

tff(c_314,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_311])).

tff(c_315,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_259,c_314])).

tff(c_362,plain,(
    ! [C_112,A_113,B_114] :
      ( m1_subset_1(C_112,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ m2_orders_2(C_112,A_113,B_114)
      | ~ m1_orders_1(B_114,k1_orders_1(u1_struct_0(A_113)))
      | ~ l1_orders_2(A_113)
      | ~ v5_orders_2(A_113)
      | ~ v4_orders_2(A_113)
      | ~ v3_orders_2(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_366,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_362])).

tff(c_373,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_366])).

tff(c_375,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_315,c_373])).

tff(c_376,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_385,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_120])).

tff(c_535,plain,(
    ! [C_145,A_146,B_147] :
      ( ~ m1_orders_2(C_145,A_146,B_147)
      | ~ m1_orders_2(B_147,A_146,C_145)
      | k1_xboole_0 = B_147
      | ~ m1_subset_1(C_145,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ l1_orders_2(A_146)
      | ~ v5_orders_2(A_146)
      | ~ v4_orders_2(A_146)
      | ~ v3_orders_2(A_146)
      | v2_struct_0(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_537,plain,
    ( ~ m1_orders_2('#skF_4','#skF_1','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_385,c_535])).

tff(c_540,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_492,c_385,c_537])).

tff(c_541,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_540])).

tff(c_14,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_121,plain,(
    ! [A_85,B_86] :
      ( k4_xboole_0(A_85,B_86) = k1_xboole_0
      | ~ r1_tarski(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_135,plain,(
    ! [B_87] : k4_xboole_0(B_87,B_87) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_121])).

tff(c_20,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_143,plain,(
    ! [B_87] : r1_tarski(k1_xboole_0,B_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_20])).

tff(c_500,plain,(
    ! [B_135,A_136,C_137] :
      ( r2_hidden(k1_funct_1(B_135,u1_struct_0(A_136)),C_137)
      | ~ m2_orders_2(C_137,A_136,B_135)
      | ~ m1_orders_1(B_135,k1_orders_1(u1_struct_0(A_136)))
      | ~ l1_orders_2(A_136)
      | ~ v5_orders_2(A_136)
      | ~ v4_orders_2(A_136)
      | ~ v3_orders_2(A_136)
      | v2_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_26,plain,(
    ! [B_15,A_14] :
      ( ~ r1_tarski(B_15,A_14)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_505,plain,(
    ! [C_138,B_139,A_140] :
      ( ~ r1_tarski(C_138,k1_funct_1(B_139,u1_struct_0(A_140)))
      | ~ m2_orders_2(C_138,A_140,B_139)
      | ~ m1_orders_1(B_139,k1_orders_1(u1_struct_0(A_140)))
      | ~ l1_orders_2(A_140)
      | ~ v5_orders_2(A_140)
      | ~ v4_orders_2(A_140)
      | ~ v3_orders_2(A_140)
      | v2_struct_0(A_140) ) ),
    inference(resolution,[status(thm)],[c_500,c_26])).

tff(c_526,plain,(
    ! [A_141,B_142] :
      ( ~ m2_orders_2(k1_xboole_0,A_141,B_142)
      | ~ m1_orders_1(B_142,k1_orders_1(u1_struct_0(A_141)))
      | ~ l1_orders_2(A_141)
      | ~ v5_orders_2(A_141)
      | ~ v4_orders_2(A_141)
      | ~ v3_orders_2(A_141)
      | v2_struct_0(A_141) ) ),
    inference(resolution,[status(thm)],[c_143,c_505])).

tff(c_529,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_1','#skF_2')
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_526])).

tff(c_532,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_529])).

tff(c_533,plain,(
    ~ m2_orders_2(k1_xboole_0,'#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_532])).

tff(c_543,plain,(
    ~ m2_orders_2('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_533])).

tff(c_559,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_543])).

tff(c_560,plain,(
    r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_562,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_560])).

tff(c_564,plain,(
    r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_22,plain,(
    ! [B_12,A_11] :
      ( ~ r2_xboole_0(B_12,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_584,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_564,c_22])).

tff(c_46,plain,(
    m2_orders_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_850,plain,(
    ! [C_175,A_176,B_177] :
      ( m1_subset_1(C_175,k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ m2_orders_2(C_175,A_176,B_177)
      | ~ m1_orders_1(B_177,k1_orders_1(u1_struct_0(A_176)))
      | ~ l1_orders_2(A_176)
      | ~ v5_orders_2(A_176)
      | ~ v4_orders_2(A_176)
      | ~ v3_orders_2(A_176)
      | v2_struct_0(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_852,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_850])).

tff(c_857,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_852])).

tff(c_858,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_857])).

tff(c_586,plain,(
    ! [A_148,B_149] :
      ( k4_xboole_0(A_148,B_149) = k1_xboole_0
      | ~ r1_tarski(A_148,B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_603,plain,(
    ! [B_6] : k4_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_586])).

tff(c_563,plain,(
    ~ m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_927,plain,(
    ! [C_201,A_202,D_203,B_204] :
      ( m1_orders_2(C_201,A_202,D_203)
      | m1_orders_2(D_203,A_202,C_201)
      | D_203 = C_201
      | ~ m2_orders_2(D_203,A_202,B_204)
      | ~ m2_orders_2(C_201,A_202,B_204)
      | ~ m1_orders_1(B_204,k1_orders_1(u1_struct_0(A_202)))
      | ~ l1_orders_2(A_202)
      | ~ v5_orders_2(A_202)
      | ~ v4_orders_2(A_202)
      | ~ v3_orders_2(A_202)
      | v2_struct_0(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_931,plain,(
    ! [C_201] :
      ( m1_orders_2(C_201,'#skF_1','#skF_4')
      | m1_orders_2('#skF_4','#skF_1',C_201)
      | C_201 = '#skF_4'
      | ~ m2_orders_2(C_201,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_927])).

tff(c_938,plain,(
    ! [C_201] :
      ( m1_orders_2(C_201,'#skF_1','#skF_4')
      | m1_orders_2('#skF_4','#skF_1',C_201)
      | C_201 = '#skF_4'
      | ~ m2_orders_2(C_201,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_931])).

tff(c_944,plain,(
    ! [C_206] :
      ( m1_orders_2(C_206,'#skF_1','#skF_4')
      | m1_orders_2('#skF_4','#skF_1',C_206)
      | C_206 = '#skF_4'
      | ~ m2_orders_2(C_206,'#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_938])).

tff(c_947,plain,
    ( m1_orders_2('#skF_3','#skF_1','#skF_4')
    | m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_944])).

tff(c_953,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_563,c_947])).

tff(c_956,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_953])).

tff(c_643,plain,(
    ! [A_152,B_153] :
      ( r1_tarski(A_152,B_153)
      | k4_xboole_0(A_152,B_153) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_655,plain,(
    k4_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_643,c_584])).

tff(c_972,plain,(
    k4_xboole_0('#skF_4','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_956,c_655])).

tff(c_983,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_603,c_972])).

tff(c_984,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_953])).

tff(c_34,plain,(
    ! [C_30,B_28,A_24] :
      ( r1_tarski(C_30,B_28)
      | ~ m1_orders_2(C_30,A_24,B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_orders_2(A_24)
      | ~ v5_orders_2(A_24)
      | ~ v4_orders_2(A_24)
      | ~ v3_orders_2(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_991,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_984,c_34])).

tff(c_1002,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_858,c_991])).

tff(c_1004,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_584,c_1002])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:30:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.56  
% 3.29/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.56  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_xboole_0 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.29/1.56  
% 3.29/1.56  %Foreground sorts:
% 3.29/1.56  
% 3.29/1.56  
% 3.29/1.56  %Background operators:
% 3.29/1.56  
% 3.29/1.56  
% 3.29/1.56  %Foreground operators:
% 3.29/1.56  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.29/1.56  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.29/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.29/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.29/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.29/1.56  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 3.29/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.29/1.56  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 3.29/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.29/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.29/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.29/1.56  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.29/1.56  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.29/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.29/1.56  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.29/1.56  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.29/1.56  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.29/1.56  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 3.29/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.56  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 3.29/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.29/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.56  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 3.29/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.29/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.29/1.56  
% 3.29/1.58  tff(f_216, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_orders_2)).
% 3.29/1.58  tff(f_100, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 3.29/1.58  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.29/1.58  tff(f_119, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_orders_2)).
% 3.29/1.58  tff(f_144, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_orders_2)).
% 3.29/1.58  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.29/1.58  tff(f_45, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.29/1.58  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.29/1.58  tff(f_163, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_orders_2)).
% 3.29/1.58  tff(f_62, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.29/1.58  tff(f_52, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_xboole_1)).
% 3.29/1.58  tff(f_191, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_orders_2)).
% 3.29/1.58  tff(c_58, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.29/1.58  tff(c_60, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4') | ~r2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.29/1.58  tff(c_119, plain, (~r2_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_60])).
% 3.29/1.58  tff(c_44, plain, (m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.29/1.58  tff(c_56, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.29/1.58  tff(c_54, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.29/1.58  tff(c_52, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.29/1.58  tff(c_50, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.29/1.58  tff(c_48, plain, (m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.29/1.58  tff(c_486, plain, (![C_129, A_130, B_131]: (m1_subset_1(C_129, k1_zfmisc_1(u1_struct_0(A_130))) | ~m2_orders_2(C_129, A_130, B_131) | ~m1_orders_1(B_131, k1_orders_1(u1_struct_0(A_130))) | ~l1_orders_2(A_130) | ~v5_orders_2(A_130) | ~v4_orders_2(A_130) | ~v3_orders_2(A_130) | v2_struct_0(A_130))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.29/1.58  tff(c_488, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_486])).
% 3.29/1.58  tff(c_491, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_488])).
% 3.29/1.58  tff(c_492, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_58, c_491])).
% 3.29/1.58  tff(c_238, plain, (![A_96, B_97]: (r2_xboole_0(A_96, B_97) | B_97=A_96 | ~r1_tarski(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.29/1.58  tff(c_252, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_238, c_119])).
% 3.29/1.58  tff(c_259, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_252])).
% 3.29/1.58  tff(c_66, plain, (r2_xboole_0('#skF_3', '#skF_4') | m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.29/1.58  tff(c_120, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(splitLeft, [status(thm)], [c_66])).
% 3.29/1.58  tff(c_309, plain, (![C_102, B_103, A_104]: (r1_tarski(C_102, B_103) | ~m1_orders_2(C_102, A_104, B_103) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_orders_2(A_104) | ~v5_orders_2(A_104) | ~v4_orders_2(A_104) | ~v3_orders_2(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.29/1.58  tff(c_311, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_120, c_309])).
% 3.29/1.58  tff(c_314, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_311])).
% 3.29/1.58  tff(c_315, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_58, c_259, c_314])).
% 3.29/1.58  tff(c_362, plain, (![C_112, A_113, B_114]: (m1_subset_1(C_112, k1_zfmisc_1(u1_struct_0(A_113))) | ~m2_orders_2(C_112, A_113, B_114) | ~m1_orders_1(B_114, k1_orders_1(u1_struct_0(A_113))) | ~l1_orders_2(A_113) | ~v5_orders_2(A_113) | ~v4_orders_2(A_113) | ~v3_orders_2(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.29/1.58  tff(c_366, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_362])).
% 3.29/1.58  tff(c_373, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_366])).
% 3.29/1.58  tff(c_375, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_315, c_373])).
% 3.29/1.58  tff(c_376, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_252])).
% 3.29/1.58  tff(c_385, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_376, c_120])).
% 3.29/1.58  tff(c_535, plain, (![C_145, A_146, B_147]: (~m1_orders_2(C_145, A_146, B_147) | ~m1_orders_2(B_147, A_146, C_145) | k1_xboole_0=B_147 | ~m1_subset_1(C_145, k1_zfmisc_1(u1_struct_0(A_146))) | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0(A_146))) | ~l1_orders_2(A_146) | ~v5_orders_2(A_146) | ~v4_orders_2(A_146) | ~v3_orders_2(A_146) | v2_struct_0(A_146))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.29/1.58  tff(c_537, plain, (~m1_orders_2('#skF_4', '#skF_1', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_385, c_535])).
% 3.29/1.58  tff(c_540, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_492, c_385, c_537])).
% 3.29/1.58  tff(c_541, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_58, c_540])).
% 3.29/1.58  tff(c_14, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.29/1.58  tff(c_121, plain, (![A_85, B_86]: (k4_xboole_0(A_85, B_86)=k1_xboole_0 | ~r1_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.29/1.58  tff(c_135, plain, (![B_87]: (k4_xboole_0(B_87, B_87)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_121])).
% 3.29/1.58  tff(c_20, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.29/1.58  tff(c_143, plain, (![B_87]: (r1_tarski(k1_xboole_0, B_87))), inference(superposition, [status(thm), theory('equality')], [c_135, c_20])).
% 3.29/1.58  tff(c_500, plain, (![B_135, A_136, C_137]: (r2_hidden(k1_funct_1(B_135, u1_struct_0(A_136)), C_137) | ~m2_orders_2(C_137, A_136, B_135) | ~m1_orders_1(B_135, k1_orders_1(u1_struct_0(A_136))) | ~l1_orders_2(A_136) | ~v5_orders_2(A_136) | ~v4_orders_2(A_136) | ~v3_orders_2(A_136) | v2_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.29/1.58  tff(c_26, plain, (![B_15, A_14]: (~r1_tarski(B_15, A_14) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.29/1.58  tff(c_505, plain, (![C_138, B_139, A_140]: (~r1_tarski(C_138, k1_funct_1(B_139, u1_struct_0(A_140))) | ~m2_orders_2(C_138, A_140, B_139) | ~m1_orders_1(B_139, k1_orders_1(u1_struct_0(A_140))) | ~l1_orders_2(A_140) | ~v5_orders_2(A_140) | ~v4_orders_2(A_140) | ~v3_orders_2(A_140) | v2_struct_0(A_140))), inference(resolution, [status(thm)], [c_500, c_26])).
% 3.29/1.58  tff(c_526, plain, (![A_141, B_142]: (~m2_orders_2(k1_xboole_0, A_141, B_142) | ~m1_orders_1(B_142, k1_orders_1(u1_struct_0(A_141))) | ~l1_orders_2(A_141) | ~v5_orders_2(A_141) | ~v4_orders_2(A_141) | ~v3_orders_2(A_141) | v2_struct_0(A_141))), inference(resolution, [status(thm)], [c_143, c_505])).
% 3.29/1.58  tff(c_529, plain, (~m2_orders_2(k1_xboole_0, '#skF_1', '#skF_2') | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_526])).
% 3.29/1.58  tff(c_532, plain, (~m2_orders_2(k1_xboole_0, '#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_529])).
% 3.29/1.58  tff(c_533, plain, (~m2_orders_2(k1_xboole_0, '#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_58, c_532])).
% 3.29/1.58  tff(c_543, plain, (~m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_541, c_533])).
% 3.29/1.58  tff(c_559, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_543])).
% 3.29/1.58  tff(c_560, plain, (r2_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_66])).
% 3.29/1.58  tff(c_562, plain, $false, inference(negUnitSimplification, [status(thm)], [c_119, c_560])).
% 3.29/1.58  tff(c_564, plain, (r2_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_60])).
% 3.29/1.58  tff(c_22, plain, (![B_12, A_11]: (~r2_xboole_0(B_12, A_11) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.29/1.58  tff(c_584, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_564, c_22])).
% 3.29/1.58  tff(c_46, plain, (m2_orders_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.29/1.58  tff(c_850, plain, (![C_175, A_176, B_177]: (m1_subset_1(C_175, k1_zfmisc_1(u1_struct_0(A_176))) | ~m2_orders_2(C_175, A_176, B_177) | ~m1_orders_1(B_177, k1_orders_1(u1_struct_0(A_176))) | ~l1_orders_2(A_176) | ~v5_orders_2(A_176) | ~v4_orders_2(A_176) | ~v3_orders_2(A_176) | v2_struct_0(A_176))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.29/1.58  tff(c_852, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_850])).
% 3.29/1.58  tff(c_857, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_852])).
% 3.29/1.58  tff(c_858, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_58, c_857])).
% 3.29/1.58  tff(c_586, plain, (![A_148, B_149]: (k4_xboole_0(A_148, B_149)=k1_xboole_0 | ~r1_tarski(A_148, B_149))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.29/1.58  tff(c_603, plain, (![B_6]: (k4_xboole_0(B_6, B_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_586])).
% 3.29/1.58  tff(c_563, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(splitRight, [status(thm)], [c_60])).
% 3.29/1.58  tff(c_927, plain, (![C_201, A_202, D_203, B_204]: (m1_orders_2(C_201, A_202, D_203) | m1_orders_2(D_203, A_202, C_201) | D_203=C_201 | ~m2_orders_2(D_203, A_202, B_204) | ~m2_orders_2(C_201, A_202, B_204) | ~m1_orders_1(B_204, k1_orders_1(u1_struct_0(A_202))) | ~l1_orders_2(A_202) | ~v5_orders_2(A_202) | ~v4_orders_2(A_202) | ~v3_orders_2(A_202) | v2_struct_0(A_202))), inference(cnfTransformation, [status(thm)], [f_191])).
% 3.29/1.58  tff(c_931, plain, (![C_201]: (m1_orders_2(C_201, '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', C_201) | C_201='#skF_4' | ~m2_orders_2(C_201, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_927])).
% 3.29/1.58  tff(c_938, plain, (![C_201]: (m1_orders_2(C_201, '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', C_201) | C_201='#skF_4' | ~m2_orders_2(C_201, '#skF_1', '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_931])).
% 3.29/1.58  tff(c_944, plain, (![C_206]: (m1_orders_2(C_206, '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', C_206) | C_206='#skF_4' | ~m2_orders_2(C_206, '#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_58, c_938])).
% 3.29/1.58  tff(c_947, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_46, c_944])).
% 3.29/1.58  tff(c_953, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_563, c_947])).
% 3.29/1.58  tff(c_956, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_953])).
% 3.29/1.58  tff(c_643, plain, (![A_152, B_153]: (r1_tarski(A_152, B_153) | k4_xboole_0(A_152, B_153)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.29/1.58  tff(c_655, plain, (k4_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_643, c_584])).
% 3.29/1.58  tff(c_972, plain, (k4_xboole_0('#skF_4', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_956, c_655])).
% 3.29/1.58  tff(c_983, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_603, c_972])).
% 3.29/1.58  tff(c_984, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_953])).
% 3.29/1.58  tff(c_34, plain, (![C_30, B_28, A_24]: (r1_tarski(C_30, B_28) | ~m1_orders_2(C_30, A_24, B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_orders_2(A_24) | ~v5_orders_2(A_24) | ~v4_orders_2(A_24) | ~v3_orders_2(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.29/1.58  tff(c_991, plain, (r1_tarski('#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_984, c_34])).
% 3.29/1.58  tff(c_1002, plain, (r1_tarski('#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_858, c_991])).
% 3.29/1.58  tff(c_1004, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_584, c_1002])).
% 3.29/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.58  
% 3.29/1.58  Inference rules
% 3.29/1.58  ----------------------
% 3.29/1.58  #Ref     : 0
% 3.29/1.58  #Sup     : 176
% 3.29/1.58  #Fact    : 0
% 3.29/1.58  #Define  : 0
% 3.29/1.58  #Split   : 5
% 3.29/1.58  #Chain   : 0
% 3.29/1.58  #Close   : 0
% 3.29/1.58  
% 3.29/1.58  Ordering : KBO
% 3.29/1.58  
% 3.29/1.58  Simplification rules
% 3.29/1.58  ----------------------
% 3.29/1.58  #Subsume      : 41
% 3.29/1.58  #Demod        : 224
% 3.29/1.58  #Tautology    : 88
% 3.29/1.58  #SimpNegUnit  : 27
% 3.29/1.58  #BackRed      : 28
% 3.29/1.58  
% 3.29/1.58  #Partial instantiations: 0
% 3.29/1.58  #Strategies tried      : 1
% 3.29/1.58  
% 3.29/1.58  Timing (in seconds)
% 3.29/1.58  ----------------------
% 3.29/1.59  Preprocessing        : 0.37
% 3.29/1.59  Parsing              : 0.20
% 3.29/1.59  CNF conversion       : 0.03
% 3.29/1.59  Main loop            : 0.39
% 3.29/1.59  Inferencing          : 0.14
% 3.29/1.59  Reduction            : 0.13
% 3.29/1.59  Demodulation         : 0.09
% 3.29/1.59  BG Simplification    : 0.02
% 3.29/1.59  Subsumption          : 0.07
% 3.29/1.59  Abstraction          : 0.02
% 3.29/1.59  MUC search           : 0.00
% 3.29/1.59  Cooper               : 0.00
% 3.29/1.59  Total                : 0.80
% 3.29/1.59  Index Insertion      : 0.00
% 3.29/1.59  Index Deletion       : 0.00
% 3.29/1.59  Index Matching       : 0.00
% 3.29/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
