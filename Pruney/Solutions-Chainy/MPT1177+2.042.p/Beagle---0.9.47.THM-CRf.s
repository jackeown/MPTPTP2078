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
% DateTime   : Thu Dec  3 10:20:01 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 318 expanded)
%              Number of leaves         :   36 ( 131 expanded)
%              Depth                    :   11
%              Number of atoms          :  300 (1350 expanded)
%              Number of equality atoms :   37 (  72 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_35,axiom,(
    ! [A,B] : ~ r2_xboole_0(A,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

tff(f_190,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_orders_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_88,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).

tff(f_69,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).

tff(f_114,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ~ ( B != k1_xboole_0
                & m1_orders_2(B,A,B) )
            & ~ ( ~ m1_orders_2(B,A,B)
                & B = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_orders_2)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_137,axiom,(
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
                 => ~ r1_xboole_0(C,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_orders_2)).

tff(f_165,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_orders_2)).

tff(c_8,plain,(
    ! [A_3] : ~ r2_xboole_0(A_3,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_52,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_50,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_48,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_46,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_102,plain,(
    ! [A_81,B_82] :
      ( r2_xboole_0(A_81,B_82)
      | B_82 = A_81
      | ~ r1_tarski(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,
    ( ~ m1_orders_2('#skF_3','#skF_1','#skF_4')
    | ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_79,plain,(
    ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_113,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_79])).

tff(c_119,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_62,plain,
    ( r2_xboole_0('#skF_3','#skF_4')
    | m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_91,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_62])).

tff(c_145,plain,(
    ! [C_90,B_91,A_92] :
      ( r1_tarski(C_90,B_91)
      | ~ m1_orders_2(C_90,A_92,B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_orders_2(A_92)
      | ~ v5_orders_2(A_92)
      | ~ v4_orders_2(A_92)
      | ~ v3_orders_2(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_147,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_91,c_145])).

tff(c_150,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_147])).

tff(c_151,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_119,c_150])).

tff(c_44,plain,(
    m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_40,plain,(
    m2_orders_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_165,plain,(
    ! [C_96,A_97,B_98] :
      ( m1_subset_1(C_96,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ m2_orders_2(C_96,A_97,B_98)
      | ~ m1_orders_1(B_98,k1_orders_1(u1_struct_0(A_97)))
      | ~ l1_orders_2(A_97)
      | ~ v5_orders_2(A_97)
      | ~ v4_orders_2(A_97)
      | ~ v3_orders_2(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_169,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_165])).

tff(c_176,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_169])).

tff(c_178,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_151,c_176])).

tff(c_179,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_181,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_91])).

tff(c_203,plain,(
    ! [B_102,A_103] :
      ( ~ m1_orders_2(B_102,A_103,B_102)
      | k1_xboole_0 = B_102
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_orders_2(A_103)
      | ~ v5_orders_2(A_103)
      | ~ v4_orders_2(A_103)
      | ~ v3_orders_2(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_205,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_181,c_203])).

tff(c_208,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_205])).

tff(c_209,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_208])).

tff(c_210,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_232,plain,(
    ! [C_112,A_113,B_114] :
      ( m1_subset_1(C_112,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ m2_orders_2(C_112,A_113,B_114)
      | ~ m1_orders_1(B_114,k1_orders_1(u1_struct_0(A_113)))
      | ~ l1_orders_2(A_113)
      | ~ v5_orders_2(A_113)
      | ~ v4_orders_2(A_113)
      | ~ v3_orders_2(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_234,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_232])).

tff(c_237,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_234])).

tff(c_239,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_210,c_237])).

tff(c_240,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_14,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_67,plain,(
    ! [A_70,B_71] :
      ( k4_xboole_0(A_70,B_71) = k1_xboole_0
      | ~ r1_tarski(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_71,plain,(
    ! [B_6] : k4_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_67])).

tff(c_246,plain,(
    ! [B_6] : k4_xboole_0(B_6,B_6) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_71])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( r1_xboole_0(A_9,B_10)
      | k4_xboole_0(A_9,B_10) != A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_330,plain,(
    ! [C_136,D_137,A_138,B_139] :
      ( ~ r1_xboole_0(C_136,D_137)
      | ~ m2_orders_2(D_137,A_138,B_139)
      | ~ m2_orders_2(C_136,A_138,B_139)
      | ~ m1_orders_1(B_139,k1_orders_1(u1_struct_0(A_138)))
      | ~ l1_orders_2(A_138)
      | ~ v5_orders_2(A_138)
      | ~ v4_orders_2(A_138)
      | ~ v3_orders_2(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_334,plain,(
    ! [B_140,A_141,B_142,A_143] :
      ( ~ m2_orders_2(B_140,A_141,B_142)
      | ~ m2_orders_2(A_143,A_141,B_142)
      | ~ m1_orders_1(B_142,k1_orders_1(u1_struct_0(A_141)))
      | ~ l1_orders_2(A_141)
      | ~ v5_orders_2(A_141)
      | ~ v4_orders_2(A_141)
      | ~ v3_orders_2(A_141)
      | v2_struct_0(A_141)
      | k4_xboole_0(A_143,B_140) != A_143 ) ),
    inference(resolution,[status(thm)],[c_22,c_330])).

tff(c_336,plain,(
    ! [A_143] :
      ( ~ m2_orders_2(A_143,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1')
      | k4_xboole_0(A_143,'#skF_4') != A_143 ) ),
    inference(resolution,[status(thm)],[c_40,c_334])).

tff(c_339,plain,(
    ! [A_143] :
      ( ~ m2_orders_2(A_143,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1')
      | k4_xboole_0(A_143,'#skF_4') != A_143 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_336])).

tff(c_341,plain,(
    ! [A_144] :
      ( ~ m2_orders_2(A_144,'#skF_1','#skF_2')
      | k4_xboole_0(A_144,'#skF_4') != A_144 ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_339])).

tff(c_344,plain,(
    k4_xboole_0('#skF_4','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_341])).

tff(c_348,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_344])).

tff(c_350,plain,(
    r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_354,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_350,c_6])).

tff(c_389,plain,(
    ! [B_153,A_154] :
      ( B_153 = A_154
      | ~ r1_tarski(B_153,A_154)
      | ~ r1_tarski(A_154,B_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_397,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_354,c_389])).

tff(c_402,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_397])).

tff(c_42,plain,(
    m2_orders_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_449,plain,(
    ! [C_168,A_169,B_170] :
      ( m1_subset_1(C_168,k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ m2_orders_2(C_168,A_169,B_170)
      | ~ m1_orders_1(B_170,k1_orders_1(u1_struct_0(A_169)))
      | ~ l1_orders_2(A_169)
      | ~ v5_orders_2(A_169)
      | ~ v4_orders_2(A_169)
      | ~ v3_orders_2(A_169)
      | v2_struct_0(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_451,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_449])).

tff(c_456,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_451])).

tff(c_457,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_456])).

tff(c_349,plain,(
    ~ m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_466,plain,(
    ! [C_175,A_176,D_177,B_178] :
      ( m1_orders_2(C_175,A_176,D_177)
      | m1_orders_2(D_177,A_176,C_175)
      | D_177 = C_175
      | ~ m2_orders_2(D_177,A_176,B_178)
      | ~ m2_orders_2(C_175,A_176,B_178)
      | ~ m1_orders_1(B_178,k1_orders_1(u1_struct_0(A_176)))
      | ~ l1_orders_2(A_176)
      | ~ v5_orders_2(A_176)
      | ~ v4_orders_2(A_176)
      | ~ v3_orders_2(A_176)
      | v2_struct_0(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_468,plain,(
    ! [C_175] :
      ( m1_orders_2(C_175,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_175)
      | C_175 = '#skF_3'
      | ~ m2_orders_2(C_175,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_466])).

tff(c_473,plain,(
    ! [C_175] :
      ( m1_orders_2(C_175,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_175)
      | C_175 = '#skF_3'
      | ~ m2_orders_2(C_175,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_468])).

tff(c_479,plain,(
    ! [C_179] :
      ( m1_orders_2(C_179,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_179)
      | C_179 = '#skF_3'
      | ~ m2_orders_2(C_179,'#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_473])).

tff(c_485,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | m1_orders_2('#skF_3','#skF_1','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_479])).

tff(c_490,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_349,c_485])).

tff(c_491,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_490])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | k4_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_407,plain,(
    k4_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_402])).

tff(c_495,plain,(
    k4_xboole_0('#skF_4','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_491,c_407])).

tff(c_506,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_495])).

tff(c_507,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_490])).

tff(c_28,plain,(
    ! [C_21,B_19,A_15] :
      ( r1_tarski(C_21,B_19)
      | ~ m1_orders_2(C_21,A_15,B_19)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_orders_2(A_15)
      | ~ v5_orders_2(A_15)
      | ~ v4_orders_2(A_15)
      | ~ v3_orders_2(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_510,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_507,c_28])).

tff(c_513,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_457,c_510])).

tff(c_515,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_402,c_513])).

tff(c_516,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_397])).

tff(c_522,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_516,c_350])).

tff(c_527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_522])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:29:44 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.55  
% 2.98/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.55  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.98/1.55  
% 2.98/1.55  %Foreground sorts:
% 2.98/1.55  
% 2.98/1.55  
% 2.98/1.55  %Background operators:
% 2.98/1.55  
% 2.98/1.55  
% 2.98/1.55  %Foreground operators:
% 2.98/1.55  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.98/1.55  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.98/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.98/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.98/1.55  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.98/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.98/1.55  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.98/1.55  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.98/1.55  tff('#skF_2', type, '#skF_2': $i).
% 2.98/1.55  tff('#skF_3', type, '#skF_3': $i).
% 2.98/1.55  tff('#skF_1', type, '#skF_1': $i).
% 2.98/1.55  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.98/1.55  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.98/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.98/1.55  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.98/1.55  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.98/1.55  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.98/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.55  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.98/1.55  tff('#skF_4', type, '#skF_4': $i).
% 2.98/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.55  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.98/1.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.98/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.98/1.55  
% 2.98/1.57  tff(f_35, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 2.98/1.57  tff(f_190, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_orders_2)).
% 2.98/1.57  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.98/1.57  tff(f_88, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_orders_2)).
% 2.98/1.57  tff(f_69, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.98/1.57  tff(f_114, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (~(~(B = k1_xboole_0) & m1_orders_2(B, A, B)) & ~(~m1_orders_2(B, A, B) & (B = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_orders_2)).
% 2.98/1.57  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.98/1.57  tff(f_45, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.98/1.57  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.98/1.57  tff(f_137, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_orders_2)).
% 2.98/1.57  tff(f_165, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_orders_2)).
% 2.98/1.57  tff(c_8, plain, (![A_3]: (~r2_xboole_0(A_3, A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.98/1.57  tff(c_54, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_190])).
% 2.98/1.57  tff(c_52, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_190])).
% 2.98/1.57  tff(c_50, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_190])).
% 2.98/1.57  tff(c_48, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_190])).
% 2.98/1.57  tff(c_46, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_190])).
% 2.98/1.57  tff(c_102, plain, (![A_81, B_82]: (r2_xboole_0(A_81, B_82) | B_82=A_81 | ~r1_tarski(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.98/1.57  tff(c_56, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4') | ~r2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_190])).
% 2.98/1.57  tff(c_79, plain, (~r2_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_56])).
% 2.98/1.57  tff(c_113, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_102, c_79])).
% 2.98/1.57  tff(c_119, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_113])).
% 2.98/1.57  tff(c_62, plain, (r2_xboole_0('#skF_3', '#skF_4') | m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_190])).
% 2.98/1.57  tff(c_91, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_79, c_62])).
% 2.98/1.57  tff(c_145, plain, (![C_90, B_91, A_92]: (r1_tarski(C_90, B_91) | ~m1_orders_2(C_90, A_92, B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_orders_2(A_92) | ~v5_orders_2(A_92) | ~v4_orders_2(A_92) | ~v3_orders_2(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.98/1.57  tff(c_147, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_91, c_145])).
% 2.98/1.57  tff(c_150, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_147])).
% 2.98/1.57  tff(c_151, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_54, c_119, c_150])).
% 2.98/1.57  tff(c_44, plain, (m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_190])).
% 2.98/1.57  tff(c_40, plain, (m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_190])).
% 2.98/1.57  tff(c_165, plain, (![C_96, A_97, B_98]: (m1_subset_1(C_96, k1_zfmisc_1(u1_struct_0(A_97))) | ~m2_orders_2(C_96, A_97, B_98) | ~m1_orders_1(B_98, k1_orders_1(u1_struct_0(A_97))) | ~l1_orders_2(A_97) | ~v5_orders_2(A_97) | ~v4_orders_2(A_97) | ~v3_orders_2(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.98/1.57  tff(c_169, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_165])).
% 2.98/1.57  tff(c_176, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_169])).
% 2.98/1.57  tff(c_178, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_151, c_176])).
% 2.98/1.57  tff(c_179, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_113])).
% 2.98/1.57  tff(c_181, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_91])).
% 2.98/1.57  tff(c_203, plain, (![B_102, A_103]: (~m1_orders_2(B_102, A_103, B_102) | k1_xboole_0=B_102 | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_orders_2(A_103) | ~v5_orders_2(A_103) | ~v4_orders_2(A_103) | ~v3_orders_2(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.98/1.57  tff(c_205, plain, (k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_181, c_203])).
% 2.98/1.57  tff(c_208, plain, (k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_205])).
% 2.98/1.57  tff(c_209, plain, (k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_54, c_208])).
% 2.98/1.57  tff(c_210, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_209])).
% 2.98/1.57  tff(c_232, plain, (![C_112, A_113, B_114]: (m1_subset_1(C_112, k1_zfmisc_1(u1_struct_0(A_113))) | ~m2_orders_2(C_112, A_113, B_114) | ~m1_orders_1(B_114, k1_orders_1(u1_struct_0(A_113))) | ~l1_orders_2(A_113) | ~v5_orders_2(A_113) | ~v4_orders_2(A_113) | ~v3_orders_2(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.98/1.57  tff(c_234, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_232])).
% 2.98/1.57  tff(c_237, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_234])).
% 2.98/1.57  tff(c_239, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_210, c_237])).
% 2.98/1.57  tff(c_240, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_209])).
% 2.98/1.57  tff(c_14, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.98/1.57  tff(c_67, plain, (![A_70, B_71]: (k4_xboole_0(A_70, B_71)=k1_xboole_0 | ~r1_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.98/1.57  tff(c_71, plain, (![B_6]: (k4_xboole_0(B_6, B_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_67])).
% 2.98/1.57  tff(c_246, plain, (![B_6]: (k4_xboole_0(B_6, B_6)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_240, c_71])).
% 2.98/1.57  tff(c_22, plain, (![A_9, B_10]: (r1_xboole_0(A_9, B_10) | k4_xboole_0(A_9, B_10)!=A_9)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.98/1.57  tff(c_330, plain, (![C_136, D_137, A_138, B_139]: (~r1_xboole_0(C_136, D_137) | ~m2_orders_2(D_137, A_138, B_139) | ~m2_orders_2(C_136, A_138, B_139) | ~m1_orders_1(B_139, k1_orders_1(u1_struct_0(A_138))) | ~l1_orders_2(A_138) | ~v5_orders_2(A_138) | ~v4_orders_2(A_138) | ~v3_orders_2(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.98/1.57  tff(c_334, plain, (![B_140, A_141, B_142, A_143]: (~m2_orders_2(B_140, A_141, B_142) | ~m2_orders_2(A_143, A_141, B_142) | ~m1_orders_1(B_142, k1_orders_1(u1_struct_0(A_141))) | ~l1_orders_2(A_141) | ~v5_orders_2(A_141) | ~v4_orders_2(A_141) | ~v3_orders_2(A_141) | v2_struct_0(A_141) | k4_xboole_0(A_143, B_140)!=A_143)), inference(resolution, [status(thm)], [c_22, c_330])).
% 2.98/1.57  tff(c_336, plain, (![A_143]: (~m2_orders_2(A_143, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1') | k4_xboole_0(A_143, '#skF_4')!=A_143)), inference(resolution, [status(thm)], [c_40, c_334])).
% 2.98/1.57  tff(c_339, plain, (![A_143]: (~m2_orders_2(A_143, '#skF_1', '#skF_2') | v2_struct_0('#skF_1') | k4_xboole_0(A_143, '#skF_4')!=A_143)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_336])).
% 2.98/1.57  tff(c_341, plain, (![A_144]: (~m2_orders_2(A_144, '#skF_1', '#skF_2') | k4_xboole_0(A_144, '#skF_4')!=A_144)), inference(negUnitSimplification, [status(thm)], [c_54, c_339])).
% 2.98/1.57  tff(c_344, plain, (k4_xboole_0('#skF_4', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_40, c_341])).
% 2.98/1.57  tff(c_348, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_246, c_344])).
% 2.98/1.57  tff(c_350, plain, (r2_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_56])).
% 2.98/1.57  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.98/1.57  tff(c_354, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_350, c_6])).
% 2.98/1.57  tff(c_389, plain, (![B_153, A_154]: (B_153=A_154 | ~r1_tarski(B_153, A_154) | ~r1_tarski(A_154, B_153))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.98/1.57  tff(c_397, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_354, c_389])).
% 2.98/1.57  tff(c_402, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_397])).
% 2.98/1.57  tff(c_42, plain, (m2_orders_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_190])).
% 2.98/1.57  tff(c_449, plain, (![C_168, A_169, B_170]: (m1_subset_1(C_168, k1_zfmisc_1(u1_struct_0(A_169))) | ~m2_orders_2(C_168, A_169, B_170) | ~m1_orders_1(B_170, k1_orders_1(u1_struct_0(A_169))) | ~l1_orders_2(A_169) | ~v5_orders_2(A_169) | ~v4_orders_2(A_169) | ~v3_orders_2(A_169) | v2_struct_0(A_169))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.98/1.57  tff(c_451, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_449])).
% 2.98/1.57  tff(c_456, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_451])).
% 2.98/1.57  tff(c_457, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_54, c_456])).
% 2.98/1.57  tff(c_349, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(splitRight, [status(thm)], [c_56])).
% 2.98/1.57  tff(c_466, plain, (![C_175, A_176, D_177, B_178]: (m1_orders_2(C_175, A_176, D_177) | m1_orders_2(D_177, A_176, C_175) | D_177=C_175 | ~m2_orders_2(D_177, A_176, B_178) | ~m2_orders_2(C_175, A_176, B_178) | ~m1_orders_1(B_178, k1_orders_1(u1_struct_0(A_176))) | ~l1_orders_2(A_176) | ~v5_orders_2(A_176) | ~v4_orders_2(A_176) | ~v3_orders_2(A_176) | v2_struct_0(A_176))), inference(cnfTransformation, [status(thm)], [f_165])).
% 2.98/1.57  tff(c_468, plain, (![C_175]: (m1_orders_2(C_175, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_175) | C_175='#skF_3' | ~m2_orders_2(C_175, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_466])).
% 2.98/1.57  tff(c_473, plain, (![C_175]: (m1_orders_2(C_175, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_175) | C_175='#skF_3' | ~m2_orders_2(C_175, '#skF_1', '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_468])).
% 2.98/1.57  tff(c_479, plain, (![C_179]: (m1_orders_2(C_179, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_179) | C_179='#skF_3' | ~m2_orders_2(C_179, '#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_473])).
% 2.98/1.57  tff(c_485, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', '#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_40, c_479])).
% 2.98/1.57  tff(c_490, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_349, c_485])).
% 2.98/1.57  tff(c_491, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_490])).
% 2.98/1.57  tff(c_16, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | k4_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.98/1.57  tff(c_407, plain, (k4_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_402])).
% 2.98/1.57  tff(c_495, plain, (k4_xboole_0('#skF_4', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_491, c_407])).
% 2.98/1.57  tff(c_506, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_495])).
% 2.98/1.57  tff(c_507, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_490])).
% 2.98/1.57  tff(c_28, plain, (![C_21, B_19, A_15]: (r1_tarski(C_21, B_19) | ~m1_orders_2(C_21, A_15, B_19) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_orders_2(A_15) | ~v5_orders_2(A_15) | ~v4_orders_2(A_15) | ~v3_orders_2(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.98/1.57  tff(c_510, plain, (r1_tarski('#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_507, c_28])).
% 2.98/1.57  tff(c_513, plain, (r1_tarski('#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_457, c_510])).
% 2.98/1.57  tff(c_515, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_402, c_513])).
% 2.98/1.57  tff(c_516, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_397])).
% 2.98/1.57  tff(c_522, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_516, c_350])).
% 2.98/1.57  tff(c_527, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_522])).
% 2.98/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.57  
% 2.98/1.57  Inference rules
% 2.98/1.57  ----------------------
% 2.98/1.57  #Ref     : 0
% 2.98/1.57  #Sup     : 73
% 2.98/1.57  #Fact    : 0
% 2.98/1.57  #Define  : 0
% 2.98/1.57  #Split   : 5
% 2.98/1.57  #Chain   : 0
% 2.98/1.57  #Close   : 0
% 2.98/1.57  
% 2.98/1.57  Ordering : KBO
% 2.98/1.57  
% 2.98/1.57  Simplification rules
% 2.98/1.57  ----------------------
% 2.98/1.57  #Subsume      : 7
% 2.98/1.57  #Demod        : 164
% 2.98/1.57  #Tautology    : 45
% 2.98/1.57  #SimpNegUnit  : 26
% 2.98/1.57  #BackRed      : 24
% 2.98/1.57  
% 2.98/1.57  #Partial instantiations: 0
% 2.98/1.57  #Strategies tried      : 1
% 2.98/1.57  
% 2.98/1.57  Timing (in seconds)
% 2.98/1.57  ----------------------
% 2.98/1.57  Preprocessing        : 0.37
% 2.98/1.57  Parsing              : 0.20
% 2.98/1.57  CNF conversion       : 0.03
% 2.98/1.57  Main loop            : 0.30
% 2.98/1.57  Inferencing          : 0.11
% 2.98/1.57  Reduction            : 0.09
% 2.98/1.57  Demodulation         : 0.07
% 2.98/1.57  BG Simplification    : 0.02
% 2.98/1.57  Subsumption          : 0.06
% 2.98/1.57  Abstraction          : 0.01
% 2.98/1.57  MUC search           : 0.00
% 2.98/1.57  Cooper               : 0.00
% 2.98/1.57  Total                : 0.72
% 2.98/1.57  Index Insertion      : 0.00
% 2.98/1.57  Index Deletion       : 0.00
% 2.98/1.57  Index Matching       : 0.00
% 2.98/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
