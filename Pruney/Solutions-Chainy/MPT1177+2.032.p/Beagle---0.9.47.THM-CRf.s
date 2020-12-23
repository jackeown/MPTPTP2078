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
% DateTime   : Thu Dec  3 10:19:59 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 304 expanded)
%              Number of leaves         :   38 ( 126 expanded)
%              Depth                    :   12
%              Number of atoms          :  312 (1266 expanded)
%              Number of equality atoms :   35 (  62 expanded)
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_213,negated_conjecture,(
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

tff(f_93,axiom,(
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

tff(f_112,axiom,(
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

tff(f_137,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_orders_2)).

tff(f_51,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & k4_xboole_0(B,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_xboole_1)).

tff(f_160,axiom,(
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

tff(f_42,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_188,axiom,(
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

tff(c_4,plain,(
    ! [B_2] : ~ r2_xboole_0(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_54,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_52,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_50,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_48,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_46,plain,(
    m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_42,plain,(
    m2_orders_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_508,plain,(
    ! [C_151,A_152,B_153] :
      ( m1_subset_1(C_151,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ m2_orders_2(C_151,A_152,B_153)
      | ~ m1_orders_1(B_153,k1_orders_1(u1_struct_0(A_152)))
      | ~ l1_orders_2(A_152)
      | ~ v5_orders_2(A_152)
      | ~ v4_orders_2(A_152)
      | ~ v3_orders_2(A_152)
      | v2_struct_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_510,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_508])).

tff(c_513,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_510])).

tff(c_514,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_513])).

tff(c_135,plain,(
    ! [A_100,B_101] :
      ( r2_xboole_0(A_100,B_101)
      | B_101 = A_100
      | ~ r1_tarski(A_100,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,
    ( ~ m1_orders_2('#skF_3','#skF_1','#skF_4')
    | ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_84,plain,(
    ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_150,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_135,c_84])).

tff(c_156,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_64,plain,
    ( r2_xboole_0('#skF_3','#skF_4')
    | m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_85,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_64])).

tff(c_238,plain,(
    ! [C_113,B_114,A_115] :
      ( r1_tarski(C_113,B_114)
      | ~ m1_orders_2(C_113,A_115,B_114)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_orders_2(A_115)
      | ~ v5_orders_2(A_115)
      | ~ v4_orders_2(A_115)
      | ~ v3_orders_2(A_115)
      | v2_struct_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_240,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_85,c_238])).

tff(c_243,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_240])).

tff(c_244,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_156,c_243])).

tff(c_323,plain,(
    ! [C_125,A_126,B_127] :
      ( m1_subset_1(C_125,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ m2_orders_2(C_125,A_126,B_127)
      | ~ m1_orders_1(B_127,k1_orders_1(u1_struct_0(A_126)))
      | ~ l1_orders_2(A_126)
      | ~ v5_orders_2(A_126)
      | ~ v4_orders_2(A_126)
      | ~ v3_orders_2(A_126)
      | v2_struct_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_327,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_323])).

tff(c_334,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_327])).

tff(c_336,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_244,c_334])).

tff(c_337,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_339,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_85])).

tff(c_531,plain,(
    ! [C_158,A_159,B_160] :
      ( ~ m1_orders_2(C_158,A_159,B_160)
      | ~ m1_orders_2(B_160,A_159,C_158)
      | k1_xboole_0 = B_160
      | ~ m1_subset_1(C_158,k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ l1_orders_2(A_159)
      | ~ v5_orders_2(A_159)
      | ~ v4_orders_2(A_159)
      | ~ v3_orders_2(A_159)
      | v2_struct_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_533,plain,
    ( ~ m1_orders_2('#skF_4','#skF_1','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_339,c_531])).

tff(c_536,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_514,c_339,c_533])).

tff(c_537,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_536])).

tff(c_20,plain,(
    ! [A_11,B_12] : r1_xboole_0(k4_xboole_0(A_11,B_12),B_12) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_70,plain,(
    ! [B_84,A_85] :
      ( r1_xboole_0(B_84,A_85)
      | ~ r1_xboole_0(A_85,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_73,plain,(
    ! [B_12,A_11] : r1_xboole_0(B_12,k4_xboole_0(A_11,B_12)) ),
    inference(resolution,[status(thm)],[c_20,c_70])).

tff(c_87,plain,(
    ! [A_94,B_95] :
      ( k4_xboole_0(A_94,B_95) = A_94
      | ~ r1_xboole_0(A_94,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_98,plain,(
    ! [B_12,A_11] : k4_xboole_0(B_12,k4_xboole_0(A_11,B_12)) = B_12 ),
    inference(resolution,[status(thm)],[c_73,c_87])).

tff(c_18,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16,plain,(
    ! [B_8,A_7] :
      ( k4_xboole_0(B_8,A_7) != k1_xboole_0
      | ~ r2_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_413,plain,(
    ! [B_137,A_138] :
      ( k4_xboole_0(B_137,A_138) != k1_xboole_0
      | B_137 = A_138
      | ~ r1_tarski(A_138,B_137) ) ),
    inference(resolution,[status(thm)],[c_135,c_16])).

tff(c_441,plain,(
    ! [A_144,B_145] :
      ( k4_xboole_0(A_144,k4_xboole_0(A_144,B_145)) != k1_xboole_0
      | k4_xboole_0(A_144,B_145) = A_144 ) ),
    inference(resolution,[status(thm)],[c_18,c_413])).

tff(c_455,plain,(
    ! [A_146] :
      ( k1_xboole_0 != A_146
      | k4_xboole_0(A_146,A_146) = A_146 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_441])).

tff(c_478,plain,(
    ! [A_146] :
      ( r1_xboole_0(A_146,A_146)
      | k1_xboole_0 != A_146 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_20])).

tff(c_515,plain,(
    ! [C_154,D_155,A_156,B_157] :
      ( ~ r1_xboole_0(C_154,D_155)
      | ~ m2_orders_2(D_155,A_156,B_157)
      | ~ m2_orders_2(C_154,A_156,B_157)
      | ~ m1_orders_1(B_157,k1_orders_1(u1_struct_0(A_156)))
      | ~ l1_orders_2(A_156)
      | ~ v5_orders_2(A_156)
      | ~ v4_orders_2(A_156)
      | ~ v3_orders_2(A_156)
      | v2_struct_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_526,plain,(
    ! [A_146,A_156,B_157] :
      ( ~ m2_orders_2(A_146,A_156,B_157)
      | ~ m1_orders_1(B_157,k1_orders_1(u1_struct_0(A_156)))
      | ~ l1_orders_2(A_156)
      | ~ v5_orders_2(A_156)
      | ~ v4_orders_2(A_156)
      | ~ v3_orders_2(A_156)
      | v2_struct_0(A_156)
      | k1_xboole_0 != A_146 ) ),
    inference(resolution,[status(thm)],[c_478,c_515])).

tff(c_650,plain,(
    ! [A_178,A_179,B_180] :
      ( ~ m2_orders_2(A_178,A_179,B_180)
      | ~ m1_orders_1(B_180,k1_orders_1(u1_struct_0(A_179)))
      | ~ l1_orders_2(A_179)
      | ~ v5_orders_2(A_179)
      | ~ v4_orders_2(A_179)
      | ~ v3_orders_2(A_179)
      | v2_struct_0(A_179)
      | A_178 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_537,c_526])).

tff(c_652,plain,
    ( ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_650])).

tff(c_655,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_652])).

tff(c_657,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_655])).

tff(c_659,plain,(
    r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_671,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_659,c_6])).

tff(c_743,plain,(
    ! [B_191,A_192] :
      ( B_191 = A_192
      | ~ r1_tarski(B_191,A_192)
      | ~ r1_tarski(A_192,B_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_750,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_671,c_743])).

tff(c_756,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_750])).

tff(c_44,plain,(
    m2_orders_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_857,plain,(
    ! [C_209,A_210,B_211] :
      ( m1_subset_1(C_209,k1_zfmisc_1(u1_struct_0(A_210)))
      | ~ m2_orders_2(C_209,A_210,B_211)
      | ~ m1_orders_1(B_211,k1_orders_1(u1_struct_0(A_210)))
      | ~ l1_orders_2(A_210)
      | ~ v5_orders_2(A_210)
      | ~ v4_orders_2(A_210)
      | ~ v3_orders_2(A_210)
      | v2_struct_0(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_859,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_857])).

tff(c_864,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_859])).

tff(c_865,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_864])).

tff(c_14,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_658,plain,(
    ~ m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1033,plain,(
    ! [C_247,A_248,D_249,B_250] :
      ( m1_orders_2(C_247,A_248,D_249)
      | m1_orders_2(D_249,A_248,C_247)
      | D_249 = C_247
      | ~ m2_orders_2(D_249,A_248,B_250)
      | ~ m2_orders_2(C_247,A_248,B_250)
      | ~ m1_orders_1(B_250,k1_orders_1(u1_struct_0(A_248)))
      | ~ l1_orders_2(A_248)
      | ~ v5_orders_2(A_248)
      | ~ v4_orders_2(A_248)
      | ~ v3_orders_2(A_248)
      | v2_struct_0(A_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_1035,plain,(
    ! [C_247] :
      ( m1_orders_2(C_247,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_247)
      | C_247 = '#skF_3'
      | ~ m2_orders_2(C_247,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_1033])).

tff(c_1040,plain,(
    ! [C_247] :
      ( m1_orders_2(C_247,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_247)
      | C_247 = '#skF_3'
      | ~ m2_orders_2(C_247,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_1035])).

tff(c_1047,plain,(
    ! [C_255] :
      ( m1_orders_2(C_255,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_255)
      | C_255 = '#skF_3'
      | ~ m2_orders_2(C_255,'#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1040])).

tff(c_1053,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | m1_orders_2('#skF_3','#skF_1','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42,c_1047])).

tff(c_1058,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_658,c_1053])).

tff(c_1059,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1058])).

tff(c_1069,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1059,c_756])).

tff(c_1079,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1069])).

tff(c_1080,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_1058])).

tff(c_32,plain,(
    ! [C_29,B_27,A_23] :
      ( r1_tarski(C_29,B_27)
      | ~ m1_orders_2(C_29,A_23,B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_orders_2(A_23)
      | ~ v5_orders_2(A_23)
      | ~ v4_orders_2(A_23)
      | ~ v3_orders_2(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1101,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1080,c_32])).

tff(c_1116,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_865,c_1101])).

tff(c_1118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_756,c_1116])).

tff(c_1119,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_750])).

tff(c_1124,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1119,c_659])).

tff(c_1128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_1124])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:58:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.57  
% 3.29/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.57  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.29/1.57  
% 3.29/1.57  %Foreground sorts:
% 3.29/1.57  
% 3.29/1.57  
% 3.29/1.57  %Background operators:
% 3.29/1.57  
% 3.29/1.57  
% 3.29/1.57  %Foreground operators:
% 3.29/1.57  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.29/1.57  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.29/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.29/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.29/1.57  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 3.29/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.29/1.57  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 3.29/1.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.29/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.29/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.29/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.29/1.57  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.29/1.57  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.29/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.29/1.57  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.29/1.57  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.29/1.57  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 3.29/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.57  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 3.29/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.29/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.57  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 3.29/1.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.29/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.29/1.57  
% 3.29/1.59  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.29/1.59  tff(f_213, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_orders_2)).
% 3.29/1.59  tff(f_93, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 3.29/1.59  tff(f_112, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_orders_2)).
% 3.29/1.59  tff(f_137, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_orders_2)).
% 3.29/1.59  tff(f_51, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.29/1.59  tff(f_36, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.29/1.59  tff(f_55, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.29/1.59  tff(f_49, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.29/1.59  tff(f_47, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (k4_xboole_0(B, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_xboole_1)).
% 3.29/1.59  tff(f_160, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_orders_2)).
% 3.29/1.59  tff(f_42, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.29/1.59  tff(f_188, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_orders_2)).
% 3.29/1.59  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.29/1.59  tff(c_56, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.29/1.59  tff(c_54, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.29/1.59  tff(c_52, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.29/1.59  tff(c_50, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.29/1.59  tff(c_48, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.29/1.59  tff(c_46, plain, (m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.29/1.59  tff(c_42, plain, (m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.29/1.59  tff(c_508, plain, (![C_151, A_152, B_153]: (m1_subset_1(C_151, k1_zfmisc_1(u1_struct_0(A_152))) | ~m2_orders_2(C_151, A_152, B_153) | ~m1_orders_1(B_153, k1_orders_1(u1_struct_0(A_152))) | ~l1_orders_2(A_152) | ~v5_orders_2(A_152) | ~v4_orders_2(A_152) | ~v3_orders_2(A_152) | v2_struct_0(A_152))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.29/1.59  tff(c_510, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_508])).
% 3.29/1.59  tff(c_513, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_510])).
% 3.29/1.59  tff(c_514, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_56, c_513])).
% 3.29/1.59  tff(c_135, plain, (![A_100, B_101]: (r2_xboole_0(A_100, B_101) | B_101=A_100 | ~r1_tarski(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.29/1.59  tff(c_58, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4') | ~r2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.29/1.59  tff(c_84, plain, (~r2_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_58])).
% 3.29/1.59  tff(c_150, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_135, c_84])).
% 3.29/1.59  tff(c_156, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_150])).
% 3.29/1.59  tff(c_64, plain, (r2_xboole_0('#skF_3', '#skF_4') | m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.29/1.59  tff(c_85, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_84, c_64])).
% 3.29/1.59  tff(c_238, plain, (![C_113, B_114, A_115]: (r1_tarski(C_113, B_114) | ~m1_orders_2(C_113, A_115, B_114) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_orders_2(A_115) | ~v5_orders_2(A_115) | ~v4_orders_2(A_115) | ~v3_orders_2(A_115) | v2_struct_0(A_115))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.29/1.59  tff(c_240, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_85, c_238])).
% 3.29/1.59  tff(c_243, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_240])).
% 3.29/1.59  tff(c_244, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_56, c_156, c_243])).
% 3.29/1.59  tff(c_323, plain, (![C_125, A_126, B_127]: (m1_subset_1(C_125, k1_zfmisc_1(u1_struct_0(A_126))) | ~m2_orders_2(C_125, A_126, B_127) | ~m1_orders_1(B_127, k1_orders_1(u1_struct_0(A_126))) | ~l1_orders_2(A_126) | ~v5_orders_2(A_126) | ~v4_orders_2(A_126) | ~v3_orders_2(A_126) | v2_struct_0(A_126))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.29/1.59  tff(c_327, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_323])).
% 3.29/1.59  tff(c_334, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_327])).
% 3.29/1.59  tff(c_336, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_244, c_334])).
% 3.29/1.59  tff(c_337, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_150])).
% 3.29/1.59  tff(c_339, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_337, c_85])).
% 3.29/1.59  tff(c_531, plain, (![C_158, A_159, B_160]: (~m1_orders_2(C_158, A_159, B_160) | ~m1_orders_2(B_160, A_159, C_158) | k1_xboole_0=B_160 | ~m1_subset_1(C_158, k1_zfmisc_1(u1_struct_0(A_159))) | ~m1_subset_1(B_160, k1_zfmisc_1(u1_struct_0(A_159))) | ~l1_orders_2(A_159) | ~v5_orders_2(A_159) | ~v4_orders_2(A_159) | ~v3_orders_2(A_159) | v2_struct_0(A_159))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.29/1.59  tff(c_533, plain, (~m1_orders_2('#skF_4', '#skF_1', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_339, c_531])).
% 3.29/1.59  tff(c_536, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_514, c_339, c_533])).
% 3.29/1.59  tff(c_537, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_56, c_536])).
% 3.29/1.59  tff(c_20, plain, (![A_11, B_12]: (r1_xboole_0(k4_xboole_0(A_11, B_12), B_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.29/1.59  tff(c_70, plain, (![B_84, A_85]: (r1_xboole_0(B_84, A_85) | ~r1_xboole_0(A_85, B_84))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.29/1.59  tff(c_73, plain, (![B_12, A_11]: (r1_xboole_0(B_12, k4_xboole_0(A_11, B_12)))), inference(resolution, [status(thm)], [c_20, c_70])).
% 3.29/1.59  tff(c_87, plain, (![A_94, B_95]: (k4_xboole_0(A_94, B_95)=A_94 | ~r1_xboole_0(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.29/1.59  tff(c_98, plain, (![B_12, A_11]: (k4_xboole_0(B_12, k4_xboole_0(A_11, B_12))=B_12)), inference(resolution, [status(thm)], [c_73, c_87])).
% 3.29/1.59  tff(c_18, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.29/1.59  tff(c_16, plain, (![B_8, A_7]: (k4_xboole_0(B_8, A_7)!=k1_xboole_0 | ~r2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.29/1.59  tff(c_413, plain, (![B_137, A_138]: (k4_xboole_0(B_137, A_138)!=k1_xboole_0 | B_137=A_138 | ~r1_tarski(A_138, B_137))), inference(resolution, [status(thm)], [c_135, c_16])).
% 3.29/1.59  tff(c_441, plain, (![A_144, B_145]: (k4_xboole_0(A_144, k4_xboole_0(A_144, B_145))!=k1_xboole_0 | k4_xboole_0(A_144, B_145)=A_144)), inference(resolution, [status(thm)], [c_18, c_413])).
% 3.29/1.59  tff(c_455, plain, (![A_146]: (k1_xboole_0!=A_146 | k4_xboole_0(A_146, A_146)=A_146)), inference(superposition, [status(thm), theory('equality')], [c_98, c_441])).
% 3.29/1.59  tff(c_478, plain, (![A_146]: (r1_xboole_0(A_146, A_146) | k1_xboole_0!=A_146)), inference(superposition, [status(thm), theory('equality')], [c_455, c_20])).
% 3.29/1.59  tff(c_515, plain, (![C_154, D_155, A_156, B_157]: (~r1_xboole_0(C_154, D_155) | ~m2_orders_2(D_155, A_156, B_157) | ~m2_orders_2(C_154, A_156, B_157) | ~m1_orders_1(B_157, k1_orders_1(u1_struct_0(A_156))) | ~l1_orders_2(A_156) | ~v5_orders_2(A_156) | ~v4_orders_2(A_156) | ~v3_orders_2(A_156) | v2_struct_0(A_156))), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.29/1.59  tff(c_526, plain, (![A_146, A_156, B_157]: (~m2_orders_2(A_146, A_156, B_157) | ~m1_orders_1(B_157, k1_orders_1(u1_struct_0(A_156))) | ~l1_orders_2(A_156) | ~v5_orders_2(A_156) | ~v4_orders_2(A_156) | ~v3_orders_2(A_156) | v2_struct_0(A_156) | k1_xboole_0!=A_146)), inference(resolution, [status(thm)], [c_478, c_515])).
% 3.29/1.59  tff(c_650, plain, (![A_178, A_179, B_180]: (~m2_orders_2(A_178, A_179, B_180) | ~m1_orders_1(B_180, k1_orders_1(u1_struct_0(A_179))) | ~l1_orders_2(A_179) | ~v5_orders_2(A_179) | ~v4_orders_2(A_179) | ~v3_orders_2(A_179) | v2_struct_0(A_179) | A_178!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_537, c_526])).
% 3.29/1.59  tff(c_652, plain, (~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_650])).
% 3.29/1.59  tff(c_655, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_652])).
% 3.29/1.59  tff(c_657, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_655])).
% 3.29/1.59  tff(c_659, plain, (r2_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_58])).
% 3.29/1.59  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.29/1.59  tff(c_671, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_659, c_6])).
% 3.29/1.59  tff(c_743, plain, (![B_191, A_192]: (B_191=A_192 | ~r1_tarski(B_191, A_192) | ~r1_tarski(A_192, B_191))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.29/1.59  tff(c_750, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_671, c_743])).
% 3.29/1.59  tff(c_756, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_750])).
% 3.29/1.59  tff(c_44, plain, (m2_orders_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.29/1.59  tff(c_857, plain, (![C_209, A_210, B_211]: (m1_subset_1(C_209, k1_zfmisc_1(u1_struct_0(A_210))) | ~m2_orders_2(C_209, A_210, B_211) | ~m1_orders_1(B_211, k1_orders_1(u1_struct_0(A_210))) | ~l1_orders_2(A_210) | ~v5_orders_2(A_210) | ~v4_orders_2(A_210) | ~v3_orders_2(A_210) | v2_struct_0(A_210))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.29/1.59  tff(c_859, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_857])).
% 3.29/1.59  tff(c_864, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_859])).
% 3.29/1.59  tff(c_865, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_56, c_864])).
% 3.29/1.59  tff(c_14, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.29/1.59  tff(c_658, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(splitRight, [status(thm)], [c_58])).
% 3.29/1.59  tff(c_1033, plain, (![C_247, A_248, D_249, B_250]: (m1_orders_2(C_247, A_248, D_249) | m1_orders_2(D_249, A_248, C_247) | D_249=C_247 | ~m2_orders_2(D_249, A_248, B_250) | ~m2_orders_2(C_247, A_248, B_250) | ~m1_orders_1(B_250, k1_orders_1(u1_struct_0(A_248))) | ~l1_orders_2(A_248) | ~v5_orders_2(A_248) | ~v4_orders_2(A_248) | ~v3_orders_2(A_248) | v2_struct_0(A_248))), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.29/1.59  tff(c_1035, plain, (![C_247]: (m1_orders_2(C_247, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_247) | C_247='#skF_3' | ~m2_orders_2(C_247, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_1033])).
% 3.29/1.59  tff(c_1040, plain, (![C_247]: (m1_orders_2(C_247, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_247) | C_247='#skF_3' | ~m2_orders_2(C_247, '#skF_1', '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_1035])).
% 3.29/1.59  tff(c_1047, plain, (![C_255]: (m1_orders_2(C_255, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_255) | C_255='#skF_3' | ~m2_orders_2(C_255, '#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_1040])).
% 3.29/1.59  tff(c_1053, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', '#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_42, c_1047])).
% 3.29/1.59  tff(c_1058, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_658, c_1053])).
% 3.29/1.59  tff(c_1059, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_1058])).
% 3.29/1.59  tff(c_1069, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1059, c_756])).
% 3.29/1.59  tff(c_1079, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_1069])).
% 3.29/1.59  tff(c_1080, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_1058])).
% 3.29/1.59  tff(c_32, plain, (![C_29, B_27, A_23]: (r1_tarski(C_29, B_27) | ~m1_orders_2(C_29, A_23, B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_orders_2(A_23) | ~v5_orders_2(A_23) | ~v4_orders_2(A_23) | ~v3_orders_2(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.29/1.59  tff(c_1101, plain, (r1_tarski('#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1080, c_32])).
% 3.29/1.59  tff(c_1116, plain, (r1_tarski('#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_865, c_1101])).
% 3.29/1.59  tff(c_1118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_756, c_1116])).
% 3.29/1.59  tff(c_1119, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_750])).
% 3.29/1.59  tff(c_1124, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1119, c_659])).
% 3.29/1.59  tff(c_1128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_1124])).
% 3.29/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.59  
% 3.29/1.59  Inference rules
% 3.29/1.59  ----------------------
% 3.29/1.59  #Ref     : 0
% 3.29/1.59  #Sup     : 219
% 3.29/1.59  #Fact    : 0
% 3.29/1.59  #Define  : 0
% 3.29/1.59  #Split   : 5
% 3.29/1.59  #Chain   : 0
% 3.29/1.59  #Close   : 0
% 3.29/1.59  
% 3.29/1.59  Ordering : KBO
% 3.29/1.59  
% 3.29/1.59  Simplification rules
% 3.29/1.59  ----------------------
% 3.29/1.59  #Subsume      : 59
% 3.29/1.59  #Demod        : 277
% 3.29/1.59  #Tautology    : 113
% 3.29/1.59  #SimpNegUnit  : 35
% 3.29/1.59  #BackRed      : 29
% 3.29/1.59  
% 3.29/1.59  #Partial instantiations: 0
% 3.29/1.59  #Strategies tried      : 1
% 3.29/1.59  
% 3.29/1.59  Timing (in seconds)
% 3.29/1.59  ----------------------
% 3.29/1.59  Preprocessing        : 0.35
% 3.29/1.59  Parsing              : 0.20
% 3.29/1.59  CNF conversion       : 0.03
% 3.29/1.59  Main loop            : 0.41
% 3.29/1.59  Inferencing          : 0.15
% 3.29/1.59  Reduction            : 0.13
% 3.29/1.59  Demodulation         : 0.10
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
