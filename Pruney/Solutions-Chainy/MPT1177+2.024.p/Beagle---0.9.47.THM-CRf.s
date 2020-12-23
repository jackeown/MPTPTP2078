%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:58 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 360 expanded)
%              Number of leaves         :   37 ( 146 expanded)
%              Depth                    :   10
%              Number of atoms          :  301 (1546 expanded)
%              Number of equality atoms :   32 (  70 expanded)
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

tff(f_207,negated_conjecture,(
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

tff(f_87,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_106,axiom,(
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

tff(f_131,axiom,(
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

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_154,axiom,(
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

tff(f_182,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_52,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_50,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_48,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_46,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_44,plain,(
    m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_40,plain,(
    m2_orders_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_227,plain,(
    ! [C_114,A_115,B_116] :
      ( m1_subset_1(C_114,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ m2_orders_2(C_114,A_115,B_116)
      | ~ m1_orders_1(B_116,k1_orders_1(u1_struct_0(A_115)))
      | ~ l1_orders_2(A_115)
      | ~ v5_orders_2(A_115)
      | ~ v4_orders_2(A_115)
      | ~ v3_orders_2(A_115)
      | v2_struct_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_229,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_227])).

tff(c_232,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_229])).

tff(c_233,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_232])).

tff(c_90,plain,(
    ! [A_88,B_89] :
      ( r2_xboole_0(A_88,B_89)
      | B_89 = A_88
      | ~ r1_tarski(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,
    ( ~ m1_orders_2('#skF_3','#skF_1','#skF_4')
    | ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_69,plain,(
    ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_101,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_69])).

tff(c_136,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_62,plain,
    ( r2_xboole_0('#skF_3','#skF_4')
    | m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_71,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_62])).

tff(c_149,plain,(
    ! [C_94,B_95,A_96] :
      ( r1_tarski(C_94,B_95)
      | ~ m1_orders_2(C_94,A_96,B_95)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_orders_2(A_96)
      | ~ v5_orders_2(A_96)
      | ~ v4_orders_2(A_96)
      | ~ v3_orders_2(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_151,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_71,c_149])).

tff(c_154,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_151])).

tff(c_155,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_136,c_154])).

tff(c_169,plain,(
    ! [C_100,A_101,B_102] :
      ( m1_subset_1(C_100,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ m2_orders_2(C_100,A_101,B_102)
      | ~ m1_orders_1(B_102,k1_orders_1(u1_struct_0(A_101)))
      | ~ l1_orders_2(A_101)
      | ~ v5_orders_2(A_101)
      | ~ v4_orders_2(A_101)
      | ~ v3_orders_2(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_173,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_169])).

tff(c_180,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_173])).

tff(c_182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_155,c_180])).

tff(c_183,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_185,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_71])).

tff(c_250,plain,(
    ! [C_126,A_127,B_128] :
      ( ~ m1_orders_2(C_126,A_127,B_128)
      | ~ m1_orders_2(B_128,A_127,C_126)
      | k1_xboole_0 = B_128
      | ~ m1_subset_1(C_126,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_orders_2(A_127)
      | ~ v5_orders_2(A_127)
      | ~ v4_orders_2(A_127)
      | ~ v3_orders_2(A_127)
      | v2_struct_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_252,plain,
    ( ~ m1_orders_2('#skF_4','#skF_1','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_185,c_250])).

tff(c_255,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_233,c_185,c_252])).

tff(c_256,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_255])).

tff(c_18,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_77,plain,(
    ! [B_86,A_87] :
      ( B_86 = A_87
      | ~ r1_tarski(B_86,A_87)
      | ~ r1_tarski(A_87,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_107,plain,(
    ! [A_90] :
      ( k1_xboole_0 = A_90
      | ~ r1_tarski(A_90,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_77])).

tff(c_120,plain,(
    ! [B_9] : k4_xboole_0(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_107])).

tff(c_258,plain,(
    ! [B_9] : k4_xboole_0('#skF_4',B_9) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_256,c_120])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( r1_xboole_0(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_234,plain,(
    ! [C_117,D_118,A_119,B_120] :
      ( ~ r1_xboole_0(C_117,D_118)
      | ~ m2_orders_2(D_118,A_119,B_120)
      | ~ m2_orders_2(C_117,A_119,B_120)
      | ~ m1_orders_1(B_120,k1_orders_1(u1_struct_0(A_119)))
      | ~ l1_orders_2(A_119)
      | ~ v5_orders_2(A_119)
      | ~ v4_orders_2(A_119)
      | ~ v3_orders_2(A_119)
      | v2_struct_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_238,plain,(
    ! [B_121,A_122,B_123,A_124] :
      ( ~ m2_orders_2(B_121,A_122,B_123)
      | ~ m2_orders_2(A_124,A_122,B_123)
      | ~ m1_orders_1(B_123,k1_orders_1(u1_struct_0(A_122)))
      | ~ l1_orders_2(A_122)
      | ~ v5_orders_2(A_122)
      | ~ v4_orders_2(A_122)
      | ~ v3_orders_2(A_122)
      | v2_struct_0(A_122)
      | k4_xboole_0(A_124,B_121) != A_124 ) ),
    inference(resolution,[status(thm)],[c_22,c_234])).

tff(c_240,plain,(
    ! [A_124] :
      ( ~ m2_orders_2(A_124,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1')
      | k4_xboole_0(A_124,'#skF_4') != A_124 ) ),
    inference(resolution,[status(thm)],[c_40,c_238])).

tff(c_243,plain,(
    ! [A_124] :
      ( ~ m2_orders_2(A_124,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1')
      | k4_xboole_0(A_124,'#skF_4') != A_124 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_240])).

tff(c_245,plain,(
    ! [A_125] :
      ( ~ m2_orders_2(A_125,'#skF_1','#skF_2')
      | k4_xboole_0(A_125,'#skF_4') != A_125 ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_243])).

tff(c_249,plain,(
    k4_xboole_0('#skF_4','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_245])).

tff(c_276,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_249])).

tff(c_278,plain,(
    r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_290,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_278,c_6])).

tff(c_298,plain,(
    ! [B_134,A_135] :
      ( B_134 = A_135
      | ~ r1_tarski(B_134,A_135)
      | ~ r1_tarski(A_135,B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_307,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_290,c_298])).

tff(c_343,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_307])).

tff(c_42,plain,(
    m2_orders_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_383,plain,(
    ! [C_148,A_149,B_150] :
      ( m1_subset_1(C_148,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ m2_orders_2(C_148,A_149,B_150)
      | ~ m1_orders_1(B_150,k1_orders_1(u1_struct_0(A_149)))
      | ~ l1_orders_2(A_149)
      | ~ v5_orders_2(A_149)
      | ~ v4_orders_2(A_149)
      | ~ v3_orders_2(A_149)
      | v2_struct_0(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_385,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_383])).

tff(c_390,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_385])).

tff(c_391,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_390])).

tff(c_14,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_277,plain,(
    ~ m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_433,plain,(
    ! [C_167,A_168,D_169,B_170] :
      ( m1_orders_2(C_167,A_168,D_169)
      | m1_orders_2(D_169,A_168,C_167)
      | D_169 = C_167
      | ~ m2_orders_2(D_169,A_168,B_170)
      | ~ m2_orders_2(C_167,A_168,B_170)
      | ~ m1_orders_1(B_170,k1_orders_1(u1_struct_0(A_168)))
      | ~ l1_orders_2(A_168)
      | ~ v5_orders_2(A_168)
      | ~ v4_orders_2(A_168)
      | ~ v3_orders_2(A_168)
      | v2_struct_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_435,plain,(
    ! [C_167] :
      ( m1_orders_2(C_167,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_167)
      | C_167 = '#skF_3'
      | ~ m2_orders_2(C_167,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_433])).

tff(c_440,plain,(
    ! [C_167] :
      ( m1_orders_2(C_167,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_167)
      | C_167 = '#skF_3'
      | ~ m2_orders_2(C_167,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_435])).

tff(c_446,plain,(
    ! [C_171] :
      ( m1_orders_2(C_171,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_171)
      | C_171 = '#skF_3'
      | ~ m2_orders_2(C_171,'#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_440])).

tff(c_452,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | m1_orders_2('#skF_3','#skF_1','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_446])).

tff(c_457,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_277,c_452])).

tff(c_458,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_457])).

tff(c_466,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_343])).

tff(c_475,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_466])).

tff(c_476,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_457])).

tff(c_30,plain,(
    ! [C_26,B_24,A_20] :
      ( r1_tarski(C_26,B_24)
      | ~ m1_orders_2(C_26,A_20,B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_orders_2(A_20)
      | ~ v5_orders_2(A_20)
      | ~ v4_orders_2(A_20)
      | ~ v3_orders_2(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_495,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_476,c_30])).

tff(c_506,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_391,c_495])).

tff(c_508,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_343,c_506])).

tff(c_509,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_307])).

tff(c_513,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_509,c_278])).

tff(c_517,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_513])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:00:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.93/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.49  
% 2.93/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.50  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.93/1.50  
% 2.93/1.50  %Foreground sorts:
% 2.93/1.50  
% 2.93/1.50  
% 2.93/1.50  %Background operators:
% 2.93/1.50  
% 2.93/1.50  
% 2.93/1.50  %Foreground operators:
% 2.93/1.50  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.93/1.50  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.93/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.93/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.93/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.93/1.50  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.93/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.93/1.50  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.93/1.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.93/1.50  tff('#skF_2', type, '#skF_2': $i).
% 2.93/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.93/1.50  tff('#skF_1', type, '#skF_1': $i).
% 2.93/1.50  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.93/1.50  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.93/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.93/1.50  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.93/1.50  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.93/1.50  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.93/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.93/1.50  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.93/1.50  tff('#skF_4', type, '#skF_4': $i).
% 2.93/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.93/1.50  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.93/1.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.93/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.93/1.50  
% 3.07/1.52  tff(f_35, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 3.07/1.52  tff(f_207, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_orders_2)).
% 3.07/1.52  tff(f_87, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 3.07/1.52  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.07/1.52  tff(f_106, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_orders_2)).
% 3.07/1.52  tff(f_131, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_orders_2)).
% 3.07/1.52  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.07/1.52  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.07/1.52  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.07/1.52  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.07/1.52  tff(f_154, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_orders_2)).
% 3.07/1.52  tff(f_182, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_orders_2)).
% 3.07/1.52  tff(c_8, plain, (![A_3]: (~r2_xboole_0(A_3, A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.07/1.52  tff(c_54, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.07/1.52  tff(c_52, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.07/1.52  tff(c_50, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.07/1.52  tff(c_48, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.07/1.52  tff(c_46, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.07/1.52  tff(c_44, plain, (m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.07/1.52  tff(c_40, plain, (m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.07/1.52  tff(c_227, plain, (![C_114, A_115, B_116]: (m1_subset_1(C_114, k1_zfmisc_1(u1_struct_0(A_115))) | ~m2_orders_2(C_114, A_115, B_116) | ~m1_orders_1(B_116, k1_orders_1(u1_struct_0(A_115))) | ~l1_orders_2(A_115) | ~v5_orders_2(A_115) | ~v4_orders_2(A_115) | ~v3_orders_2(A_115) | v2_struct_0(A_115))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.07/1.52  tff(c_229, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_227])).
% 3.07/1.52  tff(c_232, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_229])).
% 3.07/1.52  tff(c_233, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_54, c_232])).
% 3.07/1.52  tff(c_90, plain, (![A_88, B_89]: (r2_xboole_0(A_88, B_89) | B_89=A_88 | ~r1_tarski(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.07/1.52  tff(c_56, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4') | ~r2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.07/1.52  tff(c_69, plain, (~r2_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_56])).
% 3.07/1.52  tff(c_101, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_90, c_69])).
% 3.07/1.52  tff(c_136, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_101])).
% 3.07/1.52  tff(c_62, plain, (r2_xboole_0('#skF_3', '#skF_4') | m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.07/1.52  tff(c_71, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_69, c_62])).
% 3.07/1.52  tff(c_149, plain, (![C_94, B_95, A_96]: (r1_tarski(C_94, B_95) | ~m1_orders_2(C_94, A_96, B_95) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_orders_2(A_96) | ~v5_orders_2(A_96) | ~v4_orders_2(A_96) | ~v3_orders_2(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.07/1.52  tff(c_151, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_71, c_149])).
% 3.07/1.52  tff(c_154, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_151])).
% 3.07/1.52  tff(c_155, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_54, c_136, c_154])).
% 3.07/1.52  tff(c_169, plain, (![C_100, A_101, B_102]: (m1_subset_1(C_100, k1_zfmisc_1(u1_struct_0(A_101))) | ~m2_orders_2(C_100, A_101, B_102) | ~m1_orders_1(B_102, k1_orders_1(u1_struct_0(A_101))) | ~l1_orders_2(A_101) | ~v5_orders_2(A_101) | ~v4_orders_2(A_101) | ~v3_orders_2(A_101) | v2_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.07/1.52  tff(c_173, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_169])).
% 3.07/1.52  tff(c_180, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_173])).
% 3.07/1.52  tff(c_182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_155, c_180])).
% 3.07/1.52  tff(c_183, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_101])).
% 3.07/1.52  tff(c_185, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_183, c_71])).
% 3.07/1.52  tff(c_250, plain, (![C_126, A_127, B_128]: (~m1_orders_2(C_126, A_127, B_128) | ~m1_orders_2(B_128, A_127, C_126) | k1_xboole_0=B_128 | ~m1_subset_1(C_126, k1_zfmisc_1(u1_struct_0(A_127))) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_orders_2(A_127) | ~v5_orders_2(A_127) | ~v4_orders_2(A_127) | ~v3_orders_2(A_127) | v2_struct_0(A_127))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.07/1.52  tff(c_252, plain, (~m1_orders_2('#skF_4', '#skF_1', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_185, c_250])).
% 3.07/1.52  tff(c_255, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_233, c_185, c_252])).
% 3.07/1.52  tff(c_256, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_54, c_255])).
% 3.07/1.52  tff(c_18, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.07/1.52  tff(c_16, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.07/1.52  tff(c_77, plain, (![B_86, A_87]: (B_86=A_87 | ~r1_tarski(B_86, A_87) | ~r1_tarski(A_87, B_86))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.07/1.52  tff(c_107, plain, (![A_90]: (k1_xboole_0=A_90 | ~r1_tarski(A_90, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_77])).
% 3.07/1.52  tff(c_120, plain, (![B_9]: (k4_xboole_0(k1_xboole_0, B_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_107])).
% 3.07/1.52  tff(c_258, plain, (![B_9]: (k4_xboole_0('#skF_4', B_9)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_256, c_256, c_120])).
% 3.07/1.52  tff(c_22, plain, (![A_10, B_11]: (r1_xboole_0(A_10, B_11) | k4_xboole_0(A_10, B_11)!=A_10)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.07/1.52  tff(c_234, plain, (![C_117, D_118, A_119, B_120]: (~r1_xboole_0(C_117, D_118) | ~m2_orders_2(D_118, A_119, B_120) | ~m2_orders_2(C_117, A_119, B_120) | ~m1_orders_1(B_120, k1_orders_1(u1_struct_0(A_119))) | ~l1_orders_2(A_119) | ~v5_orders_2(A_119) | ~v4_orders_2(A_119) | ~v3_orders_2(A_119) | v2_struct_0(A_119))), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.07/1.52  tff(c_238, plain, (![B_121, A_122, B_123, A_124]: (~m2_orders_2(B_121, A_122, B_123) | ~m2_orders_2(A_124, A_122, B_123) | ~m1_orders_1(B_123, k1_orders_1(u1_struct_0(A_122))) | ~l1_orders_2(A_122) | ~v5_orders_2(A_122) | ~v4_orders_2(A_122) | ~v3_orders_2(A_122) | v2_struct_0(A_122) | k4_xboole_0(A_124, B_121)!=A_124)), inference(resolution, [status(thm)], [c_22, c_234])).
% 3.07/1.52  tff(c_240, plain, (![A_124]: (~m2_orders_2(A_124, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1') | k4_xboole_0(A_124, '#skF_4')!=A_124)), inference(resolution, [status(thm)], [c_40, c_238])).
% 3.07/1.52  tff(c_243, plain, (![A_124]: (~m2_orders_2(A_124, '#skF_1', '#skF_2') | v2_struct_0('#skF_1') | k4_xboole_0(A_124, '#skF_4')!=A_124)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_240])).
% 3.07/1.52  tff(c_245, plain, (![A_125]: (~m2_orders_2(A_125, '#skF_1', '#skF_2') | k4_xboole_0(A_125, '#skF_4')!=A_125)), inference(negUnitSimplification, [status(thm)], [c_54, c_243])).
% 3.07/1.52  tff(c_249, plain, (k4_xboole_0('#skF_4', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_40, c_245])).
% 3.07/1.52  tff(c_276, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_258, c_249])).
% 3.07/1.52  tff(c_278, plain, (r2_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_56])).
% 3.07/1.52  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.07/1.52  tff(c_290, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_278, c_6])).
% 3.07/1.52  tff(c_298, plain, (![B_134, A_135]: (B_134=A_135 | ~r1_tarski(B_134, A_135) | ~r1_tarski(A_135, B_134))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.07/1.52  tff(c_307, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_290, c_298])).
% 3.07/1.52  tff(c_343, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_307])).
% 3.07/1.52  tff(c_42, plain, (m2_orders_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.07/1.52  tff(c_383, plain, (![C_148, A_149, B_150]: (m1_subset_1(C_148, k1_zfmisc_1(u1_struct_0(A_149))) | ~m2_orders_2(C_148, A_149, B_150) | ~m1_orders_1(B_150, k1_orders_1(u1_struct_0(A_149))) | ~l1_orders_2(A_149) | ~v5_orders_2(A_149) | ~v4_orders_2(A_149) | ~v3_orders_2(A_149) | v2_struct_0(A_149))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.07/1.52  tff(c_385, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_383])).
% 3.07/1.52  tff(c_390, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_385])).
% 3.07/1.52  tff(c_391, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_54, c_390])).
% 3.07/1.52  tff(c_14, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.07/1.52  tff(c_277, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(splitRight, [status(thm)], [c_56])).
% 3.07/1.52  tff(c_433, plain, (![C_167, A_168, D_169, B_170]: (m1_orders_2(C_167, A_168, D_169) | m1_orders_2(D_169, A_168, C_167) | D_169=C_167 | ~m2_orders_2(D_169, A_168, B_170) | ~m2_orders_2(C_167, A_168, B_170) | ~m1_orders_1(B_170, k1_orders_1(u1_struct_0(A_168))) | ~l1_orders_2(A_168) | ~v5_orders_2(A_168) | ~v4_orders_2(A_168) | ~v3_orders_2(A_168) | v2_struct_0(A_168))), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.07/1.52  tff(c_435, plain, (![C_167]: (m1_orders_2(C_167, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_167) | C_167='#skF_3' | ~m2_orders_2(C_167, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_433])).
% 3.07/1.52  tff(c_440, plain, (![C_167]: (m1_orders_2(C_167, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_167) | C_167='#skF_3' | ~m2_orders_2(C_167, '#skF_1', '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_435])).
% 3.07/1.52  tff(c_446, plain, (![C_171]: (m1_orders_2(C_171, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_171) | C_171='#skF_3' | ~m2_orders_2(C_171, '#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_440])).
% 3.07/1.52  tff(c_452, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', '#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_40, c_446])).
% 3.07/1.52  tff(c_457, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_277, c_452])).
% 3.07/1.52  tff(c_458, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_457])).
% 3.07/1.52  tff(c_466, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_458, c_343])).
% 3.07/1.52  tff(c_475, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_466])).
% 3.07/1.52  tff(c_476, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_457])).
% 3.07/1.52  tff(c_30, plain, (![C_26, B_24, A_20]: (r1_tarski(C_26, B_24) | ~m1_orders_2(C_26, A_20, B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_orders_2(A_20) | ~v5_orders_2(A_20) | ~v4_orders_2(A_20) | ~v3_orders_2(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.07/1.52  tff(c_495, plain, (r1_tarski('#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_476, c_30])).
% 3.07/1.52  tff(c_506, plain, (r1_tarski('#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_391, c_495])).
% 3.07/1.52  tff(c_508, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_343, c_506])).
% 3.07/1.52  tff(c_509, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_307])).
% 3.07/1.52  tff(c_513, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_509, c_278])).
% 3.07/1.52  tff(c_517, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_513])).
% 3.07/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.52  
% 3.07/1.52  Inference rules
% 3.07/1.52  ----------------------
% 3.07/1.52  #Ref     : 0
% 3.07/1.52  #Sup     : 73
% 3.07/1.52  #Fact    : 0
% 3.07/1.52  #Define  : 0
% 3.07/1.52  #Split   : 5
% 3.07/1.52  #Chain   : 0
% 3.07/1.52  #Close   : 0
% 3.07/1.52  
% 3.07/1.52  Ordering : KBO
% 3.07/1.52  
% 3.07/1.52  Simplification rules
% 3.07/1.52  ----------------------
% 3.07/1.52  #Subsume      : 8
% 3.07/1.52  #Demod        : 166
% 3.07/1.52  #Tautology    : 42
% 3.07/1.52  #SimpNegUnit  : 27
% 3.07/1.52  #BackRed      : 24
% 3.07/1.52  
% 3.07/1.52  #Partial instantiations: 0
% 3.07/1.52  #Strategies tried      : 1
% 3.07/1.52  
% 3.07/1.52  Timing (in seconds)
% 3.07/1.52  ----------------------
% 3.07/1.52  Preprocessing        : 0.36
% 3.07/1.52  Parsing              : 0.20
% 3.07/1.52  CNF conversion       : 0.03
% 3.07/1.52  Main loop            : 0.31
% 3.07/1.52  Inferencing          : 0.11
% 3.07/1.52  Reduction            : 0.10
% 3.07/1.52  Demodulation         : 0.07
% 3.07/1.52  BG Simplification    : 0.02
% 3.07/1.52  Subsumption          : 0.06
% 3.07/1.52  Abstraction          : 0.01
% 3.07/1.52  MUC search           : 0.00
% 3.07/1.52  Cooper               : 0.00
% 3.07/1.52  Total                : 0.72
% 3.07/1.52  Index Insertion      : 0.00
% 3.07/1.52  Index Deletion       : 0.00
% 3.07/1.52  Index Matching       : 0.00
% 3.07/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
