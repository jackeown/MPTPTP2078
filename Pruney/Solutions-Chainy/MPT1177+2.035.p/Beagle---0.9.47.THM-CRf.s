%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:00 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 328 expanded)
%              Number of leaves         :   35 ( 135 expanded)
%              Depth                    :   11
%              Number of atoms          :  321 (1429 expanded)
%              Number of equality atoms :   29 (  57 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_204,negated_conjecture,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_84,axiom,(
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

tff(f_103,axiom,(
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

tff(f_128,axiom,(
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

tff(f_42,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_151,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_orders_2)).

tff(f_179,axiom,(
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

tff(c_4,plain,(
    ! [B_2] : ~ r2_xboole_0(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_12,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_48,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_46,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_44,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_42,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_40,plain,(
    m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_36,plain,(
    m2_orders_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_211,plain,(
    ! [C_115,A_116,B_117] :
      ( m1_subset_1(C_115,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ m2_orders_2(C_115,A_116,B_117)
      | ~ m1_orders_1(B_117,k1_orders_1(u1_struct_0(A_116)))
      | ~ l1_orders_2(A_116)
      | ~ v5_orders_2(A_116)
      | ~ v4_orders_2(A_116)
      | ~ v3_orders_2(A_116)
      | v2_struct_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_213,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_211])).

tff(c_216,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_213])).

tff(c_217,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_216])).

tff(c_75,plain,(
    ! [A_79,B_80] :
      ( r2_xboole_0(A_79,B_80)
      | B_80 = A_79
      | ~ r1_tarski(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,
    ( ~ m1_orders_2('#skF_3','#skF_1','#skF_4')
    | ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_73,plain,(
    ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_86,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_75,c_73])).

tff(c_92,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_58,plain,
    ( r2_xboole_0('#skF_3','#skF_4')
    | m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_74,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_58])).

tff(c_134,plain,(
    ! [C_92,B_93,A_94] :
      ( r1_tarski(C_92,B_93)
      | ~ m1_orders_2(C_92,A_94,B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_orders_2(A_94)
      | ~ v5_orders_2(A_94)
      | ~ v4_orders_2(A_94)
      | ~ v3_orders_2(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_136,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_134])).

tff(c_139,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_136])).

tff(c_140,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_92,c_139])).

tff(c_141,plain,(
    ! [C_95,A_96,B_97] :
      ( m1_subset_1(C_95,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ m2_orders_2(C_95,A_96,B_97)
      | ~ m1_orders_1(B_97,k1_orders_1(u1_struct_0(A_96)))
      | ~ l1_orders_2(A_96)
      | ~ v5_orders_2(A_96)
      | ~ v4_orders_2(A_96)
      | ~ v3_orders_2(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_143,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_141])).

tff(c_148,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_143])).

tff(c_150,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_140,c_148])).

tff(c_151,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_153,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_74])).

tff(c_237,plain,(
    ! [C_127,A_128,B_129] :
      ( ~ m1_orders_2(C_127,A_128,B_129)
      | ~ m1_orders_2(B_129,A_128,C_127)
      | k1_xboole_0 = B_129
      | ~ m1_subset_1(C_127,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_orders_2(A_128)
      | ~ v5_orders_2(A_128)
      | ~ v4_orders_2(A_128)
      | ~ v3_orders_2(A_128)
      | v2_struct_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_239,plain,
    ( ~ m1_orders_2('#skF_4','#skF_1','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_153,c_237])).

tff(c_242,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_217,c_153,c_239])).

tff(c_243,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_242])).

tff(c_16,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_162,plain,(
    ! [A_98,C_99,B_100] :
      ( r1_xboole_0(A_98,k4_xboole_0(C_99,B_100))
      | ~ r1_tarski(A_98,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_165,plain,(
    ! [A_98,A_6] :
      ( r1_xboole_0(A_98,A_6)
      | ~ r1_tarski(A_98,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_162])).

tff(c_218,plain,(
    ! [C_118,D_119,A_120,B_121] :
      ( ~ r1_xboole_0(C_118,D_119)
      | ~ m2_orders_2(D_119,A_120,B_121)
      | ~ m2_orders_2(C_118,A_120,B_121)
      | ~ m1_orders_1(B_121,k1_orders_1(u1_struct_0(A_120)))
      | ~ l1_orders_2(A_120)
      | ~ v5_orders_2(A_120)
      | ~ v4_orders_2(A_120)
      | ~ v3_orders_2(A_120)
      | v2_struct_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_225,plain,(
    ! [A_122,A_123,B_124,A_125] :
      ( ~ m2_orders_2(A_122,A_123,B_124)
      | ~ m2_orders_2(A_125,A_123,B_124)
      | ~ m1_orders_1(B_124,k1_orders_1(u1_struct_0(A_123)))
      | ~ l1_orders_2(A_123)
      | ~ v5_orders_2(A_123)
      | ~ v4_orders_2(A_123)
      | ~ v3_orders_2(A_123)
      | v2_struct_0(A_123)
      | ~ r1_tarski(A_125,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_165,c_218])).

tff(c_227,plain,(
    ! [A_125] :
      ( ~ m2_orders_2(A_125,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ r1_tarski(A_125,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_36,c_225])).

tff(c_230,plain,(
    ! [A_125] :
      ( ~ m2_orders_2(A_125,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1')
      | ~ r1_tarski(A_125,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_227])).

tff(c_232,plain,(
    ! [A_126] :
      ( ~ m2_orders_2(A_126,'#skF_1','#skF_2')
      | ~ r1_tarski(A_126,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_230])).

tff(c_236,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_36,c_232])).

tff(c_260,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_243,c_236])).

tff(c_262,plain,(
    r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_274,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_262,c_6])).

tff(c_294,plain,(
    ! [B_138,A_139] :
      ( B_138 = A_139
      | ~ r1_tarski(B_138,A_139)
      | ~ r1_tarski(A_139,B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_301,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_274,c_294])).

tff(c_320,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_301])).

tff(c_38,plain,(
    m2_orders_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_335,plain,(
    ! [C_147,A_148,B_149] :
      ( m1_subset_1(C_147,k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ m2_orders_2(C_147,A_148,B_149)
      | ~ m1_orders_1(B_149,k1_orders_1(u1_struct_0(A_148)))
      | ~ l1_orders_2(A_148)
      | ~ v5_orders_2(A_148)
      | ~ v4_orders_2(A_148)
      | ~ v3_orders_2(A_148)
      | v2_struct_0(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_339,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_335])).

tff(c_346,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_339])).

tff(c_347,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_346])).

tff(c_261,plain,(
    ~ m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_263,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_261,c_263])).

tff(c_270,plain,(
    ~ m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_383,plain,(
    ! [C_174,A_175,D_176,B_177] :
      ( m1_orders_2(C_174,A_175,D_176)
      | m1_orders_2(D_176,A_175,C_174)
      | D_176 = C_174
      | ~ m2_orders_2(D_176,A_175,B_177)
      | ~ m2_orders_2(C_174,A_175,B_177)
      | ~ m1_orders_1(B_177,k1_orders_1(u1_struct_0(A_175)))
      | ~ l1_orders_2(A_175)
      | ~ v5_orders_2(A_175)
      | ~ v4_orders_2(A_175)
      | ~ v3_orders_2(A_175)
      | v2_struct_0(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_385,plain,(
    ! [C_174] :
      ( m1_orders_2(C_174,'#skF_1','#skF_4')
      | m1_orders_2('#skF_4','#skF_1',C_174)
      | C_174 = '#skF_4'
      | ~ m2_orders_2(C_174,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_383])).

tff(c_390,plain,(
    ! [C_174] :
      ( m1_orders_2(C_174,'#skF_1','#skF_4')
      | m1_orders_2('#skF_4','#skF_1',C_174)
      | C_174 = '#skF_4'
      | ~ m2_orders_2(C_174,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_385])).

tff(c_396,plain,(
    ! [C_178] :
      ( m1_orders_2(C_178,'#skF_1','#skF_4')
      | m1_orders_2('#skF_4','#skF_1',C_178)
      | C_178 = '#skF_4'
      | ~ m2_orders_2(C_178,'#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_390])).

tff(c_402,plain,
    ( m1_orders_2('#skF_3','#skF_1','#skF_4')
    | m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_396])).

tff(c_407,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_270,c_402])).

tff(c_420,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_407])).

tff(c_425,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_320])).

tff(c_434,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_425])).

tff(c_436,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_407])).

tff(c_387,plain,(
    ! [C_174] :
      ( m1_orders_2(C_174,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_174)
      | C_174 = '#skF_3'
      | ~ m2_orders_2(C_174,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_383])).

tff(c_394,plain,(
    ! [C_174] :
      ( m1_orders_2(C_174,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_174)
      | C_174 = '#skF_3'
      | ~ m2_orders_2(C_174,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_387])).

tff(c_408,plain,(
    ! [C_179] :
      ( m1_orders_2(C_179,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_179)
      | C_179 = '#skF_3'
      | ~ m2_orders_2(C_179,'#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_394])).

tff(c_411,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | m1_orders_2('#skF_3','#skF_1','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_408])).

tff(c_417,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_270,c_411])).

tff(c_437,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_436,c_417])).

tff(c_26,plain,(
    ! [C_24,B_22,A_18] :
      ( r1_tarski(C_24,B_22)
      | ~ m1_orders_2(C_24,A_18,B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_orders_2(A_18)
      | ~ v5_orders_2(A_18)
      | ~ v4_orders_2(A_18)
      | ~ v3_orders_2(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_445,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_437,c_26])).

tff(c_460,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_347,c_445])).

tff(c_462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_320,c_460])).

tff(c_463,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_301])).

tff(c_467,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_262])).

tff(c_471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_467])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:41:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.44  
% 2.84/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.45  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.84/1.45  
% 2.84/1.45  %Foreground sorts:
% 2.84/1.45  
% 2.84/1.45  
% 2.84/1.45  %Background operators:
% 2.84/1.45  
% 2.84/1.45  
% 2.84/1.45  %Foreground operators:
% 2.84/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.84/1.45  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.84/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.84/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.84/1.45  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.84/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.84/1.45  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.84/1.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.84/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.84/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.84/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.84/1.45  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.84/1.45  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.84/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.84/1.45  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.84/1.45  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.84/1.45  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.84/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.45  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.84/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.84/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.45  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.84/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.84/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.84/1.45  
% 2.98/1.47  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.98/1.47  tff(f_204, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_orders_2)).
% 2.98/1.47  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.98/1.47  tff(f_84, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.98/1.47  tff(f_103, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_orders_2)).
% 2.98/1.47  tff(f_128, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_orders_2)).
% 2.98/1.47  tff(f_42, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.98/1.47  tff(f_46, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 2.98/1.47  tff(f_151, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_orders_2)).
% 2.98/1.47  tff(f_179, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_orders_2)).
% 2.98/1.47  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.98/1.47  tff(c_50, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.98/1.47  tff(c_12, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.98/1.47  tff(c_48, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.98/1.47  tff(c_46, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.98/1.47  tff(c_44, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.98/1.47  tff(c_42, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.98/1.47  tff(c_40, plain, (m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.98/1.47  tff(c_36, plain, (m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.98/1.47  tff(c_211, plain, (![C_115, A_116, B_117]: (m1_subset_1(C_115, k1_zfmisc_1(u1_struct_0(A_116))) | ~m2_orders_2(C_115, A_116, B_117) | ~m1_orders_1(B_117, k1_orders_1(u1_struct_0(A_116))) | ~l1_orders_2(A_116) | ~v5_orders_2(A_116) | ~v4_orders_2(A_116) | ~v3_orders_2(A_116) | v2_struct_0(A_116))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.98/1.47  tff(c_213, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_211])).
% 2.98/1.47  tff(c_216, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_213])).
% 2.98/1.47  tff(c_217, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_50, c_216])).
% 2.98/1.47  tff(c_75, plain, (![A_79, B_80]: (r2_xboole_0(A_79, B_80) | B_80=A_79 | ~r1_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.98/1.47  tff(c_52, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4') | ~r2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.98/1.47  tff(c_73, plain, (~r2_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_52])).
% 2.98/1.47  tff(c_86, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_75, c_73])).
% 2.98/1.47  tff(c_92, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_86])).
% 2.98/1.47  tff(c_58, plain, (r2_xboole_0('#skF_3', '#skF_4') | m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.98/1.47  tff(c_74, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_73, c_58])).
% 2.98/1.47  tff(c_134, plain, (![C_92, B_93, A_94]: (r1_tarski(C_92, B_93) | ~m1_orders_2(C_92, A_94, B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_orders_2(A_94) | ~v5_orders_2(A_94) | ~v4_orders_2(A_94) | ~v3_orders_2(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.98/1.47  tff(c_136, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_74, c_134])).
% 2.98/1.47  tff(c_139, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_136])).
% 2.98/1.47  tff(c_140, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_50, c_92, c_139])).
% 2.98/1.47  tff(c_141, plain, (![C_95, A_96, B_97]: (m1_subset_1(C_95, k1_zfmisc_1(u1_struct_0(A_96))) | ~m2_orders_2(C_95, A_96, B_97) | ~m1_orders_1(B_97, k1_orders_1(u1_struct_0(A_96))) | ~l1_orders_2(A_96) | ~v5_orders_2(A_96) | ~v4_orders_2(A_96) | ~v3_orders_2(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.98/1.47  tff(c_143, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_141])).
% 2.98/1.47  tff(c_148, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_143])).
% 2.98/1.47  tff(c_150, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_140, c_148])).
% 2.98/1.47  tff(c_151, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_86])).
% 2.98/1.47  tff(c_153, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_74])).
% 2.98/1.47  tff(c_237, plain, (![C_127, A_128, B_129]: (~m1_orders_2(C_127, A_128, B_129) | ~m1_orders_2(B_129, A_128, C_127) | k1_xboole_0=B_129 | ~m1_subset_1(C_127, k1_zfmisc_1(u1_struct_0(A_128))) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_orders_2(A_128) | ~v5_orders_2(A_128) | ~v4_orders_2(A_128) | ~v3_orders_2(A_128) | v2_struct_0(A_128))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.98/1.47  tff(c_239, plain, (~m1_orders_2('#skF_4', '#skF_1', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_153, c_237])).
% 2.98/1.47  tff(c_242, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_217, c_153, c_239])).
% 2.98/1.47  tff(c_243, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_50, c_242])).
% 2.98/1.47  tff(c_16, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.98/1.47  tff(c_162, plain, (![A_98, C_99, B_100]: (r1_xboole_0(A_98, k4_xboole_0(C_99, B_100)) | ~r1_tarski(A_98, B_100))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.98/1.47  tff(c_165, plain, (![A_98, A_6]: (r1_xboole_0(A_98, A_6) | ~r1_tarski(A_98, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_162])).
% 2.98/1.47  tff(c_218, plain, (![C_118, D_119, A_120, B_121]: (~r1_xboole_0(C_118, D_119) | ~m2_orders_2(D_119, A_120, B_121) | ~m2_orders_2(C_118, A_120, B_121) | ~m1_orders_1(B_121, k1_orders_1(u1_struct_0(A_120))) | ~l1_orders_2(A_120) | ~v5_orders_2(A_120) | ~v4_orders_2(A_120) | ~v3_orders_2(A_120) | v2_struct_0(A_120))), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.98/1.47  tff(c_225, plain, (![A_122, A_123, B_124, A_125]: (~m2_orders_2(A_122, A_123, B_124) | ~m2_orders_2(A_125, A_123, B_124) | ~m1_orders_1(B_124, k1_orders_1(u1_struct_0(A_123))) | ~l1_orders_2(A_123) | ~v5_orders_2(A_123) | ~v4_orders_2(A_123) | ~v3_orders_2(A_123) | v2_struct_0(A_123) | ~r1_tarski(A_125, k1_xboole_0))), inference(resolution, [status(thm)], [c_165, c_218])).
% 2.98/1.47  tff(c_227, plain, (![A_125]: (~m2_orders_2(A_125, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1') | ~r1_tarski(A_125, k1_xboole_0))), inference(resolution, [status(thm)], [c_36, c_225])).
% 2.98/1.47  tff(c_230, plain, (![A_125]: (~m2_orders_2(A_125, '#skF_1', '#skF_2') | v2_struct_0('#skF_1') | ~r1_tarski(A_125, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_227])).
% 2.98/1.47  tff(c_232, plain, (![A_126]: (~m2_orders_2(A_126, '#skF_1', '#skF_2') | ~r1_tarski(A_126, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_50, c_230])).
% 2.98/1.47  tff(c_236, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_232])).
% 2.98/1.47  tff(c_260, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_243, c_236])).
% 2.98/1.47  tff(c_262, plain, (r2_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 2.98/1.47  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.98/1.47  tff(c_274, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_262, c_6])).
% 2.98/1.47  tff(c_294, plain, (![B_138, A_139]: (B_138=A_139 | ~r1_tarski(B_138, A_139) | ~r1_tarski(A_139, B_138))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.98/1.47  tff(c_301, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_274, c_294])).
% 2.98/1.47  tff(c_320, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_301])).
% 2.98/1.47  tff(c_38, plain, (m2_orders_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.98/1.47  tff(c_335, plain, (![C_147, A_148, B_149]: (m1_subset_1(C_147, k1_zfmisc_1(u1_struct_0(A_148))) | ~m2_orders_2(C_147, A_148, B_149) | ~m1_orders_1(B_149, k1_orders_1(u1_struct_0(A_148))) | ~l1_orders_2(A_148) | ~v5_orders_2(A_148) | ~v4_orders_2(A_148) | ~v3_orders_2(A_148) | v2_struct_0(A_148))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.98/1.47  tff(c_339, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_335])).
% 2.98/1.47  tff(c_346, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_339])).
% 2.98/1.47  tff(c_347, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_50, c_346])).
% 2.98/1.47  tff(c_261, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 2.98/1.47  tff(c_263, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(splitLeft, [status(thm)], [c_58])).
% 2.98/1.47  tff(c_268, plain, $false, inference(negUnitSimplification, [status(thm)], [c_261, c_263])).
% 2.98/1.47  tff(c_270, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(splitRight, [status(thm)], [c_58])).
% 2.98/1.47  tff(c_383, plain, (![C_174, A_175, D_176, B_177]: (m1_orders_2(C_174, A_175, D_176) | m1_orders_2(D_176, A_175, C_174) | D_176=C_174 | ~m2_orders_2(D_176, A_175, B_177) | ~m2_orders_2(C_174, A_175, B_177) | ~m1_orders_1(B_177, k1_orders_1(u1_struct_0(A_175))) | ~l1_orders_2(A_175) | ~v5_orders_2(A_175) | ~v4_orders_2(A_175) | ~v3_orders_2(A_175) | v2_struct_0(A_175))), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.98/1.47  tff(c_385, plain, (![C_174]: (m1_orders_2(C_174, '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', C_174) | C_174='#skF_4' | ~m2_orders_2(C_174, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_383])).
% 2.98/1.47  tff(c_390, plain, (![C_174]: (m1_orders_2(C_174, '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', C_174) | C_174='#skF_4' | ~m2_orders_2(C_174, '#skF_1', '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_385])).
% 2.98/1.47  tff(c_396, plain, (![C_178]: (m1_orders_2(C_178, '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', C_178) | C_178='#skF_4' | ~m2_orders_2(C_178, '#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_390])).
% 2.98/1.47  tff(c_402, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_38, c_396])).
% 2.98/1.47  tff(c_407, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_270, c_402])).
% 2.98/1.47  tff(c_420, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_407])).
% 2.98/1.47  tff(c_425, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_420, c_320])).
% 2.98/1.47  tff(c_434, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_425])).
% 2.98/1.47  tff(c_436, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_407])).
% 2.98/1.47  tff(c_387, plain, (![C_174]: (m1_orders_2(C_174, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_174) | C_174='#skF_3' | ~m2_orders_2(C_174, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_383])).
% 2.98/1.47  tff(c_394, plain, (![C_174]: (m1_orders_2(C_174, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_174) | C_174='#skF_3' | ~m2_orders_2(C_174, '#skF_1', '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_387])).
% 2.98/1.47  tff(c_408, plain, (![C_179]: (m1_orders_2(C_179, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_179) | C_179='#skF_3' | ~m2_orders_2(C_179, '#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_394])).
% 2.98/1.47  tff(c_411, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', '#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_36, c_408])).
% 2.98/1.47  tff(c_417, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_270, c_411])).
% 2.98/1.47  tff(c_437, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_436, c_417])).
% 2.98/1.47  tff(c_26, plain, (![C_24, B_22, A_18]: (r1_tarski(C_24, B_22) | ~m1_orders_2(C_24, A_18, B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_orders_2(A_18) | ~v5_orders_2(A_18) | ~v4_orders_2(A_18) | ~v3_orders_2(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.98/1.47  tff(c_445, plain, (r1_tarski('#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_437, c_26])).
% 2.98/1.47  tff(c_460, plain, (r1_tarski('#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_347, c_445])).
% 2.98/1.47  tff(c_462, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_320, c_460])).
% 2.98/1.47  tff(c_463, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_301])).
% 2.98/1.47  tff(c_467, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_463, c_262])).
% 2.98/1.47  tff(c_471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_467])).
% 2.98/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.47  
% 2.98/1.47  Inference rules
% 2.98/1.47  ----------------------
% 2.98/1.47  #Ref     : 0
% 2.98/1.47  #Sup     : 65
% 2.98/1.47  #Fact    : 0
% 2.98/1.47  #Define  : 0
% 2.98/1.47  #Split   : 5
% 2.98/1.47  #Chain   : 0
% 2.98/1.47  #Close   : 0
% 2.98/1.47  
% 2.98/1.47  Ordering : KBO
% 2.98/1.47  
% 2.98/1.47  Simplification rules
% 2.98/1.47  ----------------------
% 2.98/1.47  #Subsume      : 8
% 2.98/1.47  #Demod        : 152
% 2.98/1.47  #Tautology    : 33
% 2.98/1.47  #SimpNegUnit  : 28
% 2.98/1.47  #BackRed      : 23
% 2.98/1.47  
% 2.98/1.47  #Partial instantiations: 0
% 2.98/1.47  #Strategies tried      : 1
% 2.98/1.47  
% 2.98/1.47  Timing (in seconds)
% 2.98/1.47  ----------------------
% 2.98/1.47  Preprocessing        : 0.35
% 2.98/1.47  Parsing              : 0.20
% 2.98/1.47  CNF conversion       : 0.03
% 2.98/1.47  Main loop            : 0.29
% 2.98/1.47  Inferencing          : 0.11
% 2.98/1.47  Reduction            : 0.09
% 2.98/1.47  Demodulation         : 0.07
% 2.98/1.47  BG Simplification    : 0.02
% 2.98/1.47  Subsumption          : 0.05
% 2.98/1.47  Abstraction          : 0.01
% 2.98/1.47  MUC search           : 0.00
% 2.98/1.47  Cooper               : 0.00
% 2.98/1.47  Total                : 0.68
% 2.98/1.47  Index Insertion      : 0.00
% 2.98/1.47  Index Deletion       : 0.00
% 2.98/1.47  Index Matching       : 0.00
% 2.98/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
