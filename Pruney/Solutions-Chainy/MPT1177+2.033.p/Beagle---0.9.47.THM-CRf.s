%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:59 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 301 expanded)
%              Number of leaves         :   38 ( 126 expanded)
%              Depth                    :   12
%              Number of atoms          :  301 (1260 expanded)
%              Number of equality atoms :   33 (  58 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

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

tff(f_210,negated_conjecture,(
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

tff(f_90,axiom,(
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

tff(f_109,axiom,(
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

tff(f_134,axiom,(
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

tff(f_44,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_157,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_185,axiom,(
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

tff(c_54,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_52,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_50,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_48,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_46,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_44,plain,(
    m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_40,plain,(
    m2_orders_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_315,plain,(
    ! [C_120,A_121,B_122] :
      ( m1_subset_1(C_120,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ m2_orders_2(C_120,A_121,B_122)
      | ~ m1_orders_1(B_122,k1_orders_1(u1_struct_0(A_121)))
      | ~ l1_orders_2(A_121)
      | ~ v5_orders_2(A_121)
      | ~ v4_orders_2(A_121)
      | ~ v3_orders_2(A_121)
      | v2_struct_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_317,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_315])).

tff(c_320,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_317])).

tff(c_321,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_320])).

tff(c_113,plain,(
    ! [A_88,B_89] :
      ( r2_xboole_0(A_88,B_89)
      | B_89 = A_88
      | ~ r1_tarski(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,
    ( ~ m1_orders_2('#skF_3','#skF_1','#skF_4')
    | ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_69,plain,(
    ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_124,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_113,c_69])).

tff(c_130,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_62,plain,
    ( r2_xboole_0('#skF_3','#skF_4')
    | m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_112,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_62])).

tff(c_190,plain,(
    ! [C_96,B_97,A_98] :
      ( r1_tarski(C_96,B_97)
      | ~ m1_orders_2(C_96,A_98,B_97)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_orders_2(A_98)
      | ~ v5_orders_2(A_98)
      | ~ v4_orders_2(A_98)
      | ~ v3_orders_2(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_192,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_112,c_190])).

tff(c_195,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_192])).

tff(c_196,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_130,c_195])).

tff(c_210,plain,(
    ! [C_102,A_103,B_104] :
      ( m1_subset_1(C_102,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ m2_orders_2(C_102,A_103,B_104)
      | ~ m1_orders_1(B_104,k1_orders_1(u1_struct_0(A_103)))
      | ~ l1_orders_2(A_103)
      | ~ v5_orders_2(A_103)
      | ~ v4_orders_2(A_103)
      | ~ v3_orders_2(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_214,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_210])).

tff(c_221,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_214])).

tff(c_223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_196,c_221])).

tff(c_224,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_226,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_112])).

tff(c_326,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_328,plain,
    ( ~ m1_orders_2('#skF_4','#skF_1','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_226,c_326])).

tff(c_331,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_321,c_226,c_328])).

tff(c_332,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_331])).

tff(c_16,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_258,plain,(
    ! [A_108,B_109] :
      ( k2_xboole_0(A_108,k4_xboole_0(B_109,A_108)) = B_109
      | ~ r1_tarski(A_108,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_75,plain,(
    ! [A_84,B_85] :
      ( k2_xboole_0(A_84,B_85) = B_85
      | ~ r1_tarski(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_83,plain,(
    ! [A_7] : k2_xboole_0(k1_xboole_0,A_7) = A_7 ),
    inference(resolution,[status(thm)],[c_16,c_75])).

tff(c_265,plain,(
    ! [B_109] :
      ( k4_xboole_0(B_109,k1_xboole_0) = B_109
      | ~ r1_tarski(k1_xboole_0,B_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_83])).

tff(c_275,plain,(
    ! [B_109] : k4_xboole_0(B_109,k1_xboole_0) = B_109 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_265])).

tff(c_334,plain,(
    ! [B_109] : k4_xboole_0(B_109,'#skF_4') = B_109 ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_275])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( r1_xboole_0(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_322,plain,(
    ! [C_123,D_124,A_125,B_126] :
      ( ~ r1_xboole_0(C_123,D_124)
      | ~ m2_orders_2(D_124,A_125,B_126)
      | ~ m2_orders_2(C_123,A_125,B_126)
      | ~ m1_orders_1(B_126,k1_orders_1(u1_struct_0(A_125)))
      | ~ l1_orders_2(A_125)
      | ~ v5_orders_2(A_125)
      | ~ v4_orders_2(A_125)
      | ~ v3_orders_2(A_125)
      | v2_struct_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_432,plain,(
    ! [B_143,A_144,B_145,A_146] :
      ( ~ m2_orders_2(B_143,A_144,B_145)
      | ~ m2_orders_2(A_146,A_144,B_145)
      | ~ m1_orders_1(B_145,k1_orders_1(u1_struct_0(A_144)))
      | ~ l1_orders_2(A_144)
      | ~ v5_orders_2(A_144)
      | ~ v4_orders_2(A_144)
      | ~ v3_orders_2(A_144)
      | v2_struct_0(A_144)
      | k4_xboole_0(A_146,B_143) != A_146 ) ),
    inference(resolution,[status(thm)],[c_22,c_322])).

tff(c_434,plain,(
    ! [A_146] :
      ( ~ m2_orders_2(A_146,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1')
      | k4_xboole_0(A_146,'#skF_4') != A_146 ) ),
    inference(resolution,[status(thm)],[c_40,c_432])).

tff(c_437,plain,(
    ! [A_146] :
      ( ~ m2_orders_2(A_146,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_52,c_50,c_48,c_46,c_44,c_434])).

tff(c_438,plain,(
    ! [A_146] : ~ m2_orders_2(A_146,'#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_437])).

tff(c_440,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_438,c_40])).

tff(c_442,plain,(
    r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_446,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_442,c_6])).

tff(c_499,plain,(
    ! [B_153,A_154] :
      ( B_153 = A_154
      | ~ r1_tarski(B_153,A_154)
      | ~ r1_tarski(A_154,B_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_506,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_446,c_499])).

tff(c_525,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_506])).

tff(c_42,plain,(
    m2_orders_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_589,plain,(
    ! [C_167,A_168,B_169] :
      ( m1_subset_1(C_167,k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ m2_orders_2(C_167,A_168,B_169)
      | ~ m1_orders_1(B_169,k1_orders_1(u1_struct_0(A_168)))
      | ~ l1_orders_2(A_168)
      | ~ v5_orders_2(A_168)
      | ~ v4_orders_2(A_168)
      | ~ v3_orders_2(A_168)
      | v2_struct_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_591,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_589])).

tff(c_596,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_591])).

tff(c_597,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_596])).

tff(c_12,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_441,plain,(
    ~ m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_640,plain,(
    ! [C_190,A_191,D_192,B_193] :
      ( m1_orders_2(C_190,A_191,D_192)
      | m1_orders_2(D_192,A_191,C_190)
      | D_192 = C_190
      | ~ m2_orders_2(D_192,A_191,B_193)
      | ~ m2_orders_2(C_190,A_191,B_193)
      | ~ m1_orders_1(B_193,k1_orders_1(u1_struct_0(A_191)))
      | ~ l1_orders_2(A_191)
      | ~ v5_orders_2(A_191)
      | ~ v4_orders_2(A_191)
      | ~ v3_orders_2(A_191)
      | v2_struct_0(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_642,plain,(
    ! [C_190] :
      ( m1_orders_2(C_190,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_190)
      | C_190 = '#skF_3'
      | ~ m2_orders_2(C_190,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_640])).

tff(c_647,plain,(
    ! [C_190] :
      ( m1_orders_2(C_190,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_190)
      | C_190 = '#skF_3'
      | ~ m2_orders_2(C_190,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_642])).

tff(c_653,plain,(
    ! [C_194] :
      ( m1_orders_2(C_194,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_194)
      | C_194 = '#skF_3'
      | ~ m2_orders_2(C_194,'#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_647])).

tff(c_659,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | m1_orders_2('#skF_3','#skF_1','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_653])).

tff(c_664,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_441,c_659])).

tff(c_665,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_664])).

tff(c_673,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_665,c_525])).

tff(c_683,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_673])).

tff(c_684,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_664])).

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
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_693,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_684,c_30])).

tff(c_708,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_597,c_693])).

tff(c_710,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_525,c_708])).

tff(c_711,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_506])).

tff(c_716,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_711,c_442])).

tff(c_721,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_716])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:37:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.42  
% 2.76/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.42  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.76/1.42  
% 2.76/1.42  %Foreground sorts:
% 2.76/1.42  
% 2.76/1.42  
% 2.76/1.42  %Background operators:
% 2.76/1.42  
% 2.76/1.42  
% 2.76/1.42  %Foreground operators:
% 2.76/1.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.76/1.42  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.76/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.76/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.76/1.42  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.76/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.76/1.42  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.76/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.76/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.76/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.76/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.76/1.42  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.76/1.42  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.76/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.76/1.42  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.76/1.42  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.76/1.42  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.76/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.42  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.76/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.76/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.42  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.76/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.76/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.76/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.76/1.42  
% 3.06/1.44  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.06/1.44  tff(f_210, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_orders_2)).
% 3.06/1.44  tff(f_90, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 3.06/1.44  tff(f_109, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_orders_2)).
% 3.06/1.44  tff(f_134, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_orders_2)).
% 3.06/1.44  tff(f_44, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.06/1.44  tff(f_48, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 3.06/1.44  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.06/1.44  tff(f_52, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.06/1.44  tff(f_157, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_orders_2)).
% 3.06/1.44  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.06/1.44  tff(f_185, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_orders_2)).
% 3.06/1.44  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.06/1.44  tff(c_54, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.06/1.44  tff(c_52, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.06/1.44  tff(c_50, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.06/1.44  tff(c_48, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.06/1.44  tff(c_46, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.06/1.44  tff(c_44, plain, (m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.06/1.44  tff(c_40, plain, (m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.06/1.44  tff(c_315, plain, (![C_120, A_121, B_122]: (m1_subset_1(C_120, k1_zfmisc_1(u1_struct_0(A_121))) | ~m2_orders_2(C_120, A_121, B_122) | ~m1_orders_1(B_122, k1_orders_1(u1_struct_0(A_121))) | ~l1_orders_2(A_121) | ~v5_orders_2(A_121) | ~v4_orders_2(A_121) | ~v3_orders_2(A_121) | v2_struct_0(A_121))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.06/1.44  tff(c_317, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_315])).
% 3.06/1.44  tff(c_320, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_317])).
% 3.06/1.44  tff(c_321, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_54, c_320])).
% 3.06/1.44  tff(c_113, plain, (![A_88, B_89]: (r2_xboole_0(A_88, B_89) | B_89=A_88 | ~r1_tarski(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.06/1.44  tff(c_56, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4') | ~r2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.06/1.44  tff(c_69, plain, (~r2_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_56])).
% 3.06/1.44  tff(c_124, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_113, c_69])).
% 3.06/1.44  tff(c_130, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_124])).
% 3.06/1.44  tff(c_62, plain, (r2_xboole_0('#skF_3', '#skF_4') | m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.06/1.44  tff(c_112, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_69, c_62])).
% 3.06/1.44  tff(c_190, plain, (![C_96, B_97, A_98]: (r1_tarski(C_96, B_97) | ~m1_orders_2(C_96, A_98, B_97) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_orders_2(A_98) | ~v5_orders_2(A_98) | ~v4_orders_2(A_98) | ~v3_orders_2(A_98) | v2_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.06/1.44  tff(c_192, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_112, c_190])).
% 3.06/1.44  tff(c_195, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_192])).
% 3.06/1.44  tff(c_196, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_54, c_130, c_195])).
% 3.06/1.44  tff(c_210, plain, (![C_102, A_103, B_104]: (m1_subset_1(C_102, k1_zfmisc_1(u1_struct_0(A_103))) | ~m2_orders_2(C_102, A_103, B_104) | ~m1_orders_1(B_104, k1_orders_1(u1_struct_0(A_103))) | ~l1_orders_2(A_103) | ~v5_orders_2(A_103) | ~v4_orders_2(A_103) | ~v3_orders_2(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.06/1.44  tff(c_214, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_210])).
% 3.06/1.44  tff(c_221, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_214])).
% 3.06/1.44  tff(c_223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_196, c_221])).
% 3.06/1.44  tff(c_224, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_124])).
% 3.06/1.44  tff(c_226, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_224, c_112])).
% 3.06/1.44  tff(c_326, plain, (![C_127, A_128, B_129]: (~m1_orders_2(C_127, A_128, B_129) | ~m1_orders_2(B_129, A_128, C_127) | k1_xboole_0=B_129 | ~m1_subset_1(C_127, k1_zfmisc_1(u1_struct_0(A_128))) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_orders_2(A_128) | ~v5_orders_2(A_128) | ~v4_orders_2(A_128) | ~v3_orders_2(A_128) | v2_struct_0(A_128))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.06/1.44  tff(c_328, plain, (~m1_orders_2('#skF_4', '#skF_1', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_226, c_326])).
% 3.06/1.44  tff(c_331, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_321, c_226, c_328])).
% 3.06/1.44  tff(c_332, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_54, c_331])).
% 3.06/1.44  tff(c_16, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.06/1.44  tff(c_258, plain, (![A_108, B_109]: (k2_xboole_0(A_108, k4_xboole_0(B_109, A_108))=B_109 | ~r1_tarski(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.06/1.44  tff(c_75, plain, (![A_84, B_85]: (k2_xboole_0(A_84, B_85)=B_85 | ~r1_tarski(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.06/1.44  tff(c_83, plain, (![A_7]: (k2_xboole_0(k1_xboole_0, A_7)=A_7)), inference(resolution, [status(thm)], [c_16, c_75])).
% 3.06/1.44  tff(c_265, plain, (![B_109]: (k4_xboole_0(B_109, k1_xboole_0)=B_109 | ~r1_tarski(k1_xboole_0, B_109))), inference(superposition, [status(thm), theory('equality')], [c_258, c_83])).
% 3.06/1.44  tff(c_275, plain, (![B_109]: (k4_xboole_0(B_109, k1_xboole_0)=B_109)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_265])).
% 3.06/1.44  tff(c_334, plain, (![B_109]: (k4_xboole_0(B_109, '#skF_4')=B_109)), inference(demodulation, [status(thm), theory('equality')], [c_332, c_275])).
% 3.06/1.44  tff(c_22, plain, (![A_10, B_11]: (r1_xboole_0(A_10, B_11) | k4_xboole_0(A_10, B_11)!=A_10)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.06/1.44  tff(c_322, plain, (![C_123, D_124, A_125, B_126]: (~r1_xboole_0(C_123, D_124) | ~m2_orders_2(D_124, A_125, B_126) | ~m2_orders_2(C_123, A_125, B_126) | ~m1_orders_1(B_126, k1_orders_1(u1_struct_0(A_125))) | ~l1_orders_2(A_125) | ~v5_orders_2(A_125) | ~v4_orders_2(A_125) | ~v3_orders_2(A_125) | v2_struct_0(A_125))), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.06/1.44  tff(c_432, plain, (![B_143, A_144, B_145, A_146]: (~m2_orders_2(B_143, A_144, B_145) | ~m2_orders_2(A_146, A_144, B_145) | ~m1_orders_1(B_145, k1_orders_1(u1_struct_0(A_144))) | ~l1_orders_2(A_144) | ~v5_orders_2(A_144) | ~v4_orders_2(A_144) | ~v3_orders_2(A_144) | v2_struct_0(A_144) | k4_xboole_0(A_146, B_143)!=A_146)), inference(resolution, [status(thm)], [c_22, c_322])).
% 3.06/1.44  tff(c_434, plain, (![A_146]: (~m2_orders_2(A_146, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1') | k4_xboole_0(A_146, '#skF_4')!=A_146)), inference(resolution, [status(thm)], [c_40, c_432])).
% 3.06/1.44  tff(c_437, plain, (![A_146]: (~m2_orders_2(A_146, '#skF_1', '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_334, c_52, c_50, c_48, c_46, c_44, c_434])).
% 3.06/1.44  tff(c_438, plain, (![A_146]: (~m2_orders_2(A_146, '#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_437])).
% 3.06/1.44  tff(c_440, plain, $false, inference(negUnitSimplification, [status(thm)], [c_438, c_40])).
% 3.06/1.44  tff(c_442, plain, (r2_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_56])).
% 3.06/1.44  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.06/1.44  tff(c_446, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_442, c_6])).
% 3.06/1.44  tff(c_499, plain, (![B_153, A_154]: (B_153=A_154 | ~r1_tarski(B_153, A_154) | ~r1_tarski(A_154, B_153))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.06/1.44  tff(c_506, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_446, c_499])).
% 3.06/1.44  tff(c_525, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_506])).
% 3.06/1.44  tff(c_42, plain, (m2_orders_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.06/1.44  tff(c_589, plain, (![C_167, A_168, B_169]: (m1_subset_1(C_167, k1_zfmisc_1(u1_struct_0(A_168))) | ~m2_orders_2(C_167, A_168, B_169) | ~m1_orders_1(B_169, k1_orders_1(u1_struct_0(A_168))) | ~l1_orders_2(A_168) | ~v5_orders_2(A_168) | ~v4_orders_2(A_168) | ~v3_orders_2(A_168) | v2_struct_0(A_168))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.06/1.44  tff(c_591, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_589])).
% 3.06/1.44  tff(c_596, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_591])).
% 3.06/1.44  tff(c_597, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_54, c_596])).
% 3.06/1.44  tff(c_12, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.06/1.44  tff(c_441, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(splitRight, [status(thm)], [c_56])).
% 3.06/1.44  tff(c_640, plain, (![C_190, A_191, D_192, B_193]: (m1_orders_2(C_190, A_191, D_192) | m1_orders_2(D_192, A_191, C_190) | D_192=C_190 | ~m2_orders_2(D_192, A_191, B_193) | ~m2_orders_2(C_190, A_191, B_193) | ~m1_orders_1(B_193, k1_orders_1(u1_struct_0(A_191))) | ~l1_orders_2(A_191) | ~v5_orders_2(A_191) | ~v4_orders_2(A_191) | ~v3_orders_2(A_191) | v2_struct_0(A_191))), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.06/1.44  tff(c_642, plain, (![C_190]: (m1_orders_2(C_190, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_190) | C_190='#skF_3' | ~m2_orders_2(C_190, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_640])).
% 3.06/1.44  tff(c_647, plain, (![C_190]: (m1_orders_2(C_190, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_190) | C_190='#skF_3' | ~m2_orders_2(C_190, '#skF_1', '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_642])).
% 3.06/1.44  tff(c_653, plain, (![C_194]: (m1_orders_2(C_194, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_194) | C_194='#skF_3' | ~m2_orders_2(C_194, '#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_647])).
% 3.06/1.44  tff(c_659, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', '#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_40, c_653])).
% 3.06/1.44  tff(c_664, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_441, c_659])).
% 3.06/1.44  tff(c_665, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_664])).
% 3.06/1.44  tff(c_673, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_665, c_525])).
% 3.06/1.44  tff(c_683, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_673])).
% 3.06/1.44  tff(c_684, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_664])).
% 3.06/1.44  tff(c_30, plain, (![C_26, B_24, A_20]: (r1_tarski(C_26, B_24) | ~m1_orders_2(C_26, A_20, B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_orders_2(A_20) | ~v5_orders_2(A_20) | ~v4_orders_2(A_20) | ~v3_orders_2(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.06/1.44  tff(c_693, plain, (r1_tarski('#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_684, c_30])).
% 3.06/1.44  tff(c_708, plain, (r1_tarski('#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_597, c_693])).
% 3.06/1.44  tff(c_710, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_525, c_708])).
% 3.06/1.44  tff(c_711, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_506])).
% 3.06/1.44  tff(c_716, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_711, c_442])).
% 3.06/1.44  tff(c_721, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_716])).
% 3.06/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.44  
% 3.06/1.44  Inference rules
% 3.06/1.44  ----------------------
% 3.06/1.44  #Ref     : 0
% 3.06/1.44  #Sup     : 112
% 3.06/1.44  #Fact    : 0
% 3.06/1.44  #Define  : 0
% 3.06/1.44  #Split   : 4
% 3.06/1.44  #Chain   : 0
% 3.06/1.44  #Close   : 0
% 3.06/1.44  
% 3.06/1.44  Ordering : KBO
% 3.06/1.44  
% 3.06/1.44  Simplification rules
% 3.06/1.44  ----------------------
% 3.06/1.44  #Subsume      : 9
% 3.06/1.44  #Demod        : 196
% 3.06/1.44  #Tautology    : 79
% 3.06/1.44  #SimpNegUnit  : 30
% 3.06/1.44  #BackRed      : 27
% 3.06/1.44  
% 3.06/1.44  #Partial instantiations: 0
% 3.06/1.44  #Strategies tried      : 1
% 3.06/1.44  
% 3.06/1.44  Timing (in seconds)
% 3.06/1.44  ----------------------
% 3.06/1.45  Preprocessing        : 0.34
% 3.06/1.45  Parsing              : 0.18
% 3.06/1.45  CNF conversion       : 0.03
% 3.06/1.45  Main loop            : 0.33
% 3.06/1.45  Inferencing          : 0.12
% 3.06/1.45  Reduction            : 0.11
% 3.06/1.45  Demodulation         : 0.08
% 3.06/1.45  BG Simplification    : 0.02
% 3.06/1.45  Subsumption          : 0.06
% 3.06/1.45  Abstraction          : 0.01
% 3.06/1.45  MUC search           : 0.00
% 3.06/1.45  Cooper               : 0.00
% 3.06/1.45  Total                : 0.71
% 3.06/1.45  Index Insertion      : 0.00
% 3.06/1.45  Index Deletion       : 0.00
% 3.06/1.45  Index Matching       : 0.00
% 3.06/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
