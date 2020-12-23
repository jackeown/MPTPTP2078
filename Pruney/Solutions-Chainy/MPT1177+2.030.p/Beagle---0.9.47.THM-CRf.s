%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:59 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 301 expanded)
%              Number of leaves         :   35 ( 125 expanded)
%              Depth                    :   10
%              Number of atoms          :  298 (1266 expanded)
%              Number of equality atoms :   35 (  65 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_orders_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_orders_2)).

tff(c_4,plain,(
    ! [B_2] : ~ r2_xboole_0(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_50,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_48,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_46,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_44,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_42,plain,(
    m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_38,plain,(
    m2_orders_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_226,plain,(
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

tff(c_228,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_226])).

tff(c_231,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_228])).

tff(c_232,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_231])).

tff(c_100,plain,(
    ! [A_87,B_88] :
      ( r2_xboole_0(A_87,B_88)
      | B_88 = A_87
      | ~ r1_tarski(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_54,plain,
    ( ~ m1_orders_2('#skF_3','#skF_1','#skF_4')
    | ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_77,plain,(
    ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_111,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_77])).

tff(c_117,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_60,plain,
    ( r2_xboole_0('#skF_3','#skF_4')
    | m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_89,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_60])).

tff(c_134,plain,(
    ! [C_91,B_92,A_93] :
      ( r1_tarski(C_91,B_92)
      | ~ m1_orders_2(C_91,A_93,B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_orders_2(A_93)
      | ~ v5_orders_2(A_93)
      | ~ v4_orders_2(A_93)
      | ~ v3_orders_2(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_136,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_89,c_134])).

tff(c_139,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_136])).

tff(c_140,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_117,c_139])).

tff(c_168,plain,(
    ! [C_102,A_103,B_104] :
      ( m1_subset_1(C_102,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ m2_orders_2(C_102,A_103,B_104)
      | ~ m1_orders_1(B_104,k1_orders_1(u1_struct_0(A_103)))
      | ~ l1_orders_2(A_103)
      | ~ v5_orders_2(A_103)
      | ~ v4_orders_2(A_103)
      | ~ v3_orders_2(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_172,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_168])).

tff(c_179,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_172])).

tff(c_181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_140,c_179])).

tff(c_182,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_184,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_89])).

tff(c_244,plain,(
    ! [C_125,A_126,B_127] :
      ( ~ m1_orders_2(C_125,A_126,B_127)
      | ~ m1_orders_2(B_127,A_126,C_125)
      | k1_xboole_0 = B_127
      | ~ m1_subset_1(C_125,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_orders_2(A_126)
      | ~ v5_orders_2(A_126)
      | ~ v4_orders_2(A_126)
      | ~ v3_orders_2(A_126)
      | v2_struct_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_246,plain,
    ( ~ m1_orders_2('#skF_4','#skF_1','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_184,c_244])).

tff(c_249,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_232,c_184,c_246])).

tff(c_250,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_249])).

tff(c_12,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_65,plain,(
    ! [A_76,B_77] :
      ( k4_xboole_0(A_76,B_77) = k1_xboole_0
      | ~ r1_tarski(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_69,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_65])).

tff(c_255,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_69])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( r1_xboole_0(A_7,B_8)
      | k4_xboole_0(A_7,B_8) != A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_240,plain,(
    ! [C_121,D_122,A_123,B_124] :
      ( ~ r1_xboole_0(C_121,D_122)
      | ~ m2_orders_2(D_122,A_123,B_124)
      | ~ m2_orders_2(C_121,A_123,B_124)
      | ~ m1_orders_1(B_124,k1_orders_1(u1_struct_0(A_123)))
      | ~ l1_orders_2(A_123)
      | ~ v5_orders_2(A_123)
      | ~ v4_orders_2(A_123)
      | ~ v3_orders_2(A_123)
      | v2_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_323,plain,(
    ! [B_146,A_147,B_148,A_149] :
      ( ~ m2_orders_2(B_146,A_147,B_148)
      | ~ m2_orders_2(A_149,A_147,B_148)
      | ~ m1_orders_1(B_148,k1_orders_1(u1_struct_0(A_147)))
      | ~ l1_orders_2(A_147)
      | ~ v5_orders_2(A_147)
      | ~ v4_orders_2(A_147)
      | ~ v3_orders_2(A_147)
      | v2_struct_0(A_147)
      | k4_xboole_0(A_149,B_146) != A_149 ) ),
    inference(resolution,[status(thm)],[c_20,c_240])).

tff(c_325,plain,(
    ! [A_149] :
      ( ~ m2_orders_2(A_149,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1')
      | k4_xboole_0(A_149,'#skF_4') != A_149 ) ),
    inference(resolution,[status(thm)],[c_38,c_323])).

tff(c_328,plain,(
    ! [A_149] :
      ( ~ m2_orders_2(A_149,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1')
      | k4_xboole_0(A_149,'#skF_4') != A_149 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_325])).

tff(c_330,plain,(
    ! [A_150] :
      ( ~ m2_orders_2(A_150,'#skF_1','#skF_2')
      | k4_xboole_0(A_150,'#skF_4') != A_150 ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_328])).

tff(c_333,plain,(
    k4_xboole_0('#skF_4','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_330])).

tff(c_337,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_333])).

tff(c_339,plain,(
    r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_355,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_339,c_6])).

tff(c_376,plain,(
    ! [B_157,A_158] :
      ( B_157 = A_158
      | ~ r1_tarski(B_157,A_158)
      | ~ r1_tarski(A_158,B_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_384,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_355,c_376])).

tff(c_389,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_384])).

tff(c_40,plain,(
    m2_orders_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_448,plain,(
    ! [C_174,A_175,B_176] :
      ( m1_subset_1(C_174,k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ m2_orders_2(C_174,A_175,B_176)
      | ~ m1_orders_1(B_176,k1_orders_1(u1_struct_0(A_175)))
      | ~ l1_orders_2(A_175)
      | ~ v5_orders_2(A_175)
      | ~ v4_orders_2(A_175)
      | ~ v3_orders_2(A_175)
      | v2_struct_0(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_450,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_448])).

tff(c_455,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_450])).

tff(c_456,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_455])).

tff(c_338,plain,(
    ~ m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_500,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_504,plain,(
    ! [C_190] :
      ( m1_orders_2(C_190,'#skF_1','#skF_4')
      | m1_orders_2('#skF_4','#skF_1',C_190)
      | C_190 = '#skF_4'
      | ~ m2_orders_2(C_190,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_500])).

tff(c_511,plain,(
    ! [C_190] :
      ( m1_orders_2(C_190,'#skF_1','#skF_4')
      | m1_orders_2('#skF_4','#skF_1',C_190)
      | C_190 = '#skF_4'
      | ~ m2_orders_2(C_190,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_504])).

tff(c_513,plain,(
    ! [C_194] :
      ( m1_orders_2(C_194,'#skF_1','#skF_4')
      | m1_orders_2('#skF_4','#skF_1',C_194)
      | C_194 = '#skF_4'
      | ~ m2_orders_2(C_194,'#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_511])).

tff(c_516,plain,
    ( m1_orders_2('#skF_3','#skF_1','#skF_4')
    | m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_513])).

tff(c_522,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_338,c_516])).

tff(c_525,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_522])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_406,plain,(
    k4_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_389])).

tff(c_544,plain,(
    k4_xboole_0('#skF_4','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_406])).

tff(c_556,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_544])).

tff(c_557,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_522])).

tff(c_28,plain,(
    ! [C_23,B_21,A_17] :
      ( r1_tarski(C_23,B_21)
      | ~ m1_orders_2(C_23,A_17,B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_orders_2(A_17)
      | ~ v5_orders_2(A_17)
      | ~ v4_orders_2(A_17)
      | ~ v3_orders_2(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_564,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_557,c_28])).

tff(c_575,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_456,c_564])).

tff(c_577,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_389,c_575])).

tff(c_578,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_384])).

tff(c_583,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_578,c_339])).

tff(c_588,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_583])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:21:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.40  
% 2.79/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.40  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.79/1.40  
% 2.79/1.40  %Foreground sorts:
% 2.79/1.40  
% 2.79/1.40  
% 2.79/1.40  %Background operators:
% 2.79/1.40  
% 2.79/1.40  
% 2.79/1.40  %Foreground operators:
% 2.79/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.79/1.40  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.79/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.79/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.79/1.40  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.79/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.79/1.40  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.79/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.79/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.79/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.79/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.79/1.40  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.79/1.40  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.79/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.79/1.40  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.79/1.40  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.79/1.40  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.79/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.40  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.79/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.79/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.40  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.79/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.79/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.79/1.40  
% 2.79/1.42  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.79/1.42  tff(f_204, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_orders_2)).
% 2.79/1.42  tff(f_84, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.79/1.42  tff(f_103, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_orders_2)).
% 2.79/1.42  tff(f_128, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_orders_2)).
% 2.79/1.42  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.79/1.42  tff(f_42, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.79/1.42  tff(f_46, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.79/1.42  tff(f_151, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_orders_2)).
% 2.79/1.42  tff(f_179, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_orders_2)).
% 2.79/1.42  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.79/1.42  tff(c_52, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.79/1.42  tff(c_50, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.79/1.42  tff(c_48, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.79/1.42  tff(c_46, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.79/1.42  tff(c_44, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.79/1.42  tff(c_42, plain, (m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.79/1.42  tff(c_38, plain, (m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.79/1.42  tff(c_226, plain, (![C_115, A_116, B_117]: (m1_subset_1(C_115, k1_zfmisc_1(u1_struct_0(A_116))) | ~m2_orders_2(C_115, A_116, B_117) | ~m1_orders_1(B_117, k1_orders_1(u1_struct_0(A_116))) | ~l1_orders_2(A_116) | ~v5_orders_2(A_116) | ~v4_orders_2(A_116) | ~v3_orders_2(A_116) | v2_struct_0(A_116))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.79/1.42  tff(c_228, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_226])).
% 2.79/1.42  tff(c_231, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_228])).
% 2.79/1.42  tff(c_232, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_52, c_231])).
% 2.79/1.42  tff(c_100, plain, (![A_87, B_88]: (r2_xboole_0(A_87, B_88) | B_88=A_87 | ~r1_tarski(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.79/1.42  tff(c_54, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4') | ~r2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.79/1.42  tff(c_77, plain, (~r2_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_54])).
% 2.79/1.42  tff(c_111, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_100, c_77])).
% 2.79/1.42  tff(c_117, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_111])).
% 2.79/1.42  tff(c_60, plain, (r2_xboole_0('#skF_3', '#skF_4') | m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.79/1.42  tff(c_89, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_77, c_60])).
% 2.79/1.42  tff(c_134, plain, (![C_91, B_92, A_93]: (r1_tarski(C_91, B_92) | ~m1_orders_2(C_91, A_93, B_92) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_orders_2(A_93) | ~v5_orders_2(A_93) | ~v4_orders_2(A_93) | ~v3_orders_2(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.79/1.42  tff(c_136, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_89, c_134])).
% 2.79/1.42  tff(c_139, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_136])).
% 2.79/1.42  tff(c_140, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_52, c_117, c_139])).
% 2.79/1.42  tff(c_168, plain, (![C_102, A_103, B_104]: (m1_subset_1(C_102, k1_zfmisc_1(u1_struct_0(A_103))) | ~m2_orders_2(C_102, A_103, B_104) | ~m1_orders_1(B_104, k1_orders_1(u1_struct_0(A_103))) | ~l1_orders_2(A_103) | ~v5_orders_2(A_103) | ~v4_orders_2(A_103) | ~v3_orders_2(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.79/1.42  tff(c_172, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_168])).
% 2.79/1.42  tff(c_179, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_172])).
% 2.79/1.42  tff(c_181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_140, c_179])).
% 2.79/1.42  tff(c_182, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_111])).
% 2.79/1.42  tff(c_184, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_182, c_89])).
% 2.79/1.42  tff(c_244, plain, (![C_125, A_126, B_127]: (~m1_orders_2(C_125, A_126, B_127) | ~m1_orders_2(B_127, A_126, C_125) | k1_xboole_0=B_127 | ~m1_subset_1(C_125, k1_zfmisc_1(u1_struct_0(A_126))) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_orders_2(A_126) | ~v5_orders_2(A_126) | ~v4_orders_2(A_126) | ~v3_orders_2(A_126) | v2_struct_0(A_126))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.79/1.42  tff(c_246, plain, (~m1_orders_2('#skF_4', '#skF_1', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_184, c_244])).
% 2.79/1.42  tff(c_249, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_232, c_184, c_246])).
% 2.79/1.42  tff(c_250, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_52, c_249])).
% 2.79/1.42  tff(c_12, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.79/1.42  tff(c_65, plain, (![A_76, B_77]: (k4_xboole_0(A_76, B_77)=k1_xboole_0 | ~r1_tarski(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.79/1.42  tff(c_69, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_65])).
% 2.79/1.42  tff(c_255, plain, (![B_4]: (k4_xboole_0(B_4, B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_250, c_69])).
% 2.79/1.42  tff(c_20, plain, (![A_7, B_8]: (r1_xboole_0(A_7, B_8) | k4_xboole_0(A_7, B_8)!=A_7)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.79/1.42  tff(c_240, plain, (![C_121, D_122, A_123, B_124]: (~r1_xboole_0(C_121, D_122) | ~m2_orders_2(D_122, A_123, B_124) | ~m2_orders_2(C_121, A_123, B_124) | ~m1_orders_1(B_124, k1_orders_1(u1_struct_0(A_123))) | ~l1_orders_2(A_123) | ~v5_orders_2(A_123) | ~v4_orders_2(A_123) | ~v3_orders_2(A_123) | v2_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.79/1.42  tff(c_323, plain, (![B_146, A_147, B_148, A_149]: (~m2_orders_2(B_146, A_147, B_148) | ~m2_orders_2(A_149, A_147, B_148) | ~m1_orders_1(B_148, k1_orders_1(u1_struct_0(A_147))) | ~l1_orders_2(A_147) | ~v5_orders_2(A_147) | ~v4_orders_2(A_147) | ~v3_orders_2(A_147) | v2_struct_0(A_147) | k4_xboole_0(A_149, B_146)!=A_149)), inference(resolution, [status(thm)], [c_20, c_240])).
% 2.79/1.42  tff(c_325, plain, (![A_149]: (~m2_orders_2(A_149, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1') | k4_xboole_0(A_149, '#skF_4')!=A_149)), inference(resolution, [status(thm)], [c_38, c_323])).
% 2.79/1.42  tff(c_328, plain, (![A_149]: (~m2_orders_2(A_149, '#skF_1', '#skF_2') | v2_struct_0('#skF_1') | k4_xboole_0(A_149, '#skF_4')!=A_149)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_325])).
% 2.79/1.42  tff(c_330, plain, (![A_150]: (~m2_orders_2(A_150, '#skF_1', '#skF_2') | k4_xboole_0(A_150, '#skF_4')!=A_150)), inference(negUnitSimplification, [status(thm)], [c_52, c_328])).
% 2.79/1.42  tff(c_333, plain, (k4_xboole_0('#skF_4', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_38, c_330])).
% 2.79/1.42  tff(c_337, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_255, c_333])).
% 2.79/1.42  tff(c_339, plain, (r2_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_54])).
% 2.79/1.42  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.79/1.42  tff(c_355, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_339, c_6])).
% 2.79/1.42  tff(c_376, plain, (![B_157, A_158]: (B_157=A_158 | ~r1_tarski(B_157, A_158) | ~r1_tarski(A_158, B_157))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.79/1.42  tff(c_384, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_355, c_376])).
% 2.79/1.42  tff(c_389, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_384])).
% 2.79/1.42  tff(c_40, plain, (m2_orders_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.79/1.42  tff(c_448, plain, (![C_174, A_175, B_176]: (m1_subset_1(C_174, k1_zfmisc_1(u1_struct_0(A_175))) | ~m2_orders_2(C_174, A_175, B_176) | ~m1_orders_1(B_176, k1_orders_1(u1_struct_0(A_175))) | ~l1_orders_2(A_175) | ~v5_orders_2(A_175) | ~v4_orders_2(A_175) | ~v3_orders_2(A_175) | v2_struct_0(A_175))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.79/1.42  tff(c_450, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_448])).
% 2.79/1.42  tff(c_455, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_450])).
% 2.79/1.42  tff(c_456, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_52, c_455])).
% 2.79/1.42  tff(c_338, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(splitRight, [status(thm)], [c_54])).
% 2.79/1.42  tff(c_500, plain, (![C_190, A_191, D_192, B_193]: (m1_orders_2(C_190, A_191, D_192) | m1_orders_2(D_192, A_191, C_190) | D_192=C_190 | ~m2_orders_2(D_192, A_191, B_193) | ~m2_orders_2(C_190, A_191, B_193) | ~m1_orders_1(B_193, k1_orders_1(u1_struct_0(A_191))) | ~l1_orders_2(A_191) | ~v5_orders_2(A_191) | ~v4_orders_2(A_191) | ~v3_orders_2(A_191) | v2_struct_0(A_191))), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.79/1.42  tff(c_504, plain, (![C_190]: (m1_orders_2(C_190, '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', C_190) | C_190='#skF_4' | ~m2_orders_2(C_190, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_500])).
% 2.79/1.42  tff(c_511, plain, (![C_190]: (m1_orders_2(C_190, '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', C_190) | C_190='#skF_4' | ~m2_orders_2(C_190, '#skF_1', '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_504])).
% 2.79/1.42  tff(c_513, plain, (![C_194]: (m1_orders_2(C_194, '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', C_194) | C_194='#skF_4' | ~m2_orders_2(C_194, '#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_511])).
% 2.79/1.42  tff(c_516, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_40, c_513])).
% 2.79/1.42  tff(c_522, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_338, c_516])).
% 2.79/1.42  tff(c_525, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_522])).
% 2.79/1.42  tff(c_14, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.79/1.42  tff(c_406, plain, (k4_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_389])).
% 2.79/1.42  tff(c_544, plain, (k4_xboole_0('#skF_4', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_525, c_406])).
% 2.79/1.42  tff(c_556, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_544])).
% 2.79/1.42  tff(c_557, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_522])).
% 2.79/1.42  tff(c_28, plain, (![C_23, B_21, A_17]: (r1_tarski(C_23, B_21) | ~m1_orders_2(C_23, A_17, B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_orders_2(A_17) | ~v5_orders_2(A_17) | ~v4_orders_2(A_17) | ~v3_orders_2(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.79/1.42  tff(c_564, plain, (r1_tarski('#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_557, c_28])).
% 2.79/1.42  tff(c_575, plain, (r1_tarski('#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_456, c_564])).
% 2.79/1.42  tff(c_577, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_389, c_575])).
% 2.79/1.42  tff(c_578, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_384])).
% 2.79/1.42  tff(c_583, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_578, c_339])).
% 2.79/1.42  tff(c_588, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_583])).
% 2.79/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.42  
% 2.79/1.42  Inference rules
% 2.79/1.42  ----------------------
% 2.79/1.42  #Ref     : 0
% 2.79/1.42  #Sup     : 85
% 2.79/1.42  #Fact    : 0
% 2.79/1.42  #Define  : 0
% 2.79/1.42  #Split   : 5
% 2.79/1.42  #Chain   : 0
% 2.79/1.42  #Close   : 0
% 2.79/1.42  
% 2.79/1.42  Ordering : KBO
% 2.79/1.42  
% 2.79/1.42  Simplification rules
% 2.79/1.42  ----------------------
% 2.79/1.42  #Subsume      : 13
% 2.79/1.42  #Demod        : 186
% 2.79/1.42  #Tautology    : 47
% 2.79/1.42  #SimpNegUnit  : 30
% 2.79/1.42  #BackRed      : 27
% 2.79/1.42  
% 2.79/1.42  #Partial instantiations: 0
% 2.79/1.42  #Strategies tried      : 1
% 2.79/1.42  
% 2.79/1.42  Timing (in seconds)
% 2.79/1.42  ----------------------
% 2.79/1.43  Preprocessing        : 0.32
% 2.79/1.43  Parsing              : 0.18
% 2.79/1.43  CNF conversion       : 0.03
% 2.79/1.43  Main loop            : 0.32
% 2.79/1.43  Inferencing          : 0.12
% 2.79/1.43  Reduction            : 0.10
% 2.79/1.43  Demodulation         : 0.07
% 2.79/1.43  BG Simplification    : 0.02
% 2.79/1.43  Subsumption          : 0.06
% 2.79/1.43  Abstraction          : 0.01
% 2.79/1.43  MUC search           : 0.00
% 2.79/1.43  Cooper               : 0.00
% 2.79/1.43  Total                : 0.69
% 2.79/1.43  Index Insertion      : 0.00
% 2.79/1.43  Index Deletion       : 0.00
% 2.79/1.43  Index Matching       : 0.00
% 2.79/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
