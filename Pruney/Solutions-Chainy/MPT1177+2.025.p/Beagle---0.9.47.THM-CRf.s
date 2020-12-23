%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:58 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 295 expanded)
%              Number of leaves         :   36 ( 123 expanded)
%              Depth                    :   10
%              Number of atoms          :  295 (1253 expanded)
%              Number of equality atoms :   23 (  48 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

tff(f_205,negated_conjecture,(
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

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_85,axiom,(
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

tff(f_104,axiom,(
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

tff(f_129,axiom,(
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

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_152,axiom,(
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

tff(f_180,axiom,(
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

tff(c_8,plain,(
    ! [A_3] : ~ r2_xboole_0(A_3,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_14,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_48,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_46,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_44,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_42,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_40,plain,(
    m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_36,plain,(
    m2_orders_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_182,plain,(
    ! [C_113,A_114,B_115] :
      ( m1_subset_1(C_113,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ m2_orders_2(C_113,A_114,B_115)
      | ~ m1_orders_1(B_115,k1_orders_1(u1_struct_0(A_114)))
      | ~ l1_orders_2(A_114)
      | ~ v5_orders_2(A_114)
      | ~ v4_orders_2(A_114)
      | ~ v3_orders_2(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_184,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_182])).

tff(c_187,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_184])).

tff(c_188,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_187])).

tff(c_74,plain,(
    ! [A_79,B_80] :
      ( r2_xboole_0(A_79,B_80)
      | B_80 = A_79
      | ~ r1_tarski(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,
    ( ~ m1_orders_2('#skF_3','#skF_1','#skF_4')
    | ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_72,plain,(
    ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_85,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_72])).

tff(c_91,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_58,plain,
    ( r2_xboole_0('#skF_3','#skF_4')
    | m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_73,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_58])).

tff(c_104,plain,(
    ! [C_88,B_89,A_90] :
      ( r1_tarski(C_88,B_89)
      | ~ m1_orders_2(C_88,A_90,B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_orders_2(A_90)
      | ~ v5_orders_2(A_90)
      | ~ v4_orders_2(A_90)
      | ~ v3_orders_2(A_90)
      | v2_struct_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_106,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_73,c_104])).

tff(c_109,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_106])).

tff(c_110,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_91,c_109])).

tff(c_131,plain,(
    ! [C_97,A_98,B_99] :
      ( m1_subset_1(C_97,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ m2_orders_2(C_97,A_98,B_99)
      | ~ m1_orders_1(B_99,k1_orders_1(u1_struct_0(A_98)))
      | ~ l1_orders_2(A_98)
      | ~ v5_orders_2(A_98)
      | ~ v4_orders_2(A_98)
      | ~ v3_orders_2(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_135,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_131])).

tff(c_142,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_135])).

tff(c_144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_110,c_142])).

tff(c_145,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_147,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_73])).

tff(c_218,plain,(
    ! [C_133,A_134,B_135] :
      ( ~ m1_orders_2(C_133,A_134,B_135)
      | ~ m1_orders_2(B_135,A_134,C_133)
      | k1_xboole_0 = B_135
      | ~ m1_subset_1(C_133,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ l1_orders_2(A_134)
      | ~ v5_orders_2(A_134)
      | ~ v4_orders_2(A_134)
      | ~ v3_orders_2(A_134)
      | v2_struct_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_220,plain,
    ( ~ m1_orders_2('#skF_4','#skF_1','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_147,c_218])).

tff(c_223,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_188,c_147,c_220])).

tff(c_224,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_223])).

tff(c_16,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_156,plain,(
    ! [A_100,C_101,B_102] :
      ( r1_xboole_0(A_100,k4_xboole_0(C_101,B_102))
      | ~ r1_tarski(A_100,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_159,plain,(
    ! [A_100,A_7] :
      ( r1_xboole_0(A_100,A_7)
      | ~ r1_tarski(A_100,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_156])).

tff(c_196,plain,(
    ! [C_119,D_120,A_121,B_122] :
      ( ~ r1_xboole_0(C_119,D_120)
      | ~ m2_orders_2(D_120,A_121,B_122)
      | ~ m2_orders_2(C_119,A_121,B_122)
      | ~ m1_orders_1(B_122,k1_orders_1(u1_struct_0(A_121)))
      | ~ l1_orders_2(A_121)
      | ~ v5_orders_2(A_121)
      | ~ v4_orders_2(A_121)
      | ~ v3_orders_2(A_121)
      | v2_struct_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_203,plain,(
    ! [A_123,A_124,B_125,A_126] :
      ( ~ m2_orders_2(A_123,A_124,B_125)
      | ~ m2_orders_2(A_126,A_124,B_125)
      | ~ m1_orders_1(B_125,k1_orders_1(u1_struct_0(A_124)))
      | ~ l1_orders_2(A_124)
      | ~ v5_orders_2(A_124)
      | ~ v4_orders_2(A_124)
      | ~ v3_orders_2(A_124)
      | v2_struct_0(A_124)
      | ~ r1_tarski(A_126,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_159,c_196])).

tff(c_205,plain,(
    ! [A_126] :
      ( ~ m2_orders_2(A_126,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ r1_tarski(A_126,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_36,c_203])).

tff(c_208,plain,(
    ! [A_126] :
      ( ~ m2_orders_2(A_126,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1')
      | ~ r1_tarski(A_126,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_205])).

tff(c_210,plain,(
    ! [A_127] :
      ( ~ m2_orders_2(A_127,'#skF_1','#skF_2')
      | ~ r1_tarski(A_127,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_208])).

tff(c_214,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_36,c_210])).

tff(c_226,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_214])).

tff(c_233,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_226])).

tff(c_235,plain,(
    r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_239,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_235,c_6])).

tff(c_259,plain,(
    ! [B_143,A_144] :
      ( B_143 = A_144
      | ~ r1_tarski(B_143,A_144)
      | ~ r1_tarski(A_144,B_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_264,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_239,c_259])).

tff(c_270,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_264])).

tff(c_38,plain,(
    m2_orders_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_285,plain,(
    ! [C_154,A_155,B_156] :
      ( m1_subset_1(C_154,k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ m2_orders_2(C_154,A_155,B_156)
      | ~ m1_orders_1(B_156,k1_orders_1(u1_struct_0(A_155)))
      | ~ l1_orders_2(A_155)
      | ~ v5_orders_2(A_155)
      | ~ v4_orders_2(A_155)
      | ~ v3_orders_2(A_155)
      | v2_struct_0(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_287,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_285])).

tff(c_292,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_287])).

tff(c_293,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_292])).

tff(c_234,plain,(
    ~ m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_331,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_333,plain,(
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
    inference(resolution,[status(thm)],[c_38,c_331])).

tff(c_338,plain,(
    ! [C_174] :
      ( m1_orders_2(C_174,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_174)
      | C_174 = '#skF_3'
      | ~ m2_orders_2(C_174,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_333])).

tff(c_344,plain,(
    ! [C_178] :
      ( m1_orders_2(C_178,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_178)
      | C_178 = '#skF_3'
      | ~ m2_orders_2(C_178,'#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_338])).

tff(c_350,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | m1_orders_2('#skF_3','#skF_1','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_344])).

tff(c_355,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_234,c_350])).

tff(c_357,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_355])).

tff(c_362,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_270])).

tff(c_371,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_362])).

tff(c_372,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_355])).

tff(c_26,plain,(
    ! [C_25,B_23,A_19] :
      ( r1_tarski(C_25,B_23)
      | ~ m1_orders_2(C_25,A_19,B_23)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_orders_2(A_19)
      | ~ v5_orders_2(A_19)
      | ~ v4_orders_2(A_19)
      | ~ v3_orders_2(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_393,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_372,c_26])).

tff(c_408,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_293,c_393])).

tff(c_410,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_270,c_408])).

tff(c_411,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_415,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_235])).

tff(c_419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_415])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:30:40 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.42  
% 2.42/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.42  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.42/1.42  
% 2.42/1.42  %Foreground sorts:
% 2.42/1.42  
% 2.42/1.42  
% 2.42/1.42  %Background operators:
% 2.42/1.42  
% 2.42/1.42  
% 2.42/1.42  %Foreground operators:
% 2.42/1.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.42/1.42  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.42/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.42/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.42/1.42  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.42/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.42/1.42  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.42/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.42/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.42/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.42/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.42/1.42  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.42/1.42  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.42/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.42/1.42  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.42/1.42  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.42/1.42  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.42/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.42  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.42/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.42/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.42  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.42/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.42/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.42/1.42  
% 2.87/1.44  tff(f_35, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 2.87/1.44  tff(f_205, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_orders_2)).
% 2.87/1.44  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.87/1.44  tff(f_85, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.87/1.44  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.87/1.44  tff(f_104, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_orders_2)).
% 2.87/1.44  tff(f_129, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_orders_2)).
% 2.87/1.44  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.87/1.44  tff(f_47, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 2.87/1.44  tff(f_152, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_orders_2)).
% 2.87/1.44  tff(f_180, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_orders_2)).
% 2.87/1.44  tff(c_8, plain, (![A_3]: (~r2_xboole_0(A_3, A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.87/1.44  tff(c_50, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_205])).
% 2.87/1.44  tff(c_14, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.87/1.44  tff(c_48, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_205])).
% 2.87/1.44  tff(c_46, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_205])).
% 2.87/1.44  tff(c_44, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_205])).
% 2.87/1.44  tff(c_42, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_205])).
% 2.87/1.44  tff(c_40, plain, (m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_205])).
% 2.87/1.44  tff(c_36, plain, (m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_205])).
% 2.87/1.44  tff(c_182, plain, (![C_113, A_114, B_115]: (m1_subset_1(C_113, k1_zfmisc_1(u1_struct_0(A_114))) | ~m2_orders_2(C_113, A_114, B_115) | ~m1_orders_1(B_115, k1_orders_1(u1_struct_0(A_114))) | ~l1_orders_2(A_114) | ~v5_orders_2(A_114) | ~v4_orders_2(A_114) | ~v3_orders_2(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.87/1.44  tff(c_184, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_182])).
% 2.87/1.44  tff(c_187, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_184])).
% 2.87/1.44  tff(c_188, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_50, c_187])).
% 2.87/1.44  tff(c_74, plain, (![A_79, B_80]: (r2_xboole_0(A_79, B_80) | B_80=A_79 | ~r1_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.87/1.44  tff(c_52, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4') | ~r2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_205])).
% 2.87/1.44  tff(c_72, plain, (~r2_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_52])).
% 2.87/1.44  tff(c_85, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_74, c_72])).
% 2.87/1.44  tff(c_91, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_85])).
% 2.87/1.44  tff(c_58, plain, (r2_xboole_0('#skF_3', '#skF_4') | m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_205])).
% 2.87/1.44  tff(c_73, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_72, c_58])).
% 2.87/1.44  tff(c_104, plain, (![C_88, B_89, A_90]: (r1_tarski(C_88, B_89) | ~m1_orders_2(C_88, A_90, B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_orders_2(A_90) | ~v5_orders_2(A_90) | ~v4_orders_2(A_90) | ~v3_orders_2(A_90) | v2_struct_0(A_90))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.87/1.44  tff(c_106, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_73, c_104])).
% 2.87/1.44  tff(c_109, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_106])).
% 2.87/1.44  tff(c_110, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_50, c_91, c_109])).
% 2.87/1.44  tff(c_131, plain, (![C_97, A_98, B_99]: (m1_subset_1(C_97, k1_zfmisc_1(u1_struct_0(A_98))) | ~m2_orders_2(C_97, A_98, B_99) | ~m1_orders_1(B_99, k1_orders_1(u1_struct_0(A_98))) | ~l1_orders_2(A_98) | ~v5_orders_2(A_98) | ~v4_orders_2(A_98) | ~v3_orders_2(A_98) | v2_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.87/1.44  tff(c_135, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_131])).
% 2.87/1.44  tff(c_142, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_135])).
% 2.87/1.44  tff(c_144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_110, c_142])).
% 2.87/1.44  tff(c_145, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_85])).
% 2.87/1.44  tff(c_147, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_73])).
% 2.87/1.44  tff(c_218, plain, (![C_133, A_134, B_135]: (~m1_orders_2(C_133, A_134, B_135) | ~m1_orders_2(B_135, A_134, C_133) | k1_xboole_0=B_135 | ~m1_subset_1(C_133, k1_zfmisc_1(u1_struct_0(A_134))) | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0(A_134))) | ~l1_orders_2(A_134) | ~v5_orders_2(A_134) | ~v4_orders_2(A_134) | ~v3_orders_2(A_134) | v2_struct_0(A_134))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.87/1.44  tff(c_220, plain, (~m1_orders_2('#skF_4', '#skF_1', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_147, c_218])).
% 2.87/1.44  tff(c_223, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_188, c_147, c_220])).
% 2.87/1.44  tff(c_224, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_50, c_223])).
% 2.87/1.44  tff(c_16, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.87/1.44  tff(c_156, plain, (![A_100, C_101, B_102]: (r1_xboole_0(A_100, k4_xboole_0(C_101, B_102)) | ~r1_tarski(A_100, B_102))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.87/1.44  tff(c_159, plain, (![A_100, A_7]: (r1_xboole_0(A_100, A_7) | ~r1_tarski(A_100, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_156])).
% 2.87/1.44  tff(c_196, plain, (![C_119, D_120, A_121, B_122]: (~r1_xboole_0(C_119, D_120) | ~m2_orders_2(D_120, A_121, B_122) | ~m2_orders_2(C_119, A_121, B_122) | ~m1_orders_1(B_122, k1_orders_1(u1_struct_0(A_121))) | ~l1_orders_2(A_121) | ~v5_orders_2(A_121) | ~v4_orders_2(A_121) | ~v3_orders_2(A_121) | v2_struct_0(A_121))), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.87/1.44  tff(c_203, plain, (![A_123, A_124, B_125, A_126]: (~m2_orders_2(A_123, A_124, B_125) | ~m2_orders_2(A_126, A_124, B_125) | ~m1_orders_1(B_125, k1_orders_1(u1_struct_0(A_124))) | ~l1_orders_2(A_124) | ~v5_orders_2(A_124) | ~v4_orders_2(A_124) | ~v3_orders_2(A_124) | v2_struct_0(A_124) | ~r1_tarski(A_126, k1_xboole_0))), inference(resolution, [status(thm)], [c_159, c_196])).
% 2.87/1.44  tff(c_205, plain, (![A_126]: (~m2_orders_2(A_126, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1') | ~r1_tarski(A_126, k1_xboole_0))), inference(resolution, [status(thm)], [c_36, c_203])).
% 2.87/1.44  tff(c_208, plain, (![A_126]: (~m2_orders_2(A_126, '#skF_1', '#skF_2') | v2_struct_0('#skF_1') | ~r1_tarski(A_126, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_205])).
% 2.87/1.44  tff(c_210, plain, (![A_127]: (~m2_orders_2(A_127, '#skF_1', '#skF_2') | ~r1_tarski(A_127, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_50, c_208])).
% 2.87/1.44  tff(c_214, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_210])).
% 2.87/1.44  tff(c_226, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_224, c_214])).
% 2.87/1.44  tff(c_233, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_226])).
% 2.87/1.44  tff(c_235, plain, (r2_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 2.87/1.44  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.87/1.44  tff(c_239, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_235, c_6])).
% 2.87/1.44  tff(c_259, plain, (![B_143, A_144]: (B_143=A_144 | ~r1_tarski(B_143, A_144) | ~r1_tarski(A_144, B_143))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.87/1.44  tff(c_264, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_239, c_259])).
% 2.87/1.44  tff(c_270, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_264])).
% 2.87/1.44  tff(c_38, plain, (m2_orders_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_205])).
% 2.87/1.44  tff(c_285, plain, (![C_154, A_155, B_156]: (m1_subset_1(C_154, k1_zfmisc_1(u1_struct_0(A_155))) | ~m2_orders_2(C_154, A_155, B_156) | ~m1_orders_1(B_156, k1_orders_1(u1_struct_0(A_155))) | ~l1_orders_2(A_155) | ~v5_orders_2(A_155) | ~v4_orders_2(A_155) | ~v3_orders_2(A_155) | v2_struct_0(A_155))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.87/1.44  tff(c_287, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_285])).
% 2.87/1.44  tff(c_292, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_287])).
% 2.87/1.44  tff(c_293, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_50, c_292])).
% 2.87/1.44  tff(c_234, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 2.87/1.44  tff(c_331, plain, (![C_174, A_175, D_176, B_177]: (m1_orders_2(C_174, A_175, D_176) | m1_orders_2(D_176, A_175, C_174) | D_176=C_174 | ~m2_orders_2(D_176, A_175, B_177) | ~m2_orders_2(C_174, A_175, B_177) | ~m1_orders_1(B_177, k1_orders_1(u1_struct_0(A_175))) | ~l1_orders_2(A_175) | ~v5_orders_2(A_175) | ~v4_orders_2(A_175) | ~v3_orders_2(A_175) | v2_struct_0(A_175))), inference(cnfTransformation, [status(thm)], [f_180])).
% 2.87/1.44  tff(c_333, plain, (![C_174]: (m1_orders_2(C_174, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_174) | C_174='#skF_3' | ~m2_orders_2(C_174, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_331])).
% 2.87/1.44  tff(c_338, plain, (![C_174]: (m1_orders_2(C_174, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_174) | C_174='#skF_3' | ~m2_orders_2(C_174, '#skF_1', '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_333])).
% 2.87/1.44  tff(c_344, plain, (![C_178]: (m1_orders_2(C_178, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_178) | C_178='#skF_3' | ~m2_orders_2(C_178, '#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_338])).
% 2.87/1.44  tff(c_350, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', '#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_36, c_344])).
% 2.87/1.44  tff(c_355, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_234, c_350])).
% 2.87/1.44  tff(c_357, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_355])).
% 2.87/1.44  tff(c_362, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_357, c_270])).
% 2.87/1.44  tff(c_371, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_362])).
% 2.87/1.44  tff(c_372, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_355])).
% 2.87/1.44  tff(c_26, plain, (![C_25, B_23, A_19]: (r1_tarski(C_25, B_23) | ~m1_orders_2(C_25, A_19, B_23) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_orders_2(A_19) | ~v5_orders_2(A_19) | ~v4_orders_2(A_19) | ~v3_orders_2(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.87/1.44  tff(c_393, plain, (r1_tarski('#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_372, c_26])).
% 2.87/1.44  tff(c_408, plain, (r1_tarski('#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_293, c_393])).
% 2.87/1.44  tff(c_410, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_270, c_408])).
% 2.87/1.44  tff(c_411, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_264])).
% 2.87/1.44  tff(c_415, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_411, c_235])).
% 2.87/1.44  tff(c_419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_415])).
% 2.87/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.44  
% 2.87/1.44  Inference rules
% 2.87/1.44  ----------------------
% 2.87/1.44  #Ref     : 0
% 2.87/1.44  #Sup     : 54
% 2.87/1.44  #Fact    : 0
% 2.87/1.44  #Define  : 0
% 2.87/1.44  #Split   : 4
% 2.87/1.44  #Chain   : 0
% 2.87/1.44  #Close   : 0
% 2.87/1.44  
% 2.87/1.44  Ordering : KBO
% 2.87/1.44  
% 2.87/1.44  Simplification rules
% 2.87/1.44  ----------------------
% 2.87/1.44  #Subsume      : 9
% 2.87/1.44  #Demod        : 160
% 2.87/1.44  #Tautology    : 25
% 2.87/1.44  #SimpNegUnit  : 28
% 2.87/1.44  #BackRed      : 22
% 2.87/1.44  
% 2.87/1.44  #Partial instantiations: 0
% 2.87/1.44  #Strategies tried      : 1
% 2.87/1.44  
% 2.87/1.44  Timing (in seconds)
% 2.87/1.44  ----------------------
% 2.87/1.44  Preprocessing        : 0.36
% 2.87/1.44  Parsing              : 0.20
% 2.87/1.44  CNF conversion       : 0.03
% 2.87/1.44  Main loop            : 0.28
% 2.87/1.44  Inferencing          : 0.10
% 2.87/1.45  Reduction            : 0.09
% 2.87/1.45  Demodulation         : 0.07
% 2.87/1.45  BG Simplification    : 0.02
% 2.87/1.45  Subsumption          : 0.05
% 2.87/1.45  Abstraction          : 0.01
% 2.87/1.45  MUC search           : 0.00
% 2.87/1.45  Cooper               : 0.00
% 2.87/1.45  Total                : 0.69
% 2.87/1.45  Index Insertion      : 0.00
% 2.87/1.45  Index Deletion       : 0.00
% 2.87/1.45  Index Matching       : 0.00
% 2.87/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
