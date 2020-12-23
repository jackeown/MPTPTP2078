%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:58 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 298 expanded)
%              Number of leaves         :   37 ( 124 expanded)
%              Depth                    :   10
%              Number of atoms          :  295 (1252 expanded)
%              Number of equality atoms :   24 (  49 expanded)
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

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

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

tff(c_52,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_38,plain,(
    m2_orders_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_50,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_48,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_46,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_44,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_42,plain,(
    m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_273,plain,(
    ! [C_121,A_122,B_123] :
      ( m1_subset_1(C_121,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ m2_orders_2(C_121,A_122,B_123)
      | ~ m1_orders_1(B_123,k1_orders_1(u1_struct_0(A_122)))
      | ~ l1_orders_2(A_122)
      | ~ v5_orders_2(A_122)
      | ~ v4_orders_2(A_122)
      | ~ v3_orders_2(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_275,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_273])).

tff(c_278,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_275])).

tff(c_279,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_278])).

tff(c_70,plain,(
    ! [A_84,B_85] :
      ( r2_xboole_0(A_84,B_85)
      | B_85 = A_84
      | ~ r1_tarski(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_54,plain,
    ( ~ m1_orders_2('#skF_3','#skF_1','#skF_4')
    | ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_68,plain,(
    ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_81,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_68])).

tff(c_87,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_60,plain,
    ( r2_xboole_0('#skF_3','#skF_4')
    | m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_69,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_60])).

tff(c_159,plain,(
    ! [C_96,B_97,A_98] :
      ( r1_tarski(C_96,B_97)
      | ~ m1_orders_2(C_96,A_98,B_97)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_orders_2(A_98)
      | ~ v5_orders_2(A_98)
      | ~ v4_orders_2(A_98)
      | ~ v3_orders_2(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_161,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_69,c_159])).

tff(c_164,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_161])).

tff(c_165,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_87,c_164])).

tff(c_173,plain,(
    ! [C_102,A_103,B_104] :
      ( m1_subset_1(C_102,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ m2_orders_2(C_102,A_103,B_104)
      | ~ m1_orders_1(B_104,k1_orders_1(u1_struct_0(A_103)))
      | ~ l1_orders_2(A_103)
      | ~ v5_orders_2(A_103)
      | ~ v4_orders_2(A_103)
      | ~ v3_orders_2(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_175,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_173])).

tff(c_180,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_175])).

tff(c_182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_165,c_180])).

tff(c_183,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_185,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_69])).

tff(c_294,plain,(
    ! [C_131,A_132,B_133] :
      ( ~ m1_orders_2(C_131,A_132,B_133)
      | ~ m1_orders_2(B_133,A_132,C_131)
      | k1_xboole_0 = B_133
      | ~ m1_subset_1(C_131,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_orders_2(A_132)
      | ~ v5_orders_2(A_132)
      | ~ v4_orders_2(A_132)
      | ~ v3_orders_2(A_132)
      | v2_struct_0(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_296,plain,
    ( ~ m1_orders_2('#skF_4','#skF_1','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_185,c_294])).

tff(c_299,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_279,c_185,c_296])).

tff(c_300,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_299])).

tff(c_18,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_194,plain,(
    ! [B_105,A_106] :
      ( B_105 = A_106
      | ~ r1_tarski(B_105,A_106)
      | ~ r1_tarski(A_106,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_207,plain,(
    ! [A_107] :
      ( k1_xboole_0 = A_107
      | ~ r1_tarski(A_107,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_194])).

tff(c_225,plain,(
    ! [B_108] : k4_xboole_0(k1_xboole_0,B_108) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_207])).

tff(c_20,plain,(
    ! [A_10,B_11] : r1_xboole_0(k4_xboole_0(A_10,B_11),B_11) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_233,plain,(
    ! [B_108] : r1_xboole_0(k1_xboole_0,B_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_20])).

tff(c_280,plain,(
    ! [C_124,D_125,A_126,B_127] :
      ( ~ r1_xboole_0(C_124,D_125)
      | ~ m2_orders_2(D_125,A_126,B_127)
      | ~ m2_orders_2(C_124,A_126,B_127)
      | ~ m1_orders_1(B_127,k1_orders_1(u1_struct_0(A_126)))
      | ~ l1_orders_2(A_126)
      | ~ v5_orders_2(A_126)
      | ~ v4_orders_2(A_126)
      | ~ v3_orders_2(A_126)
      | v2_struct_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_287,plain,(
    ! [B_128,A_129,B_130] :
      ( ~ m2_orders_2(B_128,A_129,B_130)
      | ~ m2_orders_2(k1_xboole_0,A_129,B_130)
      | ~ m1_orders_1(B_130,k1_orders_1(u1_struct_0(A_129)))
      | ~ l1_orders_2(A_129)
      | ~ v5_orders_2(A_129)
      | ~ v4_orders_2(A_129)
      | ~ v3_orders_2(A_129)
      | v2_struct_0(A_129) ) ),
    inference(resolution,[status(thm)],[c_233,c_280])).

tff(c_289,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_1','#skF_2')
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_287])).

tff(c_292,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_289])).

tff(c_293,plain,(
    ~ m2_orders_2(k1_xboole_0,'#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_292])).

tff(c_302,plain,(
    ~ m2_orders_2('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_293])).

tff(c_310,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_302])).

tff(c_312,plain,(
    r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_316,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_312,c_6])).

tff(c_319,plain,(
    ! [B_134,A_135] :
      ( B_134 = A_135
      | ~ r1_tarski(B_134,A_135)
      | ~ r1_tarski(A_135,B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_328,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_316,c_319])).

tff(c_368,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_328])).

tff(c_40,plain,(
    m2_orders_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_409,plain,(
    ! [C_152,A_153,B_154] :
      ( m1_subset_1(C_152,k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ m2_orders_2(C_152,A_153,B_154)
      | ~ m1_orders_1(B_154,k1_orders_1(u1_struct_0(A_153)))
      | ~ l1_orders_2(A_153)
      | ~ v5_orders_2(A_153)
      | ~ v4_orders_2(A_153)
      | ~ v3_orders_2(A_153)
      | v2_struct_0(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_413,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_409])).

tff(c_420,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_413])).

tff(c_421,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_420])).

tff(c_14,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_311,plain,(
    ~ m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_447,plain,(
    ! [C_173,A_174,D_175,B_176] :
      ( m1_orders_2(C_173,A_174,D_175)
      | m1_orders_2(D_175,A_174,C_173)
      | D_175 = C_173
      | ~ m2_orders_2(D_175,A_174,B_176)
      | ~ m2_orders_2(C_173,A_174,B_176)
      | ~ m1_orders_1(B_176,k1_orders_1(u1_struct_0(A_174)))
      | ~ l1_orders_2(A_174)
      | ~ v5_orders_2(A_174)
      | ~ v4_orders_2(A_174)
      | ~ v3_orders_2(A_174)
      | v2_struct_0(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_449,plain,(
    ! [C_173] :
      ( m1_orders_2(C_173,'#skF_1','#skF_4')
      | m1_orders_2('#skF_4','#skF_1',C_173)
      | C_173 = '#skF_4'
      | ~ m2_orders_2(C_173,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_447])).

tff(c_454,plain,(
    ! [C_173] :
      ( m1_orders_2(C_173,'#skF_1','#skF_4')
      | m1_orders_2('#skF_4','#skF_1',C_173)
      | C_173 = '#skF_4'
      | ~ m2_orders_2(C_173,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_449])).

tff(c_460,plain,(
    ! [C_177] :
      ( m1_orders_2(C_177,'#skF_1','#skF_4')
      | m1_orders_2('#skF_4','#skF_1',C_177)
      | C_177 = '#skF_4'
      | ~ m2_orders_2(C_177,'#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_454])).

tff(c_466,plain,
    ( m1_orders_2('#skF_3','#skF_1','#skF_4')
    | m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_460])).

tff(c_471,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_311,c_466])).

tff(c_472,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_471])).

tff(c_475,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_472,c_368])).

tff(c_484,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_475])).

tff(c_485,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_471])).

tff(c_28,plain,(
    ! [C_26,B_24,A_20] :
      ( r1_tarski(C_26,B_24)
      | ~ m1_orders_2(C_26,A_20,B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_orders_2(A_20)
      | ~ v5_orders_2(A_20)
      | ~ v4_orders_2(A_20)
      | ~ v3_orders_2(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_494,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_485,c_28])).

tff(c_509,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_421,c_494])).

tff(c_511,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_368,c_509])).

tff(c_512,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_328])).

tff(c_516,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_312])).

tff(c_520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_516])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:11:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.36  
% 2.68/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.36  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.68/1.36  
% 2.68/1.36  %Foreground sorts:
% 2.68/1.36  
% 2.68/1.36  
% 2.68/1.36  %Background operators:
% 2.68/1.36  
% 2.68/1.36  
% 2.68/1.36  %Foreground operators:
% 2.68/1.36  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.68/1.36  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.68/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.68/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.68/1.36  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.68/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.68/1.36  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.68/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.68/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.68/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.68/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.68/1.36  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.68/1.36  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.68/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.68/1.36  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.68/1.36  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.68/1.36  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.68/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.36  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.68/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.68/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.36  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.68/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.68/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.68/1.36  
% 2.81/1.38  tff(f_35, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 2.81/1.38  tff(f_205, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_orders_2)).
% 2.81/1.38  tff(f_85, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.81/1.38  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.81/1.38  tff(f_104, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_orders_2)).
% 2.81/1.38  tff(f_129, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_orders_2)).
% 2.81/1.38  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.81/1.38  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.81/1.38  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.81/1.38  tff(f_47, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.81/1.38  tff(f_152, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_orders_2)).
% 2.81/1.38  tff(f_180, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_orders_2)).
% 2.81/1.38  tff(c_8, plain, (![A_3]: (~r2_xboole_0(A_3, A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.81/1.38  tff(c_52, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_205])).
% 2.81/1.38  tff(c_38, plain, (m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_205])).
% 2.81/1.38  tff(c_50, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_205])).
% 2.81/1.38  tff(c_48, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_205])).
% 2.81/1.38  tff(c_46, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_205])).
% 2.81/1.38  tff(c_44, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_205])).
% 2.81/1.38  tff(c_42, plain, (m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_205])).
% 2.81/1.38  tff(c_273, plain, (![C_121, A_122, B_123]: (m1_subset_1(C_121, k1_zfmisc_1(u1_struct_0(A_122))) | ~m2_orders_2(C_121, A_122, B_123) | ~m1_orders_1(B_123, k1_orders_1(u1_struct_0(A_122))) | ~l1_orders_2(A_122) | ~v5_orders_2(A_122) | ~v4_orders_2(A_122) | ~v3_orders_2(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.81/1.38  tff(c_275, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_273])).
% 2.81/1.38  tff(c_278, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_275])).
% 2.81/1.38  tff(c_279, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_52, c_278])).
% 2.81/1.38  tff(c_70, plain, (![A_84, B_85]: (r2_xboole_0(A_84, B_85) | B_85=A_84 | ~r1_tarski(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.81/1.38  tff(c_54, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4') | ~r2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_205])).
% 2.81/1.38  tff(c_68, plain, (~r2_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_54])).
% 2.81/1.38  tff(c_81, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_70, c_68])).
% 2.81/1.38  tff(c_87, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_81])).
% 2.81/1.38  tff(c_60, plain, (r2_xboole_0('#skF_3', '#skF_4') | m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_205])).
% 2.81/1.38  tff(c_69, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_68, c_60])).
% 2.81/1.38  tff(c_159, plain, (![C_96, B_97, A_98]: (r1_tarski(C_96, B_97) | ~m1_orders_2(C_96, A_98, B_97) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_orders_2(A_98) | ~v5_orders_2(A_98) | ~v4_orders_2(A_98) | ~v3_orders_2(A_98) | v2_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.81/1.38  tff(c_161, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_69, c_159])).
% 2.81/1.38  tff(c_164, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_161])).
% 2.81/1.38  tff(c_165, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_52, c_87, c_164])).
% 2.81/1.38  tff(c_173, plain, (![C_102, A_103, B_104]: (m1_subset_1(C_102, k1_zfmisc_1(u1_struct_0(A_103))) | ~m2_orders_2(C_102, A_103, B_104) | ~m1_orders_1(B_104, k1_orders_1(u1_struct_0(A_103))) | ~l1_orders_2(A_103) | ~v5_orders_2(A_103) | ~v4_orders_2(A_103) | ~v3_orders_2(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.81/1.38  tff(c_175, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_173])).
% 2.81/1.38  tff(c_180, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_175])).
% 2.81/1.38  tff(c_182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_165, c_180])).
% 2.81/1.38  tff(c_183, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_81])).
% 2.81/1.38  tff(c_185, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_183, c_69])).
% 2.81/1.38  tff(c_294, plain, (![C_131, A_132, B_133]: (~m1_orders_2(C_131, A_132, B_133) | ~m1_orders_2(B_133, A_132, C_131) | k1_xboole_0=B_133 | ~m1_subset_1(C_131, k1_zfmisc_1(u1_struct_0(A_132))) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_orders_2(A_132) | ~v5_orders_2(A_132) | ~v4_orders_2(A_132) | ~v3_orders_2(A_132) | v2_struct_0(A_132))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.81/1.38  tff(c_296, plain, (~m1_orders_2('#skF_4', '#skF_1', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_185, c_294])).
% 2.81/1.38  tff(c_299, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_279, c_185, c_296])).
% 2.81/1.38  tff(c_300, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_52, c_299])).
% 2.81/1.38  tff(c_18, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.81/1.38  tff(c_16, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.81/1.38  tff(c_194, plain, (![B_105, A_106]: (B_105=A_106 | ~r1_tarski(B_105, A_106) | ~r1_tarski(A_106, B_105))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.81/1.38  tff(c_207, plain, (![A_107]: (k1_xboole_0=A_107 | ~r1_tarski(A_107, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_194])).
% 2.81/1.38  tff(c_225, plain, (![B_108]: (k4_xboole_0(k1_xboole_0, B_108)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_207])).
% 2.81/1.38  tff(c_20, plain, (![A_10, B_11]: (r1_xboole_0(k4_xboole_0(A_10, B_11), B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.81/1.38  tff(c_233, plain, (![B_108]: (r1_xboole_0(k1_xboole_0, B_108))), inference(superposition, [status(thm), theory('equality')], [c_225, c_20])).
% 2.81/1.38  tff(c_280, plain, (![C_124, D_125, A_126, B_127]: (~r1_xboole_0(C_124, D_125) | ~m2_orders_2(D_125, A_126, B_127) | ~m2_orders_2(C_124, A_126, B_127) | ~m1_orders_1(B_127, k1_orders_1(u1_struct_0(A_126))) | ~l1_orders_2(A_126) | ~v5_orders_2(A_126) | ~v4_orders_2(A_126) | ~v3_orders_2(A_126) | v2_struct_0(A_126))), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.81/1.38  tff(c_287, plain, (![B_128, A_129, B_130]: (~m2_orders_2(B_128, A_129, B_130) | ~m2_orders_2(k1_xboole_0, A_129, B_130) | ~m1_orders_1(B_130, k1_orders_1(u1_struct_0(A_129))) | ~l1_orders_2(A_129) | ~v5_orders_2(A_129) | ~v4_orders_2(A_129) | ~v3_orders_2(A_129) | v2_struct_0(A_129))), inference(resolution, [status(thm)], [c_233, c_280])).
% 2.81/1.38  tff(c_289, plain, (~m2_orders_2(k1_xboole_0, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_287])).
% 2.81/1.38  tff(c_292, plain, (~m2_orders_2(k1_xboole_0, '#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_289])).
% 2.81/1.38  tff(c_293, plain, (~m2_orders_2(k1_xboole_0, '#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_292])).
% 2.81/1.38  tff(c_302, plain, (~m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_300, c_293])).
% 2.81/1.38  tff(c_310, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_302])).
% 2.81/1.38  tff(c_312, plain, (r2_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_54])).
% 2.81/1.38  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.81/1.38  tff(c_316, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_312, c_6])).
% 2.81/1.38  tff(c_319, plain, (![B_134, A_135]: (B_134=A_135 | ~r1_tarski(B_134, A_135) | ~r1_tarski(A_135, B_134))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.81/1.38  tff(c_328, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_316, c_319])).
% 2.81/1.38  tff(c_368, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_328])).
% 2.81/1.38  tff(c_40, plain, (m2_orders_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_205])).
% 2.81/1.38  tff(c_409, plain, (![C_152, A_153, B_154]: (m1_subset_1(C_152, k1_zfmisc_1(u1_struct_0(A_153))) | ~m2_orders_2(C_152, A_153, B_154) | ~m1_orders_1(B_154, k1_orders_1(u1_struct_0(A_153))) | ~l1_orders_2(A_153) | ~v5_orders_2(A_153) | ~v4_orders_2(A_153) | ~v3_orders_2(A_153) | v2_struct_0(A_153))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.81/1.38  tff(c_413, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_409])).
% 2.81/1.38  tff(c_420, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_413])).
% 2.81/1.38  tff(c_421, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_52, c_420])).
% 2.81/1.38  tff(c_14, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.81/1.38  tff(c_311, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(splitRight, [status(thm)], [c_54])).
% 2.81/1.38  tff(c_447, plain, (![C_173, A_174, D_175, B_176]: (m1_orders_2(C_173, A_174, D_175) | m1_orders_2(D_175, A_174, C_173) | D_175=C_173 | ~m2_orders_2(D_175, A_174, B_176) | ~m2_orders_2(C_173, A_174, B_176) | ~m1_orders_1(B_176, k1_orders_1(u1_struct_0(A_174))) | ~l1_orders_2(A_174) | ~v5_orders_2(A_174) | ~v4_orders_2(A_174) | ~v3_orders_2(A_174) | v2_struct_0(A_174))), inference(cnfTransformation, [status(thm)], [f_180])).
% 2.81/1.38  tff(c_449, plain, (![C_173]: (m1_orders_2(C_173, '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', C_173) | C_173='#skF_4' | ~m2_orders_2(C_173, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_447])).
% 2.81/1.38  tff(c_454, plain, (![C_173]: (m1_orders_2(C_173, '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', C_173) | C_173='#skF_4' | ~m2_orders_2(C_173, '#skF_1', '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_449])).
% 2.81/1.38  tff(c_460, plain, (![C_177]: (m1_orders_2(C_177, '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', C_177) | C_177='#skF_4' | ~m2_orders_2(C_177, '#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_454])).
% 2.81/1.38  tff(c_466, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_40, c_460])).
% 2.81/1.38  tff(c_471, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_311, c_466])).
% 2.81/1.38  tff(c_472, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_471])).
% 2.81/1.38  tff(c_475, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_472, c_368])).
% 2.81/1.38  tff(c_484, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_475])).
% 2.81/1.38  tff(c_485, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_471])).
% 2.81/1.38  tff(c_28, plain, (![C_26, B_24, A_20]: (r1_tarski(C_26, B_24) | ~m1_orders_2(C_26, A_20, B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_orders_2(A_20) | ~v5_orders_2(A_20) | ~v4_orders_2(A_20) | ~v3_orders_2(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.81/1.38  tff(c_494, plain, (r1_tarski('#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_485, c_28])).
% 2.81/1.38  tff(c_509, plain, (r1_tarski('#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_421, c_494])).
% 2.81/1.38  tff(c_511, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_368, c_509])).
% 2.81/1.38  tff(c_512, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_328])).
% 2.81/1.38  tff(c_516, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_512, c_312])).
% 2.81/1.38  tff(c_520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_516])).
% 2.81/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.38  
% 2.81/1.38  Inference rules
% 2.81/1.38  ----------------------
% 2.81/1.38  #Ref     : 0
% 2.81/1.38  #Sup     : 76
% 2.81/1.38  #Fact    : 0
% 2.81/1.38  #Define  : 0
% 2.81/1.38  #Split   : 4
% 2.81/1.38  #Chain   : 0
% 2.81/1.38  #Close   : 0
% 2.81/1.38  
% 2.81/1.38  Ordering : KBO
% 2.81/1.38  
% 2.81/1.38  Simplification rules
% 2.81/1.38  ----------------------
% 2.81/1.38  #Subsume      : 7
% 2.81/1.38  #Demod        : 164
% 2.81/1.38  #Tautology    : 43
% 2.81/1.38  #SimpNegUnit  : 27
% 2.81/1.38  #BackRed      : 21
% 2.81/1.38  
% 2.81/1.38  #Partial instantiations: 0
% 2.81/1.38  #Strategies tried      : 1
% 2.81/1.38  
% 2.81/1.38  Timing (in seconds)
% 2.81/1.38  ----------------------
% 2.81/1.39  Preprocessing        : 0.32
% 2.81/1.39  Parsing              : 0.18
% 2.81/1.39  CNF conversion       : 0.03
% 2.81/1.39  Main loop            : 0.28
% 2.81/1.39  Inferencing          : 0.10
% 2.81/1.39  Reduction            : 0.09
% 2.81/1.39  Demodulation         : 0.07
% 2.81/1.39  BG Simplification    : 0.02
% 2.81/1.39  Subsumption          : 0.05
% 2.81/1.39  Abstraction          : 0.01
% 2.81/1.39  MUC search           : 0.00
% 2.81/1.39  Cooper               : 0.00
% 2.81/1.39  Total                : 0.64
% 2.81/1.39  Index Insertion      : 0.00
% 2.81/1.39  Index Deletion       : 0.00
% 2.81/1.39  Index Matching       : 0.00
% 2.81/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
