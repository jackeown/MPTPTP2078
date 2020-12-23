%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:58 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 291 expanded)
%              Number of leaves         :   36 ( 122 expanded)
%              Depth                    :   12
%              Number of atoms          :  290 (1244 expanded)
%              Number of equality atoms :   28 (  52 expanded)
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

tff(f_209,negated_conjecture,(
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

tff(f_89,axiom,(
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

tff(f_108,axiom,(
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

tff(f_133,axiom,(
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

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_156,axiom,(
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

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_184,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_52,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_50,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_48,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_46,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_44,plain,(
    m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_40,plain,(
    m2_orders_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_251,plain,(
    ! [C_121,A_122,B_123] :
      ( m1_subset_1(C_121,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ m2_orders_2(C_121,A_122,B_123)
      | ~ m1_orders_1(B_123,k1_orders_1(u1_struct_0(A_122)))
      | ~ l1_orders_2(A_122)
      | ~ v5_orders_2(A_122)
      | ~ v4_orders_2(A_122)
      | ~ v3_orders_2(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_253,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_251])).

tff(c_256,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_253])).

tff(c_257,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_256])).

tff(c_96,plain,(
    ! [A_88,B_89] :
      ( r2_xboole_0(A_88,B_89)
      | B_89 = A_88
      | ~ r1_tarski(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,
    ( ~ m1_orders_2('#skF_3','#skF_1','#skF_4')
    | ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_77,plain,(
    ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_107,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_77])).

tff(c_113,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_62,plain,
    ( r2_xboole_0('#skF_3','#skF_4')
    | m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_82,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_62])).

tff(c_146,plain,(
    ! [C_95,B_96,A_97] :
      ( r1_tarski(C_95,B_96)
      | ~ m1_orders_2(C_95,A_97,B_96)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_orders_2(A_97)
      | ~ v5_orders_2(A_97)
      | ~ v4_orders_2(A_97)
      | ~ v3_orders_2(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_148,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_82,c_146])).

tff(c_151,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_148])).

tff(c_152,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_113,c_151])).

tff(c_173,plain,(
    ! [C_104,A_105,B_106] :
      ( m1_subset_1(C_104,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ m2_orders_2(C_104,A_105,B_106)
      | ~ m1_orders_1(B_106,k1_orders_1(u1_struct_0(A_105)))
      | ~ l1_orders_2(A_105)
      | ~ v5_orders_2(A_105)
      | ~ v4_orders_2(A_105)
      | ~ v3_orders_2(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_177,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_173])).

tff(c_184,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_177])).

tff(c_186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_152,c_184])).

tff(c_187,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_189,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_82])).

tff(c_265,plain,(
    ! [C_128,A_129,B_130] :
      ( ~ m1_orders_2(C_128,A_129,B_130)
      | ~ m1_orders_2(B_130,A_129,C_128)
      | k1_xboole_0 = B_130
      | ~ m1_subset_1(C_128,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_orders_2(A_129)
      | ~ v5_orders_2(A_129)
      | ~ v4_orders_2(A_129)
      | ~ v3_orders_2(A_129)
      | v2_struct_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_267,plain,
    ( ~ m1_orders_2('#skF_4','#skF_1','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_189,c_265])).

tff(c_270,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_257,c_189,c_267])).

tff(c_271,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_270])).

tff(c_18,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_274,plain,(
    ! [A_9] : k4_xboole_0(A_9,'#skF_4') = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_18])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( r1_xboole_0(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_258,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_327,plain,(
    ! [B_138,A_139,B_140,A_141] :
      ( ~ m2_orders_2(B_138,A_139,B_140)
      | ~ m2_orders_2(A_141,A_139,B_140)
      | ~ m1_orders_1(B_140,k1_orders_1(u1_struct_0(A_139)))
      | ~ l1_orders_2(A_139)
      | ~ v5_orders_2(A_139)
      | ~ v4_orders_2(A_139)
      | ~ v3_orders_2(A_139)
      | v2_struct_0(A_139)
      | k4_xboole_0(A_141,B_138) != A_141 ) ),
    inference(resolution,[status(thm)],[c_22,c_258])).

tff(c_329,plain,(
    ! [A_141] :
      ( ~ m2_orders_2(A_141,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1')
      | k4_xboole_0(A_141,'#skF_4') != A_141 ) ),
    inference(resolution,[status(thm)],[c_40,c_327])).

tff(c_332,plain,(
    ! [A_141] :
      ( ~ m2_orders_2(A_141,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_52,c_50,c_48,c_46,c_44,c_329])).

tff(c_333,plain,(
    ! [A_141] : ~ m2_orders_2(A_141,'#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_332])).

tff(c_335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_333,c_40])).

tff(c_337,plain,(
    r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_341,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_337,c_6])).

tff(c_361,plain,(
    ! [B_148,A_149] :
      ( B_148 = A_149
      | ~ r1_tarski(B_148,A_149)
      | ~ r1_tarski(A_149,B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_366,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_341,c_361])).

tff(c_371,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_366])).

tff(c_42,plain,(
    m2_orders_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_425,plain,(
    ! [C_164,A_165,B_166] :
      ( m1_subset_1(C_164,k1_zfmisc_1(u1_struct_0(A_165)))
      | ~ m2_orders_2(C_164,A_165,B_166)
      | ~ m1_orders_1(B_166,k1_orders_1(u1_struct_0(A_165)))
      | ~ l1_orders_2(A_165)
      | ~ v5_orders_2(A_165)
      | ~ v4_orders_2(A_165)
      | ~ v3_orders_2(A_165)
      | v2_struct_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_427,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_425])).

tff(c_432,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_427])).

tff(c_433,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_432])).

tff(c_16,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_336,plain,(
    ~ m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_508,plain,(
    ! [C_186,A_187,D_188,B_189] :
      ( m1_orders_2(C_186,A_187,D_188)
      | m1_orders_2(D_188,A_187,C_186)
      | D_188 = C_186
      | ~ m2_orders_2(D_188,A_187,B_189)
      | ~ m2_orders_2(C_186,A_187,B_189)
      | ~ m1_orders_1(B_189,k1_orders_1(u1_struct_0(A_187)))
      | ~ l1_orders_2(A_187)
      | ~ v5_orders_2(A_187)
      | ~ v4_orders_2(A_187)
      | ~ v3_orders_2(A_187)
      | v2_struct_0(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_510,plain,(
    ! [C_186] :
      ( m1_orders_2(C_186,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_186)
      | C_186 = '#skF_3'
      | ~ m2_orders_2(C_186,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_508])).

tff(c_515,plain,(
    ! [C_186] :
      ( m1_orders_2(C_186,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_186)
      | C_186 = '#skF_3'
      | ~ m2_orders_2(C_186,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_510])).

tff(c_521,plain,(
    ! [C_190] :
      ( m1_orders_2(C_190,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_190)
      | C_190 = '#skF_3'
      | ~ m2_orders_2(C_190,'#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_515])).

tff(c_527,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | m1_orders_2('#skF_3','#skF_1','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_521])).

tff(c_532,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_336,c_527])).

tff(c_545,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_532])).

tff(c_554,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_545,c_371])).

tff(c_563,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_554])).

tff(c_564,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_532])).

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
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_571,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_564,c_30])).

tff(c_582,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_433,c_571])).

tff(c_584,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_371,c_582])).

tff(c_585,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_366])).

tff(c_589,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_585,c_337])).

tff(c_593,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_589])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:31:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.85/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.40  
% 2.92/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.40  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.92/1.40  
% 2.92/1.40  %Foreground sorts:
% 2.92/1.40  
% 2.92/1.40  
% 2.92/1.40  %Background operators:
% 2.92/1.40  
% 2.92/1.40  
% 2.92/1.40  %Foreground operators:
% 2.92/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.92/1.40  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.92/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.92/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.92/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.92/1.40  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.92/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.92/1.40  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.92/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.92/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.92/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.92/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.92/1.40  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.92/1.40  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.92/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.92/1.40  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.92/1.40  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.92/1.40  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.92/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.92/1.40  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.92/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.92/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.92/1.40  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.92/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.92/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.92/1.40  
% 2.92/1.42  tff(f_35, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 2.92/1.42  tff(f_209, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_orders_2)).
% 2.92/1.42  tff(f_89, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.92/1.42  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.92/1.42  tff(f_108, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_orders_2)).
% 2.92/1.42  tff(f_133, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_orders_2)).
% 2.92/1.42  tff(f_47, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.92/1.42  tff(f_51, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.92/1.42  tff(f_156, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_orders_2)).
% 2.92/1.42  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.92/1.42  tff(f_184, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_orders_2)).
% 2.92/1.42  tff(c_8, plain, (![A_3]: (~r2_xboole_0(A_3, A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.92/1.42  tff(c_54, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_209])).
% 2.92/1.42  tff(c_52, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_209])).
% 2.92/1.42  tff(c_50, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_209])).
% 2.92/1.42  tff(c_48, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_209])).
% 2.92/1.42  tff(c_46, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_209])).
% 2.92/1.42  tff(c_44, plain, (m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_209])).
% 2.92/1.42  tff(c_40, plain, (m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_209])).
% 2.92/1.42  tff(c_251, plain, (![C_121, A_122, B_123]: (m1_subset_1(C_121, k1_zfmisc_1(u1_struct_0(A_122))) | ~m2_orders_2(C_121, A_122, B_123) | ~m1_orders_1(B_123, k1_orders_1(u1_struct_0(A_122))) | ~l1_orders_2(A_122) | ~v5_orders_2(A_122) | ~v4_orders_2(A_122) | ~v3_orders_2(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.92/1.42  tff(c_253, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_251])).
% 2.92/1.42  tff(c_256, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_253])).
% 2.92/1.42  tff(c_257, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_54, c_256])).
% 2.92/1.42  tff(c_96, plain, (![A_88, B_89]: (r2_xboole_0(A_88, B_89) | B_89=A_88 | ~r1_tarski(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.92/1.42  tff(c_56, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4') | ~r2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_209])).
% 2.92/1.42  tff(c_77, plain, (~r2_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_56])).
% 2.92/1.42  tff(c_107, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_96, c_77])).
% 2.92/1.42  tff(c_113, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_107])).
% 2.92/1.42  tff(c_62, plain, (r2_xboole_0('#skF_3', '#skF_4') | m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_209])).
% 2.92/1.42  tff(c_82, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_77, c_62])).
% 2.92/1.42  tff(c_146, plain, (![C_95, B_96, A_97]: (r1_tarski(C_95, B_96) | ~m1_orders_2(C_95, A_97, B_96) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_orders_2(A_97) | ~v5_orders_2(A_97) | ~v4_orders_2(A_97) | ~v3_orders_2(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.92/1.42  tff(c_148, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_82, c_146])).
% 2.92/1.42  tff(c_151, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_148])).
% 2.92/1.42  tff(c_152, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_54, c_113, c_151])).
% 2.92/1.42  tff(c_173, plain, (![C_104, A_105, B_106]: (m1_subset_1(C_104, k1_zfmisc_1(u1_struct_0(A_105))) | ~m2_orders_2(C_104, A_105, B_106) | ~m1_orders_1(B_106, k1_orders_1(u1_struct_0(A_105))) | ~l1_orders_2(A_105) | ~v5_orders_2(A_105) | ~v4_orders_2(A_105) | ~v3_orders_2(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.92/1.42  tff(c_177, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_173])).
% 2.92/1.42  tff(c_184, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_177])).
% 2.92/1.42  tff(c_186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_152, c_184])).
% 2.92/1.42  tff(c_187, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_107])).
% 2.92/1.42  tff(c_189, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_187, c_82])).
% 2.92/1.42  tff(c_265, plain, (![C_128, A_129, B_130]: (~m1_orders_2(C_128, A_129, B_130) | ~m1_orders_2(B_130, A_129, C_128) | k1_xboole_0=B_130 | ~m1_subset_1(C_128, k1_zfmisc_1(u1_struct_0(A_129))) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_orders_2(A_129) | ~v5_orders_2(A_129) | ~v4_orders_2(A_129) | ~v3_orders_2(A_129) | v2_struct_0(A_129))), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.92/1.42  tff(c_267, plain, (~m1_orders_2('#skF_4', '#skF_1', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_189, c_265])).
% 2.92/1.42  tff(c_270, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_257, c_189, c_267])).
% 2.92/1.42  tff(c_271, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_54, c_270])).
% 2.92/1.42  tff(c_18, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.92/1.42  tff(c_274, plain, (![A_9]: (k4_xboole_0(A_9, '#skF_4')=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_271, c_18])).
% 2.92/1.42  tff(c_22, plain, (![A_10, B_11]: (r1_xboole_0(A_10, B_11) | k4_xboole_0(A_10, B_11)!=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.92/1.42  tff(c_258, plain, (![C_124, D_125, A_126, B_127]: (~r1_xboole_0(C_124, D_125) | ~m2_orders_2(D_125, A_126, B_127) | ~m2_orders_2(C_124, A_126, B_127) | ~m1_orders_1(B_127, k1_orders_1(u1_struct_0(A_126))) | ~l1_orders_2(A_126) | ~v5_orders_2(A_126) | ~v4_orders_2(A_126) | ~v3_orders_2(A_126) | v2_struct_0(A_126))), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.92/1.42  tff(c_327, plain, (![B_138, A_139, B_140, A_141]: (~m2_orders_2(B_138, A_139, B_140) | ~m2_orders_2(A_141, A_139, B_140) | ~m1_orders_1(B_140, k1_orders_1(u1_struct_0(A_139))) | ~l1_orders_2(A_139) | ~v5_orders_2(A_139) | ~v4_orders_2(A_139) | ~v3_orders_2(A_139) | v2_struct_0(A_139) | k4_xboole_0(A_141, B_138)!=A_141)), inference(resolution, [status(thm)], [c_22, c_258])).
% 2.92/1.42  tff(c_329, plain, (![A_141]: (~m2_orders_2(A_141, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1') | k4_xboole_0(A_141, '#skF_4')!=A_141)), inference(resolution, [status(thm)], [c_40, c_327])).
% 2.92/1.42  tff(c_332, plain, (![A_141]: (~m2_orders_2(A_141, '#skF_1', '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_274, c_52, c_50, c_48, c_46, c_44, c_329])).
% 2.92/1.42  tff(c_333, plain, (![A_141]: (~m2_orders_2(A_141, '#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_332])).
% 2.92/1.42  tff(c_335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_333, c_40])).
% 2.92/1.42  tff(c_337, plain, (r2_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_56])).
% 2.92/1.42  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.92/1.42  tff(c_341, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_337, c_6])).
% 2.92/1.42  tff(c_361, plain, (![B_148, A_149]: (B_148=A_149 | ~r1_tarski(B_148, A_149) | ~r1_tarski(A_149, B_148))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.92/1.42  tff(c_366, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_341, c_361])).
% 2.92/1.42  tff(c_371, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_366])).
% 2.92/1.42  tff(c_42, plain, (m2_orders_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_209])).
% 2.92/1.42  tff(c_425, plain, (![C_164, A_165, B_166]: (m1_subset_1(C_164, k1_zfmisc_1(u1_struct_0(A_165))) | ~m2_orders_2(C_164, A_165, B_166) | ~m1_orders_1(B_166, k1_orders_1(u1_struct_0(A_165))) | ~l1_orders_2(A_165) | ~v5_orders_2(A_165) | ~v4_orders_2(A_165) | ~v3_orders_2(A_165) | v2_struct_0(A_165))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.92/1.42  tff(c_427, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_425])).
% 2.92/1.42  tff(c_432, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_427])).
% 2.92/1.42  tff(c_433, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_54, c_432])).
% 2.92/1.42  tff(c_16, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.92/1.42  tff(c_336, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(splitRight, [status(thm)], [c_56])).
% 2.92/1.42  tff(c_508, plain, (![C_186, A_187, D_188, B_189]: (m1_orders_2(C_186, A_187, D_188) | m1_orders_2(D_188, A_187, C_186) | D_188=C_186 | ~m2_orders_2(D_188, A_187, B_189) | ~m2_orders_2(C_186, A_187, B_189) | ~m1_orders_1(B_189, k1_orders_1(u1_struct_0(A_187))) | ~l1_orders_2(A_187) | ~v5_orders_2(A_187) | ~v4_orders_2(A_187) | ~v3_orders_2(A_187) | v2_struct_0(A_187))), inference(cnfTransformation, [status(thm)], [f_184])).
% 2.92/1.42  tff(c_510, plain, (![C_186]: (m1_orders_2(C_186, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_186) | C_186='#skF_3' | ~m2_orders_2(C_186, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_508])).
% 2.92/1.42  tff(c_515, plain, (![C_186]: (m1_orders_2(C_186, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_186) | C_186='#skF_3' | ~m2_orders_2(C_186, '#skF_1', '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_510])).
% 2.92/1.42  tff(c_521, plain, (![C_190]: (m1_orders_2(C_190, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_190) | C_190='#skF_3' | ~m2_orders_2(C_190, '#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_515])).
% 2.92/1.42  tff(c_527, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', '#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_40, c_521])).
% 2.92/1.42  tff(c_532, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_336, c_527])).
% 2.92/1.42  tff(c_545, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_532])).
% 2.92/1.42  tff(c_554, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_545, c_371])).
% 2.92/1.42  tff(c_563, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_554])).
% 2.92/1.42  tff(c_564, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_532])).
% 2.92/1.42  tff(c_30, plain, (![C_26, B_24, A_20]: (r1_tarski(C_26, B_24) | ~m1_orders_2(C_26, A_20, B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_orders_2(A_20) | ~v5_orders_2(A_20) | ~v4_orders_2(A_20) | ~v3_orders_2(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.92/1.42  tff(c_571, plain, (r1_tarski('#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_564, c_30])).
% 2.92/1.42  tff(c_582, plain, (r1_tarski('#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_433, c_571])).
% 2.92/1.42  tff(c_584, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_371, c_582])).
% 2.92/1.42  tff(c_585, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_366])).
% 2.92/1.42  tff(c_589, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_585, c_337])).
% 2.92/1.42  tff(c_593, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_589])).
% 2.92/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.42  
% 2.92/1.42  Inference rules
% 2.92/1.42  ----------------------
% 2.92/1.42  #Ref     : 0
% 2.92/1.42  #Sup     : 93
% 2.92/1.42  #Fact    : 0
% 2.92/1.42  #Define  : 0
% 2.92/1.42  #Split   : 4
% 2.92/1.42  #Chain   : 0
% 2.92/1.42  #Close   : 0
% 2.92/1.42  
% 2.92/1.42  Ordering : KBO
% 2.92/1.42  
% 2.92/1.42  Simplification rules
% 2.92/1.42  ----------------------
% 2.92/1.42  #Subsume      : 17
% 2.92/1.42  #Demod        : 181
% 2.92/1.42  #Tautology    : 53
% 2.92/1.42  #SimpNegUnit  : 32
% 2.92/1.42  #BackRed      : 24
% 2.92/1.42  
% 2.92/1.42  #Partial instantiations: 0
% 2.92/1.42  #Strategies tried      : 1
% 2.92/1.42  
% 2.92/1.42  Timing (in seconds)
% 2.92/1.42  ----------------------
% 2.92/1.42  Preprocessing        : 0.33
% 2.92/1.42  Parsing              : 0.19
% 2.92/1.42  CNF conversion       : 0.03
% 2.92/1.42  Main loop            : 0.32
% 2.92/1.42  Inferencing          : 0.12
% 2.92/1.42  Reduction            : 0.11
% 2.92/1.42  Demodulation         : 0.08
% 2.92/1.42  BG Simplification    : 0.02
% 2.92/1.42  Subsumption          : 0.06
% 2.92/1.43  Abstraction          : 0.01
% 2.92/1.43  MUC search           : 0.00
% 2.92/1.43  Cooper               : 0.00
% 2.92/1.43  Total                : 0.70
% 2.92/1.43  Index Insertion      : 0.00
% 2.92/1.43  Index Deletion       : 0.00
% 2.92/1.43  Index Matching       : 0.00
% 2.92/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
