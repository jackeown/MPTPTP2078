%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:59 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 304 expanded)
%              Number of leaves         :   35 ( 126 expanded)
%              Depth                    :   10
%              Number of atoms          :  296 (1268 expanded)
%              Number of equality atoms :   27 (  58 expanded)
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

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

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

tff(c_36,plain,(
    m2_orders_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

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

tff(c_257,plain,(
    ! [C_124,A_125,B_126] :
      ( m1_subset_1(C_124,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ m2_orders_2(C_124,A_125,B_126)
      | ~ m1_orders_1(B_126,k1_orders_1(u1_struct_0(A_125)))
      | ~ l1_orders_2(A_125)
      | ~ v5_orders_2(A_125)
      | ~ v4_orders_2(A_125)
      | ~ v3_orders_2(A_125)
      | v2_struct_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_259,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_257])).

tff(c_262,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_259])).

tff(c_263,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_262])).

tff(c_96,plain,(
    ! [A_87,B_88] :
      ( r2_xboole_0(A_87,B_88)
      | B_88 = A_87
      | ~ r1_tarski(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,
    ( ~ m1_orders_2('#skF_3','#skF_1','#skF_4')
    | ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_75,plain,(
    ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_107,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_75])).

tff(c_113,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_58,plain,
    ( r2_xboole_0('#skF_3','#skF_4')
    | m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_81,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_58])).

tff(c_127,plain,(
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

tff(c_129,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_81,c_127])).

tff(c_132,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_129])).

tff(c_133,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_113,c_132])).

tff(c_174,plain,(
    ! [C_105,A_106,B_107] :
      ( m1_subset_1(C_105,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ m2_orders_2(C_105,A_106,B_107)
      | ~ m1_orders_1(B_107,k1_orders_1(u1_struct_0(A_106)))
      | ~ l1_orders_2(A_106)
      | ~ v5_orders_2(A_106)
      | ~ v4_orders_2(A_106)
      | ~ v3_orders_2(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_178,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_174])).

tff(c_185,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_178])).

tff(c_187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_133,c_185])).

tff(c_188,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_203,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_81])).

tff(c_281,plain,(
    ! [C_139,A_140,B_141] :
      ( ~ m1_orders_2(C_139,A_140,B_141)
      | ~ m1_orders_2(B_141,A_140,C_139)
      | k1_xboole_0 = B_141
      | ~ m1_subset_1(C_139,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_orders_2(A_140)
      | ~ v5_orders_2(A_140)
      | ~ v4_orders_2(A_140)
      | ~ v3_orders_2(A_140)
      | v2_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_283,plain,
    ( ~ m1_orders_2('#skF_4','#skF_1','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_203,c_281])).

tff(c_286,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_263,c_203,c_283])).

tff(c_287,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_286])).

tff(c_12,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_63,plain,(
    ! [A_77,B_78] :
      ( k4_xboole_0(A_77,B_78) = k1_xboole_0
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_67,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_63])).

tff(c_92,plain,(
    ! [A_84,C_85,B_86] :
      ( r1_xboole_0(A_84,k4_xboole_0(C_85,B_86))
      | ~ r1_tarski(A_84,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_214,plain,(
    ! [A_111,B_112] :
      ( r1_xboole_0(A_111,k1_xboole_0)
      | ~ r1_tarski(A_111,B_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_92])).

tff(c_220,plain,(
    ! [B_4] : r1_xboole_0(B_4,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_214])).

tff(c_264,plain,(
    ! [C_127,D_128,A_129,B_130] :
      ( ~ r1_xboole_0(C_127,D_128)
      | ~ m2_orders_2(D_128,A_129,B_130)
      | ~ m2_orders_2(C_127,A_129,B_130)
      | ~ m1_orders_1(B_130,k1_orders_1(u1_struct_0(A_129)))
      | ~ l1_orders_2(A_129)
      | ~ v5_orders_2(A_129)
      | ~ v4_orders_2(A_129)
      | ~ v3_orders_2(A_129)
      | v2_struct_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_271,plain,(
    ! [A_131,B_132,B_133] :
      ( ~ m2_orders_2(k1_xboole_0,A_131,B_132)
      | ~ m2_orders_2(B_133,A_131,B_132)
      | ~ m1_orders_1(B_132,k1_orders_1(u1_struct_0(A_131)))
      | ~ l1_orders_2(A_131)
      | ~ v5_orders_2(A_131)
      | ~ v4_orders_2(A_131)
      | ~ v3_orders_2(A_131)
      | v2_struct_0(A_131) ) ),
    inference(resolution,[status(thm)],[c_220,c_264])).

tff(c_273,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_1','#skF_2')
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_271])).

tff(c_276,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_273])).

tff(c_277,plain,(
    ~ m2_orders_2(k1_xboole_0,'#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_276])).

tff(c_297,plain,(
    ~ m2_orders_2('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_277])).

tff(c_307,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_297])).

tff(c_309,plain,(
    r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_313,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_309,c_6])).

tff(c_328,plain,(
    ! [B_148,A_149] :
      ( B_148 = A_149
      | ~ r1_tarski(B_148,A_149)
      | ~ r1_tarski(A_149,B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_336,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_313,c_328])).

tff(c_341,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_336])).

tff(c_38,plain,(
    m2_orders_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_421,plain,(
    ! [C_168,A_169,B_170] :
      ( m1_subset_1(C_168,k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ m2_orders_2(C_168,A_169,B_170)
      | ~ m1_orders_1(B_170,k1_orders_1(u1_struct_0(A_169)))
      | ~ l1_orders_2(A_169)
      | ~ v5_orders_2(A_169)
      | ~ v4_orders_2(A_169)
      | ~ v3_orders_2(A_169)
      | v2_struct_0(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_423,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_421])).

tff(c_428,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_423])).

tff(c_429,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_428])).

tff(c_308,plain,(
    ~ m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_462,plain,(
    ! [C_193,A_194,D_195,B_196] :
      ( m1_orders_2(C_193,A_194,D_195)
      | m1_orders_2(D_195,A_194,C_193)
      | D_195 = C_193
      | ~ m2_orders_2(D_195,A_194,B_196)
      | ~ m2_orders_2(C_193,A_194,B_196)
      | ~ m1_orders_1(B_196,k1_orders_1(u1_struct_0(A_194)))
      | ~ l1_orders_2(A_194)
      | ~ v5_orders_2(A_194)
      | ~ v4_orders_2(A_194)
      | ~ v3_orders_2(A_194)
      | v2_struct_0(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_464,plain,(
    ! [C_193] :
      ( m1_orders_2(C_193,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_193)
      | C_193 = '#skF_3'
      | ~ m2_orders_2(C_193,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_462])).

tff(c_469,plain,(
    ! [C_193] :
      ( m1_orders_2(C_193,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_193)
      | C_193 = '#skF_3'
      | ~ m2_orders_2(C_193,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_464])).

tff(c_475,plain,(
    ! [C_197] :
      ( m1_orders_2(C_197,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_197)
      | C_197 = '#skF_3'
      | ~ m2_orders_2(C_197,'#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_469])).

tff(c_481,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | m1_orders_2('#skF_3','#skF_1','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_475])).

tff(c_486,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_308,c_481])).

tff(c_487,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_486])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_352,plain,(
    k4_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_341])).

tff(c_491,plain,(
    k4_xboole_0('#skF_4','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_352])).

tff(c_502,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_491])).

tff(c_503,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_486])).

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

tff(c_524,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_503,c_26])).

tff(c_539,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_429,c_524])).

tff(c_541,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_341,c_539])).

tff(c_542,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_336])).

tff(c_547,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_309])).

tff(c_552,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_547])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:44:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.36  
% 2.59/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.37  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.82/1.37  
% 2.82/1.37  %Foreground sorts:
% 2.82/1.37  
% 2.82/1.37  
% 2.82/1.37  %Background operators:
% 2.82/1.37  
% 2.82/1.37  
% 2.82/1.37  %Foreground operators:
% 2.82/1.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.82/1.37  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.82/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.82/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.82/1.37  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.82/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.82/1.37  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.82/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.82/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.82/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.82/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.82/1.37  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.82/1.37  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.82/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.82/1.37  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.82/1.37  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.82/1.37  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.82/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.37  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.82/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.82/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.37  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.82/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.82/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.82/1.37  
% 2.82/1.39  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.82/1.39  tff(f_204, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_orders_2)).
% 2.82/1.39  tff(f_84, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.82/1.39  tff(f_103, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_orders_2)).
% 2.82/1.39  tff(f_128, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_orders_2)).
% 2.82/1.39  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.82/1.39  tff(f_42, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.82/1.39  tff(f_46, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 2.82/1.39  tff(f_151, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_orders_2)).
% 2.82/1.39  tff(f_179, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_orders_2)).
% 2.82/1.39  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.82/1.39  tff(c_50, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.82/1.39  tff(c_36, plain, (m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.82/1.39  tff(c_48, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.82/1.39  tff(c_46, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.82/1.39  tff(c_44, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.82/1.39  tff(c_42, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.82/1.39  tff(c_40, plain, (m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.82/1.39  tff(c_257, plain, (![C_124, A_125, B_126]: (m1_subset_1(C_124, k1_zfmisc_1(u1_struct_0(A_125))) | ~m2_orders_2(C_124, A_125, B_126) | ~m1_orders_1(B_126, k1_orders_1(u1_struct_0(A_125))) | ~l1_orders_2(A_125) | ~v5_orders_2(A_125) | ~v4_orders_2(A_125) | ~v3_orders_2(A_125) | v2_struct_0(A_125))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.82/1.39  tff(c_259, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_257])).
% 2.82/1.39  tff(c_262, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_259])).
% 2.82/1.39  tff(c_263, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_50, c_262])).
% 2.82/1.39  tff(c_96, plain, (![A_87, B_88]: (r2_xboole_0(A_87, B_88) | B_88=A_87 | ~r1_tarski(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.82/1.39  tff(c_52, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4') | ~r2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.82/1.39  tff(c_75, plain, (~r2_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_52])).
% 2.82/1.39  tff(c_107, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_96, c_75])).
% 2.82/1.39  tff(c_113, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_107])).
% 2.82/1.39  tff(c_58, plain, (r2_xboole_0('#skF_3', '#skF_4') | m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.82/1.39  tff(c_81, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_75, c_58])).
% 2.82/1.39  tff(c_127, plain, (![C_92, B_93, A_94]: (r1_tarski(C_92, B_93) | ~m1_orders_2(C_92, A_94, B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_orders_2(A_94) | ~v5_orders_2(A_94) | ~v4_orders_2(A_94) | ~v3_orders_2(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.82/1.39  tff(c_129, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_81, c_127])).
% 2.82/1.39  tff(c_132, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_129])).
% 2.82/1.39  tff(c_133, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_50, c_113, c_132])).
% 2.82/1.39  tff(c_174, plain, (![C_105, A_106, B_107]: (m1_subset_1(C_105, k1_zfmisc_1(u1_struct_0(A_106))) | ~m2_orders_2(C_105, A_106, B_107) | ~m1_orders_1(B_107, k1_orders_1(u1_struct_0(A_106))) | ~l1_orders_2(A_106) | ~v5_orders_2(A_106) | ~v4_orders_2(A_106) | ~v3_orders_2(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.82/1.39  tff(c_178, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_174])).
% 2.82/1.39  tff(c_185, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_178])).
% 2.82/1.39  tff(c_187, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_133, c_185])).
% 2.82/1.39  tff(c_188, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_107])).
% 2.82/1.39  tff(c_203, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_188, c_81])).
% 2.82/1.39  tff(c_281, plain, (![C_139, A_140, B_141]: (~m1_orders_2(C_139, A_140, B_141) | ~m1_orders_2(B_141, A_140, C_139) | k1_xboole_0=B_141 | ~m1_subset_1(C_139, k1_zfmisc_1(u1_struct_0(A_140))) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_orders_2(A_140) | ~v5_orders_2(A_140) | ~v4_orders_2(A_140) | ~v3_orders_2(A_140) | v2_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.82/1.39  tff(c_283, plain, (~m1_orders_2('#skF_4', '#skF_1', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_203, c_281])).
% 2.82/1.39  tff(c_286, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_263, c_203, c_283])).
% 2.82/1.39  tff(c_287, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_50, c_286])).
% 2.82/1.39  tff(c_12, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.82/1.39  tff(c_63, plain, (![A_77, B_78]: (k4_xboole_0(A_77, B_78)=k1_xboole_0 | ~r1_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.82/1.39  tff(c_67, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_63])).
% 2.82/1.39  tff(c_92, plain, (![A_84, C_85, B_86]: (r1_xboole_0(A_84, k4_xboole_0(C_85, B_86)) | ~r1_tarski(A_84, B_86))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.82/1.39  tff(c_214, plain, (![A_111, B_112]: (r1_xboole_0(A_111, k1_xboole_0) | ~r1_tarski(A_111, B_112))), inference(superposition, [status(thm), theory('equality')], [c_67, c_92])).
% 2.82/1.39  tff(c_220, plain, (![B_4]: (r1_xboole_0(B_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_214])).
% 2.82/1.39  tff(c_264, plain, (![C_127, D_128, A_129, B_130]: (~r1_xboole_0(C_127, D_128) | ~m2_orders_2(D_128, A_129, B_130) | ~m2_orders_2(C_127, A_129, B_130) | ~m1_orders_1(B_130, k1_orders_1(u1_struct_0(A_129))) | ~l1_orders_2(A_129) | ~v5_orders_2(A_129) | ~v4_orders_2(A_129) | ~v3_orders_2(A_129) | v2_struct_0(A_129))), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.82/1.39  tff(c_271, plain, (![A_131, B_132, B_133]: (~m2_orders_2(k1_xboole_0, A_131, B_132) | ~m2_orders_2(B_133, A_131, B_132) | ~m1_orders_1(B_132, k1_orders_1(u1_struct_0(A_131))) | ~l1_orders_2(A_131) | ~v5_orders_2(A_131) | ~v4_orders_2(A_131) | ~v3_orders_2(A_131) | v2_struct_0(A_131))), inference(resolution, [status(thm)], [c_220, c_264])).
% 2.82/1.39  tff(c_273, plain, (~m2_orders_2(k1_xboole_0, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_271])).
% 2.82/1.39  tff(c_276, plain, (~m2_orders_2(k1_xboole_0, '#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_273])).
% 2.82/1.39  tff(c_277, plain, (~m2_orders_2(k1_xboole_0, '#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_276])).
% 2.82/1.39  tff(c_297, plain, (~m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_287, c_277])).
% 2.82/1.39  tff(c_307, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_297])).
% 2.82/1.39  tff(c_309, plain, (r2_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 2.82/1.39  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.82/1.39  tff(c_313, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_309, c_6])).
% 2.82/1.39  tff(c_328, plain, (![B_148, A_149]: (B_148=A_149 | ~r1_tarski(B_148, A_149) | ~r1_tarski(A_149, B_148))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.82/1.39  tff(c_336, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_313, c_328])).
% 2.82/1.39  tff(c_341, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_336])).
% 2.82/1.39  tff(c_38, plain, (m2_orders_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.82/1.39  tff(c_421, plain, (![C_168, A_169, B_170]: (m1_subset_1(C_168, k1_zfmisc_1(u1_struct_0(A_169))) | ~m2_orders_2(C_168, A_169, B_170) | ~m1_orders_1(B_170, k1_orders_1(u1_struct_0(A_169))) | ~l1_orders_2(A_169) | ~v5_orders_2(A_169) | ~v4_orders_2(A_169) | ~v3_orders_2(A_169) | v2_struct_0(A_169))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.82/1.39  tff(c_423, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_421])).
% 2.82/1.39  tff(c_428, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_423])).
% 2.82/1.39  tff(c_429, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_50, c_428])).
% 2.82/1.39  tff(c_308, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 2.82/1.39  tff(c_462, plain, (![C_193, A_194, D_195, B_196]: (m1_orders_2(C_193, A_194, D_195) | m1_orders_2(D_195, A_194, C_193) | D_195=C_193 | ~m2_orders_2(D_195, A_194, B_196) | ~m2_orders_2(C_193, A_194, B_196) | ~m1_orders_1(B_196, k1_orders_1(u1_struct_0(A_194))) | ~l1_orders_2(A_194) | ~v5_orders_2(A_194) | ~v4_orders_2(A_194) | ~v3_orders_2(A_194) | v2_struct_0(A_194))), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.82/1.39  tff(c_464, plain, (![C_193]: (m1_orders_2(C_193, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_193) | C_193='#skF_3' | ~m2_orders_2(C_193, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_462])).
% 2.82/1.39  tff(c_469, plain, (![C_193]: (m1_orders_2(C_193, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_193) | C_193='#skF_3' | ~m2_orders_2(C_193, '#skF_1', '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_464])).
% 2.82/1.39  tff(c_475, plain, (![C_197]: (m1_orders_2(C_197, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_197) | C_197='#skF_3' | ~m2_orders_2(C_197, '#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_469])).
% 2.82/1.39  tff(c_481, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', '#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_36, c_475])).
% 2.82/1.39  tff(c_486, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_308, c_481])).
% 2.82/1.39  tff(c_487, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_486])).
% 2.82/1.39  tff(c_14, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.82/1.39  tff(c_352, plain, (k4_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_341])).
% 2.82/1.39  tff(c_491, plain, (k4_xboole_0('#skF_4', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_487, c_352])).
% 2.82/1.39  tff(c_502, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_491])).
% 2.82/1.39  tff(c_503, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_486])).
% 2.82/1.39  tff(c_26, plain, (![C_24, B_22, A_18]: (r1_tarski(C_24, B_22) | ~m1_orders_2(C_24, A_18, B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_orders_2(A_18) | ~v5_orders_2(A_18) | ~v4_orders_2(A_18) | ~v3_orders_2(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.82/1.39  tff(c_524, plain, (r1_tarski('#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_503, c_26])).
% 2.82/1.39  tff(c_539, plain, (r1_tarski('#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_429, c_524])).
% 2.82/1.39  tff(c_541, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_341, c_539])).
% 2.82/1.39  tff(c_542, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_336])).
% 2.82/1.39  tff(c_547, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_542, c_309])).
% 2.82/1.39  tff(c_552, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_547])).
% 2.82/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.39  
% 2.82/1.39  Inference rules
% 2.82/1.39  ----------------------
% 2.82/1.39  #Ref     : 0
% 2.82/1.39  #Sup     : 81
% 2.82/1.39  #Fact    : 0
% 2.82/1.39  #Define  : 0
% 2.82/1.39  #Split   : 4
% 2.82/1.39  #Chain   : 0
% 2.82/1.39  #Close   : 0
% 2.82/1.39  
% 2.82/1.39  Ordering : KBO
% 2.82/1.39  
% 2.82/1.39  Simplification rules
% 2.82/1.39  ----------------------
% 2.82/1.39  #Subsume      : 10
% 2.82/1.39  #Demod        : 190
% 2.82/1.39  #Tautology    : 45
% 2.82/1.39  #SimpNegUnit  : 30
% 2.82/1.39  #BackRed      : 27
% 2.82/1.39  
% 2.82/1.39  #Partial instantiations: 0
% 2.82/1.39  #Strategies tried      : 1
% 2.82/1.39  
% 2.82/1.39  Timing (in seconds)
% 2.82/1.39  ----------------------
% 2.82/1.39  Preprocessing        : 0.32
% 2.82/1.39  Parsing              : 0.18
% 2.82/1.39  CNF conversion       : 0.03
% 2.82/1.39  Main loop            : 0.30
% 2.82/1.39  Inferencing          : 0.11
% 2.82/1.39  Reduction            : 0.10
% 2.82/1.39  Demodulation         : 0.07
% 2.82/1.39  BG Simplification    : 0.02
% 2.82/1.39  Subsumption          : 0.06
% 2.82/1.39  Abstraction          : 0.01
% 2.82/1.39  MUC search           : 0.00
% 2.82/1.39  Cooper               : 0.00
% 2.82/1.39  Total                : 0.66
% 2.82/1.39  Index Insertion      : 0.00
% 2.82/1.39  Index Deletion       : 0.00
% 2.82/1.39  Index Matching       : 0.00
% 2.82/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
