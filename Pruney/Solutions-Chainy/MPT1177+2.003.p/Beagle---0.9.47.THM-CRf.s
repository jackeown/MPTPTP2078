%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:55 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 325 expanded)
%              Number of leaves         :   39 ( 136 expanded)
%              Depth                    :   11
%              Number of atoms          :  327 (1407 expanded)
%              Number of equality atoms :   27 (  54 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_221,negated_conjecture,(
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

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_168,axiom,(
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

tff(f_101,axiom,(
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

tff(f_120,axiom,(
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

tff(f_145,axiom,(
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

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_196,axiom,(
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
    ! [B_6] : ~ r2_xboole_0(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_42,plain,(
    m2_orders_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_54,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_52,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_50,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_48,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_46,plain,(
    m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_173,plain,(
    ! [A_111,B_112] :
      ( r2_hidden('#skF_2'(A_111,B_112),A_111)
      | r1_xboole_0(A_111,B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_177,plain,(
    ! [A_111,B_112] :
      ( ~ v1_xboole_0(A_111)
      | r1_xboole_0(A_111,B_112) ) ),
    inference(resolution,[status(thm)],[c_173,c_2])).

tff(c_214,plain,(
    ! [C_130,D_131,A_132,B_133] :
      ( ~ r1_xboole_0(C_130,D_131)
      | ~ m2_orders_2(D_131,A_132,B_133)
      | ~ m2_orders_2(C_130,A_132,B_133)
      | ~ m1_orders_1(B_133,k1_orders_1(u1_struct_0(A_132)))
      | ~ l1_orders_2(A_132)
      | ~ v5_orders_2(A_132)
      | ~ v4_orders_2(A_132)
      | ~ v3_orders_2(A_132)
      | v2_struct_0(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_221,plain,(
    ! [B_134,A_135,B_136,A_137] :
      ( ~ m2_orders_2(B_134,A_135,B_136)
      | ~ m2_orders_2(A_137,A_135,B_136)
      | ~ m1_orders_1(B_136,k1_orders_1(u1_struct_0(A_135)))
      | ~ l1_orders_2(A_135)
      | ~ v5_orders_2(A_135)
      | ~ v4_orders_2(A_135)
      | ~ v3_orders_2(A_135)
      | v2_struct_0(A_135)
      | ~ v1_xboole_0(A_137) ) ),
    inference(resolution,[status(thm)],[c_177,c_214])).

tff(c_223,plain,(
    ! [A_137] :
      ( ~ m2_orders_2(A_137,'#skF_3','#skF_4')
      | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ v1_xboole_0(A_137) ) ),
    inference(resolution,[status(thm)],[c_42,c_221])).

tff(c_226,plain,(
    ! [A_137] :
      ( ~ m2_orders_2(A_137,'#skF_3','#skF_4')
      | v2_struct_0('#skF_3')
      | ~ v1_xboole_0(A_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_223])).

tff(c_228,plain,(
    ! [A_138] :
      ( ~ m2_orders_2(A_138,'#skF_3','#skF_4')
      | ~ v1_xboole_0(A_138) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_226])).

tff(c_232,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_228])).

tff(c_207,plain,(
    ! [C_127,A_128,B_129] :
      ( m1_subset_1(C_127,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ m2_orders_2(C_127,A_128,B_129)
      | ~ m1_orders_1(B_129,k1_orders_1(u1_struct_0(A_128)))
      | ~ l1_orders_2(A_128)
      | ~ v5_orders_2(A_128)
      | ~ v4_orders_2(A_128)
      | ~ v3_orders_2(A_128)
      | v2_struct_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_209,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_207])).

tff(c_212,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_209])).

tff(c_213,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_212])).

tff(c_90,plain,(
    ! [A_90,B_91] :
      ( r2_xboole_0(A_90,B_91)
      | B_91 = A_90
      | ~ r1_tarski(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_58,plain,
    ( ~ m1_orders_2('#skF_5','#skF_3','#skF_6')
    | ~ r2_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_75,plain,(
    ~ r2_xboole_0('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_101,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_90,c_75])).

tff(c_107,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_64,plain,
    ( r2_xboole_0('#skF_5','#skF_6')
    | m1_orders_2('#skF_5','#skF_3','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_76,plain,(
    m1_orders_2('#skF_5','#skF_3','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_64])).

tff(c_134,plain,(
    ! [C_102,B_103,A_104] :
      ( r1_tarski(C_102,B_103)
      | ~ m1_orders_2(C_102,A_104,B_103)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_orders_2(A_104)
      | ~ v5_orders_2(A_104)
      | ~ v4_orders_2(A_104)
      | ~ v3_orders_2(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_136,plain,
    ( r1_tarski('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_134])).

tff(c_139,plain,
    ( r1_tarski('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_136])).

tff(c_140,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_107,c_139])).

tff(c_148,plain,(
    ! [C_108,A_109,B_110] :
      ( m1_subset_1(C_108,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ m2_orders_2(C_108,A_109,B_110)
      | ~ m1_orders_1(B_110,k1_orders_1(u1_struct_0(A_109)))
      | ~ l1_orders_2(A_109)
      | ~ v5_orders_2(A_109)
      | ~ v4_orders_2(A_109)
      | ~ v3_orders_2(A_109)
      | v2_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_152,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_148])).

tff(c_159,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_152])).

tff(c_161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_140,c_159])).

tff(c_162,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_164,plain,(
    m1_orders_2('#skF_6','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_76])).

tff(c_233,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_235,plain,
    ( ~ m1_orders_2('#skF_6','#skF_3','#skF_6')
    | k1_xboole_0 = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_164,c_233])).

tff(c_238,plain,
    ( k1_xboole_0 = '#skF_6'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_213,c_164,c_235])).

tff(c_239,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_238])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_241,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_12])).

tff(c_243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_232,c_241])).

tff(c_245,plain,(
    r2_xboole_0('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ r2_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_249,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_245,c_10])).

tff(c_264,plain,(
    ! [B_150,A_151] :
      ( B_150 = A_151
      | ~ r1_tarski(B_150,A_151)
      | ~ r1_tarski(A_151,B_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_269,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_249,c_264])).

tff(c_274,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_269])).

tff(c_44,plain,(
    m2_orders_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_310,plain,(
    ! [C_166,A_167,B_168] :
      ( m1_subset_1(C_166,k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ m2_orders_2(C_166,A_167,B_168)
      | ~ m1_orders_1(B_168,k1_orders_1(u1_struct_0(A_167)))
      | ~ l1_orders_2(A_167)
      | ~ v5_orders_2(A_167)
      | ~ v4_orders_2(A_167)
      | ~ v3_orders_2(A_167)
      | v2_struct_0(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_312,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_310])).

tff(c_317,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_312])).

tff(c_318,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_317])).

tff(c_24,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_244,plain,(
    ~ m1_orders_2('#skF_5','#skF_3','#skF_6') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_369,plain,(
    ! [C_189,A_190,D_191,B_192] :
      ( m1_orders_2(C_189,A_190,D_191)
      | m1_orders_2(D_191,A_190,C_189)
      | D_191 = C_189
      | ~ m2_orders_2(D_191,A_190,B_192)
      | ~ m2_orders_2(C_189,A_190,B_192)
      | ~ m1_orders_1(B_192,k1_orders_1(u1_struct_0(A_190)))
      | ~ l1_orders_2(A_190)
      | ~ v5_orders_2(A_190)
      | ~ v4_orders_2(A_190)
      | ~ v3_orders_2(A_190)
      | v2_struct_0(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_371,plain,(
    ! [C_189] :
      ( m1_orders_2(C_189,'#skF_3','#skF_5')
      | m1_orders_2('#skF_5','#skF_3',C_189)
      | C_189 = '#skF_5'
      | ~ m2_orders_2(C_189,'#skF_3','#skF_4')
      | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_369])).

tff(c_376,plain,(
    ! [C_189] :
      ( m1_orders_2(C_189,'#skF_3','#skF_5')
      | m1_orders_2('#skF_5','#skF_3',C_189)
      | C_189 = '#skF_5'
      | ~ m2_orders_2(C_189,'#skF_3','#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_371])).

tff(c_382,plain,(
    ! [C_193] :
      ( m1_orders_2(C_193,'#skF_3','#skF_5')
      | m1_orders_2('#skF_5','#skF_3',C_193)
      | C_193 = '#skF_5'
      | ~ m2_orders_2(C_193,'#skF_3','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_376])).

tff(c_388,plain,
    ( m1_orders_2('#skF_6','#skF_3','#skF_5')
    | m1_orders_2('#skF_5','#skF_3','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_42,c_382])).

tff(c_393,plain,
    ( m1_orders_2('#skF_6','#skF_3','#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_244,c_388])).

tff(c_406,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_393])).

tff(c_411,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_274])).

tff(c_420,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_411])).

tff(c_422,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_393])).

tff(c_373,plain,(
    ! [C_189] :
      ( m1_orders_2(C_189,'#skF_3','#skF_6')
      | m1_orders_2('#skF_6','#skF_3',C_189)
      | C_189 = '#skF_6'
      | ~ m2_orders_2(C_189,'#skF_3','#skF_4')
      | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_369])).

tff(c_380,plain,(
    ! [C_189] :
      ( m1_orders_2(C_189,'#skF_3','#skF_6')
      | m1_orders_2('#skF_6','#skF_3',C_189)
      | C_189 = '#skF_6'
      | ~ m2_orders_2(C_189,'#skF_3','#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_373])).

tff(c_394,plain,(
    ! [C_194] :
      ( m1_orders_2(C_194,'#skF_3','#skF_6')
      | m1_orders_2('#skF_6','#skF_3',C_194)
      | C_194 = '#skF_6'
      | ~ m2_orders_2(C_194,'#skF_3','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_380])).

tff(c_397,plain,
    ( m1_orders_2('#skF_5','#skF_3','#skF_6')
    | m1_orders_2('#skF_6','#skF_3','#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_44,c_394])).

tff(c_403,plain,
    ( m1_orders_2('#skF_6','#skF_3','#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_244,c_397])).

tff(c_423,plain,(
    m1_orders_2('#skF_6','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_422,c_403])).

tff(c_32,plain,(
    ! [C_28,B_26,A_22] :
      ( r1_tarski(C_28,B_26)
      | ~ m1_orders_2(C_28,A_22,B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_orders_2(A_22)
      | ~ v5_orders_2(A_22)
      | ~ v4_orders_2(A_22)
      | ~ v3_orders_2(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_431,plain,
    ( r1_tarski('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_423,c_32])).

tff(c_446,plain,
    ( r1_tarski('#skF_6','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_318,c_431])).

tff(c_448,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_274,c_446])).

tff(c_449,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_269])).

tff(c_453,plain,(
    r2_xboole_0('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_449,c_245])).

tff(c_457,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_453])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:24:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.43  
% 2.62/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.43  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 2.62/1.43  
% 2.62/1.43  %Foreground sorts:
% 2.62/1.43  
% 2.62/1.43  
% 2.62/1.43  %Background operators:
% 2.62/1.43  
% 2.62/1.43  
% 2.62/1.43  %Foreground operators:
% 2.62/1.43  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.62/1.43  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.62/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.62/1.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.62/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.62/1.43  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.62/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.62/1.43  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.62/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.62/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.62/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.62/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.62/1.43  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.62/1.43  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.62/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.62/1.43  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.62/1.43  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.62/1.43  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.62/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.43  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.62/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.62/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.62/1.43  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.62/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.62/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.62/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.62/1.43  
% 2.62/1.45  tff(f_38, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.62/1.45  tff(f_221, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_orders_2)).
% 2.62/1.45  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.62/1.45  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.62/1.45  tff(f_168, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_orders_2)).
% 2.62/1.45  tff(f_101, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.62/1.45  tff(f_120, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_orders_2)).
% 2.62/1.45  tff(f_145, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_orders_2)).
% 2.62/1.45  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.62/1.45  tff(f_63, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.62/1.45  tff(f_196, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_orders_2)).
% 2.62/1.45  tff(c_8, plain, (![B_6]: (~r2_xboole_0(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.62/1.45  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.62/1.45  tff(c_42, plain, (m2_orders_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.62/1.45  tff(c_54, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.62/1.45  tff(c_52, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.62/1.45  tff(c_50, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.62/1.45  tff(c_48, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.62/1.45  tff(c_46, plain, (m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.62/1.45  tff(c_173, plain, (![A_111, B_112]: (r2_hidden('#skF_2'(A_111, B_112), A_111) | r1_xboole_0(A_111, B_112))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.62/1.45  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.62/1.45  tff(c_177, plain, (![A_111, B_112]: (~v1_xboole_0(A_111) | r1_xboole_0(A_111, B_112))), inference(resolution, [status(thm)], [c_173, c_2])).
% 2.62/1.45  tff(c_214, plain, (![C_130, D_131, A_132, B_133]: (~r1_xboole_0(C_130, D_131) | ~m2_orders_2(D_131, A_132, B_133) | ~m2_orders_2(C_130, A_132, B_133) | ~m1_orders_1(B_133, k1_orders_1(u1_struct_0(A_132))) | ~l1_orders_2(A_132) | ~v5_orders_2(A_132) | ~v4_orders_2(A_132) | ~v3_orders_2(A_132) | v2_struct_0(A_132))), inference(cnfTransformation, [status(thm)], [f_168])).
% 2.62/1.45  tff(c_221, plain, (![B_134, A_135, B_136, A_137]: (~m2_orders_2(B_134, A_135, B_136) | ~m2_orders_2(A_137, A_135, B_136) | ~m1_orders_1(B_136, k1_orders_1(u1_struct_0(A_135))) | ~l1_orders_2(A_135) | ~v5_orders_2(A_135) | ~v4_orders_2(A_135) | ~v3_orders_2(A_135) | v2_struct_0(A_135) | ~v1_xboole_0(A_137))), inference(resolution, [status(thm)], [c_177, c_214])).
% 2.62/1.45  tff(c_223, plain, (![A_137]: (~m2_orders_2(A_137, '#skF_3', '#skF_4') | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3') | ~v1_xboole_0(A_137))), inference(resolution, [status(thm)], [c_42, c_221])).
% 2.62/1.45  tff(c_226, plain, (![A_137]: (~m2_orders_2(A_137, '#skF_3', '#skF_4') | v2_struct_0('#skF_3') | ~v1_xboole_0(A_137))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_223])).
% 2.62/1.45  tff(c_228, plain, (![A_138]: (~m2_orders_2(A_138, '#skF_3', '#skF_4') | ~v1_xboole_0(A_138))), inference(negUnitSimplification, [status(thm)], [c_56, c_226])).
% 2.62/1.45  tff(c_232, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_42, c_228])).
% 2.62/1.45  tff(c_207, plain, (![C_127, A_128, B_129]: (m1_subset_1(C_127, k1_zfmisc_1(u1_struct_0(A_128))) | ~m2_orders_2(C_127, A_128, B_129) | ~m1_orders_1(B_129, k1_orders_1(u1_struct_0(A_128))) | ~l1_orders_2(A_128) | ~v5_orders_2(A_128) | ~v4_orders_2(A_128) | ~v3_orders_2(A_128) | v2_struct_0(A_128))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.62/1.45  tff(c_209, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_207])).
% 2.62/1.45  tff(c_212, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_209])).
% 2.62/1.45  tff(c_213, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_56, c_212])).
% 2.62/1.45  tff(c_90, plain, (![A_90, B_91]: (r2_xboole_0(A_90, B_91) | B_91=A_90 | ~r1_tarski(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.62/1.45  tff(c_58, plain, (~m1_orders_2('#skF_5', '#skF_3', '#skF_6') | ~r2_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.62/1.45  tff(c_75, plain, (~r2_xboole_0('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_58])).
% 2.62/1.45  tff(c_101, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_90, c_75])).
% 2.62/1.45  tff(c_107, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_101])).
% 2.62/1.45  tff(c_64, plain, (r2_xboole_0('#skF_5', '#skF_6') | m1_orders_2('#skF_5', '#skF_3', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.62/1.45  tff(c_76, plain, (m1_orders_2('#skF_5', '#skF_3', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_75, c_64])).
% 2.62/1.45  tff(c_134, plain, (![C_102, B_103, A_104]: (r1_tarski(C_102, B_103) | ~m1_orders_2(C_102, A_104, B_103) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_orders_2(A_104) | ~v5_orders_2(A_104) | ~v4_orders_2(A_104) | ~v3_orders_2(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.62/1.45  tff(c_136, plain, (r1_tarski('#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_76, c_134])).
% 2.62/1.45  tff(c_139, plain, (r1_tarski('#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_136])).
% 2.62/1.45  tff(c_140, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_56, c_107, c_139])).
% 2.62/1.45  tff(c_148, plain, (![C_108, A_109, B_110]: (m1_subset_1(C_108, k1_zfmisc_1(u1_struct_0(A_109))) | ~m2_orders_2(C_108, A_109, B_110) | ~m1_orders_1(B_110, k1_orders_1(u1_struct_0(A_109))) | ~l1_orders_2(A_109) | ~v5_orders_2(A_109) | ~v4_orders_2(A_109) | ~v3_orders_2(A_109) | v2_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.62/1.45  tff(c_152, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_148])).
% 2.62/1.45  tff(c_159, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_152])).
% 2.62/1.45  tff(c_161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_140, c_159])).
% 2.62/1.45  tff(c_162, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_101])).
% 2.62/1.45  tff(c_164, plain, (m1_orders_2('#skF_6', '#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_76])).
% 2.62/1.45  tff(c_233, plain, (![C_139, A_140, B_141]: (~m1_orders_2(C_139, A_140, B_141) | ~m1_orders_2(B_141, A_140, C_139) | k1_xboole_0=B_141 | ~m1_subset_1(C_139, k1_zfmisc_1(u1_struct_0(A_140))) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_orders_2(A_140) | ~v5_orders_2(A_140) | ~v4_orders_2(A_140) | ~v3_orders_2(A_140) | v2_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_145])).
% 2.62/1.45  tff(c_235, plain, (~m1_orders_2('#skF_6', '#skF_3', '#skF_6') | k1_xboole_0='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_164, c_233])).
% 2.62/1.45  tff(c_238, plain, (k1_xboole_0='#skF_6' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_213, c_164, c_235])).
% 2.62/1.45  tff(c_239, plain, (k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_56, c_238])).
% 2.62/1.45  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.62/1.45  tff(c_241, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_239, c_12])).
% 2.62/1.45  tff(c_243, plain, $false, inference(negUnitSimplification, [status(thm)], [c_232, c_241])).
% 2.62/1.45  tff(c_245, plain, (r2_xboole_0('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_58])).
% 2.62/1.45  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~r2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.62/1.45  tff(c_249, plain, (r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_245, c_10])).
% 2.62/1.45  tff(c_264, plain, (![B_150, A_151]: (B_150=A_151 | ~r1_tarski(B_150, A_151) | ~r1_tarski(A_151, B_150))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.62/1.45  tff(c_269, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_249, c_264])).
% 2.62/1.45  tff(c_274, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_269])).
% 2.62/1.45  tff(c_44, plain, (m2_orders_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.62/1.45  tff(c_310, plain, (![C_166, A_167, B_168]: (m1_subset_1(C_166, k1_zfmisc_1(u1_struct_0(A_167))) | ~m2_orders_2(C_166, A_167, B_168) | ~m1_orders_1(B_168, k1_orders_1(u1_struct_0(A_167))) | ~l1_orders_2(A_167) | ~v5_orders_2(A_167) | ~v4_orders_2(A_167) | ~v3_orders_2(A_167) | v2_struct_0(A_167))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.62/1.45  tff(c_312, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_310])).
% 2.62/1.45  tff(c_317, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_312])).
% 2.62/1.45  tff(c_318, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_56, c_317])).
% 2.62/1.45  tff(c_24, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.62/1.45  tff(c_244, plain, (~m1_orders_2('#skF_5', '#skF_3', '#skF_6')), inference(splitRight, [status(thm)], [c_58])).
% 2.62/1.45  tff(c_369, plain, (![C_189, A_190, D_191, B_192]: (m1_orders_2(C_189, A_190, D_191) | m1_orders_2(D_191, A_190, C_189) | D_191=C_189 | ~m2_orders_2(D_191, A_190, B_192) | ~m2_orders_2(C_189, A_190, B_192) | ~m1_orders_1(B_192, k1_orders_1(u1_struct_0(A_190))) | ~l1_orders_2(A_190) | ~v5_orders_2(A_190) | ~v4_orders_2(A_190) | ~v3_orders_2(A_190) | v2_struct_0(A_190))), inference(cnfTransformation, [status(thm)], [f_196])).
% 2.62/1.45  tff(c_371, plain, (![C_189]: (m1_orders_2(C_189, '#skF_3', '#skF_5') | m1_orders_2('#skF_5', '#skF_3', C_189) | C_189='#skF_5' | ~m2_orders_2(C_189, '#skF_3', '#skF_4') | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_369])).
% 2.62/1.45  tff(c_376, plain, (![C_189]: (m1_orders_2(C_189, '#skF_3', '#skF_5') | m1_orders_2('#skF_5', '#skF_3', C_189) | C_189='#skF_5' | ~m2_orders_2(C_189, '#skF_3', '#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_371])).
% 2.62/1.45  tff(c_382, plain, (![C_193]: (m1_orders_2(C_193, '#skF_3', '#skF_5') | m1_orders_2('#skF_5', '#skF_3', C_193) | C_193='#skF_5' | ~m2_orders_2(C_193, '#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_56, c_376])).
% 2.62/1.45  tff(c_388, plain, (m1_orders_2('#skF_6', '#skF_3', '#skF_5') | m1_orders_2('#skF_5', '#skF_3', '#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_42, c_382])).
% 2.62/1.45  tff(c_393, plain, (m1_orders_2('#skF_6', '#skF_3', '#skF_5') | '#skF_5'='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_244, c_388])).
% 2.62/1.45  tff(c_406, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_393])).
% 2.62/1.45  tff(c_411, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_406, c_274])).
% 2.62/1.45  tff(c_420, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_411])).
% 2.62/1.45  tff(c_422, plain, ('#skF_5'!='#skF_6'), inference(splitRight, [status(thm)], [c_393])).
% 2.62/1.45  tff(c_373, plain, (![C_189]: (m1_orders_2(C_189, '#skF_3', '#skF_6') | m1_orders_2('#skF_6', '#skF_3', C_189) | C_189='#skF_6' | ~m2_orders_2(C_189, '#skF_3', '#skF_4') | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_369])).
% 2.62/1.45  tff(c_380, plain, (![C_189]: (m1_orders_2(C_189, '#skF_3', '#skF_6') | m1_orders_2('#skF_6', '#skF_3', C_189) | C_189='#skF_6' | ~m2_orders_2(C_189, '#skF_3', '#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_373])).
% 2.62/1.45  tff(c_394, plain, (![C_194]: (m1_orders_2(C_194, '#skF_3', '#skF_6') | m1_orders_2('#skF_6', '#skF_3', C_194) | C_194='#skF_6' | ~m2_orders_2(C_194, '#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_56, c_380])).
% 2.62/1.45  tff(c_397, plain, (m1_orders_2('#skF_5', '#skF_3', '#skF_6') | m1_orders_2('#skF_6', '#skF_3', '#skF_5') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_44, c_394])).
% 2.62/1.45  tff(c_403, plain, (m1_orders_2('#skF_6', '#skF_3', '#skF_5') | '#skF_5'='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_244, c_397])).
% 2.62/1.45  tff(c_423, plain, (m1_orders_2('#skF_6', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_422, c_403])).
% 2.62/1.45  tff(c_32, plain, (![C_28, B_26, A_22]: (r1_tarski(C_28, B_26) | ~m1_orders_2(C_28, A_22, B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_orders_2(A_22) | ~v5_orders_2(A_22) | ~v4_orders_2(A_22) | ~v3_orders_2(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.62/1.45  tff(c_431, plain, (r1_tarski('#skF_6', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_423, c_32])).
% 2.62/1.45  tff(c_446, plain, (r1_tarski('#skF_6', '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_318, c_431])).
% 2.62/1.45  tff(c_448, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_274, c_446])).
% 2.62/1.45  tff(c_449, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_269])).
% 2.62/1.45  tff(c_453, plain, (r2_xboole_0('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_449, c_245])).
% 2.62/1.45  tff(c_457, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_453])).
% 2.62/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.45  
% 2.62/1.45  Inference rules
% 2.62/1.45  ----------------------
% 2.62/1.45  #Ref     : 0
% 2.62/1.45  #Sup     : 60
% 2.62/1.45  #Fact    : 0
% 2.62/1.45  #Define  : 0
% 2.62/1.45  #Split   : 6
% 2.62/1.45  #Chain   : 0
% 2.62/1.45  #Close   : 0
% 2.62/1.45  
% 2.62/1.45  Ordering : KBO
% 2.62/1.45  
% 2.62/1.45  Simplification rules
% 2.62/1.45  ----------------------
% 2.62/1.45  #Subsume      : 15
% 2.62/1.45  #Demod        : 162
% 2.62/1.45  #Tautology    : 23
% 2.62/1.45  #SimpNegUnit  : 33
% 2.62/1.45  #BackRed      : 18
% 2.62/1.45  
% 2.62/1.45  #Partial instantiations: 0
% 2.62/1.45  #Strategies tried      : 1
% 2.62/1.45  
% 2.62/1.45  Timing (in seconds)
% 2.62/1.45  ----------------------
% 2.62/1.45  Preprocessing        : 0.35
% 2.62/1.45  Parsing              : 0.20
% 2.62/1.45  CNF conversion       : 0.03
% 2.62/1.45  Main loop            : 0.29
% 2.62/1.45  Inferencing          : 0.11
% 2.62/1.45  Reduction            : 0.09
% 2.62/1.45  Demodulation         : 0.07
% 2.62/1.45  BG Simplification    : 0.02
% 2.62/1.45  Subsumption          : 0.05
% 2.62/1.45  Abstraction          : 0.01
% 2.62/1.45  MUC search           : 0.00
% 2.62/1.45  Cooper               : 0.00
% 2.62/1.46  Total                : 0.68
% 2.62/1.46  Index Insertion      : 0.00
% 2.62/1.46  Index Deletion       : 0.00
% 2.62/1.46  Index Matching       : 0.00
% 2.62/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
