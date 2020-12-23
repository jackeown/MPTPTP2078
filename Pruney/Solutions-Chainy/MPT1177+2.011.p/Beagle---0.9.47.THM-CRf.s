%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:56 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 344 expanded)
%              Number of leaves         :   41 ( 142 expanded)
%              Depth                    :   10
%              Number of atoms          :  316 (1437 expanded)
%              Number of equality atoms :   23 (  50 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_226,negated_conjecture,(
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

tff(f_51,axiom,(
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

tff(f_59,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_61,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_173,axiom,(
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

tff(f_106,axiom,(
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

tff(f_125,axiom,(
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

tff(f_150,axiom,(
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

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_201,axiom,(
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

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_56,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_54,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_52,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_50,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_48,plain,(
    m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_46,plain,(
    m2_orders_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_12,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [A_10] : k2_subset_1(A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_24,plain,(
    ! [A_11] : m1_subset_1(k2_subset_1(A_11),k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_67,plain,(
    ! [A_11] : m1_subset_1(A_11,k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24])).

tff(c_176,plain,(
    ! [C_116,B_117,A_118] :
      ( ~ v1_xboole_0(C_116)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(C_116))
      | ~ r2_hidden(A_118,B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_190,plain,(
    ! [A_122,A_123] :
      ( ~ v1_xboole_0(A_122)
      | ~ r2_hidden(A_123,A_122) ) ),
    inference(resolution,[status(thm)],[c_67,c_176])).

tff(c_198,plain,(
    ! [B_4,A_3] :
      ( ~ v1_xboole_0(B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_12,c_190])).

tff(c_239,plain,(
    ! [C_140,D_141,A_142,B_143] :
      ( ~ r1_xboole_0(C_140,D_141)
      | ~ m2_orders_2(D_141,A_142,B_143)
      | ~ m2_orders_2(C_140,A_142,B_143)
      | ~ m1_orders_1(B_143,k1_orders_1(u1_struct_0(A_142)))
      | ~ l1_orders_2(A_142)
      | ~ v5_orders_2(A_142)
      | ~ v4_orders_2(A_142)
      | ~ v3_orders_2(A_142)
      | v2_struct_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_246,plain,(
    ! [B_144,A_145,B_146,A_147] :
      ( ~ m2_orders_2(B_144,A_145,B_146)
      | ~ m2_orders_2(A_147,A_145,B_146)
      | ~ m1_orders_1(B_146,k1_orders_1(u1_struct_0(A_145)))
      | ~ l1_orders_2(A_145)
      | ~ v5_orders_2(A_145)
      | ~ v4_orders_2(A_145)
      | ~ v3_orders_2(A_145)
      | v2_struct_0(A_145)
      | ~ v1_xboole_0(B_144) ) ),
    inference(resolution,[status(thm)],[c_198,c_239])).

tff(c_248,plain,(
    ! [A_147] :
      ( ~ m2_orders_2(A_147,'#skF_2','#skF_3')
      | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_46,c_246])).

tff(c_251,plain,(
    ! [A_147] :
      ( ~ m2_orders_2(A_147,'#skF_2','#skF_3')
      | v2_struct_0('#skF_2')
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_248])).

tff(c_252,plain,(
    ! [A_147] :
      ( ~ m2_orders_2(A_147,'#skF_2','#skF_3')
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_251])).

tff(c_253,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_252])).

tff(c_228,plain,(
    ! [C_137,A_138,B_139] :
      ( m1_subset_1(C_137,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ m2_orders_2(C_137,A_138,B_139)
      | ~ m1_orders_1(B_139,k1_orders_1(u1_struct_0(A_138)))
      | ~ l1_orders_2(A_138)
      | ~ v5_orders_2(A_138)
      | ~ v4_orders_2(A_138)
      | ~ v3_orders_2(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_230,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_228])).

tff(c_233,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_230])).

tff(c_234,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_233])).

tff(c_93,plain,(
    ! [A_90,B_91] :
      ( r2_xboole_0(A_90,B_91)
      | B_91 = A_90
      | ~ r1_tarski(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_60,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_5')
    | ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_82,plain,(
    ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_104,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_93,c_82])).

tff(c_110,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_66,plain,
    ( r2_xboole_0('#skF_4','#skF_5')
    | m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_83,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_66])).

tff(c_133,plain,(
    ! [C_104,B_105,A_106] :
      ( r1_tarski(C_104,B_105)
      | ~ m1_orders_2(C_104,A_106,B_105)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_orders_2(A_106)
      | ~ v5_orders_2(A_106)
      | ~ v4_orders_2(A_106)
      | ~ v3_orders_2(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_135,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_83,c_133])).

tff(c_138,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_135])).

tff(c_139,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_110,c_138])).

tff(c_44,plain,(
    m2_orders_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_160,plain,(
    ! [C_113,A_114,B_115] :
      ( m1_subset_1(C_113,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ m2_orders_2(C_113,A_114,B_115)
      | ~ m1_orders_1(B_115,k1_orders_1(u1_struct_0(A_114)))
      | ~ l1_orders_2(A_114)
      | ~ v5_orders_2(A_114)
      | ~ v4_orders_2(A_114)
      | ~ v3_orders_2(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_164,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_160])).

tff(c_171,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_164])).

tff(c_173,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_139,c_171])).

tff(c_174,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_180,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_83])).

tff(c_254,plain,(
    ! [C_148,A_149,B_150] :
      ( ~ m1_orders_2(C_148,A_149,B_150)
      | ~ m1_orders_2(B_150,A_149,C_148)
      | k1_xboole_0 = B_150
      | ~ m1_subset_1(C_148,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_orders_2(A_149)
      | ~ v5_orders_2(A_149)
      | ~ v4_orders_2(A_149)
      | ~ v3_orders_2(A_149)
      | v2_struct_0(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_256,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_180,c_254])).

tff(c_259,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_234,c_180,c_256])).

tff(c_260,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_259])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_262,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_8])).

tff(c_264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_253,c_262])).

tff(c_265,plain,(
    ! [A_147] : ~ m2_orders_2(A_147,'#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_265,c_46])).

tff(c_270,plain,(
    r2_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_282,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_270,c_6])).

tff(c_286,plain,(
    ! [B_155,A_156] :
      ( B_155 = A_156
      | ~ r1_tarski(B_155,A_156)
      | ~ r1_tarski(A_156,B_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_291,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_282,c_286])).

tff(c_296,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_291])).

tff(c_346,plain,(
    ! [C_177,A_178,B_179] :
      ( m1_subset_1(C_177,k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ m2_orders_2(C_177,A_178,B_179)
      | ~ m1_orders_1(B_179,k1_orders_1(u1_struct_0(A_178)))
      | ~ l1_orders_2(A_178)
      | ~ v5_orders_2(A_178)
      | ~ v4_orders_2(A_178)
      | ~ v3_orders_2(A_178)
      | v2_struct_0(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_348,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_346])).

tff(c_353,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_348])).

tff(c_354,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_353])).

tff(c_20,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_269,plain,(
    ~ m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_271,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_276,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_269,c_271])).

tff(c_278,plain,(
    ~ m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_391,plain,(
    ! [C_194,A_195,D_196,B_197] :
      ( m1_orders_2(C_194,A_195,D_196)
      | m1_orders_2(D_196,A_195,C_194)
      | D_196 = C_194
      | ~ m2_orders_2(D_196,A_195,B_197)
      | ~ m2_orders_2(C_194,A_195,B_197)
      | ~ m1_orders_1(B_197,k1_orders_1(u1_struct_0(A_195)))
      | ~ l1_orders_2(A_195)
      | ~ v5_orders_2(A_195)
      | ~ v4_orders_2(A_195)
      | ~ v3_orders_2(A_195)
      | v2_struct_0(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_393,plain,(
    ! [C_194] :
      ( m1_orders_2(C_194,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_194)
      | C_194 = '#skF_4'
      | ~ m2_orders_2(C_194,'#skF_2','#skF_3')
      | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_46,c_391])).

tff(c_398,plain,(
    ! [C_194] :
      ( m1_orders_2(C_194,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_194)
      | C_194 = '#skF_4'
      | ~ m2_orders_2(C_194,'#skF_2','#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_393])).

tff(c_404,plain,(
    ! [C_198] :
      ( m1_orders_2(C_198,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_198)
      | C_198 = '#skF_4'
      | ~ m2_orders_2(C_198,'#skF_2','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_398])).

tff(c_410,plain,
    ( m1_orders_2('#skF_5','#skF_2','#skF_4')
    | m1_orders_2('#skF_4','#skF_2','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_404])).

tff(c_415,plain,
    ( m1_orders_2('#skF_5','#skF_2','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_278,c_410])).

tff(c_416,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_415])).

tff(c_420,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_296])).

tff(c_429,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_420])).

tff(c_430,plain,(
    m1_orders_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_415])).

tff(c_34,plain,(
    ! [C_29,B_27,A_23] :
      ( r1_tarski(C_29,B_27)
      | ~ m1_orders_2(C_29,A_23,B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_orders_2(A_23)
      | ~ v5_orders_2(A_23)
      | ~ v4_orders_2(A_23)
      | ~ v3_orders_2(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_437,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_430,c_34])).

tff(c_448,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_354,c_437])).

tff(c_450,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_296,c_448])).

tff(c_451,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_291])).

tff(c_468,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_451,c_270])).

tff(c_472,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_468])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:08:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.35  
% 2.73/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.35  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.73/1.35  
% 2.73/1.35  %Foreground sorts:
% 2.73/1.35  
% 2.73/1.35  
% 2.73/1.35  %Background operators:
% 2.73/1.35  
% 2.73/1.35  
% 2.73/1.35  %Foreground operators:
% 2.73/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.73/1.35  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.73/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.73/1.35  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.73/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.35  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.73/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.73/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.73/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.73/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.73/1.35  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.73/1.35  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.73/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.73/1.35  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.73/1.35  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.73/1.35  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.73/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.35  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.73/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.73/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.35  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.73/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.73/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.73/1.35  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.73/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.73/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.73/1.35  
% 2.90/1.37  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.90/1.37  tff(f_226, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_orders_2)).
% 2.90/1.37  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.90/1.37  tff(f_59, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.90/1.37  tff(f_61, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.90/1.37  tff(f_68, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.90/1.37  tff(f_173, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_orders_2)).
% 2.90/1.37  tff(f_106, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.90/1.37  tff(f_125, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_orders_2)).
% 2.90/1.37  tff(f_150, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_orders_2)).
% 2.90/1.37  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.90/1.37  tff(f_57, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.90/1.37  tff(f_201, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_orders_2)).
% 2.90/1.37  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.90/1.37  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_226])).
% 2.90/1.37  tff(c_56, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_226])).
% 2.90/1.37  tff(c_54, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_226])).
% 2.90/1.37  tff(c_52, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_226])).
% 2.90/1.37  tff(c_50, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_226])).
% 2.90/1.37  tff(c_48, plain, (m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_226])).
% 2.90/1.37  tff(c_46, plain, (m2_orders_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_226])).
% 2.90/1.37  tff(c_12, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.90/1.37  tff(c_22, plain, (![A_10]: (k2_subset_1(A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.90/1.37  tff(c_24, plain, (![A_11]: (m1_subset_1(k2_subset_1(A_11), k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.90/1.37  tff(c_67, plain, (![A_11]: (m1_subset_1(A_11, k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24])).
% 2.90/1.37  tff(c_176, plain, (![C_116, B_117, A_118]: (~v1_xboole_0(C_116) | ~m1_subset_1(B_117, k1_zfmisc_1(C_116)) | ~r2_hidden(A_118, B_117))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.90/1.37  tff(c_190, plain, (![A_122, A_123]: (~v1_xboole_0(A_122) | ~r2_hidden(A_123, A_122))), inference(resolution, [status(thm)], [c_67, c_176])).
% 2.90/1.37  tff(c_198, plain, (![B_4, A_3]: (~v1_xboole_0(B_4) | r1_xboole_0(A_3, B_4))), inference(resolution, [status(thm)], [c_12, c_190])).
% 2.90/1.37  tff(c_239, plain, (![C_140, D_141, A_142, B_143]: (~r1_xboole_0(C_140, D_141) | ~m2_orders_2(D_141, A_142, B_143) | ~m2_orders_2(C_140, A_142, B_143) | ~m1_orders_1(B_143, k1_orders_1(u1_struct_0(A_142))) | ~l1_orders_2(A_142) | ~v5_orders_2(A_142) | ~v4_orders_2(A_142) | ~v3_orders_2(A_142) | v2_struct_0(A_142))), inference(cnfTransformation, [status(thm)], [f_173])).
% 2.90/1.37  tff(c_246, plain, (![B_144, A_145, B_146, A_147]: (~m2_orders_2(B_144, A_145, B_146) | ~m2_orders_2(A_147, A_145, B_146) | ~m1_orders_1(B_146, k1_orders_1(u1_struct_0(A_145))) | ~l1_orders_2(A_145) | ~v5_orders_2(A_145) | ~v4_orders_2(A_145) | ~v3_orders_2(A_145) | v2_struct_0(A_145) | ~v1_xboole_0(B_144))), inference(resolution, [status(thm)], [c_198, c_239])).
% 2.90/1.37  tff(c_248, plain, (![A_147]: (~m2_orders_2(A_147, '#skF_2', '#skF_3') | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_46, c_246])).
% 2.90/1.37  tff(c_251, plain, (![A_147]: (~m2_orders_2(A_147, '#skF_2', '#skF_3') | v2_struct_0('#skF_2') | ~v1_xboole_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_248])).
% 2.90/1.37  tff(c_252, plain, (![A_147]: (~m2_orders_2(A_147, '#skF_2', '#skF_3') | ~v1_xboole_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_251])).
% 2.90/1.37  tff(c_253, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_252])).
% 2.90/1.37  tff(c_228, plain, (![C_137, A_138, B_139]: (m1_subset_1(C_137, k1_zfmisc_1(u1_struct_0(A_138))) | ~m2_orders_2(C_137, A_138, B_139) | ~m1_orders_1(B_139, k1_orders_1(u1_struct_0(A_138))) | ~l1_orders_2(A_138) | ~v5_orders_2(A_138) | ~v4_orders_2(A_138) | ~v3_orders_2(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.90/1.37  tff(c_230, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_228])).
% 2.90/1.37  tff(c_233, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_230])).
% 2.90/1.37  tff(c_234, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_58, c_233])).
% 2.90/1.37  tff(c_93, plain, (![A_90, B_91]: (r2_xboole_0(A_90, B_91) | B_91=A_90 | ~r1_tarski(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.90/1.37  tff(c_60, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_5') | ~r2_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_226])).
% 2.90/1.37  tff(c_82, plain, (~r2_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_60])).
% 2.90/1.37  tff(c_104, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_93, c_82])).
% 2.90/1.37  tff(c_110, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_104])).
% 2.90/1.37  tff(c_66, plain, (r2_xboole_0('#skF_4', '#skF_5') | m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_226])).
% 2.90/1.37  tff(c_83, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_82, c_66])).
% 2.90/1.37  tff(c_133, plain, (![C_104, B_105, A_106]: (r1_tarski(C_104, B_105) | ~m1_orders_2(C_104, A_106, B_105) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_orders_2(A_106) | ~v5_orders_2(A_106) | ~v4_orders_2(A_106) | ~v3_orders_2(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.90/1.37  tff(c_135, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_83, c_133])).
% 2.90/1.37  tff(c_138, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_135])).
% 2.90/1.37  tff(c_139, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_58, c_110, c_138])).
% 2.90/1.37  tff(c_44, plain, (m2_orders_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_226])).
% 2.90/1.37  tff(c_160, plain, (![C_113, A_114, B_115]: (m1_subset_1(C_113, k1_zfmisc_1(u1_struct_0(A_114))) | ~m2_orders_2(C_113, A_114, B_115) | ~m1_orders_1(B_115, k1_orders_1(u1_struct_0(A_114))) | ~l1_orders_2(A_114) | ~v5_orders_2(A_114) | ~v4_orders_2(A_114) | ~v3_orders_2(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.90/1.37  tff(c_164, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_160])).
% 2.90/1.37  tff(c_171, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_164])).
% 2.90/1.37  tff(c_173, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_139, c_171])).
% 2.90/1.37  tff(c_174, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_104])).
% 2.90/1.37  tff(c_180, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_174, c_83])).
% 2.90/1.37  tff(c_254, plain, (![C_148, A_149, B_150]: (~m1_orders_2(C_148, A_149, B_150) | ~m1_orders_2(B_150, A_149, C_148) | k1_xboole_0=B_150 | ~m1_subset_1(C_148, k1_zfmisc_1(u1_struct_0(A_149))) | ~m1_subset_1(B_150, k1_zfmisc_1(u1_struct_0(A_149))) | ~l1_orders_2(A_149) | ~v5_orders_2(A_149) | ~v4_orders_2(A_149) | ~v3_orders_2(A_149) | v2_struct_0(A_149))), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.90/1.37  tff(c_256, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_180, c_254])).
% 2.90/1.37  tff(c_259, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_234, c_180, c_256])).
% 2.90/1.37  tff(c_260, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_58, c_259])).
% 2.90/1.37  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.90/1.37  tff(c_262, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_260, c_8])).
% 2.90/1.37  tff(c_264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_253, c_262])).
% 2.90/1.37  tff(c_265, plain, (![A_147]: (~m2_orders_2(A_147, '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_252])).
% 2.90/1.38  tff(c_268, plain, $false, inference(negUnitSimplification, [status(thm)], [c_265, c_46])).
% 2.90/1.38  tff(c_270, plain, (r2_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_60])).
% 2.90/1.38  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.90/1.38  tff(c_282, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_270, c_6])).
% 2.90/1.38  tff(c_286, plain, (![B_155, A_156]: (B_155=A_156 | ~r1_tarski(B_155, A_156) | ~r1_tarski(A_156, B_155))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.90/1.38  tff(c_291, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_282, c_286])).
% 2.90/1.38  tff(c_296, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_291])).
% 2.90/1.38  tff(c_346, plain, (![C_177, A_178, B_179]: (m1_subset_1(C_177, k1_zfmisc_1(u1_struct_0(A_178))) | ~m2_orders_2(C_177, A_178, B_179) | ~m1_orders_1(B_179, k1_orders_1(u1_struct_0(A_178))) | ~l1_orders_2(A_178) | ~v5_orders_2(A_178) | ~v4_orders_2(A_178) | ~v3_orders_2(A_178) | v2_struct_0(A_178))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.90/1.38  tff(c_348, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_346])).
% 2.90/1.38  tff(c_353, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_348])).
% 2.90/1.38  tff(c_354, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_58, c_353])).
% 2.90/1.38  tff(c_20, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.90/1.38  tff(c_269, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(splitRight, [status(thm)], [c_60])).
% 2.90/1.38  tff(c_271, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(splitLeft, [status(thm)], [c_66])).
% 2.90/1.38  tff(c_276, plain, $false, inference(negUnitSimplification, [status(thm)], [c_269, c_271])).
% 2.90/1.38  tff(c_278, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(splitRight, [status(thm)], [c_66])).
% 2.90/1.38  tff(c_391, plain, (![C_194, A_195, D_196, B_197]: (m1_orders_2(C_194, A_195, D_196) | m1_orders_2(D_196, A_195, C_194) | D_196=C_194 | ~m2_orders_2(D_196, A_195, B_197) | ~m2_orders_2(C_194, A_195, B_197) | ~m1_orders_1(B_197, k1_orders_1(u1_struct_0(A_195))) | ~l1_orders_2(A_195) | ~v5_orders_2(A_195) | ~v4_orders_2(A_195) | ~v3_orders_2(A_195) | v2_struct_0(A_195))), inference(cnfTransformation, [status(thm)], [f_201])).
% 2.90/1.38  tff(c_393, plain, (![C_194]: (m1_orders_2(C_194, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_194) | C_194='#skF_4' | ~m2_orders_2(C_194, '#skF_2', '#skF_3') | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_46, c_391])).
% 2.90/1.38  tff(c_398, plain, (![C_194]: (m1_orders_2(C_194, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_194) | C_194='#skF_4' | ~m2_orders_2(C_194, '#skF_2', '#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_393])).
% 2.90/1.38  tff(c_404, plain, (![C_198]: (m1_orders_2(C_198, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_198) | C_198='#skF_4' | ~m2_orders_2(C_198, '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_398])).
% 2.90/1.38  tff(c_410, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_44, c_404])).
% 2.90/1.38  tff(c_415, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4') | '#skF_5'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_278, c_410])).
% 2.90/1.38  tff(c_416, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_415])).
% 2.90/1.38  tff(c_420, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_416, c_296])).
% 2.90/1.38  tff(c_429, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_420])).
% 2.90/1.38  tff(c_430, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_415])).
% 2.90/1.38  tff(c_34, plain, (![C_29, B_27, A_23]: (r1_tarski(C_29, B_27) | ~m1_orders_2(C_29, A_23, B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_orders_2(A_23) | ~v5_orders_2(A_23) | ~v4_orders_2(A_23) | ~v3_orders_2(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.90/1.38  tff(c_437, plain, (r1_tarski('#skF_5', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_430, c_34])).
% 2.90/1.38  tff(c_448, plain, (r1_tarski('#skF_5', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_354, c_437])).
% 2.90/1.38  tff(c_450, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_296, c_448])).
% 2.90/1.38  tff(c_451, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_291])).
% 2.90/1.38  tff(c_468, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_451, c_270])).
% 2.90/1.38  tff(c_472, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_468])).
% 2.90/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.38  
% 2.90/1.38  Inference rules
% 2.90/1.38  ----------------------
% 2.90/1.38  #Ref     : 0
% 2.90/1.38  #Sup     : 63
% 2.90/1.38  #Fact    : 0
% 2.90/1.38  #Define  : 0
% 2.90/1.38  #Split   : 11
% 2.90/1.38  #Chain   : 0
% 2.90/1.38  #Close   : 0
% 2.90/1.38  
% 2.90/1.38  Ordering : KBO
% 2.90/1.38  
% 2.90/1.38  Simplification rules
% 2.90/1.38  ----------------------
% 2.90/1.38  #Subsume      : 12
% 2.90/1.38  #Demod        : 147
% 2.90/1.38  #Tautology    : 25
% 2.90/1.38  #SimpNegUnit  : 29
% 2.90/1.38  #BackRed      : 18
% 2.90/1.38  
% 2.90/1.38  #Partial instantiations: 0
% 2.90/1.38  #Strategies tried      : 1
% 2.90/1.38  
% 2.90/1.38  Timing (in seconds)
% 2.90/1.38  ----------------------
% 2.90/1.38  Preprocessing        : 0.31
% 2.90/1.38  Parsing              : 0.17
% 2.90/1.38  CNF conversion       : 0.03
% 2.90/1.38  Main loop            : 0.29
% 2.90/1.38  Inferencing          : 0.10
% 2.90/1.38  Reduction            : 0.09
% 2.90/1.38  Demodulation         : 0.07
% 2.90/1.38  BG Simplification    : 0.02
% 2.90/1.38  Subsumption          : 0.06
% 2.90/1.38  Abstraction          : 0.01
% 2.90/1.38  MUC search           : 0.00
% 2.90/1.38  Cooper               : 0.00
% 2.90/1.38  Total                : 0.65
% 2.90/1.38  Index Insertion      : 0.00
% 2.90/1.38  Index Deletion       : 0.00
% 2.90/1.38  Index Matching       : 0.00
% 2.90/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
