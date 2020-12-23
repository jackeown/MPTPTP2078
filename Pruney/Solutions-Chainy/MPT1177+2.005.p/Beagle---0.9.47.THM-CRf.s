%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:55 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 292 expanded)
%              Number of leaves         :   37 ( 124 expanded)
%              Depth                    :   10
%              Number of atoms          :  283 (1240 expanded)
%              Number of equality atoms :   21 (  46 expanded)
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

tff(f_222,negated_conjecture,(
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

tff(f_102,axiom,(
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

tff(f_121,axiom,(
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

tff(f_146,axiom,(
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

tff(f_64,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_169,axiom,(
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

tff(f_62,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_197,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_42,plain,(
    m2_orders_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_54,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_52,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_50,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_48,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_46,plain,(
    m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_277,plain,(
    ! [C_134,A_135,B_136] :
      ( m1_subset_1(C_134,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ m2_orders_2(C_134,A_135,B_136)
      | ~ m1_orders_1(B_136,k1_orders_1(u1_struct_0(A_135)))
      | ~ l1_orders_2(A_135)
      | ~ v5_orders_2(A_135)
      | ~ v4_orders_2(A_135)
      | ~ v3_orders_2(A_135)
      | v2_struct_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_279,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_277])).

tff(c_282,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_279])).

tff(c_283,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_282])).

tff(c_97,plain,(
    ! [A_96,B_97] :
      ( r2_xboole_0(A_96,B_97)
      | B_97 = A_96
      | ~ r1_tarski(A_96,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_58,plain,
    ( ~ m1_orders_2('#skF_5','#skF_3','#skF_6')
    | ~ r2_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_76,plain,(
    ~ r2_xboole_0('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_108,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_97,c_76])).

tff(c_114,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_64,plain,
    ( r2_xboole_0('#skF_5','#skF_6')
    | m1_orders_2('#skF_5','#skF_3','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_77,plain,(
    m1_orders_2('#skF_5','#skF_3','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_64])).

tff(c_175,plain,(
    ! [C_110,B_111,A_112] :
      ( r1_tarski(C_110,B_111)
      | ~ m1_orders_2(C_110,A_112,B_111)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_orders_2(A_112)
      | ~ v5_orders_2(A_112)
      | ~ v4_orders_2(A_112)
      | ~ v3_orders_2(A_112)
      | v2_struct_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_177,plain,
    ( r1_tarski('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_77,c_175])).

tff(c_180,plain,
    ( r1_tarski('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_177])).

tff(c_181,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_114,c_180])).

tff(c_183,plain,(
    ! [C_113,A_114,B_115] :
      ( m1_subset_1(C_113,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ m2_orders_2(C_113,A_114,B_115)
      | ~ m1_orders_1(B_115,k1_orders_1(u1_struct_0(A_114)))
      | ~ l1_orders_2(A_114)
      | ~ v5_orders_2(A_114)
      | ~ v4_orders_2(A_114)
      | ~ v3_orders_2(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_187,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_183])).

tff(c_194,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_187])).

tff(c_196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_181,c_194])).

tff(c_197,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_199,plain,(
    m1_orders_2('#skF_6','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_77])).

tff(c_304,plain,(
    ! [C_144,A_145,B_146] :
      ( ~ m1_orders_2(C_144,A_145,B_146)
      | ~ m1_orders_2(B_146,A_145,C_144)
      | k1_xboole_0 = B_146
      | ~ m1_subset_1(C_144,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_orders_2(A_145)
      | ~ v5_orders_2(A_145)
      | ~ v4_orders_2(A_145)
      | ~ v3_orders_2(A_145)
      | v2_struct_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_306,plain,
    ( ~ m1_orders_2('#skF_6','#skF_3','#skF_6')
    | k1_xboole_0 = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_199,c_304])).

tff(c_309,plain,
    ( k1_xboole_0 = '#skF_6'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_283,c_199,c_306])).

tff(c_310,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_309])).

tff(c_24,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_284,plain,(
    ! [C_137,D_138,A_139,B_140] :
      ( ~ r1_xboole_0(C_137,D_138)
      | ~ m2_orders_2(D_138,A_139,B_140)
      | ~ m2_orders_2(C_137,A_139,B_140)
      | ~ m1_orders_1(B_140,k1_orders_1(u1_struct_0(A_139)))
      | ~ l1_orders_2(A_139)
      | ~ v5_orders_2(A_139)
      | ~ v4_orders_2(A_139)
      | ~ v3_orders_2(A_139)
      | v2_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_297,plain,(
    ! [A_141,B_142,A_143] :
      ( ~ m2_orders_2(k1_xboole_0,A_141,B_142)
      | ~ m2_orders_2(A_143,A_141,B_142)
      | ~ m1_orders_1(B_142,k1_orders_1(u1_struct_0(A_141)))
      | ~ l1_orders_2(A_141)
      | ~ v5_orders_2(A_141)
      | ~ v4_orders_2(A_141)
      | ~ v3_orders_2(A_141)
      | v2_struct_0(A_141) ) ),
    inference(resolution,[status(thm)],[c_24,c_284])).

tff(c_299,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_3','#skF_4')
    | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_297])).

tff(c_302,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_299])).

tff(c_303,plain,(
    ~ m2_orders_2(k1_xboole_0,'#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_302])).

tff(c_312,plain,(
    ~ m2_orders_2('#skF_6','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_303])).

tff(c_321,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_312])).

tff(c_323,plain,(
    r2_xboole_0('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ r2_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_327,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_323,c_10])).

tff(c_330,plain,(
    ! [B_147,A_148] :
      ( B_147 = A_148
      | ~ r1_tarski(B_147,A_148)
      | ~ r1_tarski(A_148,B_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_335,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_327,c_330])).

tff(c_340,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_335])).

tff(c_44,plain,(
    m2_orders_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_429,plain,(
    ! [C_177,A_178,B_179] :
      ( m1_subset_1(C_177,k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ m2_orders_2(C_177,A_178,B_179)
      | ~ m1_orders_1(B_179,k1_orders_1(u1_struct_0(A_178)))
      | ~ l1_orders_2(A_178)
      | ~ v5_orders_2(A_178)
      | ~ v4_orders_2(A_178)
      | ~ v3_orders_2(A_178)
      | v2_struct_0(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_431,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_429])).

tff(c_436,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_431])).

tff(c_437,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_436])).

tff(c_22,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_322,plain,(
    ~ m1_orders_2('#skF_5','#skF_3','#skF_6') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_505,plain,(
    ! [C_203,A_204,D_205,B_206] :
      ( m1_orders_2(C_203,A_204,D_205)
      | m1_orders_2(D_205,A_204,C_203)
      | D_205 = C_203
      | ~ m2_orders_2(D_205,A_204,B_206)
      | ~ m2_orders_2(C_203,A_204,B_206)
      | ~ m1_orders_1(B_206,k1_orders_1(u1_struct_0(A_204)))
      | ~ l1_orders_2(A_204)
      | ~ v5_orders_2(A_204)
      | ~ v4_orders_2(A_204)
      | ~ v3_orders_2(A_204)
      | v2_struct_0(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_507,plain,(
    ! [C_203] :
      ( m1_orders_2(C_203,'#skF_3','#skF_5')
      | m1_orders_2('#skF_5','#skF_3',C_203)
      | C_203 = '#skF_5'
      | ~ m2_orders_2(C_203,'#skF_3','#skF_4')
      | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_505])).

tff(c_512,plain,(
    ! [C_203] :
      ( m1_orders_2(C_203,'#skF_3','#skF_5')
      | m1_orders_2('#skF_5','#skF_3',C_203)
      | C_203 = '#skF_5'
      | ~ m2_orders_2(C_203,'#skF_3','#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_507])).

tff(c_518,plain,(
    ! [C_207] :
      ( m1_orders_2(C_207,'#skF_3','#skF_5')
      | m1_orders_2('#skF_5','#skF_3',C_207)
      | C_207 = '#skF_5'
      | ~ m2_orders_2(C_207,'#skF_3','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_512])).

tff(c_524,plain,
    ( m1_orders_2('#skF_6','#skF_3','#skF_5')
    | m1_orders_2('#skF_5','#skF_3','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_42,c_518])).

tff(c_529,plain,
    ( m1_orders_2('#skF_6','#skF_3','#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_322,c_524])).

tff(c_530,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_529])).

tff(c_547,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_530,c_340])).

tff(c_556,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_547])).

tff(c_557,plain,(
    m1_orders_2('#skF_6','#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_529])).

tff(c_32,plain,(
    ! [C_29,B_27,A_23] :
      ( r1_tarski(C_29,B_27)
      | ~ m1_orders_2(C_29,A_23,B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_orders_2(A_23)
      | ~ v5_orders_2(A_23)
      | ~ v4_orders_2(A_23)
      | ~ v3_orders_2(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_566,plain,
    ( r1_tarski('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_557,c_32])).

tff(c_581,plain,
    ( r1_tarski('#skF_6','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_437,c_566])).

tff(c_583,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_340,c_581])).

tff(c_584,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_335])).

tff(c_588,plain,(
    r2_xboole_0('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_584,c_323])).

tff(c_592,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_588])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:56:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.43  
% 2.81/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.44  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 2.81/1.44  
% 2.81/1.44  %Foreground sorts:
% 2.81/1.44  
% 2.81/1.44  
% 2.81/1.44  %Background operators:
% 2.81/1.44  
% 2.81/1.44  
% 2.81/1.44  %Foreground operators:
% 2.81/1.44  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.81/1.44  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.81/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.81/1.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.81/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.81/1.44  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.81/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.81/1.44  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.81/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.81/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.81/1.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.81/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.81/1.44  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.81/1.44  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.81/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.81/1.44  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.81/1.44  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.81/1.44  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.81/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.44  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.81/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.81/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.81/1.44  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.81/1.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.81/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.81/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.81/1.44  
% 2.81/1.46  tff(f_38, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.81/1.46  tff(f_222, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_orders_2)).
% 2.81/1.46  tff(f_102, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.81/1.46  tff(f_121, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_orders_2)).
% 2.81/1.46  tff(f_146, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_orders_2)).
% 2.81/1.46  tff(f_64, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.81/1.46  tff(f_169, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_orders_2)).
% 2.81/1.46  tff(f_62, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.81/1.46  tff(f_197, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_orders_2)).
% 2.81/1.46  tff(c_8, plain, (![B_6]: (~r2_xboole_0(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.81/1.46  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_222])).
% 2.81/1.46  tff(c_42, plain, (m2_orders_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_222])).
% 2.81/1.46  tff(c_54, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_222])).
% 2.81/1.46  tff(c_52, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_222])).
% 2.81/1.46  tff(c_50, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_222])).
% 2.81/1.46  tff(c_48, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_222])).
% 2.81/1.46  tff(c_46, plain, (m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_222])).
% 2.81/1.46  tff(c_277, plain, (![C_134, A_135, B_136]: (m1_subset_1(C_134, k1_zfmisc_1(u1_struct_0(A_135))) | ~m2_orders_2(C_134, A_135, B_136) | ~m1_orders_1(B_136, k1_orders_1(u1_struct_0(A_135))) | ~l1_orders_2(A_135) | ~v5_orders_2(A_135) | ~v4_orders_2(A_135) | ~v3_orders_2(A_135) | v2_struct_0(A_135))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.81/1.46  tff(c_279, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_277])).
% 2.81/1.46  tff(c_282, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_279])).
% 2.81/1.46  tff(c_283, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_56, c_282])).
% 2.81/1.46  tff(c_97, plain, (![A_96, B_97]: (r2_xboole_0(A_96, B_97) | B_97=A_96 | ~r1_tarski(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.81/1.46  tff(c_58, plain, (~m1_orders_2('#skF_5', '#skF_3', '#skF_6') | ~r2_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_222])).
% 2.81/1.46  tff(c_76, plain, (~r2_xboole_0('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_58])).
% 2.81/1.46  tff(c_108, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_97, c_76])).
% 2.81/1.46  tff(c_114, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_108])).
% 2.81/1.46  tff(c_64, plain, (r2_xboole_0('#skF_5', '#skF_6') | m1_orders_2('#skF_5', '#skF_3', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_222])).
% 2.81/1.46  tff(c_77, plain, (m1_orders_2('#skF_5', '#skF_3', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_76, c_64])).
% 2.81/1.46  tff(c_175, plain, (![C_110, B_111, A_112]: (r1_tarski(C_110, B_111) | ~m1_orders_2(C_110, A_112, B_111) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_orders_2(A_112) | ~v5_orders_2(A_112) | ~v4_orders_2(A_112) | ~v3_orders_2(A_112) | v2_struct_0(A_112))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.81/1.46  tff(c_177, plain, (r1_tarski('#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_77, c_175])).
% 2.81/1.46  tff(c_180, plain, (r1_tarski('#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_177])).
% 2.81/1.46  tff(c_181, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_56, c_114, c_180])).
% 2.81/1.46  tff(c_183, plain, (![C_113, A_114, B_115]: (m1_subset_1(C_113, k1_zfmisc_1(u1_struct_0(A_114))) | ~m2_orders_2(C_113, A_114, B_115) | ~m1_orders_1(B_115, k1_orders_1(u1_struct_0(A_114))) | ~l1_orders_2(A_114) | ~v5_orders_2(A_114) | ~v4_orders_2(A_114) | ~v3_orders_2(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.81/1.46  tff(c_187, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_183])).
% 2.81/1.46  tff(c_194, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_187])).
% 2.81/1.46  tff(c_196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_181, c_194])).
% 2.81/1.46  tff(c_197, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_108])).
% 2.81/1.46  tff(c_199, plain, (m1_orders_2('#skF_6', '#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_197, c_77])).
% 2.81/1.46  tff(c_304, plain, (![C_144, A_145, B_146]: (~m1_orders_2(C_144, A_145, B_146) | ~m1_orders_2(B_146, A_145, C_144) | k1_xboole_0=B_146 | ~m1_subset_1(C_144, k1_zfmisc_1(u1_struct_0(A_145))) | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_orders_2(A_145) | ~v5_orders_2(A_145) | ~v4_orders_2(A_145) | ~v3_orders_2(A_145) | v2_struct_0(A_145))), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.81/1.46  tff(c_306, plain, (~m1_orders_2('#skF_6', '#skF_3', '#skF_6') | k1_xboole_0='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_199, c_304])).
% 2.81/1.46  tff(c_309, plain, (k1_xboole_0='#skF_6' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_283, c_199, c_306])).
% 2.81/1.46  tff(c_310, plain, (k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_56, c_309])).
% 2.81/1.46  tff(c_24, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.81/1.46  tff(c_284, plain, (![C_137, D_138, A_139, B_140]: (~r1_xboole_0(C_137, D_138) | ~m2_orders_2(D_138, A_139, B_140) | ~m2_orders_2(C_137, A_139, B_140) | ~m1_orders_1(B_140, k1_orders_1(u1_struct_0(A_139))) | ~l1_orders_2(A_139) | ~v5_orders_2(A_139) | ~v4_orders_2(A_139) | ~v3_orders_2(A_139) | v2_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.81/1.46  tff(c_297, plain, (![A_141, B_142, A_143]: (~m2_orders_2(k1_xboole_0, A_141, B_142) | ~m2_orders_2(A_143, A_141, B_142) | ~m1_orders_1(B_142, k1_orders_1(u1_struct_0(A_141))) | ~l1_orders_2(A_141) | ~v5_orders_2(A_141) | ~v4_orders_2(A_141) | ~v3_orders_2(A_141) | v2_struct_0(A_141))), inference(resolution, [status(thm)], [c_24, c_284])).
% 2.81/1.46  tff(c_299, plain, (~m2_orders_2(k1_xboole_0, '#skF_3', '#skF_4') | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_297])).
% 2.81/1.46  tff(c_302, plain, (~m2_orders_2(k1_xboole_0, '#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_299])).
% 2.81/1.46  tff(c_303, plain, (~m2_orders_2(k1_xboole_0, '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_56, c_302])).
% 2.81/1.46  tff(c_312, plain, (~m2_orders_2('#skF_6', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_310, c_303])).
% 2.81/1.46  tff(c_321, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_312])).
% 2.81/1.46  tff(c_323, plain, (r2_xboole_0('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_58])).
% 2.81/1.46  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~r2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.81/1.46  tff(c_327, plain, (r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_323, c_10])).
% 2.81/1.46  tff(c_330, plain, (![B_147, A_148]: (B_147=A_148 | ~r1_tarski(B_147, A_148) | ~r1_tarski(A_148, B_147))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.81/1.46  tff(c_335, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_327, c_330])).
% 2.81/1.46  tff(c_340, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_335])).
% 2.81/1.46  tff(c_44, plain, (m2_orders_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_222])).
% 2.81/1.46  tff(c_429, plain, (![C_177, A_178, B_179]: (m1_subset_1(C_177, k1_zfmisc_1(u1_struct_0(A_178))) | ~m2_orders_2(C_177, A_178, B_179) | ~m1_orders_1(B_179, k1_orders_1(u1_struct_0(A_178))) | ~l1_orders_2(A_178) | ~v5_orders_2(A_178) | ~v4_orders_2(A_178) | ~v3_orders_2(A_178) | v2_struct_0(A_178))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.81/1.46  tff(c_431, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_429])).
% 2.81/1.46  tff(c_436, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_431])).
% 2.81/1.46  tff(c_437, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_56, c_436])).
% 2.81/1.46  tff(c_22, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.81/1.46  tff(c_322, plain, (~m1_orders_2('#skF_5', '#skF_3', '#skF_6')), inference(splitRight, [status(thm)], [c_58])).
% 2.81/1.46  tff(c_505, plain, (![C_203, A_204, D_205, B_206]: (m1_orders_2(C_203, A_204, D_205) | m1_orders_2(D_205, A_204, C_203) | D_205=C_203 | ~m2_orders_2(D_205, A_204, B_206) | ~m2_orders_2(C_203, A_204, B_206) | ~m1_orders_1(B_206, k1_orders_1(u1_struct_0(A_204))) | ~l1_orders_2(A_204) | ~v5_orders_2(A_204) | ~v4_orders_2(A_204) | ~v3_orders_2(A_204) | v2_struct_0(A_204))), inference(cnfTransformation, [status(thm)], [f_197])).
% 2.81/1.46  tff(c_507, plain, (![C_203]: (m1_orders_2(C_203, '#skF_3', '#skF_5') | m1_orders_2('#skF_5', '#skF_3', C_203) | C_203='#skF_5' | ~m2_orders_2(C_203, '#skF_3', '#skF_4') | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_505])).
% 2.81/1.46  tff(c_512, plain, (![C_203]: (m1_orders_2(C_203, '#skF_3', '#skF_5') | m1_orders_2('#skF_5', '#skF_3', C_203) | C_203='#skF_5' | ~m2_orders_2(C_203, '#skF_3', '#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_507])).
% 2.81/1.46  tff(c_518, plain, (![C_207]: (m1_orders_2(C_207, '#skF_3', '#skF_5') | m1_orders_2('#skF_5', '#skF_3', C_207) | C_207='#skF_5' | ~m2_orders_2(C_207, '#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_56, c_512])).
% 2.81/1.46  tff(c_524, plain, (m1_orders_2('#skF_6', '#skF_3', '#skF_5') | m1_orders_2('#skF_5', '#skF_3', '#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_42, c_518])).
% 2.81/1.46  tff(c_529, plain, (m1_orders_2('#skF_6', '#skF_3', '#skF_5') | '#skF_5'='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_322, c_524])).
% 2.81/1.46  tff(c_530, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_529])).
% 2.81/1.46  tff(c_547, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_530, c_340])).
% 2.81/1.46  tff(c_556, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_547])).
% 2.81/1.46  tff(c_557, plain, (m1_orders_2('#skF_6', '#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_529])).
% 2.81/1.46  tff(c_32, plain, (![C_29, B_27, A_23]: (r1_tarski(C_29, B_27) | ~m1_orders_2(C_29, A_23, B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_orders_2(A_23) | ~v5_orders_2(A_23) | ~v4_orders_2(A_23) | ~v3_orders_2(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.81/1.46  tff(c_566, plain, (r1_tarski('#skF_6', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_557, c_32])).
% 2.81/1.46  tff(c_581, plain, (r1_tarski('#skF_6', '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_437, c_566])).
% 2.81/1.46  tff(c_583, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_340, c_581])).
% 2.81/1.46  tff(c_584, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_335])).
% 2.81/1.46  tff(c_588, plain, (r2_xboole_0('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_584, c_323])).
% 2.81/1.46  tff(c_592, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_588])).
% 2.81/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.46  
% 2.81/1.46  Inference rules
% 2.81/1.46  ----------------------
% 2.81/1.46  #Ref     : 0
% 2.81/1.46  #Sup     : 87
% 2.81/1.46  #Fact    : 0
% 2.81/1.46  #Define  : 0
% 2.81/1.46  #Split   : 7
% 2.81/1.46  #Chain   : 0
% 2.81/1.46  #Close   : 0
% 2.81/1.46  
% 2.81/1.46  Ordering : KBO
% 2.81/1.46  
% 2.81/1.46  Simplification rules
% 2.81/1.46  ----------------------
% 2.81/1.46  #Subsume      : 19
% 2.81/1.46  #Demod        : 184
% 2.81/1.46  #Tautology    : 32
% 2.81/1.46  #SimpNegUnit  : 32
% 2.81/1.46  #BackRed      : 24
% 2.81/1.46  
% 2.81/1.46  #Partial instantiations: 0
% 2.81/1.46  #Strategies tried      : 1
% 2.81/1.46  
% 2.81/1.46  Timing (in seconds)
% 2.81/1.46  ----------------------
% 2.81/1.46  Preprocessing        : 0.33
% 2.81/1.46  Parsing              : 0.18
% 2.81/1.46  CNF conversion       : 0.03
% 2.81/1.46  Main loop            : 0.32
% 2.81/1.46  Inferencing          : 0.12
% 2.81/1.46  Reduction            : 0.10
% 2.81/1.46  Demodulation         : 0.07
% 2.81/1.46  BG Simplification    : 0.02
% 2.81/1.46  Subsumption          : 0.06
% 2.81/1.46  Abstraction          : 0.01
% 2.81/1.46  MUC search           : 0.00
% 2.81/1.46  Cooper               : 0.00
% 2.81/1.46  Total                : 0.68
% 2.81/1.46  Index Insertion      : 0.00
% 2.81/1.46  Index Deletion       : 0.00
% 2.81/1.46  Index Matching       : 0.00
% 2.81/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
