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
% DateTime   : Thu Dec  3 10:20:02 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 267 expanded)
%              Number of leaves         :   37 ( 116 expanded)
%              Depth                    :   12
%              Number of atoms          :  292 (1188 expanded)
%              Number of equality atoms :   17 (  32 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_220,negated_conjecture,(
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

tff(f_100,axiom,(
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

tff(f_119,axiom,(
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

tff(f_144,axiom,(
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

tff(f_52,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_50,axiom,(
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

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_167,axiom,(
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

tff(f_57,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_195,axiom,(
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

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_48,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_46,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_44,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_42,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_40,plain,(
    m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_38,plain,(
    m2_orders_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_277,plain,(
    ! [C_141,A_142,B_143] :
      ( m1_subset_1(C_141,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ m2_orders_2(C_141,A_142,B_143)
      | ~ m1_orders_1(B_143,k1_orders_1(u1_struct_0(A_142)))
      | ~ l1_orders_2(A_142)
      | ~ v5_orders_2(A_142)
      | ~ v4_orders_2(A_142)
      | ~ v3_orders_2(A_142)
      | v2_struct_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_279,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_277])).

tff(c_282,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_279])).

tff(c_283,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_282])).

tff(c_66,plain,(
    ! [A_84,B_85] :
      ( r2_xboole_0(A_84,B_85)
      | B_85 = A_84
      | ~ r1_tarski(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_5')
    | ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_64,plain,(
    ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_80,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_64])).

tff(c_85,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_58,plain,
    ( r2_xboole_0('#skF_4','#skF_5')
    | m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_65,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58])).

tff(c_172,plain,(
    ! [C_111,B_112,A_113] :
      ( r1_tarski(C_111,B_112)
      | ~ m1_orders_2(C_111,A_113,B_112)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_orders_2(A_113)
      | ~ v5_orders_2(A_113)
      | ~ v4_orders_2(A_113)
      | ~ v3_orders_2(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_174,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_65,c_172])).

tff(c_177,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_174])).

tff(c_178,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_85,c_177])).

tff(c_36,plain,(
    m2_orders_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_179,plain,(
    ! [C_114,A_115,B_116] :
      ( m1_subset_1(C_114,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ m2_orders_2(C_114,A_115,B_116)
      | ~ m1_orders_1(B_116,k1_orders_1(u1_struct_0(A_115)))
      | ~ l1_orders_2(A_115)
      | ~ v5_orders_2(A_115)
      | ~ v4_orders_2(A_115)
      | ~ v3_orders_2(A_115)
      | v2_struct_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_183,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_179])).

tff(c_190,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_183])).

tff(c_192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_178,c_190])).

tff(c_193,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_195,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_65])).

tff(c_298,plain,(
    ! [C_151,A_152,B_153] :
      ( ~ m1_orders_2(C_151,A_152,B_153)
      | ~ m1_orders_2(B_153,A_152,C_151)
      | k1_xboole_0 = B_153
      | ~ m1_subset_1(C_151,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ l1_orders_2(A_152)
      | ~ v5_orders_2(A_152)
      | ~ v4_orders_2(A_152)
      | ~ v3_orders_2(A_152)
      | v2_struct_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_300,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_195,c_298])).

tff(c_303,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_283,c_195,c_300])).

tff(c_304,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_303])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_209,plain,(
    ! [A_119,B_120] :
      ( r2_hidden('#skF_1'(A_119,B_120),A_119)
      | r1_xboole_0(A_119,B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_18,plain,(
    ! [B_12,A_11] :
      ( ~ r1_tarski(B_12,A_11)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_259,plain,(
    ! [A_135,B_136] :
      ( ~ r1_tarski(A_135,'#skF_1'(A_135,B_136))
      | r1_xboole_0(A_135,B_136) ) ),
    inference(resolution,[status(thm)],[c_209,c_18])).

tff(c_264,plain,(
    ! [B_136] : r1_xboole_0(k1_xboole_0,B_136) ),
    inference(resolution,[status(thm)],[c_14,c_259])).

tff(c_291,plain,(
    ! [C_147,D_148,A_149,B_150] :
      ( ~ r1_xboole_0(C_147,D_148)
      | ~ m2_orders_2(D_148,A_149,B_150)
      | ~ m2_orders_2(C_147,A_149,B_150)
      | ~ m1_orders_1(B_150,k1_orders_1(u1_struct_0(A_149)))
      | ~ l1_orders_2(A_149)
      | ~ v5_orders_2(A_149)
      | ~ v4_orders_2(A_149)
      | ~ v3_orders_2(A_149)
      | v2_struct_0(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_296,plain,(
    ! [B_136,A_149,B_150] :
      ( ~ m2_orders_2(B_136,A_149,B_150)
      | ~ m2_orders_2(k1_xboole_0,A_149,B_150)
      | ~ m1_orders_1(B_150,k1_orders_1(u1_struct_0(A_149)))
      | ~ l1_orders_2(A_149)
      | ~ v5_orders_2(A_149)
      | ~ v4_orders_2(A_149)
      | ~ v3_orders_2(A_149)
      | v2_struct_0(A_149) ) ),
    inference(resolution,[status(thm)],[c_264,c_291])).

tff(c_379,plain,(
    ! [B_165,A_166,B_167] :
      ( ~ m2_orders_2(B_165,A_166,B_167)
      | ~ m2_orders_2('#skF_4',A_166,B_167)
      | ~ m1_orders_1(B_167,k1_orders_1(u1_struct_0(A_166)))
      | ~ l1_orders_2(A_166)
      | ~ v5_orders_2(A_166)
      | ~ v4_orders_2(A_166)
      | ~ v3_orders_2(A_166)
      | v2_struct_0(A_166) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_296])).

tff(c_381,plain,
    ( ~ m2_orders_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_379])).

tff(c_384,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_38,c_381])).

tff(c_386,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_384])).

tff(c_388,plain,(
    r2_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_16,plain,(
    ! [B_10,A_9] :
      ( ~ r2_xboole_0(B_10,A_9)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_396,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_388,c_16])).

tff(c_504,plain,(
    ! [C_198,A_199,B_200] :
      ( m1_subset_1(C_198,k1_zfmisc_1(u1_struct_0(A_199)))
      | ~ m2_orders_2(C_198,A_199,B_200)
      | ~ m1_orders_1(B_200,k1_orders_1(u1_struct_0(A_199)))
      | ~ l1_orders_2(A_199)
      | ~ v5_orders_2(A_199)
      | ~ v4_orders_2(A_199)
      | ~ v3_orders_2(A_199)
      | v2_struct_0(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_506,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_504])).

tff(c_511,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_506])).

tff(c_512,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_511])).

tff(c_4,plain,(
    ! [B_2] : ~ r2_xboole_0(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_387,plain,(
    ~ m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_540,plain,(
    ! [C_218,A_219,D_220,B_221] :
      ( m1_orders_2(C_218,A_219,D_220)
      | m1_orders_2(D_220,A_219,C_218)
      | D_220 = C_218
      | ~ m2_orders_2(D_220,A_219,B_221)
      | ~ m2_orders_2(C_218,A_219,B_221)
      | ~ m1_orders_1(B_221,k1_orders_1(u1_struct_0(A_219)))
      | ~ l1_orders_2(A_219)
      | ~ v5_orders_2(A_219)
      | ~ v4_orders_2(A_219)
      | ~ v3_orders_2(A_219)
      | v2_struct_0(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_542,plain,(
    ! [C_218] :
      ( m1_orders_2(C_218,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_218)
      | C_218 = '#skF_4'
      | ~ m2_orders_2(C_218,'#skF_2','#skF_3')
      | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_540])).

tff(c_547,plain,(
    ! [C_218] :
      ( m1_orders_2(C_218,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_218)
      | C_218 = '#skF_4'
      | ~ m2_orders_2(C_218,'#skF_2','#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_542])).

tff(c_553,plain,(
    ! [C_222] :
      ( m1_orders_2(C_222,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_222)
      | C_222 = '#skF_4'
      | ~ m2_orders_2(C_222,'#skF_2','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_547])).

tff(c_559,plain,
    ( m1_orders_2('#skF_5','#skF_2','#skF_4')
    | m1_orders_2('#skF_4','#skF_2','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_553])).

tff(c_564,plain,
    ( m1_orders_2('#skF_5','#skF_2','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_387,c_559])).

tff(c_565,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_564])).

tff(c_584,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_565,c_388])).

tff(c_589,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_584])).

tff(c_590,plain,(
    m1_orders_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_564])).

tff(c_26,plain,(
    ! [C_27,B_25,A_21] :
      ( r1_tarski(C_27,B_25)
      | ~ m1_orders_2(C_27,A_21,B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_orders_2(A_21)
      | ~ v5_orders_2(A_21)
      | ~ v4_orders_2(A_21)
      | ~ v3_orders_2(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_599,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_590,c_26])).

tff(c_614,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_512,c_599])).

tff(c_616,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_396,c_614])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:29:26 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.01/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.41  
% 3.01/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.41  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.01/1.41  
% 3.01/1.41  %Foreground sorts:
% 3.01/1.41  
% 3.01/1.41  
% 3.01/1.41  %Background operators:
% 3.01/1.41  
% 3.01/1.41  
% 3.01/1.41  %Foreground operators:
% 3.01/1.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.01/1.41  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.01/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.01/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.01/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.01/1.41  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 3.01/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.01/1.41  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 3.01/1.41  tff('#skF_5', type, '#skF_5': $i).
% 3.01/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.01/1.41  tff('#skF_2', type, '#skF_2': $i).
% 3.01/1.41  tff('#skF_3', type, '#skF_3': $i).
% 3.01/1.41  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.01/1.41  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.01/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.01/1.41  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.01/1.41  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.01/1.41  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 3.01/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.01/1.41  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 3.01/1.41  tff('#skF_4', type, '#skF_4': $i).
% 3.01/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.01/1.41  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 3.01/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.01/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.01/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.01/1.41  
% 3.30/1.43  tff(f_220, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_orders_2)).
% 3.30/1.43  tff(f_100, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 3.30/1.43  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.30/1.43  tff(f_119, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_orders_2)).
% 3.30/1.43  tff(f_144, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_orders_2)).
% 3.30/1.43  tff(f_52, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.30/1.43  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.30/1.43  tff(f_62, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.30/1.43  tff(f_167, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_orders_2)).
% 3.30/1.43  tff(f_57, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_xboole_1)).
% 3.30/1.43  tff(f_195, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_orders_2)).
% 3.30/1.43  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.30/1.43  tff(c_48, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.30/1.43  tff(c_46, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.30/1.43  tff(c_44, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.30/1.43  tff(c_42, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.30/1.43  tff(c_40, plain, (m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.30/1.43  tff(c_38, plain, (m2_orders_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.30/1.43  tff(c_277, plain, (![C_141, A_142, B_143]: (m1_subset_1(C_141, k1_zfmisc_1(u1_struct_0(A_142))) | ~m2_orders_2(C_141, A_142, B_143) | ~m1_orders_1(B_143, k1_orders_1(u1_struct_0(A_142))) | ~l1_orders_2(A_142) | ~v5_orders_2(A_142) | ~v4_orders_2(A_142) | ~v3_orders_2(A_142) | v2_struct_0(A_142))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.30/1.43  tff(c_279, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_277])).
% 3.30/1.43  tff(c_282, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_279])).
% 3.30/1.43  tff(c_283, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_282])).
% 3.30/1.43  tff(c_66, plain, (![A_84, B_85]: (r2_xboole_0(A_84, B_85) | B_85=A_84 | ~r1_tarski(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.30/1.43  tff(c_52, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_5') | ~r2_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.30/1.43  tff(c_64, plain, (~r2_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_52])).
% 3.30/1.43  tff(c_80, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_66, c_64])).
% 3.30/1.43  tff(c_85, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_80])).
% 3.30/1.43  tff(c_58, plain, (r2_xboole_0('#skF_4', '#skF_5') | m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.30/1.43  tff(c_65, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_64, c_58])).
% 3.30/1.43  tff(c_172, plain, (![C_111, B_112, A_113]: (r1_tarski(C_111, B_112) | ~m1_orders_2(C_111, A_113, B_112) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_orders_2(A_113) | ~v5_orders_2(A_113) | ~v4_orders_2(A_113) | ~v3_orders_2(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.30/1.43  tff(c_174, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_65, c_172])).
% 3.30/1.43  tff(c_177, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_174])).
% 3.30/1.43  tff(c_178, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_85, c_177])).
% 3.30/1.43  tff(c_36, plain, (m2_orders_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.30/1.43  tff(c_179, plain, (![C_114, A_115, B_116]: (m1_subset_1(C_114, k1_zfmisc_1(u1_struct_0(A_115))) | ~m2_orders_2(C_114, A_115, B_116) | ~m1_orders_1(B_116, k1_orders_1(u1_struct_0(A_115))) | ~l1_orders_2(A_115) | ~v5_orders_2(A_115) | ~v4_orders_2(A_115) | ~v3_orders_2(A_115) | v2_struct_0(A_115))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.30/1.43  tff(c_183, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_179])).
% 3.30/1.43  tff(c_190, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_183])).
% 3.30/1.43  tff(c_192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_178, c_190])).
% 3.30/1.43  tff(c_193, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_80])).
% 3.30/1.43  tff(c_195, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_193, c_65])).
% 3.30/1.43  tff(c_298, plain, (![C_151, A_152, B_153]: (~m1_orders_2(C_151, A_152, B_153) | ~m1_orders_2(B_153, A_152, C_151) | k1_xboole_0=B_153 | ~m1_subset_1(C_151, k1_zfmisc_1(u1_struct_0(A_152))) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_152))) | ~l1_orders_2(A_152) | ~v5_orders_2(A_152) | ~v4_orders_2(A_152) | ~v3_orders_2(A_152) | v2_struct_0(A_152))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.30/1.43  tff(c_300, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_195, c_298])).
% 3.30/1.43  tff(c_303, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_283, c_195, c_300])).
% 3.30/1.43  tff(c_304, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_50, c_303])).
% 3.30/1.43  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.30/1.43  tff(c_209, plain, (![A_119, B_120]: (r2_hidden('#skF_1'(A_119, B_120), A_119) | r1_xboole_0(A_119, B_120))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.30/1.43  tff(c_18, plain, (![B_12, A_11]: (~r1_tarski(B_12, A_11) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.30/1.43  tff(c_259, plain, (![A_135, B_136]: (~r1_tarski(A_135, '#skF_1'(A_135, B_136)) | r1_xboole_0(A_135, B_136))), inference(resolution, [status(thm)], [c_209, c_18])).
% 3.30/1.43  tff(c_264, plain, (![B_136]: (r1_xboole_0(k1_xboole_0, B_136))), inference(resolution, [status(thm)], [c_14, c_259])).
% 3.30/1.43  tff(c_291, plain, (![C_147, D_148, A_149, B_150]: (~r1_xboole_0(C_147, D_148) | ~m2_orders_2(D_148, A_149, B_150) | ~m2_orders_2(C_147, A_149, B_150) | ~m1_orders_1(B_150, k1_orders_1(u1_struct_0(A_149))) | ~l1_orders_2(A_149) | ~v5_orders_2(A_149) | ~v4_orders_2(A_149) | ~v3_orders_2(A_149) | v2_struct_0(A_149))), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.30/1.43  tff(c_296, plain, (![B_136, A_149, B_150]: (~m2_orders_2(B_136, A_149, B_150) | ~m2_orders_2(k1_xboole_0, A_149, B_150) | ~m1_orders_1(B_150, k1_orders_1(u1_struct_0(A_149))) | ~l1_orders_2(A_149) | ~v5_orders_2(A_149) | ~v4_orders_2(A_149) | ~v3_orders_2(A_149) | v2_struct_0(A_149))), inference(resolution, [status(thm)], [c_264, c_291])).
% 3.30/1.43  tff(c_379, plain, (![B_165, A_166, B_167]: (~m2_orders_2(B_165, A_166, B_167) | ~m2_orders_2('#skF_4', A_166, B_167) | ~m1_orders_1(B_167, k1_orders_1(u1_struct_0(A_166))) | ~l1_orders_2(A_166) | ~v5_orders_2(A_166) | ~v4_orders_2(A_166) | ~v3_orders_2(A_166) | v2_struct_0(A_166))), inference(demodulation, [status(thm), theory('equality')], [c_304, c_296])).
% 3.30/1.43  tff(c_381, plain, (~m2_orders_2('#skF_4', '#skF_2', '#skF_3') | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_379])).
% 3.30/1.43  tff(c_384, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_38, c_381])).
% 3.30/1.43  tff(c_386, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_384])).
% 3.30/1.43  tff(c_388, plain, (r2_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_52])).
% 3.30/1.43  tff(c_16, plain, (![B_10, A_9]: (~r2_xboole_0(B_10, A_9) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.30/1.43  tff(c_396, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_388, c_16])).
% 3.30/1.43  tff(c_504, plain, (![C_198, A_199, B_200]: (m1_subset_1(C_198, k1_zfmisc_1(u1_struct_0(A_199))) | ~m2_orders_2(C_198, A_199, B_200) | ~m1_orders_1(B_200, k1_orders_1(u1_struct_0(A_199))) | ~l1_orders_2(A_199) | ~v5_orders_2(A_199) | ~v4_orders_2(A_199) | ~v3_orders_2(A_199) | v2_struct_0(A_199))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.30/1.43  tff(c_506, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_504])).
% 3.30/1.43  tff(c_511, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_506])).
% 3.30/1.43  tff(c_512, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_511])).
% 3.30/1.43  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.30/1.43  tff(c_387, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(splitRight, [status(thm)], [c_52])).
% 3.30/1.43  tff(c_540, plain, (![C_218, A_219, D_220, B_221]: (m1_orders_2(C_218, A_219, D_220) | m1_orders_2(D_220, A_219, C_218) | D_220=C_218 | ~m2_orders_2(D_220, A_219, B_221) | ~m2_orders_2(C_218, A_219, B_221) | ~m1_orders_1(B_221, k1_orders_1(u1_struct_0(A_219))) | ~l1_orders_2(A_219) | ~v5_orders_2(A_219) | ~v4_orders_2(A_219) | ~v3_orders_2(A_219) | v2_struct_0(A_219))), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.30/1.43  tff(c_542, plain, (![C_218]: (m1_orders_2(C_218, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_218) | C_218='#skF_4' | ~m2_orders_2(C_218, '#skF_2', '#skF_3') | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_540])).
% 3.30/1.43  tff(c_547, plain, (![C_218]: (m1_orders_2(C_218, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_218) | C_218='#skF_4' | ~m2_orders_2(C_218, '#skF_2', '#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_542])).
% 3.30/1.43  tff(c_553, plain, (![C_222]: (m1_orders_2(C_222, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_222) | C_222='#skF_4' | ~m2_orders_2(C_222, '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_547])).
% 3.30/1.43  tff(c_559, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_36, c_553])).
% 3.30/1.43  tff(c_564, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4') | '#skF_5'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_387, c_559])).
% 3.30/1.43  tff(c_565, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_564])).
% 3.30/1.43  tff(c_584, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_565, c_388])).
% 3.30/1.43  tff(c_589, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_584])).
% 3.30/1.43  tff(c_590, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_564])).
% 3.30/1.43  tff(c_26, plain, (![C_27, B_25, A_21]: (r1_tarski(C_27, B_25) | ~m1_orders_2(C_27, A_21, B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_orders_2(A_21) | ~v5_orders_2(A_21) | ~v4_orders_2(A_21) | ~v3_orders_2(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.30/1.43  tff(c_599, plain, (r1_tarski('#skF_5', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_590, c_26])).
% 3.30/1.43  tff(c_614, plain, (r1_tarski('#skF_5', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_512, c_599])).
% 3.30/1.43  tff(c_616, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_396, c_614])).
% 3.30/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.43  
% 3.30/1.43  Inference rules
% 3.30/1.43  ----------------------
% 3.30/1.43  #Ref     : 0
% 3.30/1.43  #Sup     : 96
% 3.30/1.43  #Fact    : 0
% 3.30/1.43  #Define  : 0
% 3.30/1.43  #Split   : 3
% 3.30/1.43  #Chain   : 0
% 3.30/1.43  #Close   : 0
% 3.30/1.43  
% 3.30/1.43  Ordering : KBO
% 3.30/1.43  
% 3.30/1.43  Simplification rules
% 3.30/1.43  ----------------------
% 3.30/1.43  #Subsume      : 15
% 3.30/1.43  #Demod        : 166
% 3.30/1.43  #Tautology    : 40
% 3.30/1.43  #SimpNegUnit  : 29
% 3.30/1.43  #BackRed      : 17
% 3.30/1.43  
% 3.30/1.43  #Partial instantiations: 0
% 3.30/1.43  #Strategies tried      : 1
% 3.30/1.43  
% 3.30/1.43  Timing (in seconds)
% 3.30/1.43  ----------------------
% 3.30/1.43  Preprocessing        : 0.33
% 3.30/1.43  Parsing              : 0.19
% 3.30/1.43  CNF conversion       : 0.03
% 3.30/1.43  Main loop            : 0.32
% 3.30/1.43  Inferencing          : 0.12
% 3.30/1.43  Reduction            : 0.10
% 3.30/1.43  Demodulation         : 0.06
% 3.30/1.43  BG Simplification    : 0.02
% 3.30/1.43  Subsumption          : 0.06
% 3.30/1.43  Abstraction          : 0.01
% 3.30/1.43  MUC search           : 0.00
% 3.30/1.43  Cooper               : 0.00
% 3.30/1.43  Total                : 0.69
% 3.30/1.43  Index Insertion      : 0.00
% 3.30/1.43  Index Deletion       : 0.00
% 3.30/1.43  Index Matching       : 0.00
% 3.30/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
