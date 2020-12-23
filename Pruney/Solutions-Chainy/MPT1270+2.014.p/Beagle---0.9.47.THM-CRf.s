%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:57 EST 2020

% Result     : Theorem 8.66s
% Output     : CNFRefutation 8.66s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 244 expanded)
%              Number of leaves         :   37 (  95 expanded)
%              Depth                    :   18
%              Number of atoms          :  213 ( 505 expanded)
%              Number of equality atoms :   62 ( 105 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_142,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_79,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_132,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_116,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_123,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_xboole_0(k1_tops_1(A,B),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tops_1)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_54,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_52,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_2816,plain,(
    ! [B_258,A_259] :
      ( r1_tarski(B_258,k2_pre_topc(A_259,B_258))
      | ~ m1_subset_1(B_258,k1_zfmisc_1(u1_struct_0(A_259)))
      | ~ l1_pre_topc(A_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2821,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_2816])).

tff(c_2828,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2821])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1992,plain,(
    ! [A_181,B_182] :
      ( k2_xboole_0(A_181,B_182) = B_182
      | ~ r1_tarski(A_181,B_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2007,plain,(
    ! [A_5,B_6] : k2_xboole_0(k4_xboole_0(A_5,B_6),A_5) = A_5 ),
    inference(resolution,[status(thm)],[c_10,c_1992])).

tff(c_2109,plain,(
    ! [A_198,C_199,B_200] :
      ( r1_xboole_0(A_198,k4_xboole_0(C_199,B_200))
      | ~ r1_tarski(A_198,B_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_14,plain,(
    ! [A_7] :
      ( ~ r1_xboole_0(A_7,A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2460,plain,(
    ! [C_230,B_231] :
      ( k4_xboole_0(C_230,B_231) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(C_230,B_231),B_231) ) ),
    inference(resolution,[status(thm)],[c_2109,c_14])).

tff(c_2476,plain,(
    ! [A_232] : k4_xboole_0(A_232,A_232) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_2460])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( r1_xboole_0(A_11,B_12)
      | k4_xboole_0(A_11,B_12) != A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2072,plain,(
    ! [A_190,B_191,C_192] :
      ( r1_xboole_0(A_190,B_191)
      | ~ r1_xboole_0(A_190,k2_xboole_0(B_191,C_192)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2089,plain,(
    ! [A_11,B_191,C_192] :
      ( r1_xboole_0(A_11,B_191)
      | k4_xboole_0(A_11,k2_xboole_0(B_191,C_192)) != A_11 ) ),
    inference(resolution,[status(thm)],[c_24,c_2072])).

tff(c_3195,plain,(
    ! [B_278,C_279] :
      ( r1_xboole_0(k2_xboole_0(B_278,C_279),B_278)
      | k2_xboole_0(B_278,C_279) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2476,c_2089])).

tff(c_3229,plain,(
    ! [A_5,B_6] :
      ( r1_xboole_0(A_5,k4_xboole_0(A_5,B_6))
      | k2_xboole_0(k4_xboole_0(A_5,B_6),A_5) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2007,c_3195])).

tff(c_3291,plain,(
    ! [A_283,B_284] :
      ( r1_xboole_0(A_283,k4_xboole_0(A_283,B_284))
      | k1_xboole_0 != A_283 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2007,c_3229])).

tff(c_22,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = A_11
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3319,plain,(
    ! [A_285,B_286] :
      ( k4_xboole_0(A_285,k4_xboole_0(A_285,B_286)) = A_285
      | k1_xboole_0 != A_285 ) ),
    inference(resolution,[status(thm)],[c_3291,c_22])).

tff(c_26,plain,(
    ! [A_13,C_15,B_14] :
      ( r1_xboole_0(A_13,k4_xboole_0(C_15,B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4041,plain,(
    ! [A_311,A_312,B_313] :
      ( r1_xboole_0(A_311,A_312)
      | ~ r1_tarski(A_311,k4_xboole_0(A_312,B_313))
      | k1_xboole_0 != A_312 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3319,c_26])).

tff(c_4088,plain,(
    ! [A_314,B_315] :
      ( r1_xboole_0(k4_xboole_0(A_314,B_315),A_314)
      | k1_xboole_0 != A_314 ) ),
    inference(resolution,[status(thm)],[c_6,c_4041])).

tff(c_2381,plain,(
    ! [A_222,A_223,B_224] :
      ( r1_xboole_0(A_222,k4_xboole_0(A_223,B_224))
      | ~ r1_xboole_0(A_222,A_223) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2007,c_2072])).

tff(c_2396,plain,(
    ! [A_223,B_224] :
      ( k4_xboole_0(A_223,B_224) = k1_xboole_0
      | ~ r1_xboole_0(k4_xboole_0(A_223,B_224),A_223) ) ),
    inference(resolution,[status(thm)],[c_2381,c_14])).

tff(c_4171,plain,(
    ! [A_318,B_319] :
      ( k4_xboole_0(A_318,B_319) = k1_xboole_0
      | k1_xboole_0 != A_318 ) ),
    inference(resolution,[status(thm)],[c_4088,c_2396])).

tff(c_2054,plain,(
    ! [A_187,C_188,B_189] :
      ( r1_xboole_0(A_187,C_188)
      | ~ r1_xboole_0(A_187,k2_xboole_0(B_189,C_188)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2071,plain,(
    ! [A_11,C_188,B_189] :
      ( r1_xboole_0(A_11,C_188)
      | k4_xboole_0(A_11,k2_xboole_0(B_189,C_188)) != A_11 ) ),
    inference(resolution,[status(thm)],[c_24,c_2054])).

tff(c_4419,plain,(
    ! [A_322,C_323] :
      ( r1_xboole_0(A_322,C_323)
      | k1_xboole_0 != A_322
      | k1_xboole_0 != A_322 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4171,c_2071])).

tff(c_4455,plain,(
    ! [A_324,C_325] :
      ( k4_xboole_0(A_324,C_325) = A_324
      | k1_xboole_0 != A_324 ) ),
    inference(resolution,[status(thm)],[c_4419,c_22])).

tff(c_4749,plain,(
    ! [A_335,A_336,C_337] :
      ( r1_xboole_0(A_335,A_336)
      | ~ r1_tarski(A_335,C_337)
      | k1_xboole_0 != A_336 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4455,c_26])).

tff(c_4803,plain,(
    ! [B_339,A_340] :
      ( r1_xboole_0(B_339,A_340)
      | k1_xboole_0 != A_340 ) ),
    inference(resolution,[status(thm)],[c_6,c_4749])).

tff(c_4994,plain,(
    ! [B_339] : k4_xboole_0(B_339,k1_xboole_0) = B_339 ),
    inference(resolution,[status(thm)],[c_4803,c_22])).

tff(c_3828,plain,(
    ! [A_300,B_301] :
      ( m1_subset_1(k2_pre_topc(A_300,B_301),k1_zfmisc_1(u1_struct_0(A_300)))
      | ~ m1_subset_1(B_301,k1_zfmisc_1(u1_struct_0(A_300)))
      | ~ l1_pre_topc(A_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_28,plain,(
    ! [A_16,B_17,C_18] :
      ( k7_subset_1(A_16,B_17,C_18) = k4_xboole_0(B_17,C_18)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12301,plain,(
    ! [A_502,B_503,C_504] :
      ( k7_subset_1(u1_struct_0(A_502),k2_pre_topc(A_502,B_503),C_504) = k4_xboole_0(k2_pre_topc(A_502,B_503),C_504)
      | ~ m1_subset_1(B_503,k1_zfmisc_1(u1_struct_0(A_502)))
      | ~ l1_pre_topc(A_502) ) ),
    inference(resolution,[status(thm)],[c_3828,c_28])).

tff(c_12308,plain,(
    ! [C_504] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_504) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_504)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_52,c_12301])).

tff(c_12843,plain,(
    ! [C_509] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_509) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_509) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_12308])).

tff(c_30,plain,(
    ! [A_19] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_73,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,B_49)
      | ~ m1_subset_1(A_48,k1_zfmisc_1(B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_81,plain,(
    ! [A_19] : r1_tarski(k1_xboole_0,A_19) ),
    inference(resolution,[status(thm)],[c_30,c_73])).

tff(c_2238,plain,(
    ! [B_207,A_208] :
      ( B_207 = A_208
      | ~ r1_tarski(B_207,A_208)
      | ~ r1_tarski(A_208,B_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2254,plain,(
    ! [A_209] :
      ( k1_xboole_0 = A_209
      | ~ r1_tarski(A_209,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_81,c_2238])).

tff(c_2269,plain,(
    ! [B_6] : k4_xboole_0(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_2254])).

tff(c_56,plain,
    ( ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_83,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_1304,plain,(
    ! [B_153,A_154] :
      ( v2_tops_1(B_153,A_154)
      | k1_tops_1(A_154,B_153) != k1_xboole_0
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_pre_topc(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1314,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_1304])).

tff(c_1323,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1314])).

tff(c_1324,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_1323])).

tff(c_887,plain,(
    ! [A_130,B_131] :
      ( r1_tarski(k1_tops_1(A_130,B_131),B_131)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_892,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_887])).

tff(c_899,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_892])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_907,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_899,c_8])).

tff(c_20,plain,(
    ! [A_8,B_9,C_10] :
      ( r1_xboole_0(A_8,B_9)
      | ~ r1_xboole_0(A_8,k2_xboole_0(B_9,C_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1054,plain,(
    ! [A_139] :
      ( r1_xboole_0(A_139,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_xboole_0(A_139,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_907,c_20])).

tff(c_1063,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1054,c_14])).

tff(c_1847,plain,(
    ~ r1_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_1324,c_1063])).

tff(c_1938,plain,(
    ! [A_172,B_173] :
      ( r1_xboole_0(k1_tops_1(A_172,B_173),k2_tops_1(A_172,B_173))
      | ~ m1_subset_1(B_173,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ l1_pre_topc(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_62,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_150,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_62])).

tff(c_154,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_150,c_8])).

tff(c_383,plain,(
    ! [A_8] :
      ( r1_xboole_0(A_8,'#skF_2')
      | ~ r1_xboole_0(A_8,k2_tops_1('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_20])).

tff(c_1942,plain,
    ( r1_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1938,c_383])).

tff(c_1951,plain,(
    r1_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1942])).

tff(c_1953,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1847,c_1951])).

tff(c_1955,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_3747,plain,(
    ! [A_297,B_298] :
      ( k1_tops_1(A_297,B_298) = k1_xboole_0
      | ~ v2_tops_1(B_298,A_297)
      | ~ m1_subset_1(B_298,k1_zfmisc_1(u1_struct_0(A_297)))
      | ~ l1_pre_topc(A_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_3757,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_3747])).

tff(c_3766,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1955,c_3757])).

tff(c_2705,plain,(
    ! [A_253,B_254] :
      ( r1_tarski(k1_tops_1(A_253,B_254),B_254)
      | ~ m1_subset_1(B_254,k1_zfmisc_1(u1_struct_0(A_253)))
      | ~ l1_pre_topc(A_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2710,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_2705])).

tff(c_2717,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2710])).

tff(c_2725,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2717,c_8])).

tff(c_2872,plain,(
    ! [A_262] :
      ( r1_xboole_0(A_262,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_xboole_0(A_262,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2725,c_20])).

tff(c_2881,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_2872,c_14])).

tff(c_3612,plain,(
    ~ r1_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2881])).

tff(c_3620,plain,(
    k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') != k1_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_3612])).

tff(c_3769,plain,(
    k4_xboole_0(k1_xboole_0,'#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3766,c_3766,c_3620])).

tff(c_3780,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2269,c_3769])).

tff(c_3781,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2881])).

tff(c_4649,plain,(
    ! [A_329,B_330] :
      ( k7_subset_1(u1_struct_0(A_329),k2_pre_topc(A_329,B_330),k1_tops_1(A_329,B_330)) = k2_tops_1(A_329,B_330)
      | ~ m1_subset_1(B_330,k1_zfmisc_1(u1_struct_0(A_329)))
      | ~ l1_pre_topc(A_329) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_4658,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k1_xboole_0) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3781,c_4649])).

tff(c_4665,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k1_xboole_0) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_4658])).

tff(c_12849,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_xboole_0) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12843,c_4665])).

tff(c_12865,plain,(
    k2_tops_1('#skF_1','#skF_2') = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4994,c_12849])).

tff(c_1954,plain,(
    ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_12873,plain,(
    ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12865,c_1954])).

tff(c_12876,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2828,c_12873])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:44:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.66/2.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.66/2.90  
% 8.66/2.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.66/2.91  %$ v2_tops_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 8.66/2.91  
% 8.66/2.91  %Foreground sorts:
% 8.66/2.91  
% 8.66/2.91  
% 8.66/2.91  %Background operators:
% 8.66/2.91  
% 8.66/2.91  
% 8.66/2.91  %Foreground operators:
% 8.66/2.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.66/2.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.66/2.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.66/2.91  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 8.66/2.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.66/2.91  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 8.66/2.91  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.66/2.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.66/2.91  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 8.66/2.91  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.66/2.91  tff('#skF_2', type, '#skF_2': $i).
% 8.66/2.91  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 8.66/2.91  tff('#skF_1', type, '#skF_1': $i).
% 8.66/2.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.66/2.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.66/2.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.66/2.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.66/2.91  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.66/2.91  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.66/2.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.66/2.91  
% 8.66/2.93  tff(f_142, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tops_1)).
% 8.66/2.93  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 8.66/2.93  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.66/2.93  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.66/2.93  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 8.66/2.93  tff(f_73, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 8.66/2.93  tff(f_49, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 8.66/2.93  tff(f_69, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 8.66/2.93  tff(f_65, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 8.66/2.93  tff(f_95, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 8.66/2.93  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 8.66/2.93  tff(f_79, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 8.66/2.93  tff(f_83, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.66/2.93  tff(f_132, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 8.66/2.93  tff(f_116, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 8.66/2.93  tff(f_123, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_xboole_0(k1_tops_1(A, B), k2_tops_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_tops_1)).
% 8.66/2.93  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 8.66/2.93  tff(c_54, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_142])).
% 8.66/2.93  tff(c_52, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 8.66/2.93  tff(c_2816, plain, (![B_258, A_259]: (r1_tarski(B_258, k2_pre_topc(A_259, B_258)) | ~m1_subset_1(B_258, k1_zfmisc_1(u1_struct_0(A_259))) | ~l1_pre_topc(A_259))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.66/2.93  tff(c_2821, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_2816])).
% 8.66/2.93  tff(c_2828, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2821])).
% 8.66/2.93  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.66/2.93  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.66/2.93  tff(c_1992, plain, (![A_181, B_182]: (k2_xboole_0(A_181, B_182)=B_182 | ~r1_tarski(A_181, B_182))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.66/2.93  tff(c_2007, plain, (![A_5, B_6]: (k2_xboole_0(k4_xboole_0(A_5, B_6), A_5)=A_5)), inference(resolution, [status(thm)], [c_10, c_1992])).
% 8.66/2.93  tff(c_2109, plain, (![A_198, C_199, B_200]: (r1_xboole_0(A_198, k4_xboole_0(C_199, B_200)) | ~r1_tarski(A_198, B_200))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.66/2.93  tff(c_14, plain, (![A_7]: (~r1_xboole_0(A_7, A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.66/2.93  tff(c_2460, plain, (![C_230, B_231]: (k4_xboole_0(C_230, B_231)=k1_xboole_0 | ~r1_tarski(k4_xboole_0(C_230, B_231), B_231))), inference(resolution, [status(thm)], [c_2109, c_14])).
% 8.66/2.93  tff(c_2476, plain, (![A_232]: (k4_xboole_0(A_232, A_232)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_2460])).
% 8.66/2.93  tff(c_24, plain, (![A_11, B_12]: (r1_xboole_0(A_11, B_12) | k4_xboole_0(A_11, B_12)!=A_11)), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.66/2.93  tff(c_2072, plain, (![A_190, B_191, C_192]: (r1_xboole_0(A_190, B_191) | ~r1_xboole_0(A_190, k2_xboole_0(B_191, C_192)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.66/2.93  tff(c_2089, plain, (![A_11, B_191, C_192]: (r1_xboole_0(A_11, B_191) | k4_xboole_0(A_11, k2_xboole_0(B_191, C_192))!=A_11)), inference(resolution, [status(thm)], [c_24, c_2072])).
% 8.66/2.93  tff(c_3195, plain, (![B_278, C_279]: (r1_xboole_0(k2_xboole_0(B_278, C_279), B_278) | k2_xboole_0(B_278, C_279)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2476, c_2089])).
% 8.66/2.93  tff(c_3229, plain, (![A_5, B_6]: (r1_xboole_0(A_5, k4_xboole_0(A_5, B_6)) | k2_xboole_0(k4_xboole_0(A_5, B_6), A_5)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2007, c_3195])).
% 8.66/2.93  tff(c_3291, plain, (![A_283, B_284]: (r1_xboole_0(A_283, k4_xboole_0(A_283, B_284)) | k1_xboole_0!=A_283)), inference(demodulation, [status(thm), theory('equality')], [c_2007, c_3229])).
% 8.66/2.93  tff(c_22, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=A_11 | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.66/2.93  tff(c_3319, plain, (![A_285, B_286]: (k4_xboole_0(A_285, k4_xboole_0(A_285, B_286))=A_285 | k1_xboole_0!=A_285)), inference(resolution, [status(thm)], [c_3291, c_22])).
% 8.66/2.93  tff(c_26, plain, (![A_13, C_15, B_14]: (r1_xboole_0(A_13, k4_xboole_0(C_15, B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.66/2.93  tff(c_4041, plain, (![A_311, A_312, B_313]: (r1_xboole_0(A_311, A_312) | ~r1_tarski(A_311, k4_xboole_0(A_312, B_313)) | k1_xboole_0!=A_312)), inference(superposition, [status(thm), theory('equality')], [c_3319, c_26])).
% 8.66/2.93  tff(c_4088, plain, (![A_314, B_315]: (r1_xboole_0(k4_xboole_0(A_314, B_315), A_314) | k1_xboole_0!=A_314)), inference(resolution, [status(thm)], [c_6, c_4041])).
% 8.66/2.93  tff(c_2381, plain, (![A_222, A_223, B_224]: (r1_xboole_0(A_222, k4_xboole_0(A_223, B_224)) | ~r1_xboole_0(A_222, A_223))), inference(superposition, [status(thm), theory('equality')], [c_2007, c_2072])).
% 8.66/2.93  tff(c_2396, plain, (![A_223, B_224]: (k4_xboole_0(A_223, B_224)=k1_xboole_0 | ~r1_xboole_0(k4_xboole_0(A_223, B_224), A_223))), inference(resolution, [status(thm)], [c_2381, c_14])).
% 8.66/2.93  tff(c_4171, plain, (![A_318, B_319]: (k4_xboole_0(A_318, B_319)=k1_xboole_0 | k1_xboole_0!=A_318)), inference(resolution, [status(thm)], [c_4088, c_2396])).
% 8.66/2.93  tff(c_2054, plain, (![A_187, C_188, B_189]: (r1_xboole_0(A_187, C_188) | ~r1_xboole_0(A_187, k2_xboole_0(B_189, C_188)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.66/2.93  tff(c_2071, plain, (![A_11, C_188, B_189]: (r1_xboole_0(A_11, C_188) | k4_xboole_0(A_11, k2_xboole_0(B_189, C_188))!=A_11)), inference(resolution, [status(thm)], [c_24, c_2054])).
% 8.66/2.93  tff(c_4419, plain, (![A_322, C_323]: (r1_xboole_0(A_322, C_323) | k1_xboole_0!=A_322 | k1_xboole_0!=A_322)), inference(superposition, [status(thm), theory('equality')], [c_4171, c_2071])).
% 8.66/2.93  tff(c_4455, plain, (![A_324, C_325]: (k4_xboole_0(A_324, C_325)=A_324 | k1_xboole_0!=A_324)), inference(resolution, [status(thm)], [c_4419, c_22])).
% 8.66/2.93  tff(c_4749, plain, (![A_335, A_336, C_337]: (r1_xboole_0(A_335, A_336) | ~r1_tarski(A_335, C_337) | k1_xboole_0!=A_336)), inference(superposition, [status(thm), theory('equality')], [c_4455, c_26])).
% 8.66/2.93  tff(c_4803, plain, (![B_339, A_340]: (r1_xboole_0(B_339, A_340) | k1_xboole_0!=A_340)), inference(resolution, [status(thm)], [c_6, c_4749])).
% 8.66/2.93  tff(c_4994, plain, (![B_339]: (k4_xboole_0(B_339, k1_xboole_0)=B_339)), inference(resolution, [status(thm)], [c_4803, c_22])).
% 8.66/2.93  tff(c_3828, plain, (![A_300, B_301]: (m1_subset_1(k2_pre_topc(A_300, B_301), k1_zfmisc_1(u1_struct_0(A_300))) | ~m1_subset_1(B_301, k1_zfmisc_1(u1_struct_0(A_300))) | ~l1_pre_topc(A_300))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.66/2.93  tff(c_28, plain, (![A_16, B_17, C_18]: (k7_subset_1(A_16, B_17, C_18)=k4_xboole_0(B_17, C_18) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.66/2.93  tff(c_12301, plain, (![A_502, B_503, C_504]: (k7_subset_1(u1_struct_0(A_502), k2_pre_topc(A_502, B_503), C_504)=k4_xboole_0(k2_pre_topc(A_502, B_503), C_504) | ~m1_subset_1(B_503, k1_zfmisc_1(u1_struct_0(A_502))) | ~l1_pre_topc(A_502))), inference(resolution, [status(thm)], [c_3828, c_28])).
% 8.66/2.93  tff(c_12308, plain, (![C_504]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_504)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_504) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_52, c_12301])).
% 8.66/2.93  tff(c_12843, plain, (![C_509]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_509)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_509))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_12308])).
% 8.66/2.93  tff(c_30, plain, (![A_19]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.66/2.93  tff(c_73, plain, (![A_48, B_49]: (r1_tarski(A_48, B_49) | ~m1_subset_1(A_48, k1_zfmisc_1(B_49)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.66/2.93  tff(c_81, plain, (![A_19]: (r1_tarski(k1_xboole_0, A_19))), inference(resolution, [status(thm)], [c_30, c_73])).
% 8.66/2.93  tff(c_2238, plain, (![B_207, A_208]: (B_207=A_208 | ~r1_tarski(B_207, A_208) | ~r1_tarski(A_208, B_207))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.66/2.93  tff(c_2254, plain, (![A_209]: (k1_xboole_0=A_209 | ~r1_tarski(A_209, k1_xboole_0))), inference(resolution, [status(thm)], [c_81, c_2238])).
% 8.66/2.93  tff(c_2269, plain, (![B_6]: (k4_xboole_0(k1_xboole_0, B_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_2254])).
% 8.66/2.93  tff(c_56, plain, (~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_142])).
% 8.66/2.93  tff(c_83, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_56])).
% 8.66/2.93  tff(c_1304, plain, (![B_153, A_154]: (v2_tops_1(B_153, A_154) | k1_tops_1(A_154, B_153)!=k1_xboole_0 | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_154))) | ~l1_pre_topc(A_154))), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.66/2.93  tff(c_1314, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_1304])).
% 8.66/2.93  tff(c_1323, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1314])).
% 8.66/2.93  tff(c_1324, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_83, c_1323])).
% 8.66/2.93  tff(c_887, plain, (![A_130, B_131]: (r1_tarski(k1_tops_1(A_130, B_131), B_131) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.66/2.93  tff(c_892, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_887])).
% 8.66/2.93  tff(c_899, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_892])).
% 8.66/2.93  tff(c_8, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.66/2.93  tff(c_907, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_899, c_8])).
% 8.66/2.93  tff(c_20, plain, (![A_8, B_9, C_10]: (r1_xboole_0(A_8, B_9) | ~r1_xboole_0(A_8, k2_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.66/2.93  tff(c_1054, plain, (![A_139]: (r1_xboole_0(A_139, k1_tops_1('#skF_1', '#skF_2')) | ~r1_xboole_0(A_139, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_907, c_20])).
% 8.66/2.93  tff(c_1063, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_1054, c_14])).
% 8.66/2.93  tff(c_1847, plain, (~r1_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_1324, c_1063])).
% 8.66/2.93  tff(c_1938, plain, (![A_172, B_173]: (r1_xboole_0(k1_tops_1(A_172, B_173), k2_tops_1(A_172, B_173)) | ~m1_subset_1(B_173, k1_zfmisc_1(u1_struct_0(A_172))) | ~l1_pre_topc(A_172))), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.66/2.93  tff(c_62, plain, (v2_tops_1('#skF_2', '#skF_1') | r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 8.66/2.93  tff(c_150, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_83, c_62])).
% 8.66/2.93  tff(c_154, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_150, c_8])).
% 8.66/2.93  tff(c_383, plain, (![A_8]: (r1_xboole_0(A_8, '#skF_2') | ~r1_xboole_0(A_8, k2_tops_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_154, c_20])).
% 8.66/2.93  tff(c_1942, plain, (r1_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1938, c_383])).
% 8.66/2.93  tff(c_1951, plain, (r1_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1942])).
% 8.66/2.93  tff(c_1953, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1847, c_1951])).
% 8.66/2.93  tff(c_1955, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_56])).
% 8.66/2.93  tff(c_3747, plain, (![A_297, B_298]: (k1_tops_1(A_297, B_298)=k1_xboole_0 | ~v2_tops_1(B_298, A_297) | ~m1_subset_1(B_298, k1_zfmisc_1(u1_struct_0(A_297))) | ~l1_pre_topc(A_297))), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.66/2.93  tff(c_3757, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_3747])).
% 8.66/2.93  tff(c_3766, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1955, c_3757])).
% 8.66/2.93  tff(c_2705, plain, (![A_253, B_254]: (r1_tarski(k1_tops_1(A_253, B_254), B_254) | ~m1_subset_1(B_254, k1_zfmisc_1(u1_struct_0(A_253))) | ~l1_pre_topc(A_253))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.66/2.93  tff(c_2710, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_2705])).
% 8.66/2.93  tff(c_2717, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2710])).
% 8.66/2.93  tff(c_2725, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_2717, c_8])).
% 8.66/2.93  tff(c_2872, plain, (![A_262]: (r1_xboole_0(A_262, k1_tops_1('#skF_1', '#skF_2')) | ~r1_xboole_0(A_262, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2725, c_20])).
% 8.66/2.93  tff(c_2881, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_2872, c_14])).
% 8.66/2.93  tff(c_3612, plain, (~r1_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_2881])).
% 8.66/2.93  tff(c_3620, plain, (k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')!=k1_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_3612])).
% 8.66/2.93  tff(c_3769, plain, (k4_xboole_0(k1_xboole_0, '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3766, c_3766, c_3620])).
% 8.66/2.93  tff(c_3780, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2269, c_3769])).
% 8.66/2.93  tff(c_3781, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2881])).
% 8.66/2.93  tff(c_4649, plain, (![A_329, B_330]: (k7_subset_1(u1_struct_0(A_329), k2_pre_topc(A_329, B_330), k1_tops_1(A_329, B_330))=k2_tops_1(A_329, B_330) | ~m1_subset_1(B_330, k1_zfmisc_1(u1_struct_0(A_329))) | ~l1_pre_topc(A_329))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.66/2.93  tff(c_4658, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3781, c_4649])).
% 8.66/2.93  tff(c_4665, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_4658])).
% 8.66/2.93  tff(c_12849, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12843, c_4665])).
% 8.66/2.93  tff(c_12865, plain, (k2_tops_1('#skF_1', '#skF_2')=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4994, c_12849])).
% 8.66/2.93  tff(c_1954, plain, (~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_56])).
% 8.66/2.93  tff(c_12873, plain, (~r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12865, c_1954])).
% 8.66/2.93  tff(c_12876, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2828, c_12873])).
% 8.66/2.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.66/2.93  
% 8.66/2.93  Inference rules
% 8.66/2.93  ----------------------
% 8.66/2.93  #Ref     : 0
% 8.66/2.93  #Sup     : 3279
% 8.66/2.93  #Fact    : 0
% 8.66/2.93  #Define  : 0
% 8.66/2.93  #Split   : 25
% 8.66/2.93  #Chain   : 0
% 8.66/2.93  #Close   : 0
% 8.66/2.93  
% 8.66/2.93  Ordering : KBO
% 8.66/2.93  
% 8.66/2.93  Simplification rules
% 8.66/2.93  ----------------------
% 8.66/2.93  #Subsume      : 1604
% 8.66/2.93  #Demod        : 954
% 8.66/2.93  #Tautology    : 1086
% 8.66/2.93  #SimpNegUnit  : 70
% 8.66/2.93  #BackRed      : 50
% 8.66/2.93  
% 8.66/2.93  #Partial instantiations: 0
% 8.66/2.93  #Strategies tried      : 1
% 8.66/2.93  
% 8.66/2.93  Timing (in seconds)
% 8.66/2.93  ----------------------
% 8.66/2.93  Preprocessing        : 0.35
% 8.66/2.93  Parsing              : 0.19
% 8.66/2.93  CNF conversion       : 0.02
% 8.66/2.93  Main loop            : 1.79
% 8.66/2.93  Inferencing          : 0.60
% 8.66/2.93  Reduction            : 0.64
% 8.66/2.93  Demodulation         : 0.46
% 8.66/2.93  BG Simplification    : 0.06
% 8.66/2.93  Subsumption          : 0.39
% 8.66/2.93  Abstraction          : 0.09
% 8.66/2.93  MUC search           : 0.00
% 8.66/2.93  Cooper               : 0.00
% 8.66/2.93  Total                : 2.20
% 8.66/2.93  Index Insertion      : 0.00
% 8.66/2.93  Index Deletion       : 0.00
% 8.66/2.93  Index Matching       : 0.00
% 8.66/2.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
