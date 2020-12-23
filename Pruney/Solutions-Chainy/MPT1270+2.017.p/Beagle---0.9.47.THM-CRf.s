%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:57 EST 2020

% Result     : Theorem 5.22s
% Output     : CNFRefutation 5.22s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 162 expanded)
%              Number of leaves         :   31 (  66 expanded)
%              Depth                    :   11
%              Number of atoms          :  160 ( 312 expanded)
%              Number of equality atoms :   54 (  77 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_xboole_0(k1_tops_1(A,B),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_tops_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2388,plain,(
    ! [B_222,A_223] :
      ( r1_tarski(B_222,k2_pre_topc(A_223,B_222))
      | ~ m1_subset_1(B_222,k1_zfmisc_1(u1_struct_0(A_223)))
      | ~ l1_pre_topc(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2390,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_2388])).

tff(c_2393,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2390])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2406,plain,(
    k4_xboole_0('#skF_2',k2_pre_topc('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2393,c_6])).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_60,plain,(
    ! [A_41,B_42] :
      ( r1_xboole_0(A_41,B_42)
      | k4_xboole_0(A_41,B_42) != A_41 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_68,plain,(
    ! [B_43,A_44] :
      ( r1_xboole_0(B_43,A_44)
      | k4_xboole_0(A_44,B_43) != A_44 ) ),
    inference(resolution,[status(thm)],[c_60,c_2])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = A_9
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2207,plain,(
    ! [B_193,A_194] :
      ( k4_xboole_0(B_193,A_194) = B_193
      | k4_xboole_0(A_194,B_193) != A_194 ) ),
    inference(resolution,[status(thm)],[c_68,c_12])).

tff(c_2210,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2207])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( r1_xboole_0(A_9,B_10)
      | k4_xboole_0(A_9,B_10) != A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2200,plain,(
    ! [A_190,C_191,B_192] :
      ( r1_xboole_0(A_190,C_191)
      | ~ r1_xboole_0(B_192,C_191)
      | ~ r1_tarski(A_190,B_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2232,plain,(
    ! [A_196,B_197,A_198] :
      ( r1_xboole_0(A_196,B_197)
      | ~ r1_tarski(A_196,A_198)
      | k4_xboole_0(A_198,B_197) != A_198 ) ),
    inference(resolution,[status(thm)],[c_14,c_2200])).

tff(c_2253,plain,(
    ! [A_206,B_207,B_208] :
      ( r1_xboole_0(A_206,B_207)
      | k4_xboole_0(B_208,B_207) != B_208
      | k4_xboole_0(A_206,B_208) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_2232])).

tff(c_2255,plain,(
    ! [A_206,A_5] :
      ( r1_xboole_0(A_206,A_5)
      | k4_xboole_0(A_206,k1_xboole_0) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2210,c_2253])).

tff(c_2262,plain,(
    ! [A_209,A_210] :
      ( r1_xboole_0(A_209,A_210)
      | k1_xboole_0 != A_209 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2255])).

tff(c_2311,plain,(
    ! [A_215,A_216] :
      ( k4_xboole_0(A_215,A_216) = A_215
      | k1_xboole_0 != A_215 ) ),
    inference(resolution,[status(thm)],[c_2262,c_12])).

tff(c_74,plain,(
    ! [B_43,A_44] :
      ( k4_xboole_0(B_43,A_44) = B_43
      | k4_xboole_0(A_44,B_43) != A_44 ) ),
    inference(resolution,[status(thm)],[c_68,c_12])).

tff(c_2345,plain,(
    ! [A_216] : k4_xboole_0(A_216,k1_xboole_0) = A_216 ),
    inference(superposition,[status(thm),theory(equality)],[c_2311,c_74])).

tff(c_2944,plain,(
    ! [A_266,B_267] :
      ( m1_subset_1(k2_pre_topc(A_266,B_267),k1_zfmisc_1(u1_struct_0(A_266)))
      | ~ m1_subset_1(B_267,k1_zfmisc_1(u1_struct_0(A_266)))
      | ~ l1_pre_topc(A_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] :
      ( k7_subset_1(A_11,B_12,C_13) = k4_xboole_0(B_12,C_13)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3445,plain,(
    ! [A_332,B_333,C_334] :
      ( k7_subset_1(u1_struct_0(A_332),k2_pre_topc(A_332,B_333),C_334) = k4_xboole_0(k2_pre_topc(A_332,B_333),C_334)
      | ~ m1_subset_1(B_333,k1_zfmisc_1(u1_struct_0(A_332)))
      | ~ l1_pre_topc(A_332) ) ),
    inference(resolution,[status(thm)],[c_2944,c_16])).

tff(c_3449,plain,(
    ! [C_334] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_334) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_334)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_3445])).

tff(c_3454,plain,(
    ! [C_335] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_335) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_335) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3449])).

tff(c_36,plain,
    ( ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_76,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_519,plain,(
    ! [B_88,A_89] :
      ( v2_tops_1(B_88,A_89)
      | k1_tops_1(A_89,B_88) != k1_xboole_0
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_522,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_519])).

tff(c_525,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_522])).

tff(c_526,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_525])).

tff(c_316,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(k1_tops_1(A_70,B_71),B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_318,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_316])).

tff(c_321,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_318])).

tff(c_331,plain,(
    k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_321,c_6])).

tff(c_460,plain,(
    ! [A_82,B_83] :
      ( r1_xboole_0(k1_tops_1(A_82,B_83),k2_tops_1(A_82,B_83))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2077,plain,(
    ! [A_188,B_189] :
      ( k4_xboole_0(k1_tops_1(A_188,B_189),k2_tops_1(A_188,B_189)) = k1_tops_1(A_188,B_189)
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ l1_pre_topc(A_188) ) ),
    inference(resolution,[status(thm)],[c_460,c_12])).

tff(c_2081,plain,
    ( k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_2077])).

tff(c_2085,plain,(
    k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2081])).

tff(c_42,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_77,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_42])).

tff(c_67,plain,(
    ! [B_42,A_41] :
      ( r1_xboole_0(B_42,A_41)
      | k4_xboole_0(A_41,B_42) != A_41 ) ),
    inference(resolution,[status(thm)],[c_60,c_2])).

tff(c_113,plain,(
    ! [A_48,C_49,B_50] :
      ( r1_xboole_0(A_48,C_49)
      | ~ r1_xboole_0(B_50,C_49)
      | ~ r1_tarski(A_48,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_127,plain,(
    ! [A_54,A_55,B_56] :
      ( r1_xboole_0(A_54,A_55)
      | ~ r1_tarski(A_54,B_56)
      | k4_xboole_0(A_55,B_56) != A_55 ) ),
    inference(resolution,[status(thm)],[c_67,c_113])).

tff(c_132,plain,(
    ! [A_55] :
      ( r1_xboole_0('#skF_2',A_55)
      | k4_xboole_0(A_55,k2_tops_1('#skF_1','#skF_2')) != A_55 ) ),
    inference(resolution,[status(thm)],[c_77,c_127])).

tff(c_2117,plain,(
    r1_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2085,c_132])).

tff(c_2129,plain,(
    r1_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_2117,c_2])).

tff(c_2184,plain,(
    k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_2129,c_12])).

tff(c_2189,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_2184])).

tff(c_2191,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_526,c_2189])).

tff(c_2193,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_2829,plain,(
    ! [A_252,B_253] :
      ( k1_tops_1(A_252,B_253) = k1_xboole_0
      | ~ v2_tops_1(B_253,A_252)
      | ~ m1_subset_1(B_253,k1_zfmisc_1(u1_struct_0(A_252)))
      | ~ l1_pre_topc(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2832,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_2829])).

tff(c_2835,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2193,c_2832])).

tff(c_2992,plain,(
    ! [A_275,B_276] :
      ( k7_subset_1(u1_struct_0(A_275),k2_pre_topc(A_275,B_276),k1_tops_1(A_275,B_276)) = k2_tops_1(A_275,B_276)
      | ~ m1_subset_1(B_276,k1_zfmisc_1(u1_struct_0(A_275)))
      | ~ l1_pre_topc(A_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3001,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k1_xboole_0) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2835,c_2992])).

tff(c_3005,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k1_xboole_0) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_3001])).

tff(c_3460,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_xboole_0) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3454,c_3005])).

tff(c_3476,plain,(
    k2_tops_1('#skF_1','#skF_2') = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2345,c_3460])).

tff(c_2192,plain,(
    ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_2197,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_2192])).

tff(c_3492,plain,(
    k4_xboole_0('#skF_2',k2_pre_topc('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3476,c_2197])).

tff(c_3496,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2406,c_3492])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:26:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.22/2.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.22/2.03  
% 5.22/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.22/2.04  %$ v2_tops_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.22/2.04  
% 5.22/2.04  %Foreground sorts:
% 5.22/2.04  
% 5.22/2.04  
% 5.22/2.04  %Background operators:
% 5.22/2.04  
% 5.22/2.04  
% 5.22/2.04  %Foreground operators:
% 5.22/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.22/2.04  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.22/2.04  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.22/2.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.22/2.04  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 5.22/2.04  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.22/2.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.22/2.04  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.22/2.04  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.22/2.04  tff('#skF_2', type, '#skF_2': $i).
% 5.22/2.04  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.22/2.04  tff('#skF_1', type, '#skF_1': $i).
% 5.22/2.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.22/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.22/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.22/2.04  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.22/2.04  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.22/2.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.22/2.04  
% 5.22/2.05  tff(f_102, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tops_1)).
% 5.22/2.05  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 5.22/2.05  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.22/2.05  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 5.22/2.05  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 5.22/2.05  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 5.22/2.05  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 5.22/2.05  tff(f_55, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 5.22/2.05  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.22/2.05  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 5.22/2.05  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 5.22/2.05  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_xboole_0(k1_tops_1(A, B), k2_tops_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_tops_1)).
% 5.22/2.05  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 5.22/2.05  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.22/2.05  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.22/2.05  tff(c_2388, plain, (![B_222, A_223]: (r1_tarski(B_222, k2_pre_topc(A_223, B_222)) | ~m1_subset_1(B_222, k1_zfmisc_1(u1_struct_0(A_223))) | ~l1_pre_topc(A_223))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.22/2.05  tff(c_2390, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_2388])).
% 5.22/2.05  tff(c_2393, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2390])).
% 5.22/2.05  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.22/2.05  tff(c_2406, plain, (k4_xboole_0('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_2393, c_6])).
% 5.22/2.05  tff(c_8, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.22/2.05  tff(c_60, plain, (![A_41, B_42]: (r1_xboole_0(A_41, B_42) | k4_xboole_0(A_41, B_42)!=A_41)), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.22/2.05  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.22/2.05  tff(c_68, plain, (![B_43, A_44]: (r1_xboole_0(B_43, A_44) | k4_xboole_0(A_44, B_43)!=A_44)), inference(resolution, [status(thm)], [c_60, c_2])).
% 5.22/2.05  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=A_9 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.22/2.05  tff(c_2207, plain, (![B_193, A_194]: (k4_xboole_0(B_193, A_194)=B_193 | k4_xboole_0(A_194, B_193)!=A_194)), inference(resolution, [status(thm)], [c_68, c_12])).
% 5.22/2.05  tff(c_2210, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_2207])).
% 5.22/2.05  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.22/2.05  tff(c_14, plain, (![A_9, B_10]: (r1_xboole_0(A_9, B_10) | k4_xboole_0(A_9, B_10)!=A_9)), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.22/2.05  tff(c_2200, plain, (![A_190, C_191, B_192]: (r1_xboole_0(A_190, C_191) | ~r1_xboole_0(B_192, C_191) | ~r1_tarski(A_190, B_192))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.22/2.05  tff(c_2232, plain, (![A_196, B_197, A_198]: (r1_xboole_0(A_196, B_197) | ~r1_tarski(A_196, A_198) | k4_xboole_0(A_198, B_197)!=A_198)), inference(resolution, [status(thm)], [c_14, c_2200])).
% 5.22/2.05  tff(c_2253, plain, (![A_206, B_207, B_208]: (r1_xboole_0(A_206, B_207) | k4_xboole_0(B_208, B_207)!=B_208 | k4_xboole_0(A_206, B_208)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_2232])).
% 5.22/2.05  tff(c_2255, plain, (![A_206, A_5]: (r1_xboole_0(A_206, A_5) | k4_xboole_0(A_206, k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2210, c_2253])).
% 5.22/2.05  tff(c_2262, plain, (![A_209, A_210]: (r1_xboole_0(A_209, A_210) | k1_xboole_0!=A_209)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2255])).
% 5.22/2.05  tff(c_2311, plain, (![A_215, A_216]: (k4_xboole_0(A_215, A_216)=A_215 | k1_xboole_0!=A_215)), inference(resolution, [status(thm)], [c_2262, c_12])).
% 5.22/2.05  tff(c_74, plain, (![B_43, A_44]: (k4_xboole_0(B_43, A_44)=B_43 | k4_xboole_0(A_44, B_43)!=A_44)), inference(resolution, [status(thm)], [c_68, c_12])).
% 5.22/2.05  tff(c_2345, plain, (![A_216]: (k4_xboole_0(A_216, k1_xboole_0)=A_216)), inference(superposition, [status(thm), theory('equality')], [c_2311, c_74])).
% 5.22/2.05  tff(c_2944, plain, (![A_266, B_267]: (m1_subset_1(k2_pre_topc(A_266, B_267), k1_zfmisc_1(u1_struct_0(A_266))) | ~m1_subset_1(B_267, k1_zfmisc_1(u1_struct_0(A_266))) | ~l1_pre_topc(A_266))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.22/2.05  tff(c_16, plain, (![A_11, B_12, C_13]: (k7_subset_1(A_11, B_12, C_13)=k4_xboole_0(B_12, C_13) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.22/2.05  tff(c_3445, plain, (![A_332, B_333, C_334]: (k7_subset_1(u1_struct_0(A_332), k2_pre_topc(A_332, B_333), C_334)=k4_xboole_0(k2_pre_topc(A_332, B_333), C_334) | ~m1_subset_1(B_333, k1_zfmisc_1(u1_struct_0(A_332))) | ~l1_pre_topc(A_332))), inference(resolution, [status(thm)], [c_2944, c_16])).
% 5.22/2.05  tff(c_3449, plain, (![C_334]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_334)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_334) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_3445])).
% 5.22/2.05  tff(c_3454, plain, (![C_335]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_335)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_335))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_3449])).
% 5.22/2.05  tff(c_36, plain, (~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.22/2.05  tff(c_76, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_36])).
% 5.22/2.05  tff(c_519, plain, (![B_88, A_89]: (v2_tops_1(B_88, A_89) | k1_tops_1(A_89, B_88)!=k1_xboole_0 | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.22/2.05  tff(c_522, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_519])).
% 5.22/2.05  tff(c_525, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_522])).
% 5.22/2.05  tff(c_526, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_76, c_525])).
% 5.22/2.05  tff(c_316, plain, (![A_70, B_71]: (r1_tarski(k1_tops_1(A_70, B_71), B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.22/2.05  tff(c_318, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_316])).
% 5.22/2.05  tff(c_321, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_318])).
% 5.22/2.05  tff(c_331, plain, (k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_321, c_6])).
% 5.22/2.05  tff(c_460, plain, (![A_82, B_83]: (r1_xboole_0(k1_tops_1(A_82, B_83), k2_tops_1(A_82, B_83)) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.22/2.05  tff(c_2077, plain, (![A_188, B_189]: (k4_xboole_0(k1_tops_1(A_188, B_189), k2_tops_1(A_188, B_189))=k1_tops_1(A_188, B_189) | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0(A_188))) | ~l1_pre_topc(A_188))), inference(resolution, [status(thm)], [c_460, c_12])).
% 5.22/2.05  tff(c_2081, plain, (k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_2077])).
% 5.22/2.05  tff(c_2085, plain, (k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2081])).
% 5.22/2.05  tff(c_42, plain, (v2_tops_1('#skF_2', '#skF_1') | r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.22/2.05  tff(c_77, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_76, c_42])).
% 5.22/2.05  tff(c_67, plain, (![B_42, A_41]: (r1_xboole_0(B_42, A_41) | k4_xboole_0(A_41, B_42)!=A_41)), inference(resolution, [status(thm)], [c_60, c_2])).
% 5.22/2.05  tff(c_113, plain, (![A_48, C_49, B_50]: (r1_xboole_0(A_48, C_49) | ~r1_xboole_0(B_50, C_49) | ~r1_tarski(A_48, B_50))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.22/2.05  tff(c_127, plain, (![A_54, A_55, B_56]: (r1_xboole_0(A_54, A_55) | ~r1_tarski(A_54, B_56) | k4_xboole_0(A_55, B_56)!=A_55)), inference(resolution, [status(thm)], [c_67, c_113])).
% 5.22/2.05  tff(c_132, plain, (![A_55]: (r1_xboole_0('#skF_2', A_55) | k4_xboole_0(A_55, k2_tops_1('#skF_1', '#skF_2'))!=A_55)), inference(resolution, [status(thm)], [c_77, c_127])).
% 5.22/2.05  tff(c_2117, plain, (r1_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2085, c_132])).
% 5.22/2.05  tff(c_2129, plain, (r1_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_2117, c_2])).
% 5.22/2.05  tff(c_2184, plain, (k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_2129, c_12])).
% 5.22/2.05  tff(c_2189, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_331, c_2184])).
% 5.22/2.05  tff(c_2191, plain, $false, inference(negUnitSimplification, [status(thm)], [c_526, c_2189])).
% 5.22/2.05  tff(c_2193, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_36])).
% 5.22/2.05  tff(c_2829, plain, (![A_252, B_253]: (k1_tops_1(A_252, B_253)=k1_xboole_0 | ~v2_tops_1(B_253, A_252) | ~m1_subset_1(B_253, k1_zfmisc_1(u1_struct_0(A_252))) | ~l1_pre_topc(A_252))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.22/2.05  tff(c_2832, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_2829])).
% 5.22/2.05  tff(c_2835, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2193, c_2832])).
% 5.22/2.05  tff(c_2992, plain, (![A_275, B_276]: (k7_subset_1(u1_struct_0(A_275), k2_pre_topc(A_275, B_276), k1_tops_1(A_275, B_276))=k2_tops_1(A_275, B_276) | ~m1_subset_1(B_276, k1_zfmisc_1(u1_struct_0(A_275))) | ~l1_pre_topc(A_275))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.22/2.05  tff(c_3001, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2835, c_2992])).
% 5.22/2.05  tff(c_3005, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_3001])).
% 5.22/2.05  tff(c_3460, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3454, c_3005])).
% 5.22/2.05  tff(c_3476, plain, (k2_tops_1('#skF_1', '#skF_2')=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2345, c_3460])).
% 5.22/2.05  tff(c_2192, plain, (~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_36])).
% 5.22/2.05  tff(c_2197, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_2192])).
% 5.22/2.05  tff(c_3492, plain, (k4_xboole_0('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3476, c_2197])).
% 5.22/2.05  tff(c_3496, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2406, c_3492])).
% 5.22/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.22/2.05  
% 5.22/2.05  Inference rules
% 5.22/2.05  ----------------------
% 5.22/2.05  #Ref     : 0
% 5.22/2.05  #Sup     : 864
% 5.22/2.05  #Fact    : 0
% 5.22/2.05  #Define  : 0
% 5.22/2.05  #Split   : 12
% 5.22/2.05  #Chain   : 0
% 5.22/2.05  #Close   : 0
% 5.22/2.05  
% 5.22/2.05  Ordering : KBO
% 5.22/2.05  
% 5.22/2.05  Simplification rules
% 5.22/2.05  ----------------------
% 5.22/2.05  #Subsume      : 390
% 5.22/2.05  #Demod        : 236
% 5.22/2.05  #Tautology    : 266
% 5.22/2.05  #SimpNegUnit  : 35
% 5.22/2.05  #BackRed      : 25
% 5.22/2.05  
% 5.22/2.05  #Partial instantiations: 0
% 5.22/2.05  #Strategies tried      : 1
% 5.22/2.05  
% 5.22/2.05  Timing (in seconds)
% 5.22/2.05  ----------------------
% 5.22/2.06  Preprocessing        : 0.35
% 5.22/2.06  Parsing              : 0.19
% 5.22/2.06  CNF conversion       : 0.02
% 5.22/2.06  Main loop            : 0.87
% 5.22/2.06  Inferencing          : 0.28
% 5.22/2.06  Reduction            : 0.25
% 5.22/2.06  Demodulation         : 0.15
% 5.22/2.06  BG Simplification    : 0.03
% 5.22/2.06  Subsumption          : 0.25
% 5.22/2.06  Abstraction          : 0.05
% 5.22/2.06  MUC search           : 0.00
% 5.22/2.06  Cooper               : 0.00
% 5.22/2.06  Total                : 1.26
% 5.22/2.06  Index Insertion      : 0.00
% 5.22/2.06  Index Deletion       : 0.00
% 5.22/2.06  Index Matching       : 0.00
% 5.22/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
