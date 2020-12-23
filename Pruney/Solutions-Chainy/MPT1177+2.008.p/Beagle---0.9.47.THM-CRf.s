%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:56 EST 2020

% Result     : Theorem 4.86s
% Output     : CNFRefutation 5.20s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 375 expanded)
%              Number of leaves         :   44 ( 155 expanded)
%              Depth                    :   10
%              Number of atoms          :  310 (1562 expanded)
%              Number of equality atoms :   33 (  71 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_mcart_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_35,axiom,(
    ! [A,B] : ~ r2_xboole_0(A,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

tff(f_270,negated_conjecture,(
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

tff(f_150,axiom,(
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

tff(f_169,axiom,(
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

tff(f_194,axiom,(
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

tff(f_68,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_217,axiom,(
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

tff(f_245,axiom,(
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

tff(c_84,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_82,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_80,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_78,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_76,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_74,plain,(
    m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_72,plain,(
    m2_orders_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_1272,plain,(
    ! [C_307,A_308,B_309] :
      ( m1_subset_1(C_307,k1_zfmisc_1(u1_struct_0(A_308)))
      | ~ m2_orders_2(C_307,A_308,B_309)
      | ~ m1_orders_1(B_309,k1_orders_1(u1_struct_0(A_308)))
      | ~ l1_orders_2(A_308)
      | ~ v5_orders_2(A_308)
      | ~ v4_orders_2(A_308)
      | ~ v3_orders_2(A_308)
      | v2_struct_0(A_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_1274,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_1272])).

tff(c_1277,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_76,c_74,c_1274])).

tff(c_1278,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1277])).

tff(c_161,plain,(
    ! [A_138,B_139] :
      ( r2_xboole_0(A_138,B_139)
      | B_139 = A_138
      | ~ r1_tarski(A_138,B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_86,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_5')
    | ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_115,plain,(
    ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_172,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_161,c_115])).

tff(c_178,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_92,plain,
    ( r2_xboole_0('#skF_4','#skF_5')
    | m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_116,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_92])).

tff(c_562,plain,(
    ! [C_207,B_208,A_209] :
      ( r1_tarski(C_207,B_208)
      | ~ m1_orders_2(C_207,A_209,B_208)
      | ~ m1_subset_1(B_208,k1_zfmisc_1(u1_struct_0(A_209)))
      | ~ l1_orders_2(A_209)
      | ~ v5_orders_2(A_209)
      | ~ v4_orders_2(A_209)
      | ~ v3_orders_2(A_209)
      | v2_struct_0(A_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_564,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_116,c_562])).

tff(c_567,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_76,c_564])).

tff(c_568,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_178,c_567])).

tff(c_70,plain,(
    m2_orders_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_720,plain,(
    ! [C_221,A_222,B_223] :
      ( m1_subset_1(C_221,k1_zfmisc_1(u1_struct_0(A_222)))
      | ~ m2_orders_2(C_221,A_222,B_223)
      | ~ m1_orders_1(B_223,k1_orders_1(u1_struct_0(A_222)))
      | ~ l1_orders_2(A_222)
      | ~ v5_orders_2(A_222)
      | ~ v4_orders_2(A_222)
      | ~ v3_orders_2(A_222)
      | v2_struct_0(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_724,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_720])).

tff(c_731,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_76,c_74,c_724])).

tff(c_733,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_568,c_731])).

tff(c_734,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_736,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_734,c_116])).

tff(c_1366,plain,(
    ! [C_324,A_325,B_326] :
      ( ~ m1_orders_2(C_324,A_325,B_326)
      | ~ m1_orders_2(B_326,A_325,C_324)
      | k1_xboole_0 = B_326
      | ~ m1_subset_1(C_324,k1_zfmisc_1(u1_struct_0(A_325)))
      | ~ m1_subset_1(B_326,k1_zfmisc_1(u1_struct_0(A_325)))
      | ~ l1_orders_2(A_325)
      | ~ v5_orders_2(A_325)
      | ~ v4_orders_2(A_325)
      | ~ v3_orders_2(A_325)
      | v2_struct_0(A_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_1368,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_736,c_1366])).

tff(c_1371,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_76,c_1278,c_736,c_1368])).

tff(c_1372,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1371])).

tff(c_34,plain,(
    ! [A_17] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_135,plain,(
    ! [A_133,B_134] :
      ( r1_tarski(A_133,B_134)
      | ~ m1_subset_1(A_133,k1_zfmisc_1(B_134)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_144,plain,(
    ! [A_17] : r1_tarski(k1_xboole_0,A_17) ),
    inference(resolution,[status(thm)],[c_34,c_135])).

tff(c_817,plain,(
    ! [A_237,B_238,C_239] :
      ( r1_tarski(k4_xboole_0(A_237,B_238),C_239)
      | ~ r1_tarski(A_237,k2_xboole_0(B_238,C_239)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_750,plain,(
    ! [B_226,A_227] :
      ( B_226 = A_227
      | ~ r1_tarski(B_226,A_227)
      | ~ r1_tarski(A_227,B_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_757,plain,(
    ! [A_17] :
      ( k1_xboole_0 = A_17
      | ~ r1_tarski(A_17,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_144,c_750])).

tff(c_1161,plain,(
    ! [A_298,B_299] :
      ( k4_xboole_0(A_298,B_299) = k1_xboole_0
      | ~ r1_tarski(A_298,k2_xboole_0(B_299,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_817,c_757])).

tff(c_1184,plain,(
    ! [B_299] : k4_xboole_0(k1_xboole_0,B_299) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_144,c_1161])).

tff(c_1378,plain,(
    ! [B_299] : k4_xboole_0('#skF_4',B_299) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1372,c_1372,c_1184])).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( r1_xboole_0(A_12,B_13)
      | k4_xboole_0(A_12,B_13) != A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1352,plain,(
    ! [C_316,D_317,A_318,B_319] :
      ( ~ r1_xboole_0(C_316,D_317)
      | ~ m2_orders_2(D_317,A_318,B_319)
      | ~ m2_orders_2(C_316,A_318,B_319)
      | ~ m1_orders_1(B_319,k1_orders_1(u1_struct_0(A_318)))
      | ~ l1_orders_2(A_318)
      | ~ v5_orders_2(A_318)
      | ~ v4_orders_2(A_318)
      | ~ v3_orders_2(A_318)
      | v2_struct_0(A_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_2391,plain,(
    ! [B_435,A_436,B_437,A_438] :
      ( ~ m2_orders_2(B_435,A_436,B_437)
      | ~ m2_orders_2(A_438,A_436,B_437)
      | ~ m1_orders_1(B_437,k1_orders_1(u1_struct_0(A_436)))
      | ~ l1_orders_2(A_436)
      | ~ v5_orders_2(A_436)
      | ~ v4_orders_2(A_436)
      | ~ v3_orders_2(A_436)
      | v2_struct_0(A_436)
      | k4_xboole_0(A_438,B_435) != A_438 ) ),
    inference(resolution,[status(thm)],[c_22,c_1352])).

tff(c_2393,plain,(
    ! [A_438] :
      ( ~ m2_orders_2(A_438,'#skF_2','#skF_3')
      | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k4_xboole_0(A_438,'#skF_4') != A_438 ) ),
    inference(resolution,[status(thm)],[c_72,c_2391])).

tff(c_2396,plain,(
    ! [A_438] :
      ( ~ m2_orders_2(A_438,'#skF_2','#skF_3')
      | v2_struct_0('#skF_2')
      | k4_xboole_0(A_438,'#skF_4') != A_438 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_76,c_74,c_2393])).

tff(c_2420,plain,(
    ! [A_441] :
      ( ~ m2_orders_2(A_441,'#skF_2','#skF_3')
      | k4_xboole_0(A_441,'#skF_4') != A_441 ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2396])).

tff(c_2423,plain,(
    k4_xboole_0('#skF_4','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_72,c_2420])).

tff(c_2427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1378,c_2423])).

tff(c_2429,plain,(
    r2_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2433,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_2429,c_6])).

tff(c_2484,plain,(
    ! [B_458,A_459] :
      ( B_458 = A_459
      | ~ r1_tarski(B_458,A_459)
      | ~ r1_tarski(A_459,B_458) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2494,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_2433,c_2484])).

tff(c_2513,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2494])).

tff(c_2966,plain,(
    ! [C_536,A_537,B_538] :
      ( m1_subset_1(C_536,k1_zfmisc_1(u1_struct_0(A_537)))
      | ~ m2_orders_2(C_536,A_537,B_538)
      | ~ m1_orders_1(B_538,k1_orders_1(u1_struct_0(A_537)))
      | ~ l1_orders_2(A_537)
      | ~ v5_orders_2(A_537)
      | ~ v4_orders_2(A_537)
      | ~ v3_orders_2(A_537)
      | v2_struct_0(A_537) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_2968,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_2966])).

tff(c_2973,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_76,c_74,c_2968])).

tff(c_2974,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2973])).

tff(c_14,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2428,plain,(
    ~ m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_3156,plain,(
    ! [C_558,A_559,D_560,B_561] :
      ( m1_orders_2(C_558,A_559,D_560)
      | m1_orders_2(D_560,A_559,C_558)
      | D_560 = C_558
      | ~ m2_orders_2(D_560,A_559,B_561)
      | ~ m2_orders_2(C_558,A_559,B_561)
      | ~ m1_orders_1(B_561,k1_orders_1(u1_struct_0(A_559)))
      | ~ l1_orders_2(A_559)
      | ~ v5_orders_2(A_559)
      | ~ v4_orders_2(A_559)
      | ~ v3_orders_2(A_559)
      | v2_struct_0(A_559) ) ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_3158,plain,(
    ! [C_558] :
      ( m1_orders_2(C_558,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_558)
      | C_558 = '#skF_4'
      | ~ m2_orders_2(C_558,'#skF_2','#skF_3')
      | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_72,c_3156])).

tff(c_3163,plain,(
    ! [C_558] :
      ( m1_orders_2(C_558,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_558)
      | C_558 = '#skF_4'
      | ~ m2_orders_2(C_558,'#skF_2','#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_76,c_74,c_3158])).

tff(c_3341,plain,(
    ! [C_579] :
      ( m1_orders_2(C_579,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_579)
      | C_579 = '#skF_4'
      | ~ m2_orders_2(C_579,'#skF_2','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_3163])).

tff(c_3347,plain,
    ( m1_orders_2('#skF_5','#skF_2','#skF_4')
    | m1_orders_2('#skF_4','#skF_2','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_70,c_3341])).

tff(c_3352,plain,
    ( m1_orders_2('#skF_5','#skF_2','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_2428,c_3347])).

tff(c_3353,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3352])).

tff(c_3365,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3353,c_2513])).

tff(c_3375,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_3365])).

tff(c_3376,plain,(
    m1_orders_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_3352])).

tff(c_60,plain,(
    ! [C_63,B_61,A_57] :
      ( r1_tarski(C_63,B_61)
      | ~ m1_orders_2(C_63,A_57,B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_orders_2(A_57)
      | ~ v5_orders_2(A_57)
      | ~ v4_orders_2(A_57)
      | ~ v3_orders_2(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_3385,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_3376,c_60])).

tff(c_3400,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_76,c_2974,c_3385])).

tff(c_3402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2513,c_3400])).

tff(c_3403,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2494])).

tff(c_3407,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3403,c_2429])).

tff(c_3411,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_3407])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n003.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:17:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.86/1.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.20/1.92  
% 5.20/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.20/1.93  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_mcart_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 5.20/1.93  
% 5.20/1.93  %Foreground sorts:
% 5.20/1.93  
% 5.20/1.93  
% 5.20/1.93  %Background operators:
% 5.20/1.93  
% 5.20/1.93  
% 5.20/1.93  %Foreground operators:
% 5.20/1.93  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.20/1.93  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.20/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.20/1.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.20/1.93  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.20/1.93  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.20/1.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.20/1.93  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 5.20/1.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.20/1.93  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 5.20/1.93  tff('#skF_5', type, '#skF_5': $i).
% 5.20/1.93  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.20/1.93  tff('#skF_2', type, '#skF_2': $i).
% 5.20/1.93  tff('#skF_3', type, '#skF_3': $i).
% 5.20/1.93  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.20/1.93  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.20/1.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.20/1.93  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 5.20/1.93  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.20/1.93  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 5.20/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.20/1.93  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 5.20/1.93  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.20/1.93  tff('#skF_4', type, '#skF_4': $i).
% 5.20/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.20/1.93  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 5.20/1.93  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.20/1.93  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.20/1.93  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 5.20/1.93  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.20/1.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.20/1.93  
% 5.20/1.95  tff(f_35, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 5.20/1.95  tff(f_270, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_orders_2)).
% 5.20/1.95  tff(f_150, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 5.20/1.95  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 5.20/1.95  tff(f_169, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_orders_2)).
% 5.20/1.95  tff(f_194, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_orders_2)).
% 5.20/1.95  tff(f_68, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 5.20/1.95  tff(f_72, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.20/1.95  tff(f_45, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 5.20/1.95  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.20/1.95  tff(f_51, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 5.20/1.95  tff(f_217, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_orders_2)).
% 5.20/1.95  tff(f_245, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_orders_2)).
% 5.20/1.95  tff(c_8, plain, (![A_3]: (~r2_xboole_0(A_3, A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.20/1.95  tff(c_84, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_270])).
% 5.20/1.95  tff(c_82, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_270])).
% 5.20/1.95  tff(c_80, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_270])).
% 5.20/1.95  tff(c_78, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_270])).
% 5.20/1.95  tff(c_76, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_270])).
% 5.20/1.95  tff(c_74, plain, (m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_270])).
% 5.20/1.95  tff(c_72, plain, (m2_orders_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_270])).
% 5.20/1.95  tff(c_1272, plain, (![C_307, A_308, B_309]: (m1_subset_1(C_307, k1_zfmisc_1(u1_struct_0(A_308))) | ~m2_orders_2(C_307, A_308, B_309) | ~m1_orders_1(B_309, k1_orders_1(u1_struct_0(A_308))) | ~l1_orders_2(A_308) | ~v5_orders_2(A_308) | ~v4_orders_2(A_308) | ~v3_orders_2(A_308) | v2_struct_0(A_308))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.20/1.95  tff(c_1274, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_72, c_1272])).
% 5.20/1.95  tff(c_1277, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_76, c_74, c_1274])).
% 5.20/1.95  tff(c_1278, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_84, c_1277])).
% 5.20/1.95  tff(c_161, plain, (![A_138, B_139]: (r2_xboole_0(A_138, B_139) | B_139=A_138 | ~r1_tarski(A_138, B_139))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.20/1.95  tff(c_86, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_5') | ~r2_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_270])).
% 5.20/1.95  tff(c_115, plain, (~r2_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_86])).
% 5.20/1.95  tff(c_172, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_161, c_115])).
% 5.20/1.95  tff(c_178, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_172])).
% 5.20/1.95  tff(c_92, plain, (r2_xboole_0('#skF_4', '#skF_5') | m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_270])).
% 5.20/1.95  tff(c_116, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_115, c_92])).
% 5.20/1.95  tff(c_562, plain, (![C_207, B_208, A_209]: (r1_tarski(C_207, B_208) | ~m1_orders_2(C_207, A_209, B_208) | ~m1_subset_1(B_208, k1_zfmisc_1(u1_struct_0(A_209))) | ~l1_orders_2(A_209) | ~v5_orders_2(A_209) | ~v4_orders_2(A_209) | ~v3_orders_2(A_209) | v2_struct_0(A_209))), inference(cnfTransformation, [status(thm)], [f_169])).
% 5.20/1.95  tff(c_564, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_116, c_562])).
% 5.20/1.95  tff(c_567, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_76, c_564])).
% 5.20/1.95  tff(c_568, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_84, c_178, c_567])).
% 5.20/1.95  tff(c_70, plain, (m2_orders_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_270])).
% 5.20/1.95  tff(c_720, plain, (![C_221, A_222, B_223]: (m1_subset_1(C_221, k1_zfmisc_1(u1_struct_0(A_222))) | ~m2_orders_2(C_221, A_222, B_223) | ~m1_orders_1(B_223, k1_orders_1(u1_struct_0(A_222))) | ~l1_orders_2(A_222) | ~v5_orders_2(A_222) | ~v4_orders_2(A_222) | ~v3_orders_2(A_222) | v2_struct_0(A_222))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.20/1.95  tff(c_724, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_70, c_720])).
% 5.20/1.95  tff(c_731, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_76, c_74, c_724])).
% 5.20/1.95  tff(c_733, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_568, c_731])).
% 5.20/1.95  tff(c_734, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_172])).
% 5.20/1.95  tff(c_736, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_734, c_116])).
% 5.20/1.95  tff(c_1366, plain, (![C_324, A_325, B_326]: (~m1_orders_2(C_324, A_325, B_326) | ~m1_orders_2(B_326, A_325, C_324) | k1_xboole_0=B_326 | ~m1_subset_1(C_324, k1_zfmisc_1(u1_struct_0(A_325))) | ~m1_subset_1(B_326, k1_zfmisc_1(u1_struct_0(A_325))) | ~l1_orders_2(A_325) | ~v5_orders_2(A_325) | ~v4_orders_2(A_325) | ~v3_orders_2(A_325) | v2_struct_0(A_325))), inference(cnfTransformation, [status(thm)], [f_194])).
% 5.20/1.95  tff(c_1368, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_736, c_1366])).
% 5.20/1.95  tff(c_1371, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_76, c_1278, c_736, c_1368])).
% 5.20/1.95  tff(c_1372, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_84, c_1371])).
% 5.20/1.95  tff(c_34, plain, (![A_17]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.20/1.95  tff(c_135, plain, (![A_133, B_134]: (r1_tarski(A_133, B_134) | ~m1_subset_1(A_133, k1_zfmisc_1(B_134)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.20/1.95  tff(c_144, plain, (![A_17]: (r1_tarski(k1_xboole_0, A_17))), inference(resolution, [status(thm)], [c_34, c_135])).
% 5.20/1.95  tff(c_817, plain, (![A_237, B_238, C_239]: (r1_tarski(k4_xboole_0(A_237, B_238), C_239) | ~r1_tarski(A_237, k2_xboole_0(B_238, C_239)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.20/1.95  tff(c_750, plain, (![B_226, A_227]: (B_226=A_227 | ~r1_tarski(B_226, A_227) | ~r1_tarski(A_227, B_226))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.20/1.95  tff(c_757, plain, (![A_17]: (k1_xboole_0=A_17 | ~r1_tarski(A_17, k1_xboole_0))), inference(resolution, [status(thm)], [c_144, c_750])).
% 5.20/1.95  tff(c_1161, plain, (![A_298, B_299]: (k4_xboole_0(A_298, B_299)=k1_xboole_0 | ~r1_tarski(A_298, k2_xboole_0(B_299, k1_xboole_0)))), inference(resolution, [status(thm)], [c_817, c_757])).
% 5.20/1.95  tff(c_1184, plain, (![B_299]: (k4_xboole_0(k1_xboole_0, B_299)=k1_xboole_0)), inference(resolution, [status(thm)], [c_144, c_1161])).
% 5.20/1.95  tff(c_1378, plain, (![B_299]: (k4_xboole_0('#skF_4', B_299)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1372, c_1372, c_1184])).
% 5.20/1.95  tff(c_22, plain, (![A_12, B_13]: (r1_xboole_0(A_12, B_13) | k4_xboole_0(A_12, B_13)!=A_12)), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.20/1.95  tff(c_1352, plain, (![C_316, D_317, A_318, B_319]: (~r1_xboole_0(C_316, D_317) | ~m2_orders_2(D_317, A_318, B_319) | ~m2_orders_2(C_316, A_318, B_319) | ~m1_orders_1(B_319, k1_orders_1(u1_struct_0(A_318))) | ~l1_orders_2(A_318) | ~v5_orders_2(A_318) | ~v4_orders_2(A_318) | ~v3_orders_2(A_318) | v2_struct_0(A_318))), inference(cnfTransformation, [status(thm)], [f_217])).
% 5.20/1.95  tff(c_2391, plain, (![B_435, A_436, B_437, A_438]: (~m2_orders_2(B_435, A_436, B_437) | ~m2_orders_2(A_438, A_436, B_437) | ~m1_orders_1(B_437, k1_orders_1(u1_struct_0(A_436))) | ~l1_orders_2(A_436) | ~v5_orders_2(A_436) | ~v4_orders_2(A_436) | ~v3_orders_2(A_436) | v2_struct_0(A_436) | k4_xboole_0(A_438, B_435)!=A_438)), inference(resolution, [status(thm)], [c_22, c_1352])).
% 5.20/1.95  tff(c_2393, plain, (![A_438]: (~m2_orders_2(A_438, '#skF_2', '#skF_3') | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k4_xboole_0(A_438, '#skF_4')!=A_438)), inference(resolution, [status(thm)], [c_72, c_2391])).
% 5.20/1.95  tff(c_2396, plain, (![A_438]: (~m2_orders_2(A_438, '#skF_2', '#skF_3') | v2_struct_0('#skF_2') | k4_xboole_0(A_438, '#skF_4')!=A_438)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_76, c_74, c_2393])).
% 5.20/1.95  tff(c_2420, plain, (![A_441]: (~m2_orders_2(A_441, '#skF_2', '#skF_3') | k4_xboole_0(A_441, '#skF_4')!=A_441)), inference(negUnitSimplification, [status(thm)], [c_84, c_2396])).
% 5.20/1.95  tff(c_2423, plain, (k4_xboole_0('#skF_4', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_72, c_2420])).
% 5.20/1.95  tff(c_2427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1378, c_2423])).
% 5.20/1.95  tff(c_2429, plain, (r2_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_86])).
% 5.20/1.95  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.20/1.95  tff(c_2433, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_2429, c_6])).
% 5.20/1.95  tff(c_2484, plain, (![B_458, A_459]: (B_458=A_459 | ~r1_tarski(B_458, A_459) | ~r1_tarski(A_459, B_458))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.20/1.95  tff(c_2494, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_2433, c_2484])).
% 5.20/1.95  tff(c_2513, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_2494])).
% 5.20/1.95  tff(c_2966, plain, (![C_536, A_537, B_538]: (m1_subset_1(C_536, k1_zfmisc_1(u1_struct_0(A_537))) | ~m2_orders_2(C_536, A_537, B_538) | ~m1_orders_1(B_538, k1_orders_1(u1_struct_0(A_537))) | ~l1_orders_2(A_537) | ~v5_orders_2(A_537) | ~v4_orders_2(A_537) | ~v3_orders_2(A_537) | v2_struct_0(A_537))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.20/1.95  tff(c_2968, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_72, c_2966])).
% 5.20/1.95  tff(c_2973, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_76, c_74, c_2968])).
% 5.20/1.95  tff(c_2974, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_84, c_2973])).
% 5.20/1.95  tff(c_14, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.20/1.95  tff(c_2428, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(splitRight, [status(thm)], [c_86])).
% 5.20/1.95  tff(c_3156, plain, (![C_558, A_559, D_560, B_561]: (m1_orders_2(C_558, A_559, D_560) | m1_orders_2(D_560, A_559, C_558) | D_560=C_558 | ~m2_orders_2(D_560, A_559, B_561) | ~m2_orders_2(C_558, A_559, B_561) | ~m1_orders_1(B_561, k1_orders_1(u1_struct_0(A_559))) | ~l1_orders_2(A_559) | ~v5_orders_2(A_559) | ~v4_orders_2(A_559) | ~v3_orders_2(A_559) | v2_struct_0(A_559))), inference(cnfTransformation, [status(thm)], [f_245])).
% 5.20/1.95  tff(c_3158, plain, (![C_558]: (m1_orders_2(C_558, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_558) | C_558='#skF_4' | ~m2_orders_2(C_558, '#skF_2', '#skF_3') | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_72, c_3156])).
% 5.20/1.95  tff(c_3163, plain, (![C_558]: (m1_orders_2(C_558, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_558) | C_558='#skF_4' | ~m2_orders_2(C_558, '#skF_2', '#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_76, c_74, c_3158])).
% 5.20/1.95  tff(c_3341, plain, (![C_579]: (m1_orders_2(C_579, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_579) | C_579='#skF_4' | ~m2_orders_2(C_579, '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_84, c_3163])).
% 5.20/1.95  tff(c_3347, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_70, c_3341])).
% 5.20/1.95  tff(c_3352, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4') | '#skF_5'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_2428, c_3347])).
% 5.20/1.95  tff(c_3353, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_3352])).
% 5.20/1.95  tff(c_3365, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3353, c_2513])).
% 5.20/1.95  tff(c_3375, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_3365])).
% 5.20/1.95  tff(c_3376, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_3352])).
% 5.20/1.95  tff(c_60, plain, (![C_63, B_61, A_57]: (r1_tarski(C_63, B_61) | ~m1_orders_2(C_63, A_57, B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_orders_2(A_57) | ~v5_orders_2(A_57) | ~v4_orders_2(A_57) | ~v3_orders_2(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_169])).
% 5.20/1.95  tff(c_3385, plain, (r1_tarski('#skF_5', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_3376, c_60])).
% 5.20/1.95  tff(c_3400, plain, (r1_tarski('#skF_5', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_76, c_2974, c_3385])).
% 5.20/1.95  tff(c_3402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_2513, c_3400])).
% 5.20/1.95  tff(c_3403, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_2494])).
% 5.20/1.95  tff(c_3407, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3403, c_2429])).
% 5.20/1.95  tff(c_3411, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_3407])).
% 5.20/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.20/1.95  
% 5.20/1.95  Inference rules
% 5.20/1.95  ----------------------
% 5.20/1.95  #Ref     : 0
% 5.20/1.95  #Sup     : 699
% 5.20/1.95  #Fact    : 0
% 5.20/1.95  #Define  : 0
% 5.20/1.95  #Split   : 30
% 5.20/1.95  #Chain   : 0
% 5.20/1.95  #Close   : 0
% 5.20/1.95  
% 5.20/1.95  Ordering : KBO
% 5.20/1.95  
% 5.20/1.95  Simplification rules
% 5.20/1.95  ----------------------
% 5.20/1.95  #Subsume      : 157
% 5.20/1.95  #Demod        : 340
% 5.20/1.95  #Tautology    : 216
% 5.20/1.95  #SimpNegUnit  : 148
% 5.20/1.95  #BackRed      : 55
% 5.20/1.95  
% 5.20/1.95  #Partial instantiations: 0
% 5.20/1.95  #Strategies tried      : 1
% 5.20/1.95  
% 5.20/1.95  Timing (in seconds)
% 5.20/1.95  ----------------------
% 5.20/1.95  Preprocessing        : 0.37
% 5.20/1.95  Parsing              : 0.20
% 5.20/1.95  CNF conversion       : 0.03
% 5.20/1.95  Main loop            : 0.80
% 5.20/1.95  Inferencing          : 0.28
% 5.20/1.95  Reduction            : 0.26
% 5.20/1.95  Demodulation         : 0.17
% 5.20/1.95  BG Simplification    : 0.03
% 5.20/1.95  Subsumption          : 0.17
% 5.20/1.95  Abstraction          : 0.03
% 5.20/1.95  MUC search           : 0.00
% 5.20/1.95  Cooper               : 0.00
% 5.20/1.95  Total                : 1.21
% 5.20/1.95  Index Insertion      : 0.00
% 5.20/1.95  Index Deletion       : 0.00
% 5.20/1.95  Index Matching       : 0.00
% 5.20/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
