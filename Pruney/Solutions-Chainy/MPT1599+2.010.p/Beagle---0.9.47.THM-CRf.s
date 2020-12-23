%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:23 EST 2020

% Result     : Theorem 4.76s
% Output     : CNFRefutation 5.09s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 594 expanded)
%              Number of leaves         :   41 ( 239 expanded)
%              Depth                    :   16
%              Number of atoms          :  568 (1685 expanded)
%              Number of equality atoms :   64 ( 315 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k12_lattice3 > k11_lattice3 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k11_lattice3,type,(
    k11_lattice3: ( $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k12_lattice3,type,(
    k12_lattice3: ( $i * $i * $i ) > $i )).

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

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_154,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_181,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( v2_lattice3(k2_yellow_1(A))
         => ! [B] :
              ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(A),B,C),k3_xboole_0(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_1)).

tff(f_142,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k11_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).

tff(f_150,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,B,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_167,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

tff(f_138,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( B = k12_lattice3(A,B,C)
              <=> r3_orders_2(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_yellow_0)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(f_120,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( v4_orders_2(A)
                   => k11_lattice3(A,k11_lattice3(A,B,C),D) = k11_lattice3(A,B,k11_lattice3(A,C,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_lattice3)).

tff(f_101,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k11_lattice3(A,B,C) = k11_lattice3(A,C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_lattice3)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_38,plain,(
    ! [A_50] : u1_struct_0(k2_yellow_1(A_50)) = A_50 ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_56,plain,(
    m1_subset_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_48])).

tff(c_50,plain,(
    m1_subset_1('#skF_2',u1_struct_0(k2_yellow_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_55,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_50])).

tff(c_28,plain,(
    ! [A_48] : l1_orders_2(k2_yellow_1(A_48)) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_1358,plain,(
    ! [A_205,B_206,C_207] :
      ( m1_subset_1(k11_lattice3(A_205,B_206,C_207),u1_struct_0(A_205))
      | ~ m1_subset_1(C_207,u1_struct_0(A_205))
      | ~ m1_subset_1(B_206,u1_struct_0(A_205))
      | ~ l1_orders_2(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1363,plain,(
    ! [A_50,B_206,C_207] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_50),B_206,C_207),A_50)
      | ~ m1_subset_1(C_207,u1_struct_0(k2_yellow_1(A_50)))
      | ~ m1_subset_1(B_206,u1_struct_0(k2_yellow_1(A_50)))
      | ~ l1_orders_2(k2_yellow_1(A_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1358])).

tff(c_1366,plain,(
    ! [A_50,B_206,C_207] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_50),B_206,C_207),A_50)
      | ~ m1_subset_1(C_207,A_50)
      | ~ m1_subset_1(B_206,A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_38,c_38,c_1363])).

tff(c_52,plain,(
    v2_lattice3(k2_yellow_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_32,plain,(
    ! [A_49] : v3_orders_2(k2_yellow_1(A_49)) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_98,plain,(
    ! [A_75,B_76] :
      ( r1_orders_2(A_75,B_76,B_76)
      | ~ m1_subset_1(B_76,u1_struct_0(A_75))
      | ~ l1_orders_2(A_75)
      | ~ v3_orders_2(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_100,plain,(
    ! [A_50,B_76] :
      ( r1_orders_2(k2_yellow_1(A_50),B_76,B_76)
      | ~ m1_subset_1(B_76,A_50)
      | ~ l1_orders_2(k2_yellow_1(A_50))
      | ~ v3_orders_2(k2_yellow_1(A_50))
      | v2_struct_0(k2_yellow_1(A_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_98])).

tff(c_102,plain,(
    ! [A_50,B_76] :
      ( r1_orders_2(k2_yellow_1(A_50),B_76,B_76)
      | ~ m1_subset_1(B_76,A_50)
      | v2_struct_0(k2_yellow_1(A_50)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_100])).

tff(c_1397,plain,(
    ! [A_219,B_220,C_221] :
      ( r3_orders_2(A_219,B_220,C_221)
      | ~ r1_orders_2(A_219,B_220,C_221)
      | ~ m1_subset_1(C_221,u1_struct_0(A_219))
      | ~ m1_subset_1(B_220,u1_struct_0(A_219))
      | ~ l1_orders_2(A_219)
      | ~ v3_orders_2(A_219)
      | v2_struct_0(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1404,plain,(
    ! [A_50,B_220,C_221] :
      ( r3_orders_2(k2_yellow_1(A_50),B_220,C_221)
      | ~ r1_orders_2(k2_yellow_1(A_50),B_220,C_221)
      | ~ m1_subset_1(C_221,A_50)
      | ~ m1_subset_1(B_220,u1_struct_0(k2_yellow_1(A_50)))
      | ~ l1_orders_2(k2_yellow_1(A_50))
      | ~ v3_orders_2(k2_yellow_1(A_50))
      | v2_struct_0(k2_yellow_1(A_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1397])).

tff(c_1415,plain,(
    ! [A_225,B_226,C_227] :
      ( r3_orders_2(k2_yellow_1(A_225),B_226,C_227)
      | ~ r1_orders_2(k2_yellow_1(A_225),B_226,C_227)
      | ~ m1_subset_1(C_227,A_225)
      | ~ m1_subset_1(B_226,A_225)
      | v2_struct_0(k2_yellow_1(A_225)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_38,c_1404])).

tff(c_44,plain,(
    ! [B_55,C_57,A_51] :
      ( r1_tarski(B_55,C_57)
      | ~ r3_orders_2(k2_yellow_1(A_51),B_55,C_57)
      | ~ m1_subset_1(C_57,u1_struct_0(k2_yellow_1(A_51)))
      | ~ m1_subset_1(B_55,u1_struct_0(k2_yellow_1(A_51)))
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_57,plain,(
    ! [B_55,C_57,A_51] :
      ( r1_tarski(B_55,C_57)
      | ~ r3_orders_2(k2_yellow_1(A_51),B_55,C_57)
      | ~ m1_subset_1(C_57,A_51)
      | ~ m1_subset_1(B_55,A_51)
      | v1_xboole_0(A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_44])).

tff(c_1426,plain,(
    ! [B_231,C_232,A_233] :
      ( r1_tarski(B_231,C_232)
      | v1_xboole_0(A_233)
      | ~ r1_orders_2(k2_yellow_1(A_233),B_231,C_232)
      | ~ m1_subset_1(C_232,A_233)
      | ~ m1_subset_1(B_231,A_233)
      | v2_struct_0(k2_yellow_1(A_233)) ) ),
    inference(resolution,[status(thm)],[c_1415,c_57])).

tff(c_1447,plain,(
    ! [B_237,A_238] :
      ( r1_tarski(B_237,B_237)
      | v1_xboole_0(A_238)
      | ~ m1_subset_1(B_237,A_238)
      | v2_struct_0(k2_yellow_1(A_238)) ) ),
    inference(resolution,[status(thm)],[c_102,c_1426])).

tff(c_1453,plain,
    ( r1_tarski('#skF_3','#skF_3')
    | v1_xboole_0('#skF_1')
    | v2_struct_0(k2_yellow_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_56,c_1447])).

tff(c_1460,plain,
    ( r1_tarski('#skF_3','#skF_3')
    | v2_struct_0(k2_yellow_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1453])).

tff(c_1464,plain,(
    v2_struct_0(k2_yellow_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1460])).

tff(c_12,plain,(
    ! [A_12] :
      ( ~ v2_struct_0(A_12)
      | ~ v2_lattice3(A_12)
      | ~ l1_orders_2(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1467,plain,
    ( ~ v2_lattice3(k2_yellow_1('#skF_1'))
    | ~ l1_orders_2(k2_yellow_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1464,c_12])).

tff(c_1471,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_52,c_1467])).

tff(c_1473,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1460])).

tff(c_36,plain,(
    ! [A_49] : v5_orders_2(k2_yellow_1(A_49)) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_1408,plain,(
    ! [A_50,B_220,C_221] :
      ( r3_orders_2(k2_yellow_1(A_50),B_220,C_221)
      | ~ r1_orders_2(k2_yellow_1(A_50),B_220,C_221)
      | ~ m1_subset_1(C_221,A_50)
      | ~ m1_subset_1(B_220,A_50)
      | v2_struct_0(k2_yellow_1(A_50)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_38,c_1404])).

tff(c_1575,plain,(
    ! [A_247,B_248,C_249] :
      ( k12_lattice3(A_247,B_248,C_249) = B_248
      | ~ r3_orders_2(A_247,B_248,C_249)
      | ~ m1_subset_1(C_249,u1_struct_0(A_247))
      | ~ m1_subset_1(B_248,u1_struct_0(A_247))
      | ~ l1_orders_2(A_247)
      | ~ v2_lattice3(A_247)
      | ~ v5_orders_2(A_247)
      | ~ v3_orders_2(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1577,plain,(
    ! [A_50,B_220,C_221] :
      ( k12_lattice3(k2_yellow_1(A_50),B_220,C_221) = B_220
      | ~ m1_subset_1(C_221,u1_struct_0(k2_yellow_1(A_50)))
      | ~ m1_subset_1(B_220,u1_struct_0(k2_yellow_1(A_50)))
      | ~ l1_orders_2(k2_yellow_1(A_50))
      | ~ v2_lattice3(k2_yellow_1(A_50))
      | ~ v5_orders_2(k2_yellow_1(A_50))
      | ~ v3_orders_2(k2_yellow_1(A_50))
      | ~ r1_orders_2(k2_yellow_1(A_50),B_220,C_221)
      | ~ m1_subset_1(C_221,A_50)
      | ~ m1_subset_1(B_220,A_50)
      | v2_struct_0(k2_yellow_1(A_50)) ) ),
    inference(resolution,[status(thm)],[c_1408,c_1575])).

tff(c_1759,plain,(
    ! [A_277,B_278,C_279] :
      ( k12_lattice3(k2_yellow_1(A_277),B_278,C_279) = B_278
      | ~ v2_lattice3(k2_yellow_1(A_277))
      | ~ r1_orders_2(k2_yellow_1(A_277),B_278,C_279)
      | ~ m1_subset_1(C_279,A_277)
      | ~ m1_subset_1(B_278,A_277)
      | v2_struct_0(k2_yellow_1(A_277)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36,c_28,c_38,c_38,c_1577])).

tff(c_1772,plain,(
    ! [A_280,B_281] :
      ( k12_lattice3(k2_yellow_1(A_280),B_281,B_281) = B_281
      | ~ v2_lattice3(k2_yellow_1(A_280))
      | ~ m1_subset_1(B_281,A_280)
      | v2_struct_0(k2_yellow_1(A_280)) ) ),
    inference(resolution,[status(thm)],[c_102,c_1759])).

tff(c_1372,plain,(
    ! [A_211,B_212,C_213] :
      ( k12_lattice3(A_211,B_212,C_213) = k11_lattice3(A_211,B_212,C_213)
      | ~ m1_subset_1(C_213,u1_struct_0(A_211))
      | ~ m1_subset_1(B_212,u1_struct_0(A_211))
      | ~ l1_orders_2(A_211)
      | ~ v2_lattice3(A_211)
      | ~ v5_orders_2(A_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1379,plain,(
    ! [A_50,B_212,C_213] :
      ( k12_lattice3(k2_yellow_1(A_50),B_212,C_213) = k11_lattice3(k2_yellow_1(A_50),B_212,C_213)
      | ~ m1_subset_1(C_213,A_50)
      | ~ m1_subset_1(B_212,u1_struct_0(k2_yellow_1(A_50)))
      | ~ l1_orders_2(k2_yellow_1(A_50))
      | ~ v2_lattice3(k2_yellow_1(A_50))
      | ~ v5_orders_2(k2_yellow_1(A_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1372])).

tff(c_1384,plain,(
    ! [A_214,B_215,C_216] :
      ( k12_lattice3(k2_yellow_1(A_214),B_215,C_216) = k11_lattice3(k2_yellow_1(A_214),B_215,C_216)
      | ~ m1_subset_1(C_216,A_214)
      | ~ m1_subset_1(B_215,A_214)
      | ~ v2_lattice3(k2_yellow_1(A_214)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_28,c_38,c_1379])).

tff(c_1387,plain,(
    ! [B_215,C_216] :
      ( k12_lattice3(k2_yellow_1('#skF_1'),B_215,C_216) = k11_lattice3(k2_yellow_1('#skF_1'),B_215,C_216)
      | ~ m1_subset_1(C_216,'#skF_1')
      | ~ m1_subset_1(B_215,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_52,c_1384])).

tff(c_1785,plain,(
    ! [B_281] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),B_281,B_281) = B_281
      | ~ m1_subset_1(B_281,'#skF_1')
      | ~ m1_subset_1(B_281,'#skF_1')
      | ~ v2_lattice3(k2_yellow_1('#skF_1'))
      | ~ m1_subset_1(B_281,'#skF_1')
      | v2_struct_0(k2_yellow_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1772,c_1387])).

tff(c_1810,plain,(
    ! [B_281] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),B_281,B_281) = B_281
      | ~ m1_subset_1(B_281,'#skF_1')
      | v2_struct_0(k2_yellow_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1785])).

tff(c_1811,plain,(
    ! [B_281] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),B_281,B_281) = B_281
      | ~ m1_subset_1(B_281,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1473,c_1810])).

tff(c_34,plain,(
    ! [A_49] : v4_orders_2(k2_yellow_1(A_49)) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_1683,plain,(
    ! [A_260,B_261,C_262,D_263] :
      ( k11_lattice3(A_260,k11_lattice3(A_260,B_261,C_262),D_263) = k11_lattice3(A_260,B_261,k11_lattice3(A_260,C_262,D_263))
      | ~ v4_orders_2(A_260)
      | ~ m1_subset_1(D_263,u1_struct_0(A_260))
      | ~ m1_subset_1(C_262,u1_struct_0(A_260))
      | ~ m1_subset_1(B_261,u1_struct_0(A_260))
      | ~ l1_orders_2(A_260)
      | ~ v2_lattice3(A_260)
      | ~ v5_orders_2(A_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1690,plain,(
    ! [A_50,B_261,C_262,D_263] :
      ( k11_lattice3(k2_yellow_1(A_50),k11_lattice3(k2_yellow_1(A_50),B_261,C_262),D_263) = k11_lattice3(k2_yellow_1(A_50),B_261,k11_lattice3(k2_yellow_1(A_50),C_262,D_263))
      | ~ v4_orders_2(k2_yellow_1(A_50))
      | ~ m1_subset_1(D_263,A_50)
      | ~ m1_subset_1(C_262,u1_struct_0(k2_yellow_1(A_50)))
      | ~ m1_subset_1(B_261,u1_struct_0(k2_yellow_1(A_50)))
      | ~ l1_orders_2(k2_yellow_1(A_50))
      | ~ v2_lattice3(k2_yellow_1(A_50))
      | ~ v5_orders_2(k2_yellow_1(A_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1683])).

tff(c_2024,plain,(
    ! [A_293,B_294,C_295,D_296] :
      ( k11_lattice3(k2_yellow_1(A_293),k11_lattice3(k2_yellow_1(A_293),B_294,C_295),D_296) = k11_lattice3(k2_yellow_1(A_293),B_294,k11_lattice3(k2_yellow_1(A_293),C_295,D_296))
      | ~ m1_subset_1(D_296,A_293)
      | ~ m1_subset_1(C_295,A_293)
      | ~ m1_subset_1(B_294,A_293)
      | ~ v2_lattice3(k2_yellow_1(A_293)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_28,c_38,c_38,c_34,c_1690])).

tff(c_2089,plain,(
    ! [B_281,D_296] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),B_281,k11_lattice3(k2_yellow_1('#skF_1'),B_281,D_296)) = k11_lattice3(k2_yellow_1('#skF_1'),B_281,D_296)
      | ~ m1_subset_1(D_296,'#skF_1')
      | ~ m1_subset_1(B_281,'#skF_1')
      | ~ m1_subset_1(B_281,'#skF_1')
      | ~ v2_lattice3(k2_yellow_1('#skF_1'))
      | ~ m1_subset_1(B_281,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1811,c_2024])).

tff(c_2381,plain,(
    ! [B_311,D_312] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),B_311,k11_lattice3(k2_yellow_1('#skF_1'),B_311,D_312)) = k11_lattice3(k2_yellow_1('#skF_1'),B_311,D_312)
      | ~ m1_subset_1(D_312,'#skF_1')
      | ~ m1_subset_1(B_311,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2089])).

tff(c_1435,plain,(
    ! [A_234,C_235,B_236] :
      ( k11_lattice3(A_234,C_235,B_236) = k11_lattice3(A_234,B_236,C_235)
      | ~ m1_subset_1(C_235,u1_struct_0(A_234))
      | ~ m1_subset_1(B_236,u1_struct_0(A_234))
      | ~ l1_orders_2(A_234)
      | ~ v2_lattice3(A_234)
      | ~ v5_orders_2(A_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1442,plain,(
    ! [A_50,C_235,B_236] :
      ( k11_lattice3(k2_yellow_1(A_50),C_235,B_236) = k11_lattice3(k2_yellow_1(A_50),B_236,C_235)
      | ~ m1_subset_1(C_235,A_50)
      | ~ m1_subset_1(B_236,u1_struct_0(k2_yellow_1(A_50)))
      | ~ l1_orders_2(k2_yellow_1(A_50))
      | ~ v2_lattice3(k2_yellow_1(A_50))
      | ~ v5_orders_2(k2_yellow_1(A_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1435])).

tff(c_1487,plain,(
    ! [A_242,C_243,B_244] :
      ( k11_lattice3(k2_yellow_1(A_242),C_243,B_244) = k11_lattice3(k2_yellow_1(A_242),B_244,C_243)
      | ~ m1_subset_1(C_243,A_242)
      | ~ m1_subset_1(B_244,A_242)
      | ~ v2_lattice3(k2_yellow_1(A_242)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_28,c_38,c_1442])).

tff(c_1490,plain,(
    ! [C_243,B_244] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),C_243,B_244) = k11_lattice3(k2_yellow_1('#skF_1'),B_244,C_243)
      | ~ m1_subset_1(C_243,'#skF_1')
      | ~ m1_subset_1(B_244,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_52,c_1487])).

tff(c_1474,plain,(
    ! [A_239,B_240,C_241] :
      ( r3_orders_2(A_239,B_240,C_241)
      | k12_lattice3(A_239,B_240,C_241) != B_240
      | ~ m1_subset_1(C_241,u1_struct_0(A_239))
      | ~ m1_subset_1(B_240,u1_struct_0(A_239))
      | ~ l1_orders_2(A_239)
      | ~ v2_lattice3(A_239)
      | ~ v5_orders_2(A_239)
      | ~ v3_orders_2(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1481,plain,(
    ! [A_50,B_240,C_241] :
      ( r3_orders_2(k2_yellow_1(A_50),B_240,C_241)
      | k12_lattice3(k2_yellow_1(A_50),B_240,C_241) != B_240
      | ~ m1_subset_1(C_241,A_50)
      | ~ m1_subset_1(B_240,u1_struct_0(k2_yellow_1(A_50)))
      | ~ l1_orders_2(k2_yellow_1(A_50))
      | ~ v2_lattice3(k2_yellow_1(A_50))
      | ~ v5_orders_2(k2_yellow_1(A_50))
      | ~ v3_orders_2(k2_yellow_1(A_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1474])).

tff(c_1668,plain,(
    ! [A_257,B_258,C_259] :
      ( r3_orders_2(k2_yellow_1(A_257),B_258,C_259)
      | k12_lattice3(k2_yellow_1(A_257),B_258,C_259) != B_258
      | ~ m1_subset_1(C_259,A_257)
      | ~ m1_subset_1(B_258,A_257)
      | ~ v2_lattice3(k2_yellow_1(A_257)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36,c_28,c_38,c_1481])).

tff(c_1695,plain,(
    ! [B_264,C_265,A_266] :
      ( r1_tarski(B_264,C_265)
      | v1_xboole_0(A_266)
      | k12_lattice3(k2_yellow_1(A_266),B_264,C_265) != B_264
      | ~ m1_subset_1(C_265,A_266)
      | ~ m1_subset_1(B_264,A_266)
      | ~ v2_lattice3(k2_yellow_1(A_266)) ) ),
    inference(resolution,[status(thm)],[c_1668,c_57])).

tff(c_1699,plain,(
    ! [B_215,C_216] :
      ( r1_tarski(B_215,C_216)
      | v1_xboole_0('#skF_1')
      | k11_lattice3(k2_yellow_1('#skF_1'),B_215,C_216) != B_215
      | ~ m1_subset_1(C_216,'#skF_1')
      | ~ m1_subset_1(B_215,'#skF_1')
      | ~ v2_lattice3(k2_yellow_1('#skF_1'))
      | ~ m1_subset_1(C_216,'#skF_1')
      | ~ m1_subset_1(B_215,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1387,c_1695])).

tff(c_1705,plain,(
    ! [B_215,C_216] :
      ( r1_tarski(B_215,C_216)
      | v1_xboole_0('#skF_1')
      | k11_lattice3(k2_yellow_1('#skF_1'),B_215,C_216) != B_215
      | ~ m1_subset_1(C_216,'#skF_1')
      | ~ m1_subset_1(B_215,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1699])).

tff(c_1707,plain,(
    ! [B_267,C_268] :
      ( r1_tarski(B_267,C_268)
      | k11_lattice3(k2_yellow_1('#skF_1'),B_267,C_268) != B_267
      | ~ m1_subset_1(C_268,'#skF_1')
      | ~ m1_subset_1(B_267,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1705])).

tff(c_1713,plain,(
    ! [B_244,C_243] :
      ( r1_tarski(B_244,C_243)
      | k11_lattice3(k2_yellow_1('#skF_1'),C_243,B_244) != B_244
      | ~ m1_subset_1(C_243,'#skF_1')
      | ~ m1_subset_1(B_244,'#skF_1')
      | ~ m1_subset_1(C_243,'#skF_1')
      | ~ m1_subset_1(B_244,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1490,c_1707])).

tff(c_2851,plain,(
    ! [B_334,D_335] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),B_334,D_335),B_334)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'),B_334,D_335),'#skF_1')
      | ~ m1_subset_1(D_335,'#skF_1')
      | ~ m1_subset_1(B_334,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2381,c_1713])).

tff(c_1491,plain,(
    ! [C_245,B_246] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),C_245,B_246) = k11_lattice3(k2_yellow_1('#skF_1'),B_246,C_245)
      | ~ m1_subset_1(C_245,'#skF_1')
      | ~ m1_subset_1(B_246,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_52,c_1487])).

tff(c_105,plain,(
    ! [A_79,B_80,C_81] :
      ( m1_subset_1(k11_lattice3(A_79,B_80,C_81),u1_struct_0(A_79))
      | ~ m1_subset_1(C_81,u1_struct_0(A_79))
      | ~ m1_subset_1(B_80,u1_struct_0(A_79))
      | ~ l1_orders_2(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_110,plain,(
    ! [A_50,B_80,C_81] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_50),B_80,C_81),A_50)
      | ~ m1_subset_1(C_81,u1_struct_0(k2_yellow_1(A_50)))
      | ~ m1_subset_1(B_80,u1_struct_0(k2_yellow_1(A_50)))
      | ~ l1_orders_2(k2_yellow_1(A_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_105])).

tff(c_113,plain,(
    ! [A_50,B_80,C_81] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_50),B_80,C_81),A_50)
      | ~ m1_subset_1(C_81,A_50)
      | ~ m1_subset_1(B_80,A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_38,c_38,c_110])).

tff(c_125,plain,(
    ! [A_91,B_92,C_93] :
      ( r3_orders_2(A_91,B_92,C_93)
      | ~ r1_orders_2(A_91,B_92,C_93)
      | ~ m1_subset_1(C_93,u1_struct_0(A_91))
      | ~ m1_subset_1(B_92,u1_struct_0(A_91))
      | ~ l1_orders_2(A_91)
      | ~ v3_orders_2(A_91)
      | v2_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_132,plain,(
    ! [A_50,B_92,C_93] :
      ( r3_orders_2(k2_yellow_1(A_50),B_92,C_93)
      | ~ r1_orders_2(k2_yellow_1(A_50),B_92,C_93)
      | ~ m1_subset_1(C_93,A_50)
      | ~ m1_subset_1(B_92,u1_struct_0(k2_yellow_1(A_50)))
      | ~ l1_orders_2(k2_yellow_1(A_50))
      | ~ v3_orders_2(k2_yellow_1(A_50))
      | v2_struct_0(k2_yellow_1(A_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_125])).

tff(c_137,plain,(
    ! [A_94,B_95,C_96] :
      ( r3_orders_2(k2_yellow_1(A_94),B_95,C_96)
      | ~ r1_orders_2(k2_yellow_1(A_94),B_95,C_96)
      | ~ m1_subset_1(C_96,A_94)
      | ~ m1_subset_1(B_95,A_94)
      | v2_struct_0(k2_yellow_1(A_94)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_38,c_132])).

tff(c_231,plain,(
    ! [B_105,C_106,A_107] :
      ( r1_tarski(B_105,C_106)
      | v1_xboole_0(A_107)
      | ~ r1_orders_2(k2_yellow_1(A_107),B_105,C_106)
      | ~ m1_subset_1(C_106,A_107)
      | ~ m1_subset_1(B_105,A_107)
      | v2_struct_0(k2_yellow_1(A_107)) ) ),
    inference(resolution,[status(thm)],[c_137,c_57])).

tff(c_236,plain,(
    ! [B_108,A_109] :
      ( r1_tarski(B_108,B_108)
      | v1_xboole_0(A_109)
      | ~ m1_subset_1(B_108,A_109)
      | v2_struct_0(k2_yellow_1(A_109)) ) ),
    inference(resolution,[status(thm)],[c_102,c_231])).

tff(c_242,plain,
    ( r1_tarski('#skF_3','#skF_3')
    | v1_xboole_0('#skF_1')
    | v2_struct_0(k2_yellow_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_56,c_236])).

tff(c_249,plain,
    ( r1_tarski('#skF_3','#skF_3')
    | v2_struct_0(k2_yellow_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_242])).

tff(c_253,plain,(
    v2_struct_0(k2_yellow_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_249])).

tff(c_267,plain,
    ( ~ v2_lattice3(k2_yellow_1('#skF_1'))
    | ~ l1_orders_2(k2_yellow_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_253,c_12])).

tff(c_271,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_52,c_267])).

tff(c_273,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_136,plain,(
    ! [A_50,B_92,C_93] :
      ( r3_orders_2(k2_yellow_1(A_50),B_92,C_93)
      | ~ r1_orders_2(k2_yellow_1(A_50),B_92,C_93)
      | ~ m1_subset_1(C_93,A_50)
      | ~ m1_subset_1(B_92,A_50)
      | v2_struct_0(k2_yellow_1(A_50)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_38,c_132])).

tff(c_393,plain,(
    ! [A_148,B_149,C_150] :
      ( k12_lattice3(A_148,B_149,C_150) = B_149
      | ~ r3_orders_2(A_148,B_149,C_150)
      | ~ m1_subset_1(C_150,u1_struct_0(A_148))
      | ~ m1_subset_1(B_149,u1_struct_0(A_148))
      | ~ l1_orders_2(A_148)
      | ~ v2_lattice3(A_148)
      | ~ v5_orders_2(A_148)
      | ~ v3_orders_2(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_397,plain,(
    ! [A_50,B_92,C_93] :
      ( k12_lattice3(k2_yellow_1(A_50),B_92,C_93) = B_92
      | ~ m1_subset_1(C_93,u1_struct_0(k2_yellow_1(A_50)))
      | ~ m1_subset_1(B_92,u1_struct_0(k2_yellow_1(A_50)))
      | ~ l1_orders_2(k2_yellow_1(A_50))
      | ~ v2_lattice3(k2_yellow_1(A_50))
      | ~ v5_orders_2(k2_yellow_1(A_50))
      | ~ v3_orders_2(k2_yellow_1(A_50))
      | ~ r1_orders_2(k2_yellow_1(A_50),B_92,C_93)
      | ~ m1_subset_1(C_93,A_50)
      | ~ m1_subset_1(B_92,A_50)
      | v2_struct_0(k2_yellow_1(A_50)) ) ),
    inference(resolution,[status(thm)],[c_136,c_393])).

tff(c_519,plain,(
    ! [A_162,B_163,C_164] :
      ( k12_lattice3(k2_yellow_1(A_162),B_163,C_164) = B_163
      | ~ v2_lattice3(k2_yellow_1(A_162))
      | ~ r1_orders_2(k2_yellow_1(A_162),B_163,C_164)
      | ~ m1_subset_1(C_164,A_162)
      | ~ m1_subset_1(B_163,A_162)
      | v2_struct_0(k2_yellow_1(A_162)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36,c_28,c_38,c_38,c_397])).

tff(c_532,plain,(
    ! [A_165,B_166] :
      ( k12_lattice3(k2_yellow_1(A_165),B_166,B_166) = B_166
      | ~ v2_lattice3(k2_yellow_1(A_165))
      | ~ m1_subset_1(B_166,A_165)
      | v2_struct_0(k2_yellow_1(A_165)) ) ),
    inference(resolution,[status(thm)],[c_102,c_519])).

tff(c_275,plain,(
    ! [A_113,B_114,C_115] :
      ( k12_lattice3(A_113,B_114,C_115) = k11_lattice3(A_113,B_114,C_115)
      | ~ m1_subset_1(C_115,u1_struct_0(A_113))
      | ~ m1_subset_1(B_114,u1_struct_0(A_113))
      | ~ l1_orders_2(A_113)
      | ~ v2_lattice3(A_113)
      | ~ v5_orders_2(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_282,plain,(
    ! [A_50,B_114,C_115] :
      ( k12_lattice3(k2_yellow_1(A_50),B_114,C_115) = k11_lattice3(k2_yellow_1(A_50),B_114,C_115)
      | ~ m1_subset_1(C_115,A_50)
      | ~ m1_subset_1(B_114,u1_struct_0(k2_yellow_1(A_50)))
      | ~ l1_orders_2(k2_yellow_1(A_50))
      | ~ v2_lattice3(k2_yellow_1(A_50))
      | ~ v5_orders_2(k2_yellow_1(A_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_275])).

tff(c_287,plain,(
    ! [A_116,B_117,C_118] :
      ( k12_lattice3(k2_yellow_1(A_116),B_117,C_118) = k11_lattice3(k2_yellow_1(A_116),B_117,C_118)
      | ~ m1_subset_1(C_118,A_116)
      | ~ m1_subset_1(B_117,A_116)
      | ~ v2_lattice3(k2_yellow_1(A_116)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_28,c_38,c_282])).

tff(c_290,plain,(
    ! [B_117,C_118] :
      ( k12_lattice3(k2_yellow_1('#skF_1'),B_117,C_118) = k11_lattice3(k2_yellow_1('#skF_1'),B_117,C_118)
      | ~ m1_subset_1(C_118,'#skF_1')
      | ~ m1_subset_1(B_117,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_52,c_287])).

tff(c_545,plain,(
    ! [B_166] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),B_166,B_166) = B_166
      | ~ m1_subset_1(B_166,'#skF_1')
      | ~ m1_subset_1(B_166,'#skF_1')
      | ~ v2_lattice3(k2_yellow_1('#skF_1'))
      | ~ m1_subset_1(B_166,'#skF_1')
      | v2_struct_0(k2_yellow_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_532,c_290])).

tff(c_570,plain,(
    ! [B_166] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),B_166,B_166) = B_166
      | ~ m1_subset_1(B_166,'#skF_1')
      | v2_struct_0(k2_yellow_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_545])).

tff(c_571,plain,(
    ! [B_166] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),B_166,B_166) = B_166
      | ~ m1_subset_1(B_166,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_273,c_570])).

tff(c_507,plain,(
    ! [A_158,B_159,C_160,D_161] :
      ( k11_lattice3(A_158,k11_lattice3(A_158,B_159,C_160),D_161) = k11_lattice3(A_158,B_159,k11_lattice3(A_158,C_160,D_161))
      | ~ v4_orders_2(A_158)
      | ~ m1_subset_1(D_161,u1_struct_0(A_158))
      | ~ m1_subset_1(C_160,u1_struct_0(A_158))
      | ~ m1_subset_1(B_159,u1_struct_0(A_158))
      | ~ l1_orders_2(A_158)
      | ~ v2_lattice3(A_158)
      | ~ v5_orders_2(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_514,plain,(
    ! [A_50,B_159,C_160,D_161] :
      ( k11_lattice3(k2_yellow_1(A_50),k11_lattice3(k2_yellow_1(A_50),B_159,C_160),D_161) = k11_lattice3(k2_yellow_1(A_50),B_159,k11_lattice3(k2_yellow_1(A_50),C_160,D_161))
      | ~ v4_orders_2(k2_yellow_1(A_50))
      | ~ m1_subset_1(D_161,A_50)
      | ~ m1_subset_1(C_160,u1_struct_0(k2_yellow_1(A_50)))
      | ~ m1_subset_1(B_159,u1_struct_0(k2_yellow_1(A_50)))
      | ~ l1_orders_2(k2_yellow_1(A_50))
      | ~ v2_lattice3(k2_yellow_1(A_50))
      | ~ v5_orders_2(k2_yellow_1(A_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_507])).

tff(c_887,plain,(
    ! [A_186,B_187,C_188,D_189] :
      ( k11_lattice3(k2_yellow_1(A_186),k11_lattice3(k2_yellow_1(A_186),B_187,C_188),D_189) = k11_lattice3(k2_yellow_1(A_186),B_187,k11_lattice3(k2_yellow_1(A_186),C_188,D_189))
      | ~ m1_subset_1(D_189,A_186)
      | ~ m1_subset_1(C_188,A_186)
      | ~ m1_subset_1(B_187,A_186)
      | ~ v2_lattice3(k2_yellow_1(A_186)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_28,c_38,c_38,c_34,c_514])).

tff(c_984,plain,(
    ! [B_166,D_189] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),B_166,k11_lattice3(k2_yellow_1('#skF_1'),B_166,D_189)) = k11_lattice3(k2_yellow_1('#skF_1'),B_166,D_189)
      | ~ m1_subset_1(D_189,'#skF_1')
      | ~ m1_subset_1(B_166,'#skF_1')
      | ~ m1_subset_1(B_166,'#skF_1')
      | ~ v2_lattice3(k2_yellow_1('#skF_1'))
      | ~ m1_subset_1(B_166,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_571,c_887])).

tff(c_1141,plain,(
    ! [B_194,D_195] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),B_194,k11_lattice3(k2_yellow_1('#skF_1'),B_194,D_195)) = k11_lattice3(k2_yellow_1('#skF_1'),B_194,D_195)
      | ~ m1_subset_1(D_195,'#skF_1')
      | ~ m1_subset_1(B_194,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_984])).

tff(c_142,plain,(
    ! [A_97,C_98,B_99] :
      ( k11_lattice3(A_97,C_98,B_99) = k11_lattice3(A_97,B_99,C_98)
      | ~ m1_subset_1(C_98,u1_struct_0(A_97))
      | ~ m1_subset_1(B_99,u1_struct_0(A_97))
      | ~ l1_orders_2(A_97)
      | ~ v2_lattice3(A_97)
      | ~ v5_orders_2(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_149,plain,(
    ! [A_50,C_98,B_99] :
      ( k11_lattice3(k2_yellow_1(A_50),C_98,B_99) = k11_lattice3(k2_yellow_1(A_50),B_99,C_98)
      | ~ m1_subset_1(C_98,A_50)
      | ~ m1_subset_1(B_99,u1_struct_0(k2_yellow_1(A_50)))
      | ~ l1_orders_2(k2_yellow_1(A_50))
      | ~ v2_lattice3(k2_yellow_1(A_50))
      | ~ v5_orders_2(k2_yellow_1(A_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_142])).

tff(c_154,plain,(
    ! [A_100,C_101,B_102] :
      ( k11_lattice3(k2_yellow_1(A_100),C_101,B_102) = k11_lattice3(k2_yellow_1(A_100),B_102,C_101)
      | ~ m1_subset_1(C_101,A_100)
      | ~ m1_subset_1(B_102,A_100)
      | ~ v2_lattice3(k2_yellow_1(A_100)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_28,c_38,c_149])).

tff(c_157,plain,(
    ! [C_101,B_102] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),C_101,B_102) = k11_lattice3(k2_yellow_1('#skF_1'),B_102,C_101)
      | ~ m1_subset_1(C_101,'#skF_1')
      | ~ m1_subset_1(B_102,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_52,c_154])).

tff(c_316,plain,(
    ! [A_127,B_128,C_129] :
      ( r3_orders_2(A_127,B_128,C_129)
      | k12_lattice3(A_127,B_128,C_129) != B_128
      | ~ m1_subset_1(C_129,u1_struct_0(A_127))
      | ~ m1_subset_1(B_128,u1_struct_0(A_127))
      | ~ l1_orders_2(A_127)
      | ~ v2_lattice3(A_127)
      | ~ v5_orders_2(A_127)
      | ~ v3_orders_2(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_323,plain,(
    ! [A_50,B_128,C_129] :
      ( r3_orders_2(k2_yellow_1(A_50),B_128,C_129)
      | k12_lattice3(k2_yellow_1(A_50),B_128,C_129) != B_128
      | ~ m1_subset_1(C_129,A_50)
      | ~ m1_subset_1(B_128,u1_struct_0(k2_yellow_1(A_50)))
      | ~ l1_orders_2(k2_yellow_1(A_50))
      | ~ v2_lattice3(k2_yellow_1(A_50))
      | ~ v5_orders_2(k2_yellow_1(A_50))
      | ~ v3_orders_2(k2_yellow_1(A_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_316])).

tff(c_328,plain,(
    ! [A_130,B_131,C_132] :
      ( r3_orders_2(k2_yellow_1(A_130),B_131,C_132)
      | k12_lattice3(k2_yellow_1(A_130),B_131,C_132) != B_131
      | ~ m1_subset_1(C_132,A_130)
      | ~ m1_subset_1(B_131,A_130)
      | ~ v2_lattice3(k2_yellow_1(A_130)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36,c_28,c_38,c_323])).

tff(c_338,plain,(
    ! [B_133,C_134,A_135] :
      ( r1_tarski(B_133,C_134)
      | v1_xboole_0(A_135)
      | k12_lattice3(k2_yellow_1(A_135),B_133,C_134) != B_133
      | ~ m1_subset_1(C_134,A_135)
      | ~ m1_subset_1(B_133,A_135)
      | ~ v2_lattice3(k2_yellow_1(A_135)) ) ),
    inference(resolution,[status(thm)],[c_328,c_57])).

tff(c_340,plain,(
    ! [B_117,C_118] :
      ( r1_tarski(B_117,C_118)
      | v1_xboole_0('#skF_1')
      | k11_lattice3(k2_yellow_1('#skF_1'),B_117,C_118) != B_117
      | ~ m1_subset_1(C_118,'#skF_1')
      | ~ m1_subset_1(B_117,'#skF_1')
      | ~ v2_lattice3(k2_yellow_1('#skF_1'))
      | ~ m1_subset_1(C_118,'#skF_1')
      | ~ m1_subset_1(B_117,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_338])).

tff(c_342,plain,(
    ! [B_117,C_118] :
      ( r1_tarski(B_117,C_118)
      | v1_xboole_0('#skF_1')
      | k11_lattice3(k2_yellow_1('#skF_1'),B_117,C_118) != B_117
      | ~ m1_subset_1(C_118,'#skF_1')
      | ~ m1_subset_1(B_117,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_340])).

tff(c_344,plain,(
    ! [B_136,C_137] :
      ( r1_tarski(B_136,C_137)
      | k11_lattice3(k2_yellow_1('#skF_1'),B_136,C_137) != B_136
      | ~ m1_subset_1(C_137,'#skF_1')
      | ~ m1_subset_1(B_136,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_342])).

tff(c_347,plain,(
    ! [B_102,C_101] :
      ( r1_tarski(B_102,C_101)
      | k11_lattice3(k2_yellow_1('#skF_1'),C_101,B_102) != B_102
      | ~ m1_subset_1(C_101,'#skF_1')
      | ~ m1_subset_1(B_102,'#skF_1')
      | ~ m1_subset_1(C_101,'#skF_1')
      | ~ m1_subset_1(B_102,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_344])).

tff(c_1300,plain,(
    ! [B_197,D_198] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),B_197,D_198),B_197)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'),B_197,D_198),'#skF_1')
      | ~ m1_subset_1(D_198,'#skF_1')
      | ~ m1_subset_1(B_197,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1141,c_347])).

tff(c_93,plain,(
    ! [A_72,B_73,C_74] :
      ( r1_tarski(A_72,k3_xboole_0(B_73,C_74))
      | ~ r1_tarski(A_72,C_74)
      | ~ r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2','#skF_3'),k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_97,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2','#skF_3'),'#skF_3')
    | ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_93,c_46])).

tff(c_104,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_1303,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2','#skF_3'),'#skF_1')
    | ~ m1_subset_1('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_1300,c_104])).

tff(c_1325,plain,(
    ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_56,c_1303])).

tff(c_1339,plain,
    ( ~ m1_subset_1('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_113,c_1325])).

tff(c_1349,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_56,c_1339])).

tff(c_1350,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2','#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_1527,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),'#skF_3')
    | ~ m1_subset_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1491,c_1350])).

tff(c_1561,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_55,c_1527])).

tff(c_2854,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),'#skF_1')
    | ~ m1_subset_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_2851,c_1561])).

tff(c_2876,plain,(
    ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_55,c_2854])).

tff(c_2896,plain,
    ( ~ m1_subset_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_1366,c_2876])).

tff(c_2902,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_55,c_2896])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:03:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.76/1.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.76/1.88  
% 4.76/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.76/1.88  %$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k12_lattice3 > k11_lattice3 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 4.76/1.88  
% 4.76/1.88  %Foreground sorts:
% 4.76/1.88  
% 4.76/1.88  
% 4.76/1.88  %Background operators:
% 4.76/1.88  
% 4.76/1.88  
% 4.76/1.88  %Foreground operators:
% 4.76/1.88  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 4.76/1.88  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.76/1.88  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 4.76/1.88  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.76/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.76/1.88  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 4.76/1.88  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 4.76/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.76/1.88  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 4.76/1.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.76/1.88  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 4.76/1.88  tff('#skF_2', type, '#skF_2': $i).
% 4.76/1.88  tff('#skF_3', type, '#skF_3': $i).
% 4.76/1.88  tff('#skF_1', type, '#skF_1': $i).
% 4.76/1.88  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.76/1.88  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.76/1.88  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.76/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.76/1.88  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 4.76/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.76/1.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.76/1.88  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 4.76/1.88  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 4.76/1.88  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.76/1.88  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.76/1.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.76/1.88  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.76/1.88  
% 5.09/1.91  tff(f_154, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 5.09/1.91  tff(f_181, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (v2_lattice3(k2_yellow_1(A)) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => r1_tarski(k11_lattice3(k2_yellow_1(A), B, C), k3_xboole_0(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_yellow_1)).
% 5.09/1.91  tff(f_142, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 5.09/1.91  tff(f_75, axiom, (![A, B, C]: (((l1_orders_2(A) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k11_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k11_lattice3)).
% 5.09/1.91  tff(f_150, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 5.09/1.91  tff(f_60, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, B, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_orders_2)).
% 5.09/1.91  tff(f_48, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 5.09/1.91  tff(f_167, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 5.09/1.91  tff(f_67, axiom, (![A]: (l1_orders_2(A) => (v2_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_lattice3)).
% 5.09/1.91  tff(f_138, axiom, (![A]: ((((v3_orders_2(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((B = k12_lattice3(A, B, C)) <=> r3_orders_2(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_yellow_0)).
% 5.09/1.91  tff(f_87, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 5.09/1.91  tff(f_120, axiom, (![A]: (((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (v4_orders_2(A) => (k11_lattice3(A, k11_lattice3(A, B, C), D) = k11_lattice3(A, B, k11_lattice3(A, C, D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_lattice3)).
% 5.09/1.91  tff(f_101, axiom, (![A]: (((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k11_lattice3(A, B, C) = k11_lattice3(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_lattice3)).
% 5.09/1.91  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 5.09/1.91  tff(c_38, plain, (![A_50]: (u1_struct_0(k2_yellow_1(A_50))=A_50)), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.09/1.91  tff(c_48, plain, (m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.09/1.91  tff(c_56, plain, (m1_subset_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_48])).
% 5.09/1.91  tff(c_50, plain, (m1_subset_1('#skF_2', u1_struct_0(k2_yellow_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.09/1.91  tff(c_55, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_50])).
% 5.09/1.91  tff(c_28, plain, (![A_48]: (l1_orders_2(k2_yellow_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.09/1.91  tff(c_1358, plain, (![A_205, B_206, C_207]: (m1_subset_1(k11_lattice3(A_205, B_206, C_207), u1_struct_0(A_205)) | ~m1_subset_1(C_207, u1_struct_0(A_205)) | ~m1_subset_1(B_206, u1_struct_0(A_205)) | ~l1_orders_2(A_205))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.09/1.91  tff(c_1363, plain, (![A_50, B_206, C_207]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_50), B_206, C_207), A_50) | ~m1_subset_1(C_207, u1_struct_0(k2_yellow_1(A_50))) | ~m1_subset_1(B_206, u1_struct_0(k2_yellow_1(A_50))) | ~l1_orders_2(k2_yellow_1(A_50)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1358])).
% 5.09/1.91  tff(c_1366, plain, (![A_50, B_206, C_207]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_50), B_206, C_207), A_50) | ~m1_subset_1(C_207, A_50) | ~m1_subset_1(B_206, A_50))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_38, c_38, c_1363])).
% 5.09/1.91  tff(c_52, plain, (v2_lattice3(k2_yellow_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.09/1.91  tff(c_54, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.09/1.91  tff(c_32, plain, (![A_49]: (v3_orders_2(k2_yellow_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.09/1.91  tff(c_98, plain, (![A_75, B_76]: (r1_orders_2(A_75, B_76, B_76) | ~m1_subset_1(B_76, u1_struct_0(A_75)) | ~l1_orders_2(A_75) | ~v3_orders_2(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.09/1.91  tff(c_100, plain, (![A_50, B_76]: (r1_orders_2(k2_yellow_1(A_50), B_76, B_76) | ~m1_subset_1(B_76, A_50) | ~l1_orders_2(k2_yellow_1(A_50)) | ~v3_orders_2(k2_yellow_1(A_50)) | v2_struct_0(k2_yellow_1(A_50)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_98])).
% 5.09/1.91  tff(c_102, plain, (![A_50, B_76]: (r1_orders_2(k2_yellow_1(A_50), B_76, B_76) | ~m1_subset_1(B_76, A_50) | v2_struct_0(k2_yellow_1(A_50)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_100])).
% 5.09/1.91  tff(c_1397, plain, (![A_219, B_220, C_221]: (r3_orders_2(A_219, B_220, C_221) | ~r1_orders_2(A_219, B_220, C_221) | ~m1_subset_1(C_221, u1_struct_0(A_219)) | ~m1_subset_1(B_220, u1_struct_0(A_219)) | ~l1_orders_2(A_219) | ~v3_orders_2(A_219) | v2_struct_0(A_219))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.09/1.91  tff(c_1404, plain, (![A_50, B_220, C_221]: (r3_orders_2(k2_yellow_1(A_50), B_220, C_221) | ~r1_orders_2(k2_yellow_1(A_50), B_220, C_221) | ~m1_subset_1(C_221, A_50) | ~m1_subset_1(B_220, u1_struct_0(k2_yellow_1(A_50))) | ~l1_orders_2(k2_yellow_1(A_50)) | ~v3_orders_2(k2_yellow_1(A_50)) | v2_struct_0(k2_yellow_1(A_50)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1397])).
% 5.09/1.91  tff(c_1415, plain, (![A_225, B_226, C_227]: (r3_orders_2(k2_yellow_1(A_225), B_226, C_227) | ~r1_orders_2(k2_yellow_1(A_225), B_226, C_227) | ~m1_subset_1(C_227, A_225) | ~m1_subset_1(B_226, A_225) | v2_struct_0(k2_yellow_1(A_225)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_38, c_1404])).
% 5.09/1.91  tff(c_44, plain, (![B_55, C_57, A_51]: (r1_tarski(B_55, C_57) | ~r3_orders_2(k2_yellow_1(A_51), B_55, C_57) | ~m1_subset_1(C_57, u1_struct_0(k2_yellow_1(A_51))) | ~m1_subset_1(B_55, u1_struct_0(k2_yellow_1(A_51))) | v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_167])).
% 5.09/1.91  tff(c_57, plain, (![B_55, C_57, A_51]: (r1_tarski(B_55, C_57) | ~r3_orders_2(k2_yellow_1(A_51), B_55, C_57) | ~m1_subset_1(C_57, A_51) | ~m1_subset_1(B_55, A_51) | v1_xboole_0(A_51))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_44])).
% 5.09/1.91  tff(c_1426, plain, (![B_231, C_232, A_233]: (r1_tarski(B_231, C_232) | v1_xboole_0(A_233) | ~r1_orders_2(k2_yellow_1(A_233), B_231, C_232) | ~m1_subset_1(C_232, A_233) | ~m1_subset_1(B_231, A_233) | v2_struct_0(k2_yellow_1(A_233)))), inference(resolution, [status(thm)], [c_1415, c_57])).
% 5.09/1.91  tff(c_1447, plain, (![B_237, A_238]: (r1_tarski(B_237, B_237) | v1_xboole_0(A_238) | ~m1_subset_1(B_237, A_238) | v2_struct_0(k2_yellow_1(A_238)))), inference(resolution, [status(thm)], [c_102, c_1426])).
% 5.09/1.91  tff(c_1453, plain, (r1_tarski('#skF_3', '#skF_3') | v1_xboole_0('#skF_1') | v2_struct_0(k2_yellow_1('#skF_1'))), inference(resolution, [status(thm)], [c_56, c_1447])).
% 5.09/1.91  tff(c_1460, plain, (r1_tarski('#skF_3', '#skF_3') | v2_struct_0(k2_yellow_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_54, c_1453])).
% 5.09/1.91  tff(c_1464, plain, (v2_struct_0(k2_yellow_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_1460])).
% 5.09/1.91  tff(c_12, plain, (![A_12]: (~v2_struct_0(A_12) | ~v2_lattice3(A_12) | ~l1_orders_2(A_12))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.09/1.91  tff(c_1467, plain, (~v2_lattice3(k2_yellow_1('#skF_1')) | ~l1_orders_2(k2_yellow_1('#skF_1'))), inference(resolution, [status(thm)], [c_1464, c_12])).
% 5.09/1.91  tff(c_1471, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_52, c_1467])).
% 5.09/1.91  tff(c_1473, plain, (~v2_struct_0(k2_yellow_1('#skF_1'))), inference(splitRight, [status(thm)], [c_1460])).
% 5.09/1.91  tff(c_36, plain, (![A_49]: (v5_orders_2(k2_yellow_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.09/1.91  tff(c_1408, plain, (![A_50, B_220, C_221]: (r3_orders_2(k2_yellow_1(A_50), B_220, C_221) | ~r1_orders_2(k2_yellow_1(A_50), B_220, C_221) | ~m1_subset_1(C_221, A_50) | ~m1_subset_1(B_220, A_50) | v2_struct_0(k2_yellow_1(A_50)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_38, c_1404])).
% 5.09/1.91  tff(c_1575, plain, (![A_247, B_248, C_249]: (k12_lattice3(A_247, B_248, C_249)=B_248 | ~r3_orders_2(A_247, B_248, C_249) | ~m1_subset_1(C_249, u1_struct_0(A_247)) | ~m1_subset_1(B_248, u1_struct_0(A_247)) | ~l1_orders_2(A_247) | ~v2_lattice3(A_247) | ~v5_orders_2(A_247) | ~v3_orders_2(A_247))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.09/1.91  tff(c_1577, plain, (![A_50, B_220, C_221]: (k12_lattice3(k2_yellow_1(A_50), B_220, C_221)=B_220 | ~m1_subset_1(C_221, u1_struct_0(k2_yellow_1(A_50))) | ~m1_subset_1(B_220, u1_struct_0(k2_yellow_1(A_50))) | ~l1_orders_2(k2_yellow_1(A_50)) | ~v2_lattice3(k2_yellow_1(A_50)) | ~v5_orders_2(k2_yellow_1(A_50)) | ~v3_orders_2(k2_yellow_1(A_50)) | ~r1_orders_2(k2_yellow_1(A_50), B_220, C_221) | ~m1_subset_1(C_221, A_50) | ~m1_subset_1(B_220, A_50) | v2_struct_0(k2_yellow_1(A_50)))), inference(resolution, [status(thm)], [c_1408, c_1575])).
% 5.09/1.91  tff(c_1759, plain, (![A_277, B_278, C_279]: (k12_lattice3(k2_yellow_1(A_277), B_278, C_279)=B_278 | ~v2_lattice3(k2_yellow_1(A_277)) | ~r1_orders_2(k2_yellow_1(A_277), B_278, C_279) | ~m1_subset_1(C_279, A_277) | ~m1_subset_1(B_278, A_277) | v2_struct_0(k2_yellow_1(A_277)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_36, c_28, c_38, c_38, c_1577])).
% 5.09/1.91  tff(c_1772, plain, (![A_280, B_281]: (k12_lattice3(k2_yellow_1(A_280), B_281, B_281)=B_281 | ~v2_lattice3(k2_yellow_1(A_280)) | ~m1_subset_1(B_281, A_280) | v2_struct_0(k2_yellow_1(A_280)))), inference(resolution, [status(thm)], [c_102, c_1759])).
% 5.09/1.91  tff(c_1372, plain, (![A_211, B_212, C_213]: (k12_lattice3(A_211, B_212, C_213)=k11_lattice3(A_211, B_212, C_213) | ~m1_subset_1(C_213, u1_struct_0(A_211)) | ~m1_subset_1(B_212, u1_struct_0(A_211)) | ~l1_orders_2(A_211) | ~v2_lattice3(A_211) | ~v5_orders_2(A_211))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.09/1.91  tff(c_1379, plain, (![A_50, B_212, C_213]: (k12_lattice3(k2_yellow_1(A_50), B_212, C_213)=k11_lattice3(k2_yellow_1(A_50), B_212, C_213) | ~m1_subset_1(C_213, A_50) | ~m1_subset_1(B_212, u1_struct_0(k2_yellow_1(A_50))) | ~l1_orders_2(k2_yellow_1(A_50)) | ~v2_lattice3(k2_yellow_1(A_50)) | ~v5_orders_2(k2_yellow_1(A_50)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1372])).
% 5.09/1.91  tff(c_1384, plain, (![A_214, B_215, C_216]: (k12_lattice3(k2_yellow_1(A_214), B_215, C_216)=k11_lattice3(k2_yellow_1(A_214), B_215, C_216) | ~m1_subset_1(C_216, A_214) | ~m1_subset_1(B_215, A_214) | ~v2_lattice3(k2_yellow_1(A_214)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_28, c_38, c_1379])).
% 5.09/1.91  tff(c_1387, plain, (![B_215, C_216]: (k12_lattice3(k2_yellow_1('#skF_1'), B_215, C_216)=k11_lattice3(k2_yellow_1('#skF_1'), B_215, C_216) | ~m1_subset_1(C_216, '#skF_1') | ~m1_subset_1(B_215, '#skF_1'))), inference(resolution, [status(thm)], [c_52, c_1384])).
% 5.09/1.91  tff(c_1785, plain, (![B_281]: (k11_lattice3(k2_yellow_1('#skF_1'), B_281, B_281)=B_281 | ~m1_subset_1(B_281, '#skF_1') | ~m1_subset_1(B_281, '#skF_1') | ~v2_lattice3(k2_yellow_1('#skF_1')) | ~m1_subset_1(B_281, '#skF_1') | v2_struct_0(k2_yellow_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1772, c_1387])).
% 5.09/1.91  tff(c_1810, plain, (![B_281]: (k11_lattice3(k2_yellow_1('#skF_1'), B_281, B_281)=B_281 | ~m1_subset_1(B_281, '#skF_1') | v2_struct_0(k2_yellow_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1785])).
% 5.09/1.91  tff(c_1811, plain, (![B_281]: (k11_lattice3(k2_yellow_1('#skF_1'), B_281, B_281)=B_281 | ~m1_subset_1(B_281, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_1473, c_1810])).
% 5.09/1.91  tff(c_34, plain, (![A_49]: (v4_orders_2(k2_yellow_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.09/1.91  tff(c_1683, plain, (![A_260, B_261, C_262, D_263]: (k11_lattice3(A_260, k11_lattice3(A_260, B_261, C_262), D_263)=k11_lattice3(A_260, B_261, k11_lattice3(A_260, C_262, D_263)) | ~v4_orders_2(A_260) | ~m1_subset_1(D_263, u1_struct_0(A_260)) | ~m1_subset_1(C_262, u1_struct_0(A_260)) | ~m1_subset_1(B_261, u1_struct_0(A_260)) | ~l1_orders_2(A_260) | ~v2_lattice3(A_260) | ~v5_orders_2(A_260))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.09/1.91  tff(c_1690, plain, (![A_50, B_261, C_262, D_263]: (k11_lattice3(k2_yellow_1(A_50), k11_lattice3(k2_yellow_1(A_50), B_261, C_262), D_263)=k11_lattice3(k2_yellow_1(A_50), B_261, k11_lattice3(k2_yellow_1(A_50), C_262, D_263)) | ~v4_orders_2(k2_yellow_1(A_50)) | ~m1_subset_1(D_263, A_50) | ~m1_subset_1(C_262, u1_struct_0(k2_yellow_1(A_50))) | ~m1_subset_1(B_261, u1_struct_0(k2_yellow_1(A_50))) | ~l1_orders_2(k2_yellow_1(A_50)) | ~v2_lattice3(k2_yellow_1(A_50)) | ~v5_orders_2(k2_yellow_1(A_50)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1683])).
% 5.09/1.91  tff(c_2024, plain, (![A_293, B_294, C_295, D_296]: (k11_lattice3(k2_yellow_1(A_293), k11_lattice3(k2_yellow_1(A_293), B_294, C_295), D_296)=k11_lattice3(k2_yellow_1(A_293), B_294, k11_lattice3(k2_yellow_1(A_293), C_295, D_296)) | ~m1_subset_1(D_296, A_293) | ~m1_subset_1(C_295, A_293) | ~m1_subset_1(B_294, A_293) | ~v2_lattice3(k2_yellow_1(A_293)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_28, c_38, c_38, c_34, c_1690])).
% 5.09/1.91  tff(c_2089, plain, (![B_281, D_296]: (k11_lattice3(k2_yellow_1('#skF_1'), B_281, k11_lattice3(k2_yellow_1('#skF_1'), B_281, D_296))=k11_lattice3(k2_yellow_1('#skF_1'), B_281, D_296) | ~m1_subset_1(D_296, '#skF_1') | ~m1_subset_1(B_281, '#skF_1') | ~m1_subset_1(B_281, '#skF_1') | ~v2_lattice3(k2_yellow_1('#skF_1')) | ~m1_subset_1(B_281, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1811, c_2024])).
% 5.09/1.91  tff(c_2381, plain, (![B_311, D_312]: (k11_lattice3(k2_yellow_1('#skF_1'), B_311, k11_lattice3(k2_yellow_1('#skF_1'), B_311, D_312))=k11_lattice3(k2_yellow_1('#skF_1'), B_311, D_312) | ~m1_subset_1(D_312, '#skF_1') | ~m1_subset_1(B_311, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2089])).
% 5.09/1.91  tff(c_1435, plain, (![A_234, C_235, B_236]: (k11_lattice3(A_234, C_235, B_236)=k11_lattice3(A_234, B_236, C_235) | ~m1_subset_1(C_235, u1_struct_0(A_234)) | ~m1_subset_1(B_236, u1_struct_0(A_234)) | ~l1_orders_2(A_234) | ~v2_lattice3(A_234) | ~v5_orders_2(A_234))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.09/1.91  tff(c_1442, plain, (![A_50, C_235, B_236]: (k11_lattice3(k2_yellow_1(A_50), C_235, B_236)=k11_lattice3(k2_yellow_1(A_50), B_236, C_235) | ~m1_subset_1(C_235, A_50) | ~m1_subset_1(B_236, u1_struct_0(k2_yellow_1(A_50))) | ~l1_orders_2(k2_yellow_1(A_50)) | ~v2_lattice3(k2_yellow_1(A_50)) | ~v5_orders_2(k2_yellow_1(A_50)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1435])).
% 5.09/1.91  tff(c_1487, plain, (![A_242, C_243, B_244]: (k11_lattice3(k2_yellow_1(A_242), C_243, B_244)=k11_lattice3(k2_yellow_1(A_242), B_244, C_243) | ~m1_subset_1(C_243, A_242) | ~m1_subset_1(B_244, A_242) | ~v2_lattice3(k2_yellow_1(A_242)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_28, c_38, c_1442])).
% 5.09/1.91  tff(c_1490, plain, (![C_243, B_244]: (k11_lattice3(k2_yellow_1('#skF_1'), C_243, B_244)=k11_lattice3(k2_yellow_1('#skF_1'), B_244, C_243) | ~m1_subset_1(C_243, '#skF_1') | ~m1_subset_1(B_244, '#skF_1'))), inference(resolution, [status(thm)], [c_52, c_1487])).
% 5.09/1.91  tff(c_1474, plain, (![A_239, B_240, C_241]: (r3_orders_2(A_239, B_240, C_241) | k12_lattice3(A_239, B_240, C_241)!=B_240 | ~m1_subset_1(C_241, u1_struct_0(A_239)) | ~m1_subset_1(B_240, u1_struct_0(A_239)) | ~l1_orders_2(A_239) | ~v2_lattice3(A_239) | ~v5_orders_2(A_239) | ~v3_orders_2(A_239))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.09/1.91  tff(c_1481, plain, (![A_50, B_240, C_241]: (r3_orders_2(k2_yellow_1(A_50), B_240, C_241) | k12_lattice3(k2_yellow_1(A_50), B_240, C_241)!=B_240 | ~m1_subset_1(C_241, A_50) | ~m1_subset_1(B_240, u1_struct_0(k2_yellow_1(A_50))) | ~l1_orders_2(k2_yellow_1(A_50)) | ~v2_lattice3(k2_yellow_1(A_50)) | ~v5_orders_2(k2_yellow_1(A_50)) | ~v3_orders_2(k2_yellow_1(A_50)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1474])).
% 5.09/1.91  tff(c_1668, plain, (![A_257, B_258, C_259]: (r3_orders_2(k2_yellow_1(A_257), B_258, C_259) | k12_lattice3(k2_yellow_1(A_257), B_258, C_259)!=B_258 | ~m1_subset_1(C_259, A_257) | ~m1_subset_1(B_258, A_257) | ~v2_lattice3(k2_yellow_1(A_257)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_36, c_28, c_38, c_1481])).
% 5.09/1.91  tff(c_1695, plain, (![B_264, C_265, A_266]: (r1_tarski(B_264, C_265) | v1_xboole_0(A_266) | k12_lattice3(k2_yellow_1(A_266), B_264, C_265)!=B_264 | ~m1_subset_1(C_265, A_266) | ~m1_subset_1(B_264, A_266) | ~v2_lattice3(k2_yellow_1(A_266)))), inference(resolution, [status(thm)], [c_1668, c_57])).
% 5.09/1.91  tff(c_1699, plain, (![B_215, C_216]: (r1_tarski(B_215, C_216) | v1_xboole_0('#skF_1') | k11_lattice3(k2_yellow_1('#skF_1'), B_215, C_216)!=B_215 | ~m1_subset_1(C_216, '#skF_1') | ~m1_subset_1(B_215, '#skF_1') | ~v2_lattice3(k2_yellow_1('#skF_1')) | ~m1_subset_1(C_216, '#skF_1') | ~m1_subset_1(B_215, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1387, c_1695])).
% 5.09/1.91  tff(c_1705, plain, (![B_215, C_216]: (r1_tarski(B_215, C_216) | v1_xboole_0('#skF_1') | k11_lattice3(k2_yellow_1('#skF_1'), B_215, C_216)!=B_215 | ~m1_subset_1(C_216, '#skF_1') | ~m1_subset_1(B_215, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1699])).
% 5.09/1.91  tff(c_1707, plain, (![B_267, C_268]: (r1_tarski(B_267, C_268) | k11_lattice3(k2_yellow_1('#skF_1'), B_267, C_268)!=B_267 | ~m1_subset_1(C_268, '#skF_1') | ~m1_subset_1(B_267, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_54, c_1705])).
% 5.09/1.91  tff(c_1713, plain, (![B_244, C_243]: (r1_tarski(B_244, C_243) | k11_lattice3(k2_yellow_1('#skF_1'), C_243, B_244)!=B_244 | ~m1_subset_1(C_243, '#skF_1') | ~m1_subset_1(B_244, '#skF_1') | ~m1_subset_1(C_243, '#skF_1') | ~m1_subset_1(B_244, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1490, c_1707])).
% 5.09/1.91  tff(c_2851, plain, (![B_334, D_335]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), B_334, D_335), B_334) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'), B_334, D_335), '#skF_1') | ~m1_subset_1(D_335, '#skF_1') | ~m1_subset_1(B_334, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2381, c_1713])).
% 5.09/1.91  tff(c_1491, plain, (![C_245, B_246]: (k11_lattice3(k2_yellow_1('#skF_1'), C_245, B_246)=k11_lattice3(k2_yellow_1('#skF_1'), B_246, C_245) | ~m1_subset_1(C_245, '#skF_1') | ~m1_subset_1(B_246, '#skF_1'))), inference(resolution, [status(thm)], [c_52, c_1487])).
% 5.09/1.91  tff(c_105, plain, (![A_79, B_80, C_81]: (m1_subset_1(k11_lattice3(A_79, B_80, C_81), u1_struct_0(A_79)) | ~m1_subset_1(C_81, u1_struct_0(A_79)) | ~m1_subset_1(B_80, u1_struct_0(A_79)) | ~l1_orders_2(A_79))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.09/1.91  tff(c_110, plain, (![A_50, B_80, C_81]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_50), B_80, C_81), A_50) | ~m1_subset_1(C_81, u1_struct_0(k2_yellow_1(A_50))) | ~m1_subset_1(B_80, u1_struct_0(k2_yellow_1(A_50))) | ~l1_orders_2(k2_yellow_1(A_50)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_105])).
% 5.09/1.91  tff(c_113, plain, (![A_50, B_80, C_81]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_50), B_80, C_81), A_50) | ~m1_subset_1(C_81, A_50) | ~m1_subset_1(B_80, A_50))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_38, c_38, c_110])).
% 5.09/1.91  tff(c_125, plain, (![A_91, B_92, C_93]: (r3_orders_2(A_91, B_92, C_93) | ~r1_orders_2(A_91, B_92, C_93) | ~m1_subset_1(C_93, u1_struct_0(A_91)) | ~m1_subset_1(B_92, u1_struct_0(A_91)) | ~l1_orders_2(A_91) | ~v3_orders_2(A_91) | v2_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.09/1.91  tff(c_132, plain, (![A_50, B_92, C_93]: (r3_orders_2(k2_yellow_1(A_50), B_92, C_93) | ~r1_orders_2(k2_yellow_1(A_50), B_92, C_93) | ~m1_subset_1(C_93, A_50) | ~m1_subset_1(B_92, u1_struct_0(k2_yellow_1(A_50))) | ~l1_orders_2(k2_yellow_1(A_50)) | ~v3_orders_2(k2_yellow_1(A_50)) | v2_struct_0(k2_yellow_1(A_50)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_125])).
% 5.09/1.91  tff(c_137, plain, (![A_94, B_95, C_96]: (r3_orders_2(k2_yellow_1(A_94), B_95, C_96) | ~r1_orders_2(k2_yellow_1(A_94), B_95, C_96) | ~m1_subset_1(C_96, A_94) | ~m1_subset_1(B_95, A_94) | v2_struct_0(k2_yellow_1(A_94)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_38, c_132])).
% 5.09/1.91  tff(c_231, plain, (![B_105, C_106, A_107]: (r1_tarski(B_105, C_106) | v1_xboole_0(A_107) | ~r1_orders_2(k2_yellow_1(A_107), B_105, C_106) | ~m1_subset_1(C_106, A_107) | ~m1_subset_1(B_105, A_107) | v2_struct_0(k2_yellow_1(A_107)))), inference(resolution, [status(thm)], [c_137, c_57])).
% 5.09/1.91  tff(c_236, plain, (![B_108, A_109]: (r1_tarski(B_108, B_108) | v1_xboole_0(A_109) | ~m1_subset_1(B_108, A_109) | v2_struct_0(k2_yellow_1(A_109)))), inference(resolution, [status(thm)], [c_102, c_231])).
% 5.09/1.91  tff(c_242, plain, (r1_tarski('#skF_3', '#skF_3') | v1_xboole_0('#skF_1') | v2_struct_0(k2_yellow_1('#skF_1'))), inference(resolution, [status(thm)], [c_56, c_236])).
% 5.09/1.91  tff(c_249, plain, (r1_tarski('#skF_3', '#skF_3') | v2_struct_0(k2_yellow_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_54, c_242])).
% 5.09/1.91  tff(c_253, plain, (v2_struct_0(k2_yellow_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_249])).
% 5.09/1.91  tff(c_267, plain, (~v2_lattice3(k2_yellow_1('#skF_1')) | ~l1_orders_2(k2_yellow_1('#skF_1'))), inference(resolution, [status(thm)], [c_253, c_12])).
% 5.09/1.91  tff(c_271, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_52, c_267])).
% 5.09/1.91  tff(c_273, plain, (~v2_struct_0(k2_yellow_1('#skF_1'))), inference(splitRight, [status(thm)], [c_249])).
% 5.09/1.91  tff(c_136, plain, (![A_50, B_92, C_93]: (r3_orders_2(k2_yellow_1(A_50), B_92, C_93) | ~r1_orders_2(k2_yellow_1(A_50), B_92, C_93) | ~m1_subset_1(C_93, A_50) | ~m1_subset_1(B_92, A_50) | v2_struct_0(k2_yellow_1(A_50)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_38, c_132])).
% 5.09/1.91  tff(c_393, plain, (![A_148, B_149, C_150]: (k12_lattice3(A_148, B_149, C_150)=B_149 | ~r3_orders_2(A_148, B_149, C_150) | ~m1_subset_1(C_150, u1_struct_0(A_148)) | ~m1_subset_1(B_149, u1_struct_0(A_148)) | ~l1_orders_2(A_148) | ~v2_lattice3(A_148) | ~v5_orders_2(A_148) | ~v3_orders_2(A_148))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.09/1.91  tff(c_397, plain, (![A_50, B_92, C_93]: (k12_lattice3(k2_yellow_1(A_50), B_92, C_93)=B_92 | ~m1_subset_1(C_93, u1_struct_0(k2_yellow_1(A_50))) | ~m1_subset_1(B_92, u1_struct_0(k2_yellow_1(A_50))) | ~l1_orders_2(k2_yellow_1(A_50)) | ~v2_lattice3(k2_yellow_1(A_50)) | ~v5_orders_2(k2_yellow_1(A_50)) | ~v3_orders_2(k2_yellow_1(A_50)) | ~r1_orders_2(k2_yellow_1(A_50), B_92, C_93) | ~m1_subset_1(C_93, A_50) | ~m1_subset_1(B_92, A_50) | v2_struct_0(k2_yellow_1(A_50)))), inference(resolution, [status(thm)], [c_136, c_393])).
% 5.09/1.91  tff(c_519, plain, (![A_162, B_163, C_164]: (k12_lattice3(k2_yellow_1(A_162), B_163, C_164)=B_163 | ~v2_lattice3(k2_yellow_1(A_162)) | ~r1_orders_2(k2_yellow_1(A_162), B_163, C_164) | ~m1_subset_1(C_164, A_162) | ~m1_subset_1(B_163, A_162) | v2_struct_0(k2_yellow_1(A_162)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_36, c_28, c_38, c_38, c_397])).
% 5.09/1.91  tff(c_532, plain, (![A_165, B_166]: (k12_lattice3(k2_yellow_1(A_165), B_166, B_166)=B_166 | ~v2_lattice3(k2_yellow_1(A_165)) | ~m1_subset_1(B_166, A_165) | v2_struct_0(k2_yellow_1(A_165)))), inference(resolution, [status(thm)], [c_102, c_519])).
% 5.09/1.91  tff(c_275, plain, (![A_113, B_114, C_115]: (k12_lattice3(A_113, B_114, C_115)=k11_lattice3(A_113, B_114, C_115) | ~m1_subset_1(C_115, u1_struct_0(A_113)) | ~m1_subset_1(B_114, u1_struct_0(A_113)) | ~l1_orders_2(A_113) | ~v2_lattice3(A_113) | ~v5_orders_2(A_113))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.09/1.91  tff(c_282, plain, (![A_50, B_114, C_115]: (k12_lattice3(k2_yellow_1(A_50), B_114, C_115)=k11_lattice3(k2_yellow_1(A_50), B_114, C_115) | ~m1_subset_1(C_115, A_50) | ~m1_subset_1(B_114, u1_struct_0(k2_yellow_1(A_50))) | ~l1_orders_2(k2_yellow_1(A_50)) | ~v2_lattice3(k2_yellow_1(A_50)) | ~v5_orders_2(k2_yellow_1(A_50)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_275])).
% 5.09/1.91  tff(c_287, plain, (![A_116, B_117, C_118]: (k12_lattice3(k2_yellow_1(A_116), B_117, C_118)=k11_lattice3(k2_yellow_1(A_116), B_117, C_118) | ~m1_subset_1(C_118, A_116) | ~m1_subset_1(B_117, A_116) | ~v2_lattice3(k2_yellow_1(A_116)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_28, c_38, c_282])).
% 5.09/1.91  tff(c_290, plain, (![B_117, C_118]: (k12_lattice3(k2_yellow_1('#skF_1'), B_117, C_118)=k11_lattice3(k2_yellow_1('#skF_1'), B_117, C_118) | ~m1_subset_1(C_118, '#skF_1') | ~m1_subset_1(B_117, '#skF_1'))), inference(resolution, [status(thm)], [c_52, c_287])).
% 5.09/1.91  tff(c_545, plain, (![B_166]: (k11_lattice3(k2_yellow_1('#skF_1'), B_166, B_166)=B_166 | ~m1_subset_1(B_166, '#skF_1') | ~m1_subset_1(B_166, '#skF_1') | ~v2_lattice3(k2_yellow_1('#skF_1')) | ~m1_subset_1(B_166, '#skF_1') | v2_struct_0(k2_yellow_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_532, c_290])).
% 5.09/1.91  tff(c_570, plain, (![B_166]: (k11_lattice3(k2_yellow_1('#skF_1'), B_166, B_166)=B_166 | ~m1_subset_1(B_166, '#skF_1') | v2_struct_0(k2_yellow_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_545])).
% 5.09/1.91  tff(c_571, plain, (![B_166]: (k11_lattice3(k2_yellow_1('#skF_1'), B_166, B_166)=B_166 | ~m1_subset_1(B_166, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_273, c_570])).
% 5.09/1.91  tff(c_507, plain, (![A_158, B_159, C_160, D_161]: (k11_lattice3(A_158, k11_lattice3(A_158, B_159, C_160), D_161)=k11_lattice3(A_158, B_159, k11_lattice3(A_158, C_160, D_161)) | ~v4_orders_2(A_158) | ~m1_subset_1(D_161, u1_struct_0(A_158)) | ~m1_subset_1(C_160, u1_struct_0(A_158)) | ~m1_subset_1(B_159, u1_struct_0(A_158)) | ~l1_orders_2(A_158) | ~v2_lattice3(A_158) | ~v5_orders_2(A_158))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.09/1.91  tff(c_514, plain, (![A_50, B_159, C_160, D_161]: (k11_lattice3(k2_yellow_1(A_50), k11_lattice3(k2_yellow_1(A_50), B_159, C_160), D_161)=k11_lattice3(k2_yellow_1(A_50), B_159, k11_lattice3(k2_yellow_1(A_50), C_160, D_161)) | ~v4_orders_2(k2_yellow_1(A_50)) | ~m1_subset_1(D_161, A_50) | ~m1_subset_1(C_160, u1_struct_0(k2_yellow_1(A_50))) | ~m1_subset_1(B_159, u1_struct_0(k2_yellow_1(A_50))) | ~l1_orders_2(k2_yellow_1(A_50)) | ~v2_lattice3(k2_yellow_1(A_50)) | ~v5_orders_2(k2_yellow_1(A_50)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_507])).
% 5.09/1.91  tff(c_887, plain, (![A_186, B_187, C_188, D_189]: (k11_lattice3(k2_yellow_1(A_186), k11_lattice3(k2_yellow_1(A_186), B_187, C_188), D_189)=k11_lattice3(k2_yellow_1(A_186), B_187, k11_lattice3(k2_yellow_1(A_186), C_188, D_189)) | ~m1_subset_1(D_189, A_186) | ~m1_subset_1(C_188, A_186) | ~m1_subset_1(B_187, A_186) | ~v2_lattice3(k2_yellow_1(A_186)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_28, c_38, c_38, c_34, c_514])).
% 5.09/1.91  tff(c_984, plain, (![B_166, D_189]: (k11_lattice3(k2_yellow_1('#skF_1'), B_166, k11_lattice3(k2_yellow_1('#skF_1'), B_166, D_189))=k11_lattice3(k2_yellow_1('#skF_1'), B_166, D_189) | ~m1_subset_1(D_189, '#skF_1') | ~m1_subset_1(B_166, '#skF_1') | ~m1_subset_1(B_166, '#skF_1') | ~v2_lattice3(k2_yellow_1('#skF_1')) | ~m1_subset_1(B_166, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_571, c_887])).
% 5.09/1.91  tff(c_1141, plain, (![B_194, D_195]: (k11_lattice3(k2_yellow_1('#skF_1'), B_194, k11_lattice3(k2_yellow_1('#skF_1'), B_194, D_195))=k11_lattice3(k2_yellow_1('#skF_1'), B_194, D_195) | ~m1_subset_1(D_195, '#skF_1') | ~m1_subset_1(B_194, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_984])).
% 5.09/1.91  tff(c_142, plain, (![A_97, C_98, B_99]: (k11_lattice3(A_97, C_98, B_99)=k11_lattice3(A_97, B_99, C_98) | ~m1_subset_1(C_98, u1_struct_0(A_97)) | ~m1_subset_1(B_99, u1_struct_0(A_97)) | ~l1_orders_2(A_97) | ~v2_lattice3(A_97) | ~v5_orders_2(A_97))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.09/1.91  tff(c_149, plain, (![A_50, C_98, B_99]: (k11_lattice3(k2_yellow_1(A_50), C_98, B_99)=k11_lattice3(k2_yellow_1(A_50), B_99, C_98) | ~m1_subset_1(C_98, A_50) | ~m1_subset_1(B_99, u1_struct_0(k2_yellow_1(A_50))) | ~l1_orders_2(k2_yellow_1(A_50)) | ~v2_lattice3(k2_yellow_1(A_50)) | ~v5_orders_2(k2_yellow_1(A_50)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_142])).
% 5.09/1.91  tff(c_154, plain, (![A_100, C_101, B_102]: (k11_lattice3(k2_yellow_1(A_100), C_101, B_102)=k11_lattice3(k2_yellow_1(A_100), B_102, C_101) | ~m1_subset_1(C_101, A_100) | ~m1_subset_1(B_102, A_100) | ~v2_lattice3(k2_yellow_1(A_100)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_28, c_38, c_149])).
% 5.09/1.91  tff(c_157, plain, (![C_101, B_102]: (k11_lattice3(k2_yellow_1('#skF_1'), C_101, B_102)=k11_lattice3(k2_yellow_1('#skF_1'), B_102, C_101) | ~m1_subset_1(C_101, '#skF_1') | ~m1_subset_1(B_102, '#skF_1'))), inference(resolution, [status(thm)], [c_52, c_154])).
% 5.09/1.91  tff(c_316, plain, (![A_127, B_128, C_129]: (r3_orders_2(A_127, B_128, C_129) | k12_lattice3(A_127, B_128, C_129)!=B_128 | ~m1_subset_1(C_129, u1_struct_0(A_127)) | ~m1_subset_1(B_128, u1_struct_0(A_127)) | ~l1_orders_2(A_127) | ~v2_lattice3(A_127) | ~v5_orders_2(A_127) | ~v3_orders_2(A_127))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.09/1.91  tff(c_323, plain, (![A_50, B_128, C_129]: (r3_orders_2(k2_yellow_1(A_50), B_128, C_129) | k12_lattice3(k2_yellow_1(A_50), B_128, C_129)!=B_128 | ~m1_subset_1(C_129, A_50) | ~m1_subset_1(B_128, u1_struct_0(k2_yellow_1(A_50))) | ~l1_orders_2(k2_yellow_1(A_50)) | ~v2_lattice3(k2_yellow_1(A_50)) | ~v5_orders_2(k2_yellow_1(A_50)) | ~v3_orders_2(k2_yellow_1(A_50)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_316])).
% 5.09/1.91  tff(c_328, plain, (![A_130, B_131, C_132]: (r3_orders_2(k2_yellow_1(A_130), B_131, C_132) | k12_lattice3(k2_yellow_1(A_130), B_131, C_132)!=B_131 | ~m1_subset_1(C_132, A_130) | ~m1_subset_1(B_131, A_130) | ~v2_lattice3(k2_yellow_1(A_130)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_36, c_28, c_38, c_323])).
% 5.09/1.91  tff(c_338, plain, (![B_133, C_134, A_135]: (r1_tarski(B_133, C_134) | v1_xboole_0(A_135) | k12_lattice3(k2_yellow_1(A_135), B_133, C_134)!=B_133 | ~m1_subset_1(C_134, A_135) | ~m1_subset_1(B_133, A_135) | ~v2_lattice3(k2_yellow_1(A_135)))), inference(resolution, [status(thm)], [c_328, c_57])).
% 5.09/1.91  tff(c_340, plain, (![B_117, C_118]: (r1_tarski(B_117, C_118) | v1_xboole_0('#skF_1') | k11_lattice3(k2_yellow_1('#skF_1'), B_117, C_118)!=B_117 | ~m1_subset_1(C_118, '#skF_1') | ~m1_subset_1(B_117, '#skF_1') | ~v2_lattice3(k2_yellow_1('#skF_1')) | ~m1_subset_1(C_118, '#skF_1') | ~m1_subset_1(B_117, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_290, c_338])).
% 5.09/1.91  tff(c_342, plain, (![B_117, C_118]: (r1_tarski(B_117, C_118) | v1_xboole_0('#skF_1') | k11_lattice3(k2_yellow_1('#skF_1'), B_117, C_118)!=B_117 | ~m1_subset_1(C_118, '#skF_1') | ~m1_subset_1(B_117, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_340])).
% 5.09/1.91  tff(c_344, plain, (![B_136, C_137]: (r1_tarski(B_136, C_137) | k11_lattice3(k2_yellow_1('#skF_1'), B_136, C_137)!=B_136 | ~m1_subset_1(C_137, '#skF_1') | ~m1_subset_1(B_136, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_54, c_342])).
% 5.09/1.91  tff(c_347, plain, (![B_102, C_101]: (r1_tarski(B_102, C_101) | k11_lattice3(k2_yellow_1('#skF_1'), C_101, B_102)!=B_102 | ~m1_subset_1(C_101, '#skF_1') | ~m1_subset_1(B_102, '#skF_1') | ~m1_subset_1(C_101, '#skF_1') | ~m1_subset_1(B_102, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_157, c_344])).
% 5.09/1.91  tff(c_1300, plain, (![B_197, D_198]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), B_197, D_198), B_197) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'), B_197, D_198), '#skF_1') | ~m1_subset_1(D_198, '#skF_1') | ~m1_subset_1(B_197, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1141, c_347])).
% 5.09/1.91  tff(c_93, plain, (![A_72, B_73, C_74]: (r1_tarski(A_72, k3_xboole_0(B_73, C_74)) | ~r1_tarski(A_72, C_74) | ~r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.09/1.91  tff(c_46, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', '#skF_3'), k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.09/1.91  tff(c_97, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', '#skF_3'), '#skF_3') | ~r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_93, c_46])).
% 5.09/1.91  tff(c_104, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_97])).
% 5.09/1.91  tff(c_1303, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', '#skF_3'), '#skF_1') | ~m1_subset_1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_1300, c_104])).
% 5.09/1.91  tff(c_1325, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_56, c_1303])).
% 5.09/1.91  tff(c_1339, plain, (~m1_subset_1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_113, c_1325])).
% 5.09/1.91  tff(c_1349, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_56, c_1339])).
% 5.09/1.91  tff(c_1350, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_97])).
% 5.09/1.91  tff(c_1527, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), '#skF_3') | ~m1_subset_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1491, c_1350])).
% 5.09/1.91  tff(c_1561, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_55, c_1527])).
% 5.09/1.91  tff(c_2854, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), '#skF_1') | ~m1_subset_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_2851, c_1561])).
% 5.09/1.91  tff(c_2876, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_55, c_2854])).
% 5.09/1.91  tff(c_2896, plain, (~m1_subset_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_1366, c_2876])).
% 5.09/1.91  tff(c_2902, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_55, c_2896])).
% 5.09/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.09/1.91  
% 5.09/1.91  Inference rules
% 5.09/1.91  ----------------------
% 5.09/1.91  #Ref     : 0
% 5.09/1.91  #Sup     : 606
% 5.09/1.91  #Fact    : 0
% 5.09/1.91  #Define  : 0
% 5.09/1.91  #Split   : 3
% 5.09/1.91  #Chain   : 0
% 5.09/1.91  #Close   : 0
% 5.09/1.91  
% 5.09/1.91  Ordering : KBO
% 5.09/1.91  
% 5.09/1.91  Simplification rules
% 5.09/1.91  ----------------------
% 5.09/1.91  #Subsume      : 146
% 5.09/1.91  #Demod        : 556
% 5.09/1.91  #Tautology    : 113
% 5.09/1.91  #SimpNegUnit  : 116
% 5.09/1.91  #BackRed      : 0
% 5.09/1.91  
% 5.09/1.91  #Partial instantiations: 0
% 5.09/1.91  #Strategies tried      : 1
% 5.09/1.91  
% 5.09/1.91  Timing (in seconds)
% 5.09/1.91  ----------------------
% 5.09/1.91  Preprocessing        : 0.35
% 5.09/1.91  Parsing              : 0.19
% 5.09/1.91  CNF conversion       : 0.03
% 5.09/1.91  Main loop            : 0.75
% 5.09/1.91  Inferencing          : 0.28
% 5.09/1.91  Reduction            : 0.24
% 5.09/1.91  Demodulation         : 0.17
% 5.09/1.91  BG Simplification    : 0.04
% 5.09/1.91  Subsumption          : 0.13
% 5.09/1.91  Abstraction          : 0.04
% 5.09/1.91  MUC search           : 0.00
% 5.09/1.91  Cooper               : 0.00
% 5.09/1.91  Total                : 1.15
% 5.09/1.91  Index Insertion      : 0.00
% 5.09/1.91  Index Deletion       : 0.00
% 5.09/1.91  Index Matching       : 0.00
% 5.09/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
