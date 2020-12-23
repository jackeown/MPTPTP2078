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
% DateTime   : Thu Dec  3 10:20:22 EST 2020

% Result     : Theorem 7.42s
% Output     : CNFRefutation 7.42s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 161 expanded)
%              Number of leaves         :   35 (  68 expanded)
%              Depth                    :   13
%              Number of atoms          :  141 ( 309 expanded)
%              Number of equality atoms :   20 (  47 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => k2_pre_topc(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tops_1)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => v1_xboole_0(k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_struct_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_64,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_66,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

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

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = k3_subset_1(u1_struct_0(A),k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_pre_topc)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(c_48,plain,(
    k2_pre_topc('#skF_3',k2_struct_0('#skF_3')) != k2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_50,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_40,plain,(
    ! [A_30] :
      ( l1_struct_0(A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_42,plain,(
    ! [A_31] :
      ( v1_xboole_0(k1_struct_0(A_31))
      | ~ l1_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    ! [A_16] : k2_subset_1(A_16) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24,plain,(
    ! [A_17] : m1_subset_1(k2_subset_1(A_17),k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_51,plain,(
    ! [A_17] : m1_subset_1(A_17,k1_zfmisc_1(A_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24])).

tff(c_103,plain,(
    ! [C_57,B_58,A_59] :
      ( ~ v1_xboole_0(C_57)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(C_57))
      | ~ r2_hidden(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_113,plain,(
    ! [A_60,A_61] :
      ( ~ v1_xboole_0(A_60)
      | ~ r2_hidden(A_61,A_60) ) ),
    inference(resolution,[status(thm)],[c_51,c_103])).

tff(c_123,plain,(
    ! [A_1,B_2] :
      ( ~ v1_xboole_0(A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_113])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_124,plain,(
    ! [B_7,A_6] :
      ( ~ v1_xboole_0(B_7)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_113])).

tff(c_32,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(A_22,k1_zfmisc_1(B_23))
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_44,plain,(
    ! [A_32] :
      ( k3_subset_1(u1_struct_0(A_32),k1_struct_0(A_32)) = k2_struct_0(A_32)
      | ~ l1_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_452,plain,(
    ! [B_134,A_135,C_136] :
      ( r1_tarski(B_134,k3_subset_1(A_135,C_136))
      | ~ r1_xboole_0(B_134,C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(A_135))
      | ~ m1_subset_1(B_134,k1_zfmisc_1(A_135)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1878,plain,(
    ! [B_295,A_296] :
      ( r1_tarski(B_295,k2_struct_0(A_296))
      | ~ r1_xboole_0(B_295,k1_struct_0(A_296))
      | ~ m1_subset_1(k1_struct_0(A_296),k1_zfmisc_1(u1_struct_0(A_296)))
      | ~ m1_subset_1(B_295,k1_zfmisc_1(u1_struct_0(A_296)))
      | ~ l1_struct_0(A_296) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_452])).

tff(c_3484,plain,(
    ! [B_466,A_467] :
      ( r1_tarski(B_466,k2_struct_0(A_467))
      | ~ r1_xboole_0(B_466,k1_struct_0(A_467))
      | ~ m1_subset_1(B_466,k1_zfmisc_1(u1_struct_0(A_467)))
      | ~ l1_struct_0(A_467)
      | ~ r1_tarski(k1_struct_0(A_467),u1_struct_0(A_467)) ) ),
    inference(resolution,[status(thm)],[c_32,c_1878])).

tff(c_4101,plain,(
    ! [A_553] :
      ( r1_tarski(u1_struct_0(A_553),k2_struct_0(A_553))
      | ~ r1_xboole_0(u1_struct_0(A_553),k1_struct_0(A_553))
      | ~ l1_struct_0(A_553)
      | ~ r1_tarski(k1_struct_0(A_553),u1_struct_0(A_553)) ) ),
    inference(resolution,[status(thm)],[c_51,c_3484])).

tff(c_4110,plain,(
    ! [A_554] :
      ( r1_tarski(u1_struct_0(A_554),k2_struct_0(A_554))
      | ~ l1_struct_0(A_554)
      | ~ r1_tarski(k1_struct_0(A_554),u1_struct_0(A_554))
      | ~ v1_xboole_0(k1_struct_0(A_554)) ) ),
    inference(resolution,[status(thm)],[c_124,c_4101])).

tff(c_77,plain,(
    ! [A_45] :
      ( m1_subset_1(k2_struct_0(A_45),k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_30,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ m1_subset_1(A_22,k1_zfmisc_1(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_81,plain,(
    ! [A_45] :
      ( r1_tarski(k2_struct_0(A_45),u1_struct_0(A_45))
      | ~ l1_struct_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_77,c_30])).

tff(c_85,plain,(
    ! [B_51,A_52] :
      ( B_51 = A_52
      | ~ r1_tarski(B_51,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_90,plain,(
    ! [A_45] :
      ( u1_struct_0(A_45) = k2_struct_0(A_45)
      | ~ r1_tarski(u1_struct_0(A_45),k2_struct_0(A_45))
      | ~ l1_struct_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_81,c_85])).

tff(c_4326,plain,(
    ! [A_557] :
      ( u1_struct_0(A_557) = k2_struct_0(A_557)
      | ~ l1_struct_0(A_557)
      | ~ r1_tarski(k1_struct_0(A_557),u1_struct_0(A_557))
      | ~ v1_xboole_0(k1_struct_0(A_557)) ) ),
    inference(resolution,[status(thm)],[c_4110,c_90])).

tff(c_4336,plain,(
    ! [A_558] :
      ( u1_struct_0(A_558) = k2_struct_0(A_558)
      | ~ l1_struct_0(A_558)
      | ~ v1_xboole_0(k1_struct_0(A_558)) ) ),
    inference(resolution,[status(thm)],[c_123,c_4326])).

tff(c_4341,plain,(
    ! [A_559] :
      ( u1_struct_0(A_559) = k2_struct_0(A_559)
      | ~ l1_struct_0(A_559) ) ),
    inference(resolution,[status(thm)],[c_42,c_4336])).

tff(c_4346,plain,(
    ! [A_560] :
      ( u1_struct_0(A_560) = k2_struct_0(A_560)
      | ~ l1_pre_topc(A_560) ) ),
    inference(resolution,[status(thm)],[c_40,c_4341])).

tff(c_4350,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_4346])).

tff(c_18,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_324,plain,(
    ! [A_114,B_115] :
      ( m1_subset_1(k2_pre_topc(A_114,B_115),k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_334,plain,(
    ! [A_114,B_115] :
      ( r1_tarski(k2_pre_topc(A_114,B_115),u1_struct_0(A_114))
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(resolution,[status(thm)],[c_324,c_30])).

tff(c_284,plain,(
    ! [B_107,A_108] :
      ( r1_tarski(B_107,k2_pre_topc(A_108,B_107))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_479,plain,(
    ! [A_137,A_138] :
      ( r1_tarski(A_137,k2_pre_topc(A_138,A_137))
      | ~ l1_pre_topc(A_138)
      | ~ r1_tarski(A_137,u1_struct_0(A_138)) ) ),
    inference(resolution,[status(thm)],[c_32,c_284])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( B_12 = A_11
      | ~ r1_tarski(B_12,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1648,plain,(
    ! [A_283,A_284] :
      ( k2_pre_topc(A_283,A_284) = A_284
      | ~ r1_tarski(k2_pre_topc(A_283,A_284),A_284)
      | ~ l1_pre_topc(A_283)
      | ~ r1_tarski(A_284,u1_struct_0(A_283)) ) ),
    inference(resolution,[status(thm)],[c_479,c_14])).

tff(c_1672,plain,(
    ! [A_114] :
      ( k2_pre_topc(A_114,u1_struct_0(A_114)) = u1_struct_0(A_114)
      | ~ r1_tarski(u1_struct_0(A_114),u1_struct_0(A_114))
      | ~ m1_subset_1(u1_struct_0(A_114),k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(resolution,[status(thm)],[c_334,c_1648])).

tff(c_1694,plain,(
    ! [A_114] :
      ( k2_pre_topc(A_114,u1_struct_0(A_114)) = u1_struct_0(A_114)
      | ~ l1_pre_topc(A_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_18,c_1672])).

tff(c_4517,plain,
    ( k2_pre_topc('#skF_3',k2_struct_0('#skF_3')) = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4350,c_1694])).

tff(c_4711,plain,(
    k2_pre_topc('#skF_3',k2_struct_0('#skF_3')) = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_4350,c_4517])).

tff(c_4713,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_4711])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:30:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.42/2.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.42/2.48  
% 7.42/2.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.42/2.48  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > #skF_3 > #skF_2 > #skF_1
% 7.42/2.48  
% 7.42/2.48  %Foreground sorts:
% 7.42/2.48  
% 7.42/2.48  
% 7.42/2.48  %Background operators:
% 7.42/2.48  
% 7.42/2.48  
% 7.42/2.48  %Foreground operators:
% 7.42/2.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.42/2.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.42/2.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.42/2.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.42/2.48  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 7.42/2.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.42/2.48  tff('#skF_3', type, '#skF_3': $i).
% 7.42/2.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.42/2.48  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.42/2.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.42/2.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.42/2.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.42/2.48  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 7.42/2.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.42/2.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.42/2.48  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 7.42/2.48  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 7.42/2.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.42/2.48  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.42/2.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.42/2.48  
% 7.42/2.49  tff(f_120, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (k2_pre_topc(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_tops_1)).
% 7.42/2.49  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.42/2.49  tff(f_104, axiom, (![A]: (l1_struct_0(A) => v1_xboole_0(k1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_struct_0)).
% 7.42/2.49  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.42/2.49  tff(f_64, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 7.42/2.49  tff(f_66, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 7.42/2.49  tff(f_86, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 7.42/2.49  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 7.42/2.49  tff(f_79, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.42/2.49  tff(f_108, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = k3_subset_1(u1_struct_0(A), k1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_pre_topc)).
% 7.42/2.49  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_subset_1)).
% 7.42/2.49  tff(f_96, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 7.42/2.49  tff(f_56, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.42/2.49  tff(f_92, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 7.42/2.49  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 7.42/2.49  tff(c_48, plain, (k2_pre_topc('#skF_3', k2_struct_0('#skF_3'))!=k2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.42/2.49  tff(c_50, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.42/2.49  tff(c_40, plain, (![A_30]: (l1_struct_0(A_30) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.42/2.49  tff(c_42, plain, (![A_31]: (v1_xboole_0(k1_struct_0(A_31)) | ~l1_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.42/2.49  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.42/2.49  tff(c_22, plain, (![A_16]: (k2_subset_1(A_16)=A_16)), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.42/2.49  tff(c_24, plain, (![A_17]: (m1_subset_1(k2_subset_1(A_17), k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.42/2.49  tff(c_51, plain, (![A_17]: (m1_subset_1(A_17, k1_zfmisc_1(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24])).
% 7.42/2.49  tff(c_103, plain, (![C_57, B_58, A_59]: (~v1_xboole_0(C_57) | ~m1_subset_1(B_58, k1_zfmisc_1(C_57)) | ~r2_hidden(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.42/2.49  tff(c_113, plain, (![A_60, A_61]: (~v1_xboole_0(A_60) | ~r2_hidden(A_61, A_60))), inference(resolution, [status(thm)], [c_51, c_103])).
% 7.42/2.49  tff(c_123, plain, (![A_1, B_2]: (~v1_xboole_0(A_1) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_113])).
% 7.42/2.49  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.42/2.49  tff(c_124, plain, (![B_7, A_6]: (~v1_xboole_0(B_7) | r1_xboole_0(A_6, B_7))), inference(resolution, [status(thm)], [c_10, c_113])).
% 7.42/2.49  tff(c_32, plain, (![A_22, B_23]: (m1_subset_1(A_22, k1_zfmisc_1(B_23)) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.42/2.49  tff(c_44, plain, (![A_32]: (k3_subset_1(u1_struct_0(A_32), k1_struct_0(A_32))=k2_struct_0(A_32) | ~l1_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.42/2.49  tff(c_452, plain, (![B_134, A_135, C_136]: (r1_tarski(B_134, k3_subset_1(A_135, C_136)) | ~r1_xboole_0(B_134, C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(A_135)) | ~m1_subset_1(B_134, k1_zfmisc_1(A_135)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.42/2.49  tff(c_1878, plain, (![B_295, A_296]: (r1_tarski(B_295, k2_struct_0(A_296)) | ~r1_xboole_0(B_295, k1_struct_0(A_296)) | ~m1_subset_1(k1_struct_0(A_296), k1_zfmisc_1(u1_struct_0(A_296))) | ~m1_subset_1(B_295, k1_zfmisc_1(u1_struct_0(A_296))) | ~l1_struct_0(A_296))), inference(superposition, [status(thm), theory('equality')], [c_44, c_452])).
% 7.42/2.49  tff(c_3484, plain, (![B_466, A_467]: (r1_tarski(B_466, k2_struct_0(A_467)) | ~r1_xboole_0(B_466, k1_struct_0(A_467)) | ~m1_subset_1(B_466, k1_zfmisc_1(u1_struct_0(A_467))) | ~l1_struct_0(A_467) | ~r1_tarski(k1_struct_0(A_467), u1_struct_0(A_467)))), inference(resolution, [status(thm)], [c_32, c_1878])).
% 7.42/2.49  tff(c_4101, plain, (![A_553]: (r1_tarski(u1_struct_0(A_553), k2_struct_0(A_553)) | ~r1_xboole_0(u1_struct_0(A_553), k1_struct_0(A_553)) | ~l1_struct_0(A_553) | ~r1_tarski(k1_struct_0(A_553), u1_struct_0(A_553)))), inference(resolution, [status(thm)], [c_51, c_3484])).
% 7.42/2.49  tff(c_4110, plain, (![A_554]: (r1_tarski(u1_struct_0(A_554), k2_struct_0(A_554)) | ~l1_struct_0(A_554) | ~r1_tarski(k1_struct_0(A_554), u1_struct_0(A_554)) | ~v1_xboole_0(k1_struct_0(A_554)))), inference(resolution, [status(thm)], [c_124, c_4101])).
% 7.42/2.49  tff(c_77, plain, (![A_45]: (m1_subset_1(k2_struct_0(A_45), k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.42/2.49  tff(c_30, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | ~m1_subset_1(A_22, k1_zfmisc_1(B_23)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.42/2.49  tff(c_81, plain, (![A_45]: (r1_tarski(k2_struct_0(A_45), u1_struct_0(A_45)) | ~l1_struct_0(A_45))), inference(resolution, [status(thm)], [c_77, c_30])).
% 7.42/2.49  tff(c_85, plain, (![B_51, A_52]: (B_51=A_52 | ~r1_tarski(B_51, A_52) | ~r1_tarski(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.42/2.49  tff(c_90, plain, (![A_45]: (u1_struct_0(A_45)=k2_struct_0(A_45) | ~r1_tarski(u1_struct_0(A_45), k2_struct_0(A_45)) | ~l1_struct_0(A_45))), inference(resolution, [status(thm)], [c_81, c_85])).
% 7.42/2.49  tff(c_4326, plain, (![A_557]: (u1_struct_0(A_557)=k2_struct_0(A_557) | ~l1_struct_0(A_557) | ~r1_tarski(k1_struct_0(A_557), u1_struct_0(A_557)) | ~v1_xboole_0(k1_struct_0(A_557)))), inference(resolution, [status(thm)], [c_4110, c_90])).
% 7.42/2.49  tff(c_4336, plain, (![A_558]: (u1_struct_0(A_558)=k2_struct_0(A_558) | ~l1_struct_0(A_558) | ~v1_xboole_0(k1_struct_0(A_558)))), inference(resolution, [status(thm)], [c_123, c_4326])).
% 7.42/2.49  tff(c_4341, plain, (![A_559]: (u1_struct_0(A_559)=k2_struct_0(A_559) | ~l1_struct_0(A_559))), inference(resolution, [status(thm)], [c_42, c_4336])).
% 7.42/2.49  tff(c_4346, plain, (![A_560]: (u1_struct_0(A_560)=k2_struct_0(A_560) | ~l1_pre_topc(A_560))), inference(resolution, [status(thm)], [c_40, c_4341])).
% 7.42/2.49  tff(c_4350, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_4346])).
% 7.42/2.49  tff(c_18, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.42/2.49  tff(c_324, plain, (![A_114, B_115]: (m1_subset_1(k2_pre_topc(A_114, B_115), k1_zfmisc_1(u1_struct_0(A_114))) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.42/2.49  tff(c_334, plain, (![A_114, B_115]: (r1_tarski(k2_pre_topc(A_114, B_115), u1_struct_0(A_114)) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114))), inference(resolution, [status(thm)], [c_324, c_30])).
% 7.42/2.49  tff(c_284, plain, (![B_107, A_108]: (r1_tarski(B_107, k2_pre_topc(A_108, B_107)) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.42/2.49  tff(c_479, plain, (![A_137, A_138]: (r1_tarski(A_137, k2_pre_topc(A_138, A_137)) | ~l1_pre_topc(A_138) | ~r1_tarski(A_137, u1_struct_0(A_138)))), inference(resolution, [status(thm)], [c_32, c_284])).
% 7.42/2.49  tff(c_14, plain, (![B_12, A_11]: (B_12=A_11 | ~r1_tarski(B_12, A_11) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.42/2.49  tff(c_1648, plain, (![A_283, A_284]: (k2_pre_topc(A_283, A_284)=A_284 | ~r1_tarski(k2_pre_topc(A_283, A_284), A_284) | ~l1_pre_topc(A_283) | ~r1_tarski(A_284, u1_struct_0(A_283)))), inference(resolution, [status(thm)], [c_479, c_14])).
% 7.42/2.49  tff(c_1672, plain, (![A_114]: (k2_pre_topc(A_114, u1_struct_0(A_114))=u1_struct_0(A_114) | ~r1_tarski(u1_struct_0(A_114), u1_struct_0(A_114)) | ~m1_subset_1(u1_struct_0(A_114), k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114))), inference(resolution, [status(thm)], [c_334, c_1648])).
% 7.42/2.49  tff(c_1694, plain, (![A_114]: (k2_pre_topc(A_114, u1_struct_0(A_114))=u1_struct_0(A_114) | ~l1_pre_topc(A_114))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_18, c_1672])).
% 7.42/2.49  tff(c_4517, plain, (k2_pre_topc('#skF_3', k2_struct_0('#skF_3'))=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4350, c_1694])).
% 7.42/2.49  tff(c_4711, plain, (k2_pre_topc('#skF_3', k2_struct_0('#skF_3'))=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_4350, c_4517])).
% 7.42/2.49  tff(c_4713, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_4711])).
% 7.42/2.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.42/2.49  
% 7.42/2.49  Inference rules
% 7.42/2.49  ----------------------
% 7.42/2.49  #Ref     : 0
% 7.42/2.49  #Sup     : 1244
% 7.42/2.49  #Fact    : 0
% 7.42/2.49  #Define  : 0
% 7.42/2.49  #Split   : 2
% 7.42/2.49  #Chain   : 0
% 7.42/2.49  #Close   : 0
% 7.42/2.49  
% 7.42/2.49  Ordering : KBO
% 7.42/2.49  
% 7.42/2.49  Simplification rules
% 7.42/2.49  ----------------------
% 7.42/2.49  #Subsume      : 606
% 7.42/2.49  #Demod        : 183
% 7.42/2.49  #Tautology    : 48
% 7.42/2.49  #SimpNegUnit  : 10
% 7.42/2.49  #BackRed      : 6
% 7.42/2.49  
% 7.42/2.49  #Partial instantiations: 0
% 7.42/2.49  #Strategies tried      : 1
% 7.42/2.49  
% 7.42/2.49  Timing (in seconds)
% 7.42/2.49  ----------------------
% 7.42/2.50  Preprocessing        : 0.30
% 7.42/2.50  Parsing              : 0.16
% 7.42/2.50  CNF conversion       : 0.02
% 7.42/2.50  Main loop            : 1.44
% 7.42/2.50  Inferencing          : 0.40
% 7.42/2.50  Reduction            : 0.28
% 7.42/2.50  Demodulation         : 0.18
% 7.42/2.50  BG Simplification    : 0.04
% 7.42/2.50  Subsumption          : 0.62
% 7.42/2.50  Abstraction          : 0.05
% 7.42/2.50  MUC search           : 0.00
% 7.42/2.50  Cooper               : 0.00
% 7.42/2.50  Total                : 1.77
% 7.42/2.50  Index Insertion      : 0.00
% 7.42/2.50  Index Deletion       : 0.00
% 7.42/2.50  Index Matching       : 0.00
% 7.42/2.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
