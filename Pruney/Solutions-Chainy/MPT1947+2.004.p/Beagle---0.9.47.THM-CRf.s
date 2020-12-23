%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:54 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :   59 (  69 expanded)
%              Number of leaves         :   31 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :  205 ( 304 expanded)
%              Number of equality atoms :    9 (  18 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_yellow_6 > v1_yellow_6 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k4_yellow_6 > k11_yellow_6 > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v8_pre_topc,type,(
    v8_pre_topc: $i > $o )).

tff(k4_yellow_6,type,(
    k4_yellow_6: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k10_yellow_6,type,(
    k10_yellow_6: ( $i * $i ) > $i )).

tff(v3_yellow_6,type,(
    v3_yellow_6: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v1_yellow_6,type,(
    v1_yellow_6: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k11_yellow_6,type,(
    k11_yellow_6: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_159,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v8_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_orders_2(B)
              & v7_waybel_0(B)
              & v1_yellow_6(B,A)
              & l1_waybel_0(B,A) )
           => k11_yellow_6(A,B) = k4_yellow_6(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_yellow_6)).

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_waybel_0(B,A)
         => ( ( ~ v2_struct_0(B)
              & v4_orders_2(B)
              & v7_waybel_0(B)
              & v1_yellow_6(B,A) )
           => ( ~ v2_struct_0(B)
              & v4_orders_2(B)
              & v7_waybel_0(B)
              & v3_yellow_6(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_yellow_6)).

tff(f_114,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v4_orders_2(B)
        & v7_waybel_0(B)
        & l1_waybel_0(B,A) )
     => m1_subset_1(k10_yellow_6(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_yellow_6)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_135,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & v1_yellow_6(B,A)
            & l1_waybel_0(B,A) )
         => r2_hidden(k4_yellow_6(A,B),k10_yellow_6(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_6)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v8_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & v3_yellow_6(B,A)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( C = k11_yellow_6(A,B)
              <=> r2_hidden(C,k10_yellow_6(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_yellow_6)).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_30,plain,(
    k4_yellow_6('#skF_2','#skF_3') != k11_yellow_6('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_46,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_32,plain,(
    l1_waybel_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_38,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_36,plain,(
    v7_waybel_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_44,plain,(
    v8_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_34,plain,(
    v1_yellow_6('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_14,plain,(
    ! [B_12,A_10] :
      ( v3_yellow_6(B_12,A_10)
      | ~ v1_yellow_6(B_12,A_10)
      | ~ v7_waybel_0(B_12)
      | ~ v4_orders_2(B_12)
      | v2_struct_0(B_12)
      | ~ l1_waybel_0(B_12,A_10)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_123,plain,(
    ! [A_63,B_64] :
      ( m1_subset_1(k10_yellow_6(A_63,B_64),k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_waybel_0(B_64,A_63)
      | ~ v7_waybel_0(B_64)
      | ~ v4_orders_2(B_64)
      | v2_struct_0(B_64)
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_127,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(k10_yellow_6(A_63,B_64),u1_struct_0(A_63))
      | ~ l1_waybel_0(B_64,A_63)
      | ~ v7_waybel_0(B_64)
      | ~ v4_orders_2(B_64)
      | v2_struct_0(B_64)
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_123,c_10])).

tff(c_160,plain,(
    ! [A_76,B_77] :
      ( r2_hidden(k4_yellow_6(A_76,B_77),k10_yellow_6(A_76,B_77))
      | ~ l1_waybel_0(B_77,A_76)
      | ~ v1_yellow_6(B_77,A_76)
      | ~ v7_waybel_0(B_77)
      | ~ v4_orders_2(B_77)
      | v2_struct_0(B_77)
      | ~ l1_pre_topc(A_76)
      | ~ v2_pre_topc(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_381,plain,(
    ! [A_132,B_133,B_134] :
      ( r2_hidden(k4_yellow_6(A_132,B_133),B_134)
      | ~ r1_tarski(k10_yellow_6(A_132,B_133),B_134)
      | ~ l1_waybel_0(B_133,A_132)
      | ~ v1_yellow_6(B_133,A_132)
      | ~ v7_waybel_0(B_133)
      | ~ v4_orders_2(B_133)
      | v2_struct_0(B_133)
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132)
      | v2_struct_0(A_132) ) ),
    inference(resolution,[status(thm)],[c_160,c_2])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_423,plain,(
    ! [A_140,B_141,B_142] :
      ( m1_subset_1(k4_yellow_6(A_140,B_141),B_142)
      | ~ r1_tarski(k10_yellow_6(A_140,B_141),B_142)
      | ~ l1_waybel_0(B_141,A_140)
      | ~ v1_yellow_6(B_141,A_140)
      | ~ v7_waybel_0(B_141)
      | ~ v4_orders_2(B_141)
      | v2_struct_0(B_141)
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140) ) ),
    inference(resolution,[status(thm)],[c_381,c_8])).

tff(c_431,plain,(
    ! [A_63,B_64] :
      ( m1_subset_1(k4_yellow_6(A_63,B_64),u1_struct_0(A_63))
      | ~ v1_yellow_6(B_64,A_63)
      | ~ l1_waybel_0(B_64,A_63)
      | ~ v7_waybel_0(B_64)
      | ~ v4_orders_2(B_64)
      | v2_struct_0(B_64)
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_127,c_423])).

tff(c_28,plain,(
    ! [A_22,B_24] :
      ( r2_hidden(k4_yellow_6(A_22,B_24),k10_yellow_6(A_22,B_24))
      | ~ l1_waybel_0(B_24,A_22)
      | ~ v1_yellow_6(B_24,A_22)
      | ~ v7_waybel_0(B_24)
      | ~ v4_orders_2(B_24)
      | v2_struct_0(B_24)
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_254,plain,(
    ! [A_108,B_109,C_110] :
      ( k11_yellow_6(A_108,B_109) = C_110
      | ~ r2_hidden(C_110,k10_yellow_6(A_108,B_109))
      | ~ m1_subset_1(C_110,u1_struct_0(A_108))
      | ~ l1_waybel_0(B_109,A_108)
      | ~ v3_yellow_6(B_109,A_108)
      | ~ v7_waybel_0(B_109)
      | ~ v4_orders_2(B_109)
      | v2_struct_0(B_109)
      | ~ l1_pre_topc(A_108)
      | ~ v8_pre_topc(A_108)
      | ~ v2_pre_topc(A_108)
      | v2_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_672,plain,(
    ! [A_199,B_200] :
      ( k4_yellow_6(A_199,B_200) = k11_yellow_6(A_199,B_200)
      | ~ m1_subset_1(k4_yellow_6(A_199,B_200),u1_struct_0(A_199))
      | ~ v3_yellow_6(B_200,A_199)
      | ~ v8_pre_topc(A_199)
      | ~ l1_waybel_0(B_200,A_199)
      | ~ v1_yellow_6(B_200,A_199)
      | ~ v7_waybel_0(B_200)
      | ~ v4_orders_2(B_200)
      | v2_struct_0(B_200)
      | ~ l1_pre_topc(A_199)
      | ~ v2_pre_topc(A_199)
      | v2_struct_0(A_199) ) ),
    inference(resolution,[status(thm)],[c_28,c_254])).

tff(c_677,plain,(
    ! [A_201,B_202] :
      ( k4_yellow_6(A_201,B_202) = k11_yellow_6(A_201,B_202)
      | ~ v3_yellow_6(B_202,A_201)
      | ~ v8_pre_topc(A_201)
      | ~ v1_yellow_6(B_202,A_201)
      | ~ l1_waybel_0(B_202,A_201)
      | ~ v7_waybel_0(B_202)
      | ~ v4_orders_2(B_202)
      | v2_struct_0(B_202)
      | ~ l1_pre_topc(A_201)
      | ~ v2_pre_topc(A_201)
      | v2_struct_0(A_201) ) ),
    inference(resolution,[status(thm)],[c_431,c_672])).

tff(c_682,plain,(
    ! [A_203,B_204] :
      ( k4_yellow_6(A_203,B_204) = k11_yellow_6(A_203,B_204)
      | ~ v8_pre_topc(A_203)
      | ~ v1_yellow_6(B_204,A_203)
      | ~ v7_waybel_0(B_204)
      | ~ v4_orders_2(B_204)
      | v2_struct_0(B_204)
      | ~ l1_waybel_0(B_204,A_203)
      | ~ l1_pre_topc(A_203)
      | ~ v2_pre_topc(A_203)
      | v2_struct_0(A_203) ) ),
    inference(resolution,[status(thm)],[c_14,c_677])).

tff(c_685,plain,
    ( k4_yellow_6('#skF_2','#skF_3') = k11_yellow_6('#skF_2','#skF_3')
    | ~ v8_pre_topc('#skF_2')
    | ~ v7_waybel_0('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_waybel_0('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_682])).

tff(c_688,plain,
    ( k4_yellow_6('#skF_2','#skF_3') = k11_yellow_6('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_32,c_38,c_36,c_44,c_685])).

tff(c_690,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_40,c_30,c_688])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:14:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.35/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.50  
% 3.35/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.51  %$ v3_yellow_6 > v1_yellow_6 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k4_yellow_6 > k11_yellow_6 > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.35/1.51  
% 3.35/1.51  %Foreground sorts:
% 3.35/1.51  
% 3.35/1.51  
% 3.35/1.51  %Background operators:
% 3.35/1.51  
% 3.35/1.51  
% 3.35/1.51  %Foreground operators:
% 3.35/1.51  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.35/1.51  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 3.35/1.51  tff(k4_yellow_6, type, k4_yellow_6: ($i * $i) > $i).
% 3.35/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.35/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.35/1.51  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 3.35/1.51  tff(v3_yellow_6, type, v3_yellow_6: ($i * $i) > $o).
% 3.35/1.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.35/1.51  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 3.35/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.35/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.35/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.35/1.51  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.35/1.51  tff(v1_yellow_6, type, v1_yellow_6: ($i * $i) > $o).
% 3.35/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.35/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.35/1.51  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 3.35/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.35/1.51  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.35/1.51  tff(k11_yellow_6, type, k11_yellow_6: ($i * $i) > $i).
% 3.35/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.35/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.35/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.35/1.51  
% 3.35/1.52  tff(f_159, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v8_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v1_yellow_6(B, A)) & l1_waybel_0(B, A)) => (k11_yellow_6(A, B) = k4_yellow_6(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_yellow_6)).
% 3.35/1.52  tff(f_68, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (l1_waybel_0(B, A) => ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v1_yellow_6(B, A)) => (((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v3_yellow_6(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_yellow_6)).
% 3.35/1.52  tff(f_114, axiom, (![A, B]: (((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => m1_subset_1(k10_yellow_6(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 3.35/1.52  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.35/1.52  tff(f_135, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v1_yellow_6(B, A)) & l1_waybel_0(B, A)) => r2_hidden(k4_yellow_6(A, B), k10_yellow_6(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_yellow_6)).
% 3.35/1.52  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.35/1.52  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.35/1.52  tff(f_96, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v8_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v3_yellow_6(B, A)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k11_yellow_6(A, B)) <=> r2_hidden(C, k10_yellow_6(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_yellow_6)).
% 3.35/1.52  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.35/1.52  tff(c_40, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.35/1.52  tff(c_30, plain, (k4_yellow_6('#skF_2', '#skF_3')!=k11_yellow_6('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.35/1.52  tff(c_46, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.35/1.52  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.35/1.52  tff(c_32, plain, (l1_waybel_0('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.35/1.52  tff(c_38, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.35/1.52  tff(c_36, plain, (v7_waybel_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.35/1.52  tff(c_44, plain, (v8_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.35/1.52  tff(c_34, plain, (v1_yellow_6('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.35/1.52  tff(c_14, plain, (![B_12, A_10]: (v3_yellow_6(B_12, A_10) | ~v1_yellow_6(B_12, A_10) | ~v7_waybel_0(B_12) | ~v4_orders_2(B_12) | v2_struct_0(B_12) | ~l1_waybel_0(B_12, A_10) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.35/1.52  tff(c_123, plain, (![A_63, B_64]: (m1_subset_1(k10_yellow_6(A_63, B_64), k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_waybel_0(B_64, A_63) | ~v7_waybel_0(B_64) | ~v4_orders_2(B_64) | v2_struct_0(B_64) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.35/1.52  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.35/1.52  tff(c_127, plain, (![A_63, B_64]: (r1_tarski(k10_yellow_6(A_63, B_64), u1_struct_0(A_63)) | ~l1_waybel_0(B_64, A_63) | ~v7_waybel_0(B_64) | ~v4_orders_2(B_64) | v2_struct_0(B_64) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63) | v2_struct_0(A_63))), inference(resolution, [status(thm)], [c_123, c_10])).
% 3.35/1.52  tff(c_160, plain, (![A_76, B_77]: (r2_hidden(k4_yellow_6(A_76, B_77), k10_yellow_6(A_76, B_77)) | ~l1_waybel_0(B_77, A_76) | ~v1_yellow_6(B_77, A_76) | ~v7_waybel_0(B_77) | ~v4_orders_2(B_77) | v2_struct_0(B_77) | ~l1_pre_topc(A_76) | ~v2_pre_topc(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.35/1.52  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.35/1.52  tff(c_381, plain, (![A_132, B_133, B_134]: (r2_hidden(k4_yellow_6(A_132, B_133), B_134) | ~r1_tarski(k10_yellow_6(A_132, B_133), B_134) | ~l1_waybel_0(B_133, A_132) | ~v1_yellow_6(B_133, A_132) | ~v7_waybel_0(B_133) | ~v4_orders_2(B_133) | v2_struct_0(B_133) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132) | v2_struct_0(A_132))), inference(resolution, [status(thm)], [c_160, c_2])).
% 3.35/1.52  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(A_6, B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.35/1.52  tff(c_423, plain, (![A_140, B_141, B_142]: (m1_subset_1(k4_yellow_6(A_140, B_141), B_142) | ~r1_tarski(k10_yellow_6(A_140, B_141), B_142) | ~l1_waybel_0(B_141, A_140) | ~v1_yellow_6(B_141, A_140) | ~v7_waybel_0(B_141) | ~v4_orders_2(B_141) | v2_struct_0(B_141) | ~l1_pre_topc(A_140) | ~v2_pre_topc(A_140) | v2_struct_0(A_140))), inference(resolution, [status(thm)], [c_381, c_8])).
% 3.35/1.52  tff(c_431, plain, (![A_63, B_64]: (m1_subset_1(k4_yellow_6(A_63, B_64), u1_struct_0(A_63)) | ~v1_yellow_6(B_64, A_63) | ~l1_waybel_0(B_64, A_63) | ~v7_waybel_0(B_64) | ~v4_orders_2(B_64) | v2_struct_0(B_64) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63) | v2_struct_0(A_63))), inference(resolution, [status(thm)], [c_127, c_423])).
% 3.35/1.52  tff(c_28, plain, (![A_22, B_24]: (r2_hidden(k4_yellow_6(A_22, B_24), k10_yellow_6(A_22, B_24)) | ~l1_waybel_0(B_24, A_22) | ~v1_yellow_6(B_24, A_22) | ~v7_waybel_0(B_24) | ~v4_orders_2(B_24) | v2_struct_0(B_24) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.35/1.52  tff(c_254, plain, (![A_108, B_109, C_110]: (k11_yellow_6(A_108, B_109)=C_110 | ~r2_hidden(C_110, k10_yellow_6(A_108, B_109)) | ~m1_subset_1(C_110, u1_struct_0(A_108)) | ~l1_waybel_0(B_109, A_108) | ~v3_yellow_6(B_109, A_108) | ~v7_waybel_0(B_109) | ~v4_orders_2(B_109) | v2_struct_0(B_109) | ~l1_pre_topc(A_108) | ~v8_pre_topc(A_108) | ~v2_pre_topc(A_108) | v2_struct_0(A_108))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.35/1.52  tff(c_672, plain, (![A_199, B_200]: (k4_yellow_6(A_199, B_200)=k11_yellow_6(A_199, B_200) | ~m1_subset_1(k4_yellow_6(A_199, B_200), u1_struct_0(A_199)) | ~v3_yellow_6(B_200, A_199) | ~v8_pre_topc(A_199) | ~l1_waybel_0(B_200, A_199) | ~v1_yellow_6(B_200, A_199) | ~v7_waybel_0(B_200) | ~v4_orders_2(B_200) | v2_struct_0(B_200) | ~l1_pre_topc(A_199) | ~v2_pre_topc(A_199) | v2_struct_0(A_199))), inference(resolution, [status(thm)], [c_28, c_254])).
% 3.35/1.52  tff(c_677, plain, (![A_201, B_202]: (k4_yellow_6(A_201, B_202)=k11_yellow_6(A_201, B_202) | ~v3_yellow_6(B_202, A_201) | ~v8_pre_topc(A_201) | ~v1_yellow_6(B_202, A_201) | ~l1_waybel_0(B_202, A_201) | ~v7_waybel_0(B_202) | ~v4_orders_2(B_202) | v2_struct_0(B_202) | ~l1_pre_topc(A_201) | ~v2_pre_topc(A_201) | v2_struct_0(A_201))), inference(resolution, [status(thm)], [c_431, c_672])).
% 3.35/1.52  tff(c_682, plain, (![A_203, B_204]: (k4_yellow_6(A_203, B_204)=k11_yellow_6(A_203, B_204) | ~v8_pre_topc(A_203) | ~v1_yellow_6(B_204, A_203) | ~v7_waybel_0(B_204) | ~v4_orders_2(B_204) | v2_struct_0(B_204) | ~l1_waybel_0(B_204, A_203) | ~l1_pre_topc(A_203) | ~v2_pre_topc(A_203) | v2_struct_0(A_203))), inference(resolution, [status(thm)], [c_14, c_677])).
% 3.35/1.52  tff(c_685, plain, (k4_yellow_6('#skF_2', '#skF_3')=k11_yellow_6('#skF_2', '#skF_3') | ~v8_pre_topc('#skF_2') | ~v7_waybel_0('#skF_3') | ~v4_orders_2('#skF_3') | v2_struct_0('#skF_3') | ~l1_waybel_0('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_682])).
% 3.35/1.52  tff(c_688, plain, (k4_yellow_6('#skF_2', '#skF_3')=k11_yellow_6('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_32, c_38, c_36, c_44, c_685])).
% 3.35/1.52  tff(c_690, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_40, c_30, c_688])).
% 3.35/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.52  
% 3.35/1.52  Inference rules
% 3.35/1.52  ----------------------
% 3.35/1.52  #Ref     : 0
% 3.35/1.52  #Sup     : 151
% 3.35/1.52  #Fact    : 0
% 3.35/1.52  #Define  : 0
% 3.35/1.52  #Split   : 0
% 3.35/1.52  #Chain   : 0
% 3.35/1.52  #Close   : 0
% 3.35/1.52  
% 3.35/1.52  Ordering : KBO
% 3.35/1.52  
% 3.35/1.52  Simplification rules
% 3.35/1.52  ----------------------
% 3.35/1.52  #Subsume      : 17
% 3.35/1.52  #Demod        : 6
% 3.35/1.52  #Tautology    : 6
% 3.35/1.52  #SimpNegUnit  : 1
% 3.35/1.52  #BackRed      : 0
% 3.35/1.52  
% 3.35/1.52  #Partial instantiations: 0
% 3.35/1.52  #Strategies tried      : 1
% 3.35/1.52  
% 3.35/1.52  Timing (in seconds)
% 3.35/1.52  ----------------------
% 3.35/1.52  Preprocessing        : 0.32
% 3.35/1.52  Parsing              : 0.17
% 3.35/1.52  CNF conversion       : 0.02
% 3.35/1.52  Main loop            : 0.43
% 3.35/1.52  Inferencing          : 0.15
% 3.35/1.52  Reduction            : 0.09
% 3.35/1.52  Demodulation         : 0.06
% 3.35/1.52  BG Simplification    : 0.02
% 3.35/1.52  Subsumption          : 0.14
% 3.35/1.52  Abstraction          : 0.02
% 3.35/1.52  MUC search           : 0.00
% 3.35/1.52  Cooper               : 0.00
% 3.35/1.52  Total                : 0.79
% 3.35/1.52  Index Insertion      : 0.00
% 3.35/1.52  Index Deletion       : 0.00
% 3.35/1.52  Index Matching       : 0.00
% 3.35/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
