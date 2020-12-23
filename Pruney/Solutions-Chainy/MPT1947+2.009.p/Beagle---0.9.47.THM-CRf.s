%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:55 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   59 (  72 expanded)
%              Number of leaves         :   31 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :  200 ( 303 expanded)
%              Number of equality atoms :   12 (  22 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_yellow_6 > v1_yellow_6 > r2_hidden > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_waybel_0 > k4_yellow_6 > k11_yellow_6 > k10_yellow_6 > #nlpp > u1_struct_0 > #skF_1 > #skF_2 > #skF_3

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k10_yellow_6,type,(
    k10_yellow_6: ( $i * $i ) > $i )).

tff(v3_yellow_6,type,(
    v3_yellow_6: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k2_waybel_0,type,(
    k2_waybel_0: ( $i * $i * $i ) > $i )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v1_yellow_6,type,(
    v1_yellow_6: ( $i * $i ) > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_169,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_yellow_6)).

tff(f_32,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_74,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_yellow_6)).

tff(f_28,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_124,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & v1_yellow_6(B,A)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => k2_waybel_0(A,B,C) = k4_yellow_6(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_yellow_6)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A)
        & m1_subset_1(C,u1_struct_0(B)) )
     => m1_subset_1(k2_waybel_0(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_waybel_0)).

tff(f_145,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_6)).

tff(f_102,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_yellow_6)).

tff(c_36,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_4,plain,(
    ! [A_3] :
      ( l1_struct_0(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_24,plain,(
    k4_yellow_6('#skF_2','#skF_3') != k11_yellow_6('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_40,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_26,plain,(
    l1_waybel_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_32,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_30,plain,(
    v7_waybel_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_38,plain,(
    v8_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_28,plain,(
    v1_yellow_6('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_8,plain,(
    ! [B_9,A_7] :
      ( v3_yellow_6(B_9,A_7)
      | ~ v1_yellow_6(B_9,A_7)
      | ~ v7_waybel_0(B_9)
      | ~ v4_orders_2(B_9)
      | v2_struct_0(B_9)
      | ~ l1_waybel_0(B_9,A_7)
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2,plain,(
    ! [A_1] : m1_subset_1('#skF_1'(A_1),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_48,plain,(
    ! [A_37,B_38,C_39] :
      ( k2_waybel_0(A_37,B_38,C_39) = k4_yellow_6(A_37,B_38)
      | ~ m1_subset_1(C_39,u1_struct_0(B_38))
      | ~ l1_waybel_0(B_38,A_37)
      | ~ v1_yellow_6(B_38,A_37)
      | ~ v7_waybel_0(B_38)
      | ~ v4_orders_2(B_38)
      | v2_struct_0(B_38)
      | ~ l1_struct_0(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_56,plain,(
    ! [A_40,B_41] :
      ( k2_waybel_0(A_40,B_41,'#skF_1'(u1_struct_0(B_41))) = k4_yellow_6(A_40,B_41)
      | ~ l1_waybel_0(B_41,A_40)
      | ~ v1_yellow_6(B_41,A_40)
      | ~ v7_waybel_0(B_41)
      | ~ v4_orders_2(B_41)
      | v2_struct_0(B_41)
      | ~ l1_struct_0(A_40)
      | v2_struct_0(A_40) ) ),
    inference(resolution,[status(thm)],[c_2,c_48])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] :
      ( m1_subset_1(k2_waybel_0(A_4,B_5,C_6),u1_struct_0(A_4))
      | ~ m1_subset_1(C_6,u1_struct_0(B_5))
      | ~ l1_waybel_0(B_5,A_4)
      | v2_struct_0(B_5)
      | ~ l1_struct_0(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_62,plain,(
    ! [A_40,B_41] :
      ( m1_subset_1(k4_yellow_6(A_40,B_41),u1_struct_0(A_40))
      | ~ m1_subset_1('#skF_1'(u1_struct_0(B_41)),u1_struct_0(B_41))
      | ~ l1_waybel_0(B_41,A_40)
      | v2_struct_0(B_41)
      | ~ l1_struct_0(A_40)
      | v2_struct_0(A_40)
      | ~ l1_waybel_0(B_41,A_40)
      | ~ v1_yellow_6(B_41,A_40)
      | ~ v7_waybel_0(B_41)
      | ~ v4_orders_2(B_41)
      | v2_struct_0(B_41)
      | ~ l1_struct_0(A_40)
      | v2_struct_0(A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_6])).

tff(c_68,plain,(
    ! [A_40,B_41] :
      ( m1_subset_1(k4_yellow_6(A_40,B_41),u1_struct_0(A_40))
      | ~ l1_waybel_0(B_41,A_40)
      | ~ v1_yellow_6(B_41,A_40)
      | ~ v7_waybel_0(B_41)
      | ~ v4_orders_2(B_41)
      | v2_struct_0(B_41)
      | ~ l1_struct_0(A_40)
      | v2_struct_0(A_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_62])).

tff(c_22,plain,(
    ! [A_24,B_26] :
      ( r2_hidden(k4_yellow_6(A_24,B_26),k10_yellow_6(A_24,B_26))
      | ~ l1_waybel_0(B_26,A_24)
      | ~ v1_yellow_6(B_26,A_24)
      | ~ v7_waybel_0(B_26)
      | ~ v4_orders_2(B_26)
      | v2_struct_0(B_26)
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_74,plain,(
    ! [A_44,B_45,C_46] :
      ( k11_yellow_6(A_44,B_45) = C_46
      | ~ r2_hidden(C_46,k10_yellow_6(A_44,B_45))
      | ~ m1_subset_1(C_46,u1_struct_0(A_44))
      | ~ l1_waybel_0(B_45,A_44)
      | ~ v3_yellow_6(B_45,A_44)
      | ~ v7_waybel_0(B_45)
      | ~ v4_orders_2(B_45)
      | v2_struct_0(B_45)
      | ~ l1_pre_topc(A_44)
      | ~ v8_pre_topc(A_44)
      | ~ v2_pre_topc(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_85,plain,(
    ! [A_49,B_50] :
      ( k4_yellow_6(A_49,B_50) = k11_yellow_6(A_49,B_50)
      | ~ m1_subset_1(k4_yellow_6(A_49,B_50),u1_struct_0(A_49))
      | ~ v3_yellow_6(B_50,A_49)
      | ~ v8_pre_topc(A_49)
      | ~ l1_waybel_0(B_50,A_49)
      | ~ v1_yellow_6(B_50,A_49)
      | ~ v7_waybel_0(B_50)
      | ~ v4_orders_2(B_50)
      | v2_struct_0(B_50)
      | ~ l1_pre_topc(A_49)
      | ~ v2_pre_topc(A_49)
      | v2_struct_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_22,c_74])).

tff(c_90,plain,(
    ! [A_51,B_52] :
      ( k4_yellow_6(A_51,B_52) = k11_yellow_6(A_51,B_52)
      | ~ v3_yellow_6(B_52,A_51)
      | ~ v8_pre_topc(A_51)
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | ~ l1_waybel_0(B_52,A_51)
      | ~ v1_yellow_6(B_52,A_51)
      | ~ v7_waybel_0(B_52)
      | ~ v4_orders_2(B_52)
      | v2_struct_0(B_52)
      | ~ l1_struct_0(A_51)
      | v2_struct_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_68,c_85])).

tff(c_95,plain,(
    ! [A_53,B_54] :
      ( k4_yellow_6(A_53,B_54) = k11_yellow_6(A_53,B_54)
      | ~ v8_pre_topc(A_53)
      | ~ l1_struct_0(A_53)
      | ~ v1_yellow_6(B_54,A_53)
      | ~ v7_waybel_0(B_54)
      | ~ v4_orders_2(B_54)
      | v2_struct_0(B_54)
      | ~ l1_waybel_0(B_54,A_53)
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(resolution,[status(thm)],[c_8,c_90])).

tff(c_98,plain,
    ( k4_yellow_6('#skF_2','#skF_3') = k11_yellow_6('#skF_2','#skF_3')
    | ~ v8_pre_topc('#skF_2')
    | ~ l1_struct_0('#skF_2')
    | ~ v7_waybel_0('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_waybel_0('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_95])).

tff(c_101,plain,
    ( k4_yellow_6('#skF_2','#skF_3') = k11_yellow_6('#skF_2','#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_26,c_32,c_30,c_38,c_98])).

tff(c_102,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_34,c_24,c_101])).

tff(c_105,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_102])).

tff(c_109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_105])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:25:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.28  
% 2.14/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.28  %$ v3_yellow_6 > v1_yellow_6 > r2_hidden > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_waybel_0 > k4_yellow_6 > k11_yellow_6 > k10_yellow_6 > #nlpp > u1_struct_0 > #skF_1 > #skF_2 > #skF_3
% 2.14/1.28  
% 2.14/1.28  %Foreground sorts:
% 2.14/1.28  
% 2.14/1.28  
% 2.14/1.28  %Background operators:
% 2.14/1.28  
% 2.14/1.28  
% 2.14/1.28  %Foreground operators:
% 2.14/1.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.14/1.28  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 2.14/1.28  tff(k4_yellow_6, type, k4_yellow_6: ($i * $i) > $i).
% 2.14/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.28  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.14/1.28  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 2.14/1.28  tff(v3_yellow_6, type, v3_yellow_6: ($i * $i) > $o).
% 2.14/1.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.14/1.28  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.14/1.28  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.14/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.28  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.14/1.28  tff(v1_yellow_6, type, v1_yellow_6: ($i * $i) > $o).
% 2.14/1.28  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.14/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.28  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.14/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.28  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.14/1.28  tff(k11_yellow_6, type, k11_yellow_6: ($i * $i) > $i).
% 2.14/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.14/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.28  
% 2.14/1.30  tff(f_169, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v8_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v1_yellow_6(B, A)) & l1_waybel_0(B, A)) => (k11_yellow_6(A, B) = k4_yellow_6(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_yellow_6)).
% 2.14/1.30  tff(f_32, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.14/1.30  tff(f_74, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (l1_waybel_0(B, A) => ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v1_yellow_6(B, A)) => (((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v3_yellow_6(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_yellow_6)).
% 2.14/1.30  tff(f_28, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.14/1.30  tff(f_124, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v1_yellow_6(B, A)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => (k2_waybel_0(A, B, C) = k4_yellow_6(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_yellow_6)).
% 2.14/1.30  tff(f_46, axiom, (![A, B, C]: (((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & l1_waybel_0(B, A)) & m1_subset_1(C, u1_struct_0(B))) => m1_subset_1(k2_waybel_0(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_waybel_0)).
% 2.14/1.30  tff(f_145, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v1_yellow_6(B, A)) & l1_waybel_0(B, A)) => r2_hidden(k4_yellow_6(A, B), k10_yellow_6(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_yellow_6)).
% 2.14/1.30  tff(f_102, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v8_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v3_yellow_6(B, A)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k11_yellow_6(A, B)) <=> r2_hidden(C, k10_yellow_6(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_yellow_6)).
% 2.14/1.30  tff(c_36, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.14/1.30  tff(c_4, plain, (![A_3]: (l1_struct_0(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.14/1.30  tff(c_42, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.14/1.30  tff(c_34, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.14/1.30  tff(c_24, plain, (k4_yellow_6('#skF_2', '#skF_3')!=k11_yellow_6('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.14/1.30  tff(c_40, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.14/1.30  tff(c_26, plain, (l1_waybel_0('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.14/1.30  tff(c_32, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.14/1.30  tff(c_30, plain, (v7_waybel_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.14/1.30  tff(c_38, plain, (v8_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.14/1.30  tff(c_28, plain, (v1_yellow_6('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.14/1.30  tff(c_8, plain, (![B_9, A_7]: (v3_yellow_6(B_9, A_7) | ~v1_yellow_6(B_9, A_7) | ~v7_waybel_0(B_9) | ~v4_orders_2(B_9) | v2_struct_0(B_9) | ~l1_waybel_0(B_9, A_7) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.14/1.30  tff(c_2, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.14/1.30  tff(c_48, plain, (![A_37, B_38, C_39]: (k2_waybel_0(A_37, B_38, C_39)=k4_yellow_6(A_37, B_38) | ~m1_subset_1(C_39, u1_struct_0(B_38)) | ~l1_waybel_0(B_38, A_37) | ~v1_yellow_6(B_38, A_37) | ~v7_waybel_0(B_38) | ~v4_orders_2(B_38) | v2_struct_0(B_38) | ~l1_struct_0(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.14/1.30  tff(c_56, plain, (![A_40, B_41]: (k2_waybel_0(A_40, B_41, '#skF_1'(u1_struct_0(B_41)))=k4_yellow_6(A_40, B_41) | ~l1_waybel_0(B_41, A_40) | ~v1_yellow_6(B_41, A_40) | ~v7_waybel_0(B_41) | ~v4_orders_2(B_41) | v2_struct_0(B_41) | ~l1_struct_0(A_40) | v2_struct_0(A_40))), inference(resolution, [status(thm)], [c_2, c_48])).
% 2.14/1.30  tff(c_6, plain, (![A_4, B_5, C_6]: (m1_subset_1(k2_waybel_0(A_4, B_5, C_6), u1_struct_0(A_4)) | ~m1_subset_1(C_6, u1_struct_0(B_5)) | ~l1_waybel_0(B_5, A_4) | v2_struct_0(B_5) | ~l1_struct_0(A_4) | v2_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.14/1.30  tff(c_62, plain, (![A_40, B_41]: (m1_subset_1(k4_yellow_6(A_40, B_41), u1_struct_0(A_40)) | ~m1_subset_1('#skF_1'(u1_struct_0(B_41)), u1_struct_0(B_41)) | ~l1_waybel_0(B_41, A_40) | v2_struct_0(B_41) | ~l1_struct_0(A_40) | v2_struct_0(A_40) | ~l1_waybel_0(B_41, A_40) | ~v1_yellow_6(B_41, A_40) | ~v7_waybel_0(B_41) | ~v4_orders_2(B_41) | v2_struct_0(B_41) | ~l1_struct_0(A_40) | v2_struct_0(A_40))), inference(superposition, [status(thm), theory('equality')], [c_56, c_6])).
% 2.14/1.30  tff(c_68, plain, (![A_40, B_41]: (m1_subset_1(k4_yellow_6(A_40, B_41), u1_struct_0(A_40)) | ~l1_waybel_0(B_41, A_40) | ~v1_yellow_6(B_41, A_40) | ~v7_waybel_0(B_41) | ~v4_orders_2(B_41) | v2_struct_0(B_41) | ~l1_struct_0(A_40) | v2_struct_0(A_40))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_62])).
% 2.14/1.30  tff(c_22, plain, (![A_24, B_26]: (r2_hidden(k4_yellow_6(A_24, B_26), k10_yellow_6(A_24, B_26)) | ~l1_waybel_0(B_26, A_24) | ~v1_yellow_6(B_26, A_24) | ~v7_waybel_0(B_26) | ~v4_orders_2(B_26) | v2_struct_0(B_26) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_145])).
% 2.14/1.30  tff(c_74, plain, (![A_44, B_45, C_46]: (k11_yellow_6(A_44, B_45)=C_46 | ~r2_hidden(C_46, k10_yellow_6(A_44, B_45)) | ~m1_subset_1(C_46, u1_struct_0(A_44)) | ~l1_waybel_0(B_45, A_44) | ~v3_yellow_6(B_45, A_44) | ~v7_waybel_0(B_45) | ~v4_orders_2(B_45) | v2_struct_0(B_45) | ~l1_pre_topc(A_44) | ~v8_pre_topc(A_44) | ~v2_pre_topc(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.14/1.30  tff(c_85, plain, (![A_49, B_50]: (k4_yellow_6(A_49, B_50)=k11_yellow_6(A_49, B_50) | ~m1_subset_1(k4_yellow_6(A_49, B_50), u1_struct_0(A_49)) | ~v3_yellow_6(B_50, A_49) | ~v8_pre_topc(A_49) | ~l1_waybel_0(B_50, A_49) | ~v1_yellow_6(B_50, A_49) | ~v7_waybel_0(B_50) | ~v4_orders_2(B_50) | v2_struct_0(B_50) | ~l1_pre_topc(A_49) | ~v2_pre_topc(A_49) | v2_struct_0(A_49))), inference(resolution, [status(thm)], [c_22, c_74])).
% 2.14/1.30  tff(c_90, plain, (![A_51, B_52]: (k4_yellow_6(A_51, B_52)=k11_yellow_6(A_51, B_52) | ~v3_yellow_6(B_52, A_51) | ~v8_pre_topc(A_51) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51) | ~l1_waybel_0(B_52, A_51) | ~v1_yellow_6(B_52, A_51) | ~v7_waybel_0(B_52) | ~v4_orders_2(B_52) | v2_struct_0(B_52) | ~l1_struct_0(A_51) | v2_struct_0(A_51))), inference(resolution, [status(thm)], [c_68, c_85])).
% 2.14/1.30  tff(c_95, plain, (![A_53, B_54]: (k4_yellow_6(A_53, B_54)=k11_yellow_6(A_53, B_54) | ~v8_pre_topc(A_53) | ~l1_struct_0(A_53) | ~v1_yellow_6(B_54, A_53) | ~v7_waybel_0(B_54) | ~v4_orders_2(B_54) | v2_struct_0(B_54) | ~l1_waybel_0(B_54, A_53) | ~l1_pre_topc(A_53) | ~v2_pre_topc(A_53) | v2_struct_0(A_53))), inference(resolution, [status(thm)], [c_8, c_90])).
% 2.14/1.30  tff(c_98, plain, (k4_yellow_6('#skF_2', '#skF_3')=k11_yellow_6('#skF_2', '#skF_3') | ~v8_pre_topc('#skF_2') | ~l1_struct_0('#skF_2') | ~v7_waybel_0('#skF_3') | ~v4_orders_2('#skF_3') | v2_struct_0('#skF_3') | ~l1_waybel_0('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_95])).
% 2.14/1.30  tff(c_101, plain, (k4_yellow_6('#skF_2', '#skF_3')=k11_yellow_6('#skF_2', '#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_26, c_32, c_30, c_38, c_98])).
% 2.14/1.30  tff(c_102, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_42, c_34, c_24, c_101])).
% 2.14/1.30  tff(c_105, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_102])).
% 2.14/1.30  tff(c_109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_105])).
% 2.14/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.30  
% 2.14/1.30  Inference rules
% 2.14/1.30  ----------------------
% 2.14/1.30  #Ref     : 0
% 2.14/1.30  #Sup     : 12
% 2.14/1.30  #Fact    : 0
% 2.14/1.30  #Define  : 0
% 2.14/1.30  #Split   : 0
% 2.14/1.30  #Chain   : 0
% 2.14/1.30  #Close   : 0
% 2.14/1.30  
% 2.14/1.30  Ordering : KBO
% 2.14/1.30  
% 2.14/1.30  Simplification rules
% 2.14/1.30  ----------------------
% 2.14/1.30  #Subsume      : 1
% 2.14/1.30  #Demod        : 8
% 2.14/1.30  #Tautology    : 6
% 2.14/1.30  #SimpNegUnit  : 1
% 2.14/1.30  #BackRed      : 0
% 2.14/1.30  
% 2.14/1.30  #Partial instantiations: 0
% 2.14/1.30  #Strategies tried      : 1
% 2.14/1.30  
% 2.14/1.30  Timing (in seconds)
% 2.14/1.30  ----------------------
% 2.14/1.30  Preprocessing        : 0.34
% 2.14/1.30  Parsing              : 0.18
% 2.14/1.30  CNF conversion       : 0.02
% 2.14/1.30  Main loop            : 0.15
% 2.14/1.30  Inferencing          : 0.06
% 2.14/1.30  Reduction            : 0.04
% 2.14/1.30  Demodulation         : 0.03
% 2.14/1.30  BG Simplification    : 0.02
% 2.14/1.30  Subsumption          : 0.02
% 2.14/1.30  Abstraction          : 0.01
% 2.14/1.30  MUC search           : 0.00
% 2.14/1.30  Cooper               : 0.00
% 2.14/1.30  Total                : 0.52
% 2.14/1.30  Index Insertion      : 0.00
% 2.14/1.30  Index Deletion       : 0.00
% 2.14/1.30  Index Matching       : 0.00
% 2.14/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
