%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:55 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   50 (  61 expanded)
%              Number of leaves         :   27 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :  147 ( 248 expanded)
%              Number of equality atoms :    9 (  19 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_yellow_6 > v1_yellow_6 > r2_hidden > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k4_yellow_6 > k11_yellow_6 > k10_yellow_6 > #nlpp > u1_struct_0 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_139,negated_conjecture,(
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

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_57,axiom,(
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

tff(f_94,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & l1_waybel_0(B,A) )
     => m1_subset_1(k4_yellow_6(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_yellow_6)).

tff(f_115,axiom,(
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

tff(f_85,axiom,(
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

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_20,plain,(
    k4_yellow_6('#skF_1','#skF_2') != k11_yellow_6('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_22,plain,(
    l1_waybel_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_28,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_26,plain,(
    v7_waybel_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_34,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_24,plain,(
    v1_yellow_6('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_4,plain,(
    ! [B_4,A_2] :
      ( v3_yellow_6(B_4,A_2)
      | ~ v1_yellow_6(B_4,A_2)
      | ~ v7_waybel_0(B_4)
      | ~ v4_orders_2(B_4)
      | v2_struct_0(B_4)
      | ~ l1_waybel_0(B_4,A_2)
      | ~ l1_pre_topc(A_2)
      | ~ v2_pre_topc(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(k4_yellow_6(A_12,B_13),u1_struct_0(A_12))
      | ~ l1_waybel_0(B_13,A_12)
      | ~ l1_struct_0(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_18,plain,(
    ! [A_14,B_16] :
      ( r2_hidden(k4_yellow_6(A_14,B_16),k10_yellow_6(A_14,B_16))
      | ~ l1_waybel_0(B_16,A_14)
      | ~ v1_yellow_6(B_16,A_14)
      | ~ v7_waybel_0(B_16)
      | ~ v4_orders_2(B_16)
      | v2_struct_0(B_16)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_44,plain,(
    ! [A_27,B_28,C_29] :
      ( k11_yellow_6(A_27,B_28) = C_29
      | ~ r2_hidden(C_29,k10_yellow_6(A_27,B_28))
      | ~ m1_subset_1(C_29,u1_struct_0(A_27))
      | ~ l1_waybel_0(B_28,A_27)
      | ~ v3_yellow_6(B_28,A_27)
      | ~ v7_waybel_0(B_28)
      | ~ v4_orders_2(B_28)
      | v2_struct_0(B_28)
      | ~ l1_pre_topc(A_27)
      | ~ v8_pre_topc(A_27)
      | ~ v2_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_54,plain,(
    ! [A_30,B_31] :
      ( k4_yellow_6(A_30,B_31) = k11_yellow_6(A_30,B_31)
      | ~ m1_subset_1(k4_yellow_6(A_30,B_31),u1_struct_0(A_30))
      | ~ v3_yellow_6(B_31,A_30)
      | ~ v8_pre_topc(A_30)
      | ~ l1_waybel_0(B_31,A_30)
      | ~ v1_yellow_6(B_31,A_30)
      | ~ v7_waybel_0(B_31)
      | ~ v4_orders_2(B_31)
      | v2_struct_0(B_31)
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(resolution,[status(thm)],[c_18,c_44])).

tff(c_59,plain,(
    ! [A_32,B_33] :
      ( k4_yellow_6(A_32,B_33) = k11_yellow_6(A_32,B_33)
      | ~ v3_yellow_6(B_33,A_32)
      | ~ v8_pre_topc(A_32)
      | ~ v1_yellow_6(B_33,A_32)
      | ~ v7_waybel_0(B_33)
      | ~ v4_orders_2(B_33)
      | v2_struct_0(B_33)
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | ~ l1_waybel_0(B_33,A_32)
      | ~ l1_struct_0(A_32)
      | v2_struct_0(A_32) ) ),
    inference(resolution,[status(thm)],[c_16,c_54])).

tff(c_64,plain,(
    ! [A_34,B_35] :
      ( k4_yellow_6(A_34,B_35) = k11_yellow_6(A_34,B_35)
      | ~ v8_pre_topc(A_34)
      | ~ l1_struct_0(A_34)
      | ~ v1_yellow_6(B_35,A_34)
      | ~ v7_waybel_0(B_35)
      | ~ v4_orders_2(B_35)
      | v2_struct_0(B_35)
      | ~ l1_waybel_0(B_35,A_34)
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(resolution,[status(thm)],[c_4,c_59])).

tff(c_67,plain,
    ( k4_yellow_6('#skF_1','#skF_2') = k11_yellow_6('#skF_1','#skF_2')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_struct_0('#skF_1')
    | ~ v7_waybel_0('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_waybel_0('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_64])).

tff(c_70,plain,
    ( k4_yellow_6('#skF_1','#skF_2') = k11_yellow_6('#skF_1','#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_22,c_28,c_26,c_34,c_67])).

tff(c_71,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_30,c_20,c_70])).

tff(c_74,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_71])).

tff(c_78,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_74])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:48:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.18  
% 2.03/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.18  %$ v3_yellow_6 > v1_yellow_6 > r2_hidden > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k4_yellow_6 > k11_yellow_6 > k10_yellow_6 > #nlpp > u1_struct_0 > #skF_2 > #skF_1
% 2.03/1.18  
% 2.03/1.18  %Foreground sorts:
% 2.03/1.18  
% 2.03/1.18  
% 2.03/1.18  %Background operators:
% 2.03/1.18  
% 2.03/1.18  
% 2.03/1.18  %Foreground operators:
% 2.03/1.18  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.03/1.18  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 2.03/1.18  tff(k4_yellow_6, type, k4_yellow_6: ($i * $i) > $i).
% 2.03/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.18  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 2.03/1.18  tff(v3_yellow_6, type, v3_yellow_6: ($i * $i) > $o).
% 2.03/1.18  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.03/1.18  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.03/1.18  tff('#skF_2', type, '#skF_2': $i).
% 2.03/1.18  tff('#skF_1', type, '#skF_1': $i).
% 2.03/1.18  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.03/1.18  tff(v1_yellow_6, type, v1_yellow_6: ($i * $i) > $o).
% 2.03/1.18  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.03/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.18  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.03/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.18  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.03/1.18  tff(k11_yellow_6, type, k11_yellow_6: ($i * $i) > $i).
% 2.03/1.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.03/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.03/1.18  
% 2.03/1.19  tff(f_139, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v8_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v1_yellow_6(B, A)) & l1_waybel_0(B, A)) => (k11_yellow_6(A, B) = k4_yellow_6(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_yellow_6)).
% 2.03/1.19  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.03/1.19  tff(f_57, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (l1_waybel_0(B, A) => ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v1_yellow_6(B, A)) => (((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v3_yellow_6(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_yellow_6)).
% 2.03/1.19  tff(f_94, axiom, (![A, B]: (((~v2_struct_0(A) & l1_struct_0(A)) & l1_waybel_0(B, A)) => m1_subset_1(k4_yellow_6(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_yellow_6)).
% 2.03/1.19  tff(f_115, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v1_yellow_6(B, A)) & l1_waybel_0(B, A)) => r2_hidden(k4_yellow_6(A, B), k10_yellow_6(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_yellow_6)).
% 2.03/1.19  tff(f_85, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v8_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v3_yellow_6(B, A)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k11_yellow_6(A, B)) <=> r2_hidden(C, k10_yellow_6(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_yellow_6)).
% 2.03/1.19  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.03/1.19  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.03/1.19  tff(c_38, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.03/1.19  tff(c_30, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.03/1.19  tff(c_20, plain, (k4_yellow_6('#skF_1', '#skF_2')!=k11_yellow_6('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.03/1.19  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.03/1.19  tff(c_22, plain, (l1_waybel_0('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.03/1.19  tff(c_28, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.03/1.19  tff(c_26, plain, (v7_waybel_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.03/1.19  tff(c_34, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.03/1.19  tff(c_24, plain, (v1_yellow_6('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.03/1.19  tff(c_4, plain, (![B_4, A_2]: (v3_yellow_6(B_4, A_2) | ~v1_yellow_6(B_4, A_2) | ~v7_waybel_0(B_4) | ~v4_orders_2(B_4) | v2_struct_0(B_4) | ~l1_waybel_0(B_4, A_2) | ~l1_pre_topc(A_2) | ~v2_pre_topc(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.03/1.19  tff(c_16, plain, (![A_12, B_13]: (m1_subset_1(k4_yellow_6(A_12, B_13), u1_struct_0(A_12)) | ~l1_waybel_0(B_13, A_12) | ~l1_struct_0(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.03/1.19  tff(c_18, plain, (![A_14, B_16]: (r2_hidden(k4_yellow_6(A_14, B_16), k10_yellow_6(A_14, B_16)) | ~l1_waybel_0(B_16, A_14) | ~v1_yellow_6(B_16, A_14) | ~v7_waybel_0(B_16) | ~v4_orders_2(B_16) | v2_struct_0(B_16) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.03/1.19  tff(c_44, plain, (![A_27, B_28, C_29]: (k11_yellow_6(A_27, B_28)=C_29 | ~r2_hidden(C_29, k10_yellow_6(A_27, B_28)) | ~m1_subset_1(C_29, u1_struct_0(A_27)) | ~l1_waybel_0(B_28, A_27) | ~v3_yellow_6(B_28, A_27) | ~v7_waybel_0(B_28) | ~v4_orders_2(B_28) | v2_struct_0(B_28) | ~l1_pre_topc(A_27) | ~v8_pre_topc(A_27) | ~v2_pre_topc(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.03/1.19  tff(c_54, plain, (![A_30, B_31]: (k4_yellow_6(A_30, B_31)=k11_yellow_6(A_30, B_31) | ~m1_subset_1(k4_yellow_6(A_30, B_31), u1_struct_0(A_30)) | ~v3_yellow_6(B_31, A_30) | ~v8_pre_topc(A_30) | ~l1_waybel_0(B_31, A_30) | ~v1_yellow_6(B_31, A_30) | ~v7_waybel_0(B_31) | ~v4_orders_2(B_31) | v2_struct_0(B_31) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30) | v2_struct_0(A_30))), inference(resolution, [status(thm)], [c_18, c_44])).
% 2.03/1.19  tff(c_59, plain, (![A_32, B_33]: (k4_yellow_6(A_32, B_33)=k11_yellow_6(A_32, B_33) | ~v3_yellow_6(B_33, A_32) | ~v8_pre_topc(A_32) | ~v1_yellow_6(B_33, A_32) | ~v7_waybel_0(B_33) | ~v4_orders_2(B_33) | v2_struct_0(B_33) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32) | ~l1_waybel_0(B_33, A_32) | ~l1_struct_0(A_32) | v2_struct_0(A_32))), inference(resolution, [status(thm)], [c_16, c_54])).
% 2.03/1.19  tff(c_64, plain, (![A_34, B_35]: (k4_yellow_6(A_34, B_35)=k11_yellow_6(A_34, B_35) | ~v8_pre_topc(A_34) | ~l1_struct_0(A_34) | ~v1_yellow_6(B_35, A_34) | ~v7_waybel_0(B_35) | ~v4_orders_2(B_35) | v2_struct_0(B_35) | ~l1_waybel_0(B_35, A_34) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34) | v2_struct_0(A_34))), inference(resolution, [status(thm)], [c_4, c_59])).
% 2.03/1.19  tff(c_67, plain, (k4_yellow_6('#skF_1', '#skF_2')=k11_yellow_6('#skF_1', '#skF_2') | ~v8_pre_topc('#skF_1') | ~l1_struct_0('#skF_1') | ~v7_waybel_0('#skF_2') | ~v4_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~l1_waybel_0('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_24, c_64])).
% 2.03/1.19  tff(c_70, plain, (k4_yellow_6('#skF_1', '#skF_2')=k11_yellow_6('#skF_1', '#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_22, c_28, c_26, c_34, c_67])).
% 2.03/1.19  tff(c_71, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_38, c_30, c_20, c_70])).
% 2.03/1.19  tff(c_74, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2, c_71])).
% 2.03/1.19  tff(c_78, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_74])).
% 2.03/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.19  
% 2.03/1.19  Inference rules
% 2.03/1.19  ----------------------
% 2.03/1.19  #Ref     : 0
% 2.03/1.19  #Sup     : 6
% 2.03/1.19  #Fact    : 0
% 2.03/1.19  #Define  : 0
% 2.03/1.19  #Split   : 0
% 2.03/1.19  #Chain   : 0
% 2.03/1.19  #Close   : 0
% 2.03/1.19  
% 2.03/1.19  Ordering : KBO
% 2.03/1.19  
% 2.03/1.19  Simplification rules
% 2.03/1.19  ----------------------
% 2.03/1.19  #Subsume      : 1
% 2.03/1.19  #Demod        : 7
% 2.03/1.19  #Tautology    : 4
% 2.03/1.19  #SimpNegUnit  : 1
% 2.03/1.19  #BackRed      : 0
% 2.03/1.19  
% 2.03/1.19  #Partial instantiations: 0
% 2.03/1.19  #Strategies tried      : 1
% 2.03/1.19  
% 2.03/1.19  Timing (in seconds)
% 2.03/1.19  ----------------------
% 2.03/1.20  Preprocessing        : 0.31
% 2.03/1.20  Parsing              : 0.16
% 2.03/1.20  CNF conversion       : 0.02
% 2.03/1.20  Main loop            : 0.13
% 2.03/1.20  Inferencing          : 0.06
% 2.03/1.20  Reduction            : 0.04
% 2.03/1.20  Demodulation         : 0.03
% 2.03/1.20  BG Simplification    : 0.02
% 2.03/1.20  Subsumption          : 0.02
% 2.03/1.20  Abstraction          : 0.01
% 2.03/1.20  MUC search           : 0.00
% 2.03/1.20  Cooper               : 0.00
% 2.03/1.20  Total                : 0.47
% 2.03/1.20  Index Insertion      : 0.00
% 2.03/1.20  Index Deletion       : 0.00
% 2.03/1.20  Index Matching       : 0.00
% 2.03/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
