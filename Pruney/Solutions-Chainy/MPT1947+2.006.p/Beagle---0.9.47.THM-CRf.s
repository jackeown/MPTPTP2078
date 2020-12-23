%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:55 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   51 (  61 expanded)
%              Number of leaves         :   27 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :  178 ( 277 expanded)
%              Number of equality atoms :    9 (  18 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_yellow_6 > v1_yellow_6 > r2_hidden > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k4_yellow_6 > k11_yellow_6 > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_150,negated_conjecture,(
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

tff(f_59,axiom,(
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

tff(f_126,axiom,(
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

tff(f_105,axiom,(
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

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_87,axiom,(
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

tff(c_38,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_20,plain,(
    k4_yellow_6('#skF_1','#skF_2') != k11_yellow_6('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_22,plain,(
    l1_waybel_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_28,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_26,plain,(
    v7_waybel_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_34,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_24,plain,(
    v1_yellow_6('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_4,plain,(
    ! [B_6,A_4] :
      ( v3_yellow_6(B_6,A_4)
      | ~ v1_yellow_6(B_6,A_4)
      | ~ v7_waybel_0(B_6)
      | ~ v4_orders_2(B_6)
      | v2_struct_0(B_6)
      | ~ l1_waybel_0(B_6,A_4)
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_46,plain,(
    ! [A_30,B_31] :
      ( r2_hidden(k4_yellow_6(A_30,B_31),k10_yellow_6(A_30,B_31))
      | ~ l1_waybel_0(B_31,A_30)
      | ~ v1_yellow_6(B_31,A_30)
      | ~ v7_waybel_0(B_31)
      | ~ v4_orders_2(B_31)
      | v2_struct_0(B_31)
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_41,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(k10_yellow_6(A_25,B_26),k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_waybel_0(B_26,A_25)
      | ~ v7_waybel_0(B_26)
      | ~ v4_orders_2(B_26)
      | v2_struct_0(B_26)
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( m1_subset_1(A_1,C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    ! [A_1,A_25,B_26] :
      ( m1_subset_1(A_1,u1_struct_0(A_25))
      | ~ r2_hidden(A_1,k10_yellow_6(A_25,B_26))
      | ~ l1_waybel_0(B_26,A_25)
      | ~ v7_waybel_0(B_26)
      | ~ v4_orders_2(B_26)
      | v2_struct_0(B_26)
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(resolution,[status(thm)],[c_41,c_2])).

tff(c_50,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(k4_yellow_6(A_30,B_31),u1_struct_0(A_30))
      | ~ l1_waybel_0(B_31,A_30)
      | ~ v1_yellow_6(B_31,A_30)
      | ~ v7_waybel_0(B_31)
      | ~ v4_orders_2(B_31)
      | v2_struct_0(B_31)
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(resolution,[status(thm)],[c_46,c_44])).

tff(c_18,plain,(
    ! [A_16,B_18] :
      ( r2_hidden(k4_yellow_6(A_16,B_18),k10_yellow_6(A_16,B_18))
      | ~ l1_waybel_0(B_18,A_16)
      | ~ v1_yellow_6(B_18,A_16)
      | ~ v7_waybel_0(B_18)
      | ~ v4_orders_2(B_18)
      | v2_struct_0(B_18)
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_51,plain,(
    ! [A_32,B_33,C_34] :
      ( k11_yellow_6(A_32,B_33) = C_34
      | ~ r2_hidden(C_34,k10_yellow_6(A_32,B_33))
      | ~ m1_subset_1(C_34,u1_struct_0(A_32))
      | ~ l1_waybel_0(B_33,A_32)
      | ~ v3_yellow_6(B_33,A_32)
      | ~ v7_waybel_0(B_33)
      | ~ v4_orders_2(B_33)
      | v2_struct_0(B_33)
      | ~ l1_pre_topc(A_32)
      | ~ v8_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_67,plain,(
    ! [A_39,B_40] :
      ( k4_yellow_6(A_39,B_40) = k11_yellow_6(A_39,B_40)
      | ~ m1_subset_1(k4_yellow_6(A_39,B_40),u1_struct_0(A_39))
      | ~ v3_yellow_6(B_40,A_39)
      | ~ v8_pre_topc(A_39)
      | ~ l1_waybel_0(B_40,A_39)
      | ~ v1_yellow_6(B_40,A_39)
      | ~ v7_waybel_0(B_40)
      | ~ v4_orders_2(B_40)
      | v2_struct_0(B_40)
      | ~ l1_pre_topc(A_39)
      | ~ v2_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_18,c_51])).

tff(c_72,plain,(
    ! [A_41,B_42] :
      ( k4_yellow_6(A_41,B_42) = k11_yellow_6(A_41,B_42)
      | ~ v3_yellow_6(B_42,A_41)
      | ~ v8_pre_topc(A_41)
      | ~ l1_waybel_0(B_42,A_41)
      | ~ v1_yellow_6(B_42,A_41)
      | ~ v7_waybel_0(B_42)
      | ~ v4_orders_2(B_42)
      | v2_struct_0(B_42)
      | ~ l1_pre_topc(A_41)
      | ~ v2_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_50,c_67])).

tff(c_77,plain,(
    ! [A_43,B_44] :
      ( k4_yellow_6(A_43,B_44) = k11_yellow_6(A_43,B_44)
      | ~ v8_pre_topc(A_43)
      | ~ v1_yellow_6(B_44,A_43)
      | ~ v7_waybel_0(B_44)
      | ~ v4_orders_2(B_44)
      | v2_struct_0(B_44)
      | ~ l1_waybel_0(B_44,A_43)
      | ~ l1_pre_topc(A_43)
      | ~ v2_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(resolution,[status(thm)],[c_4,c_72])).

tff(c_80,plain,
    ( k4_yellow_6('#skF_1','#skF_2') = k11_yellow_6('#skF_1','#skF_2')
    | ~ v8_pre_topc('#skF_1')
    | ~ v7_waybel_0('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_waybel_0('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_77])).

tff(c_83,plain,
    ( k4_yellow_6('#skF_1','#skF_2') = k11_yellow_6('#skF_1','#skF_2')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_22,c_28,c_26,c_34,c_80])).

tff(c_85,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_30,c_20,c_83])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:20:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.26  
% 2.07/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.26  %$ v3_yellow_6 > v1_yellow_6 > r2_hidden > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k4_yellow_6 > k11_yellow_6 > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.07/1.26  
% 2.07/1.26  %Foreground sorts:
% 2.07/1.26  
% 2.07/1.26  
% 2.07/1.26  %Background operators:
% 2.07/1.26  
% 2.07/1.26  
% 2.07/1.26  %Foreground operators:
% 2.07/1.26  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.07/1.26  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 2.07/1.26  tff(k4_yellow_6, type, k4_yellow_6: ($i * $i) > $i).
% 2.07/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.26  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 2.07/1.26  tff(v3_yellow_6, type, v3_yellow_6: ($i * $i) > $o).
% 2.07/1.26  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.07/1.26  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.07/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.26  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.07/1.26  tff(v1_yellow_6, type, v1_yellow_6: ($i * $i) > $o).
% 2.07/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.07/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.26  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.07/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.26  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.07/1.26  tff(k11_yellow_6, type, k11_yellow_6: ($i * $i) > $i).
% 2.07/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.07/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.07/1.26  
% 2.07/1.28  tff(f_150, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v8_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v1_yellow_6(B, A)) & l1_waybel_0(B, A)) => (k11_yellow_6(A, B) = k4_yellow_6(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_yellow_6)).
% 2.07/1.28  tff(f_59, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (l1_waybel_0(B, A) => ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v1_yellow_6(B, A)) => (((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v3_yellow_6(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_yellow_6)).
% 2.07/1.28  tff(f_126, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v1_yellow_6(B, A)) & l1_waybel_0(B, A)) => r2_hidden(k4_yellow_6(A, B), k10_yellow_6(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_yellow_6)).
% 2.07/1.28  tff(f_105, axiom, (![A, B]: (((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => m1_subset_1(k10_yellow_6(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 2.07/1.28  tff(f_31, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.07/1.28  tff(f_87, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v8_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v3_yellow_6(B, A)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k11_yellow_6(A, B)) <=> r2_hidden(C, k10_yellow_6(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_yellow_6)).
% 2.07/1.28  tff(c_38, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.07/1.28  tff(c_30, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.07/1.28  tff(c_20, plain, (k4_yellow_6('#skF_1', '#skF_2')!=k11_yellow_6('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.07/1.28  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.07/1.28  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.07/1.28  tff(c_22, plain, (l1_waybel_0('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.07/1.28  tff(c_28, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.07/1.28  tff(c_26, plain, (v7_waybel_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.07/1.28  tff(c_34, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.07/1.28  tff(c_24, plain, (v1_yellow_6('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.07/1.28  tff(c_4, plain, (![B_6, A_4]: (v3_yellow_6(B_6, A_4) | ~v1_yellow_6(B_6, A_4) | ~v7_waybel_0(B_6) | ~v4_orders_2(B_6) | v2_struct_0(B_6) | ~l1_waybel_0(B_6, A_4) | ~l1_pre_topc(A_4) | ~v2_pre_topc(A_4) | v2_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.07/1.28  tff(c_46, plain, (![A_30, B_31]: (r2_hidden(k4_yellow_6(A_30, B_31), k10_yellow_6(A_30, B_31)) | ~l1_waybel_0(B_31, A_30) | ~v1_yellow_6(B_31, A_30) | ~v7_waybel_0(B_31) | ~v4_orders_2(B_31) | v2_struct_0(B_31) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.07/1.28  tff(c_41, plain, (![A_25, B_26]: (m1_subset_1(k10_yellow_6(A_25, B_26), k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_waybel_0(B_26, A_25) | ~v7_waybel_0(B_26) | ~v4_orders_2(B_26) | v2_struct_0(B_26) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.07/1.28  tff(c_2, plain, (![A_1, C_3, B_2]: (m1_subset_1(A_1, C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.07/1.28  tff(c_44, plain, (![A_1, A_25, B_26]: (m1_subset_1(A_1, u1_struct_0(A_25)) | ~r2_hidden(A_1, k10_yellow_6(A_25, B_26)) | ~l1_waybel_0(B_26, A_25) | ~v7_waybel_0(B_26) | ~v4_orders_2(B_26) | v2_struct_0(B_26) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(resolution, [status(thm)], [c_41, c_2])).
% 2.07/1.28  tff(c_50, plain, (![A_30, B_31]: (m1_subset_1(k4_yellow_6(A_30, B_31), u1_struct_0(A_30)) | ~l1_waybel_0(B_31, A_30) | ~v1_yellow_6(B_31, A_30) | ~v7_waybel_0(B_31) | ~v4_orders_2(B_31) | v2_struct_0(B_31) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30) | v2_struct_0(A_30))), inference(resolution, [status(thm)], [c_46, c_44])).
% 2.07/1.28  tff(c_18, plain, (![A_16, B_18]: (r2_hidden(k4_yellow_6(A_16, B_18), k10_yellow_6(A_16, B_18)) | ~l1_waybel_0(B_18, A_16) | ~v1_yellow_6(B_18, A_16) | ~v7_waybel_0(B_18) | ~v4_orders_2(B_18) | v2_struct_0(B_18) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.07/1.28  tff(c_51, plain, (![A_32, B_33, C_34]: (k11_yellow_6(A_32, B_33)=C_34 | ~r2_hidden(C_34, k10_yellow_6(A_32, B_33)) | ~m1_subset_1(C_34, u1_struct_0(A_32)) | ~l1_waybel_0(B_33, A_32) | ~v3_yellow_6(B_33, A_32) | ~v7_waybel_0(B_33) | ~v4_orders_2(B_33) | v2_struct_0(B_33) | ~l1_pre_topc(A_32) | ~v8_pre_topc(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.07/1.28  tff(c_67, plain, (![A_39, B_40]: (k4_yellow_6(A_39, B_40)=k11_yellow_6(A_39, B_40) | ~m1_subset_1(k4_yellow_6(A_39, B_40), u1_struct_0(A_39)) | ~v3_yellow_6(B_40, A_39) | ~v8_pre_topc(A_39) | ~l1_waybel_0(B_40, A_39) | ~v1_yellow_6(B_40, A_39) | ~v7_waybel_0(B_40) | ~v4_orders_2(B_40) | v2_struct_0(B_40) | ~l1_pre_topc(A_39) | ~v2_pre_topc(A_39) | v2_struct_0(A_39))), inference(resolution, [status(thm)], [c_18, c_51])).
% 2.07/1.28  tff(c_72, plain, (![A_41, B_42]: (k4_yellow_6(A_41, B_42)=k11_yellow_6(A_41, B_42) | ~v3_yellow_6(B_42, A_41) | ~v8_pre_topc(A_41) | ~l1_waybel_0(B_42, A_41) | ~v1_yellow_6(B_42, A_41) | ~v7_waybel_0(B_42) | ~v4_orders_2(B_42) | v2_struct_0(B_42) | ~l1_pre_topc(A_41) | ~v2_pre_topc(A_41) | v2_struct_0(A_41))), inference(resolution, [status(thm)], [c_50, c_67])).
% 2.07/1.28  tff(c_77, plain, (![A_43, B_44]: (k4_yellow_6(A_43, B_44)=k11_yellow_6(A_43, B_44) | ~v8_pre_topc(A_43) | ~v1_yellow_6(B_44, A_43) | ~v7_waybel_0(B_44) | ~v4_orders_2(B_44) | v2_struct_0(B_44) | ~l1_waybel_0(B_44, A_43) | ~l1_pre_topc(A_43) | ~v2_pre_topc(A_43) | v2_struct_0(A_43))), inference(resolution, [status(thm)], [c_4, c_72])).
% 2.07/1.28  tff(c_80, plain, (k4_yellow_6('#skF_1', '#skF_2')=k11_yellow_6('#skF_1', '#skF_2') | ~v8_pre_topc('#skF_1') | ~v7_waybel_0('#skF_2') | ~v4_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~l1_waybel_0('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_24, c_77])).
% 2.07/1.28  tff(c_83, plain, (k4_yellow_6('#skF_1', '#skF_2')=k11_yellow_6('#skF_1', '#skF_2') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_22, c_28, c_26, c_34, c_80])).
% 2.07/1.28  tff(c_85, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_30, c_20, c_83])).
% 2.07/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.28  
% 2.07/1.28  Inference rules
% 2.07/1.28  ----------------------
% 2.07/1.28  #Ref     : 0
% 2.07/1.28  #Sup     : 8
% 2.07/1.28  #Fact    : 0
% 2.07/1.28  #Define  : 0
% 2.07/1.28  #Split   : 0
% 2.07/1.28  #Chain   : 0
% 2.07/1.28  #Close   : 0
% 2.07/1.28  
% 2.07/1.28  Ordering : KBO
% 2.07/1.28  
% 2.07/1.28  Simplification rules
% 2.07/1.28  ----------------------
% 2.07/1.28  #Subsume      : 2
% 2.07/1.28  #Demod        : 6
% 2.07/1.28  #Tautology    : 5
% 2.07/1.28  #SimpNegUnit  : 1
% 2.07/1.28  #BackRed      : 0
% 2.07/1.28  
% 2.07/1.28  #Partial instantiations: 0
% 2.07/1.28  #Strategies tried      : 1
% 2.07/1.28  
% 2.07/1.28  Timing (in seconds)
% 2.07/1.28  ----------------------
% 2.07/1.28  Preprocessing        : 0.34
% 2.07/1.28  Parsing              : 0.18
% 2.07/1.28  CNF conversion       : 0.02
% 2.07/1.28  Main loop            : 0.14
% 2.07/1.28  Inferencing          : 0.06
% 2.07/1.28  Reduction            : 0.04
% 2.07/1.28  Demodulation         : 0.03
% 2.07/1.28  BG Simplification    : 0.02
% 2.07/1.28  Subsumption          : 0.02
% 2.07/1.28  Abstraction          : 0.01
% 2.07/1.28  MUC search           : 0.00
% 2.07/1.28  Cooper               : 0.00
% 2.07/1.28  Total                : 0.51
% 2.07/1.28  Index Insertion      : 0.00
% 2.07/1.28  Index Deletion       : 0.00
% 2.07/1.28  Index Matching       : 0.00
% 2.07/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
