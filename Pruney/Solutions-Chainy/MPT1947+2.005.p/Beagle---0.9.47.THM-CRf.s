%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:55 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   54 (  64 expanded)
%              Number of leaves         :   28 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :  192 ( 291 expanded)
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

tff(f_155,negated_conjecture,(
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

tff(f_64,axiom,(
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

tff(f_110,axiom,(
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

tff(f_131,axiom,(
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
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_92,axiom,(
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

tff(c_40,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_22,plain,(
    k4_yellow_6('#skF_1','#skF_2') != k11_yellow_6('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_24,plain,(
    l1_waybel_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_30,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_28,plain,(
    v7_waybel_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_36,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_26,plain,(
    v1_yellow_6('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_6,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k10_yellow_6(A_17,B_18),k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_waybel_0(B_18,A_17)
      | ~ v7_waybel_0(B_18)
      | ~ v4_orders_2(B_18)
      | v2_struct_0(B_18)
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_45,plain,(
    ! [A_32,B_33] :
      ( r2_hidden(k4_yellow_6(A_32,B_33),k10_yellow_6(A_32,B_33))
      | ~ l1_waybel_0(B_33,A_32)
      | ~ v1_yellow_6(B_33,A_32)
      | ~ v7_waybel_0(B_33)
      | ~ v4_orders_2(B_33)
      | v2_struct_0(B_33)
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_62,plain,(
    ! [A_38,B_39,A_40] :
      ( r2_hidden(k4_yellow_6(A_38,B_39),A_40)
      | ~ m1_subset_1(k10_yellow_6(A_38,B_39),k1_zfmisc_1(A_40))
      | ~ l1_waybel_0(B_39,A_38)
      | ~ v1_yellow_6(B_39,A_38)
      | ~ v7_waybel_0(B_39)
      | ~ v4_orders_2(B_39)
      | v2_struct_0(B_39)
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_45,c_2])).

tff(c_67,plain,(
    ! [A_41,B_42] :
      ( r2_hidden(k4_yellow_6(A_41,B_42),u1_struct_0(A_41))
      | ~ v1_yellow_6(B_42,A_41)
      | ~ l1_waybel_0(B_42,A_41)
      | ~ v7_waybel_0(B_42)
      | ~ v4_orders_2(B_42)
      | v2_struct_0(B_42)
      | ~ l1_pre_topc(A_41)
      | ~ v2_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_18,c_62])).

tff(c_4,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_74,plain,(
    ! [A_41,B_42] :
      ( m1_subset_1(k4_yellow_6(A_41,B_42),u1_struct_0(A_41))
      | ~ v1_yellow_6(B_42,A_41)
      | ~ l1_waybel_0(B_42,A_41)
      | ~ v7_waybel_0(B_42)
      | ~ v4_orders_2(B_42)
      | v2_struct_0(B_42)
      | ~ l1_pre_topc(A_41)
      | ~ v2_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_67,c_4])).

tff(c_20,plain,(
    ! [A_19,B_21] :
      ( r2_hidden(k4_yellow_6(A_19,B_21),k10_yellow_6(A_19,B_21))
      | ~ l1_waybel_0(B_21,A_19)
      | ~ v1_yellow_6(B_21,A_19)
      | ~ v7_waybel_0(B_21)
      | ~ v4_orders_2(B_21)
      | v2_struct_0(B_21)
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_75,plain,(
    ! [A_43,B_44,C_45] :
      ( k11_yellow_6(A_43,B_44) = C_45
      | ~ r2_hidden(C_45,k10_yellow_6(A_43,B_44))
      | ~ m1_subset_1(C_45,u1_struct_0(A_43))
      | ~ l1_waybel_0(B_44,A_43)
      | ~ v3_yellow_6(B_44,A_43)
      | ~ v7_waybel_0(B_44)
      | ~ v4_orders_2(B_44)
      | v2_struct_0(B_44)
      | ~ l1_pre_topc(A_43)
      | ~ v8_pre_topc(A_43)
      | ~ v2_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_88,plain,(
    ! [A_53,B_54] :
      ( k4_yellow_6(A_53,B_54) = k11_yellow_6(A_53,B_54)
      | ~ m1_subset_1(k4_yellow_6(A_53,B_54),u1_struct_0(A_53))
      | ~ v3_yellow_6(B_54,A_53)
      | ~ v8_pre_topc(A_53)
      | ~ l1_waybel_0(B_54,A_53)
      | ~ v1_yellow_6(B_54,A_53)
      | ~ v7_waybel_0(B_54)
      | ~ v4_orders_2(B_54)
      | v2_struct_0(B_54)
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(resolution,[status(thm)],[c_20,c_75])).

tff(c_93,plain,(
    ! [A_55,B_56] :
      ( k4_yellow_6(A_55,B_56) = k11_yellow_6(A_55,B_56)
      | ~ v3_yellow_6(B_56,A_55)
      | ~ v8_pre_topc(A_55)
      | ~ v1_yellow_6(B_56,A_55)
      | ~ l1_waybel_0(B_56,A_55)
      | ~ v7_waybel_0(B_56)
      | ~ v4_orders_2(B_56)
      | v2_struct_0(B_56)
      | ~ l1_pre_topc(A_55)
      | ~ v2_pre_topc(A_55)
      | v2_struct_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_74,c_88])).

tff(c_102,plain,(
    ! [A_60,B_61] :
      ( k4_yellow_6(A_60,B_61) = k11_yellow_6(A_60,B_61)
      | ~ v8_pre_topc(A_60)
      | ~ v1_yellow_6(B_61,A_60)
      | ~ v7_waybel_0(B_61)
      | ~ v4_orders_2(B_61)
      | v2_struct_0(B_61)
      | ~ l1_waybel_0(B_61,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_6,c_93])).

tff(c_105,plain,
    ( k4_yellow_6('#skF_1','#skF_2') = k11_yellow_6('#skF_1','#skF_2')
    | ~ v8_pre_topc('#skF_1')
    | ~ v7_waybel_0('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_waybel_0('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_102])).

tff(c_108,plain,
    ( k4_yellow_6('#skF_1','#skF_2') = k11_yellow_6('#skF_1','#skF_2')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_24,c_30,c_28,c_36,c_105])).

tff(c_110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_32,c_22,c_108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:56:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.22  
% 2.19/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.23  %$ v3_yellow_6 > v1_yellow_6 > r2_hidden > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k4_yellow_6 > k11_yellow_6 > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.19/1.23  
% 2.19/1.23  %Foreground sorts:
% 2.19/1.23  
% 2.19/1.23  
% 2.19/1.23  %Background operators:
% 2.19/1.23  
% 2.19/1.23  
% 2.19/1.23  %Foreground operators:
% 2.19/1.23  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.19/1.23  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 2.19/1.23  tff(k4_yellow_6, type, k4_yellow_6: ($i * $i) > $i).
% 2.19/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.23  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 2.19/1.23  tff(v3_yellow_6, type, v3_yellow_6: ($i * $i) > $o).
% 2.19/1.23  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.19/1.23  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.19/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.19/1.23  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.19/1.23  tff(v1_yellow_6, type, v1_yellow_6: ($i * $i) > $o).
% 2.19/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.23  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.19/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.23  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.19/1.23  tff(k11_yellow_6, type, k11_yellow_6: ($i * $i) > $i).
% 2.19/1.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.19/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.23  
% 2.19/1.24  tff(f_155, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v8_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v1_yellow_6(B, A)) & l1_waybel_0(B, A)) => (k11_yellow_6(A, B) = k4_yellow_6(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_yellow_6)).
% 2.19/1.24  tff(f_64, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (l1_waybel_0(B, A) => ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v1_yellow_6(B, A)) => (((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v3_yellow_6(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_yellow_6)).
% 2.19/1.24  tff(f_110, axiom, (![A, B]: (((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => m1_subset_1(k10_yellow_6(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 2.19/1.24  tff(f_131, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v1_yellow_6(B, A)) & l1_waybel_0(B, A)) => r2_hidden(k4_yellow_6(A, B), k10_yellow_6(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_yellow_6)).
% 2.19/1.24  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.19/1.24  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.19/1.24  tff(f_92, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v8_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v3_yellow_6(B, A)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k11_yellow_6(A, B)) <=> r2_hidden(C, k10_yellow_6(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_yellow_6)).
% 2.19/1.24  tff(c_40, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 2.19/1.24  tff(c_32, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 2.19/1.24  tff(c_22, plain, (k4_yellow_6('#skF_1', '#skF_2')!=k11_yellow_6('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 2.19/1.24  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 2.19/1.24  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 2.19/1.24  tff(c_24, plain, (l1_waybel_0('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 2.19/1.24  tff(c_30, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 2.19/1.24  tff(c_28, plain, (v7_waybel_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 2.19/1.24  tff(c_36, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 2.19/1.24  tff(c_26, plain, (v1_yellow_6('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 2.19/1.24  tff(c_6, plain, (![B_9, A_7]: (v3_yellow_6(B_9, A_7) | ~v1_yellow_6(B_9, A_7) | ~v7_waybel_0(B_9) | ~v4_orders_2(B_9) | v2_struct_0(B_9) | ~l1_waybel_0(B_9, A_7) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.19/1.24  tff(c_18, plain, (![A_17, B_18]: (m1_subset_1(k10_yellow_6(A_17, B_18), k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_waybel_0(B_18, A_17) | ~v7_waybel_0(B_18) | ~v4_orders_2(B_18) | v2_struct_0(B_18) | ~l1_pre_topc(A_17) | ~v2_pre_topc(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.19/1.24  tff(c_45, plain, (![A_32, B_33]: (r2_hidden(k4_yellow_6(A_32, B_33), k10_yellow_6(A_32, B_33)) | ~l1_waybel_0(B_33, A_32) | ~v1_yellow_6(B_33, A_32) | ~v7_waybel_0(B_33) | ~v4_orders_2(B_33) | v2_struct_0(B_33) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.19/1.24  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.19/1.24  tff(c_62, plain, (![A_38, B_39, A_40]: (r2_hidden(k4_yellow_6(A_38, B_39), A_40) | ~m1_subset_1(k10_yellow_6(A_38, B_39), k1_zfmisc_1(A_40)) | ~l1_waybel_0(B_39, A_38) | ~v1_yellow_6(B_39, A_38) | ~v7_waybel_0(B_39) | ~v4_orders_2(B_39) | v2_struct_0(B_39) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38) | v2_struct_0(A_38))), inference(resolution, [status(thm)], [c_45, c_2])).
% 2.19/1.24  tff(c_67, plain, (![A_41, B_42]: (r2_hidden(k4_yellow_6(A_41, B_42), u1_struct_0(A_41)) | ~v1_yellow_6(B_42, A_41) | ~l1_waybel_0(B_42, A_41) | ~v7_waybel_0(B_42) | ~v4_orders_2(B_42) | v2_struct_0(B_42) | ~l1_pre_topc(A_41) | ~v2_pre_topc(A_41) | v2_struct_0(A_41))), inference(resolution, [status(thm)], [c_18, c_62])).
% 2.19/1.24  tff(c_4, plain, (![A_5, B_6]: (m1_subset_1(A_5, B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.19/1.24  tff(c_74, plain, (![A_41, B_42]: (m1_subset_1(k4_yellow_6(A_41, B_42), u1_struct_0(A_41)) | ~v1_yellow_6(B_42, A_41) | ~l1_waybel_0(B_42, A_41) | ~v7_waybel_0(B_42) | ~v4_orders_2(B_42) | v2_struct_0(B_42) | ~l1_pre_topc(A_41) | ~v2_pre_topc(A_41) | v2_struct_0(A_41))), inference(resolution, [status(thm)], [c_67, c_4])).
% 2.19/1.24  tff(c_20, plain, (![A_19, B_21]: (r2_hidden(k4_yellow_6(A_19, B_21), k10_yellow_6(A_19, B_21)) | ~l1_waybel_0(B_21, A_19) | ~v1_yellow_6(B_21, A_19) | ~v7_waybel_0(B_21) | ~v4_orders_2(B_21) | v2_struct_0(B_21) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.19/1.24  tff(c_75, plain, (![A_43, B_44, C_45]: (k11_yellow_6(A_43, B_44)=C_45 | ~r2_hidden(C_45, k10_yellow_6(A_43, B_44)) | ~m1_subset_1(C_45, u1_struct_0(A_43)) | ~l1_waybel_0(B_44, A_43) | ~v3_yellow_6(B_44, A_43) | ~v7_waybel_0(B_44) | ~v4_orders_2(B_44) | v2_struct_0(B_44) | ~l1_pre_topc(A_43) | ~v8_pre_topc(A_43) | ~v2_pre_topc(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.19/1.24  tff(c_88, plain, (![A_53, B_54]: (k4_yellow_6(A_53, B_54)=k11_yellow_6(A_53, B_54) | ~m1_subset_1(k4_yellow_6(A_53, B_54), u1_struct_0(A_53)) | ~v3_yellow_6(B_54, A_53) | ~v8_pre_topc(A_53) | ~l1_waybel_0(B_54, A_53) | ~v1_yellow_6(B_54, A_53) | ~v7_waybel_0(B_54) | ~v4_orders_2(B_54) | v2_struct_0(B_54) | ~l1_pre_topc(A_53) | ~v2_pre_topc(A_53) | v2_struct_0(A_53))), inference(resolution, [status(thm)], [c_20, c_75])).
% 2.19/1.24  tff(c_93, plain, (![A_55, B_56]: (k4_yellow_6(A_55, B_56)=k11_yellow_6(A_55, B_56) | ~v3_yellow_6(B_56, A_55) | ~v8_pre_topc(A_55) | ~v1_yellow_6(B_56, A_55) | ~l1_waybel_0(B_56, A_55) | ~v7_waybel_0(B_56) | ~v4_orders_2(B_56) | v2_struct_0(B_56) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55) | v2_struct_0(A_55))), inference(resolution, [status(thm)], [c_74, c_88])).
% 2.19/1.24  tff(c_102, plain, (![A_60, B_61]: (k4_yellow_6(A_60, B_61)=k11_yellow_6(A_60, B_61) | ~v8_pre_topc(A_60) | ~v1_yellow_6(B_61, A_60) | ~v7_waybel_0(B_61) | ~v4_orders_2(B_61) | v2_struct_0(B_61) | ~l1_waybel_0(B_61, A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(resolution, [status(thm)], [c_6, c_93])).
% 2.19/1.24  tff(c_105, plain, (k4_yellow_6('#skF_1', '#skF_2')=k11_yellow_6('#skF_1', '#skF_2') | ~v8_pre_topc('#skF_1') | ~v7_waybel_0('#skF_2') | ~v4_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~l1_waybel_0('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_102])).
% 2.19/1.24  tff(c_108, plain, (k4_yellow_6('#skF_1', '#skF_2')=k11_yellow_6('#skF_1', '#skF_2') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_24, c_30, c_28, c_36, c_105])).
% 2.19/1.24  tff(c_110, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_32, c_22, c_108])).
% 2.19/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.24  
% 2.19/1.24  Inference rules
% 2.19/1.24  ----------------------
% 2.19/1.24  #Ref     : 0
% 2.19/1.24  #Sup     : 13
% 2.19/1.24  #Fact    : 0
% 2.19/1.24  #Define  : 0
% 2.19/1.24  #Split   : 0
% 2.19/1.24  #Chain   : 0
% 2.19/1.24  #Close   : 0
% 2.19/1.24  
% 2.19/1.24  Ordering : KBO
% 2.19/1.24  
% 2.19/1.24  Simplification rules
% 2.19/1.24  ----------------------
% 2.19/1.24  #Subsume      : 2
% 2.19/1.24  #Demod        : 6
% 2.19/1.24  #Tautology    : 4
% 2.19/1.24  #SimpNegUnit  : 1
% 2.19/1.24  #BackRed      : 0
% 2.19/1.24  
% 2.19/1.24  #Partial instantiations: 0
% 2.19/1.24  #Strategies tried      : 1
% 2.19/1.24  
% 2.19/1.24  Timing (in seconds)
% 2.19/1.24  ----------------------
% 2.19/1.24  Preprocessing        : 0.31
% 2.19/1.24  Parsing              : 0.16
% 2.19/1.24  CNF conversion       : 0.02
% 2.19/1.24  Main loop            : 0.16
% 2.19/1.24  Inferencing          : 0.07
% 2.19/1.24  Reduction            : 0.04
% 2.19/1.24  Demodulation         : 0.03
% 2.19/1.24  BG Simplification    : 0.01
% 2.19/1.24  Subsumption          : 0.03
% 2.19/1.24  Abstraction          : 0.01
% 2.19/1.24  MUC search           : 0.00
% 2.19/1.24  Cooper               : 0.00
% 2.19/1.24  Total                : 0.50
% 2.19/1.24  Index Insertion      : 0.00
% 2.19/1.24  Index Deletion       : 0.00
% 2.19/1.24  Index Matching       : 0.00
% 2.19/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
