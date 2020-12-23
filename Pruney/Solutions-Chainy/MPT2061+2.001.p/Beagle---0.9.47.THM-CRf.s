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
% DateTime   : Thu Dec  3 10:31:38 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   50 (  96 expanded)
%              Number of leaves         :   21 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :  145 ( 414 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_0 > r1_waybel_0 > m2_yellow_6 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > k6_subset_1 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m2_yellow_6,type,(
    m2_yellow_6: ( $i * $i * $i ) > $o )).

tff(r2_waybel_0,type,(
    r2_waybel_0: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B,C] :
            ( ( ~ v2_struct_0(C)
              & v4_orders_2(C)
              & v7_waybel_0(C)
              & l1_waybel_0(C,A) )
           => ( r1_waybel_0(A,C,B)
             => ! [D] :
                  ( m2_yellow_6(D,A,C)
                 => r1_waybel_0(A,D,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_yellow19)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & v4_orders_2(B)
        & v7_waybel_0(B)
        & l1_waybel_0(B,A) )
     => ! [C] :
          ( m2_yellow_6(C,A,B)
         => ( ~ v2_struct_0(C)
            & v4_orders_2(C)
            & v7_waybel_0(C)
            & l1_waybel_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_yellow_6)).

tff(f_42,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r1_waybel_0(A,B,C)
            <=> ~ r2_waybel_0(A,B,k6_subset_1(u1_struct_0(A),C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_waybel_0)).

tff(f_91,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m2_yellow_6(C,A,B)
             => ! [D] :
                  ( r2_waybel_0(A,C,D)
                 => r2_waybel_0(A,B,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_6)).

tff(c_16,plain,(
    ~ r1_waybel_0('#skF_1','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_20,plain,(
    r1_waybel_0('#skF_1','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_30,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_22,plain,(
    l1_waybel_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_26,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_24,plain,(
    v7_waybel_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_18,plain,(
    m2_yellow_6('#skF_4','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_41,plain,(
    ! [C_35,A_36,B_37] :
      ( ~ v2_struct_0(C_35)
      | ~ m2_yellow_6(C_35,A_36,B_37)
      | ~ l1_waybel_0(B_37,A_36)
      | ~ v7_waybel_0(B_37)
      | ~ v4_orders_2(B_37)
      | v2_struct_0(B_37)
      | ~ l1_struct_0(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_44,plain,
    ( ~ v2_struct_0('#skF_4')
    | ~ l1_waybel_0('#skF_3','#skF_1')
    | ~ v7_waybel_0('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_41])).

tff(c_47,plain,
    ( ~ v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_24,c_22,c_44])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_28,c_47])).

tff(c_58,plain,(
    ! [C_44,A_45,B_46] :
      ( l1_waybel_0(C_44,A_45)
      | ~ m2_yellow_6(C_44,A_45,B_46)
      | ~ l1_waybel_0(B_46,A_45)
      | ~ v7_waybel_0(B_46)
      | ~ v4_orders_2(B_46)
      | v2_struct_0(B_46)
      | ~ l1_struct_0(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_61,plain,
    ( l1_waybel_0('#skF_4','#skF_1')
    | ~ l1_waybel_0('#skF_3','#skF_1')
    | ~ v7_waybel_0('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_58])).

tff(c_64,plain,
    ( l1_waybel_0('#skF_4','#skF_1')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_24,c_22,c_61])).

tff(c_65,plain,(
    l1_waybel_0('#skF_4','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_28,c_64])).

tff(c_4,plain,(
    ! [A_1,B_5,C_7] :
      ( r1_waybel_0(A_1,B_5,C_7)
      | r2_waybel_0(A_1,B_5,k6_subset_1(u1_struct_0(A_1),C_7))
      | ~ l1_waybel_0(B_5,A_1)
      | v2_struct_0(B_5)
      | ~ l1_struct_0(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_71,plain,(
    ! [A_50,B_51,D_52,C_53] :
      ( r2_waybel_0(A_50,B_51,D_52)
      | ~ r2_waybel_0(A_50,C_53,D_52)
      | ~ m2_yellow_6(C_53,A_50,B_51)
      | ~ l1_waybel_0(B_51,A_50)
      | ~ v7_waybel_0(B_51)
      | ~ v4_orders_2(B_51)
      | v2_struct_0(B_51)
      | ~ l1_struct_0(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_75,plain,(
    ! [A_54,B_55,C_56,B_57] :
      ( r2_waybel_0(A_54,B_55,k6_subset_1(u1_struct_0(A_54),C_56))
      | ~ m2_yellow_6(B_57,A_54,B_55)
      | ~ l1_waybel_0(B_55,A_54)
      | ~ v7_waybel_0(B_55)
      | ~ v4_orders_2(B_55)
      | v2_struct_0(B_55)
      | r1_waybel_0(A_54,B_57,C_56)
      | ~ l1_waybel_0(B_57,A_54)
      | v2_struct_0(B_57)
      | ~ l1_struct_0(A_54)
      | v2_struct_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_4,c_71])).

tff(c_77,plain,(
    ! [C_56] :
      ( r2_waybel_0('#skF_1','#skF_3',k6_subset_1(u1_struct_0('#skF_1'),C_56))
      | ~ l1_waybel_0('#skF_3','#skF_1')
      | ~ v7_waybel_0('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | v2_struct_0('#skF_3')
      | r1_waybel_0('#skF_1','#skF_4',C_56)
      | ~ l1_waybel_0('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_struct_0('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_18,c_75])).

tff(c_80,plain,(
    ! [C_56] :
      ( r2_waybel_0('#skF_1','#skF_3',k6_subset_1(u1_struct_0('#skF_1'),C_56))
      | v2_struct_0('#skF_3')
      | r1_waybel_0('#skF_1','#skF_4',C_56)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_65,c_26,c_24,c_22,c_77])).

tff(c_82,plain,(
    ! [C_58] :
      ( r2_waybel_0('#skF_1','#skF_3',k6_subset_1(u1_struct_0('#skF_1'),C_58))
      | r1_waybel_0('#skF_1','#skF_4',C_58) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_48,c_28,c_80])).

tff(c_2,plain,(
    ! [A_1,B_5,C_7] :
      ( ~ r2_waybel_0(A_1,B_5,k6_subset_1(u1_struct_0(A_1),C_7))
      | ~ r1_waybel_0(A_1,B_5,C_7)
      | ~ l1_waybel_0(B_5,A_1)
      | v2_struct_0(B_5)
      | ~ l1_struct_0(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_87,plain,(
    ! [C_58] :
      ( ~ r1_waybel_0('#skF_1','#skF_3',C_58)
      | ~ l1_waybel_0('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_struct_0('#skF_1')
      | v2_struct_0('#skF_1')
      | r1_waybel_0('#skF_1','#skF_4',C_58) ) ),
    inference(resolution,[status(thm)],[c_82,c_2])).

tff(c_94,plain,(
    ! [C_58] :
      ( ~ r1_waybel_0('#skF_1','#skF_3',C_58)
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_1')
      | r1_waybel_0('#skF_1','#skF_4',C_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_22,c_87])).

tff(c_96,plain,(
    ! [C_59] :
      ( ~ r1_waybel_0('#skF_1','#skF_3',C_59)
      | r1_waybel_0('#skF_1','#skF_4',C_59) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_28,c_94])).

tff(c_99,plain,(
    r1_waybel_0('#skF_1','#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_96])).

tff(c_103,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_99])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:04:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.24  
% 1.99/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.24  %$ r2_waybel_0 > r1_waybel_0 > m2_yellow_6 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > k6_subset_1 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.99/1.24  
% 1.99/1.24  %Foreground sorts:
% 1.99/1.24  
% 1.99/1.24  
% 1.99/1.24  %Background operators:
% 1.99/1.24  
% 1.99/1.24  
% 1.99/1.24  %Foreground operators:
% 1.99/1.24  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.99/1.24  tff(m2_yellow_6, type, m2_yellow_6: ($i * $i * $i) > $o).
% 1.99/1.24  tff(r2_waybel_0, type, r2_waybel_0: ($i * $i * $i) > $o).
% 1.99/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.24  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 1.99/1.24  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 1.99/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.24  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.99/1.24  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.24  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 1.99/1.24  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.99/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.24  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 1.99/1.24  tff('#skF_4', type, '#skF_4': $i).
% 1.99/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.99/1.24  
% 1.99/1.25  tff(f_114, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B, C]: ((((~v2_struct_0(C) & v4_orders_2(C)) & v7_waybel_0(C)) & l1_waybel_0(C, A)) => (r1_waybel_0(A, C, B) => (![D]: (m2_yellow_6(D, A, C) => r1_waybel_0(A, D, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_yellow19)).
% 1.99/1.25  tff(f_68, axiom, (![A, B]: ((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m2_yellow_6(C, A, B) => (((~v2_struct_0(C) & v4_orders_2(C)) & v7_waybel_0(C)) & l1_waybel_0(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_yellow_6)).
% 1.99/1.25  tff(f_42, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r1_waybel_0(A, B, C) <=> ~r2_waybel_0(A, B, k6_subset_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_waybel_0)).
% 1.99/1.25  tff(f_91, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m2_yellow_6(C, A, B) => (![D]: (r2_waybel_0(A, C, D) => r2_waybel_0(A, B, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_yellow_6)).
% 1.99/1.25  tff(c_16, plain, (~r1_waybel_0('#skF_1', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 1.99/1.25  tff(c_20, plain, (r1_waybel_0('#skF_1', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 1.99/1.25  tff(c_32, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 1.99/1.25  tff(c_28, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 1.99/1.25  tff(c_30, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 1.99/1.25  tff(c_22, plain, (l1_waybel_0('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 1.99/1.25  tff(c_26, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 1.99/1.25  tff(c_24, plain, (v7_waybel_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 1.99/1.25  tff(c_18, plain, (m2_yellow_6('#skF_4', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 1.99/1.25  tff(c_41, plain, (![C_35, A_36, B_37]: (~v2_struct_0(C_35) | ~m2_yellow_6(C_35, A_36, B_37) | ~l1_waybel_0(B_37, A_36) | ~v7_waybel_0(B_37) | ~v4_orders_2(B_37) | v2_struct_0(B_37) | ~l1_struct_0(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.99/1.25  tff(c_44, plain, (~v2_struct_0('#skF_4') | ~l1_waybel_0('#skF_3', '#skF_1') | ~v7_waybel_0('#skF_3') | ~v4_orders_2('#skF_3') | v2_struct_0('#skF_3') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_41])).
% 1.99/1.25  tff(c_47, plain, (~v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_24, c_22, c_44])).
% 1.99/1.25  tff(c_48, plain, (~v2_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_32, c_28, c_47])).
% 1.99/1.25  tff(c_58, plain, (![C_44, A_45, B_46]: (l1_waybel_0(C_44, A_45) | ~m2_yellow_6(C_44, A_45, B_46) | ~l1_waybel_0(B_46, A_45) | ~v7_waybel_0(B_46) | ~v4_orders_2(B_46) | v2_struct_0(B_46) | ~l1_struct_0(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.99/1.25  tff(c_61, plain, (l1_waybel_0('#skF_4', '#skF_1') | ~l1_waybel_0('#skF_3', '#skF_1') | ~v7_waybel_0('#skF_3') | ~v4_orders_2('#skF_3') | v2_struct_0('#skF_3') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_58])).
% 1.99/1.25  tff(c_64, plain, (l1_waybel_0('#skF_4', '#skF_1') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_24, c_22, c_61])).
% 1.99/1.25  tff(c_65, plain, (l1_waybel_0('#skF_4', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_32, c_28, c_64])).
% 1.99/1.25  tff(c_4, plain, (![A_1, B_5, C_7]: (r1_waybel_0(A_1, B_5, C_7) | r2_waybel_0(A_1, B_5, k6_subset_1(u1_struct_0(A_1), C_7)) | ~l1_waybel_0(B_5, A_1) | v2_struct_0(B_5) | ~l1_struct_0(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.99/1.25  tff(c_71, plain, (![A_50, B_51, D_52, C_53]: (r2_waybel_0(A_50, B_51, D_52) | ~r2_waybel_0(A_50, C_53, D_52) | ~m2_yellow_6(C_53, A_50, B_51) | ~l1_waybel_0(B_51, A_50) | ~v7_waybel_0(B_51) | ~v4_orders_2(B_51) | v2_struct_0(B_51) | ~l1_struct_0(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_91])).
% 1.99/1.25  tff(c_75, plain, (![A_54, B_55, C_56, B_57]: (r2_waybel_0(A_54, B_55, k6_subset_1(u1_struct_0(A_54), C_56)) | ~m2_yellow_6(B_57, A_54, B_55) | ~l1_waybel_0(B_55, A_54) | ~v7_waybel_0(B_55) | ~v4_orders_2(B_55) | v2_struct_0(B_55) | r1_waybel_0(A_54, B_57, C_56) | ~l1_waybel_0(B_57, A_54) | v2_struct_0(B_57) | ~l1_struct_0(A_54) | v2_struct_0(A_54))), inference(resolution, [status(thm)], [c_4, c_71])).
% 1.99/1.25  tff(c_77, plain, (![C_56]: (r2_waybel_0('#skF_1', '#skF_3', k6_subset_1(u1_struct_0('#skF_1'), C_56)) | ~l1_waybel_0('#skF_3', '#skF_1') | ~v7_waybel_0('#skF_3') | ~v4_orders_2('#skF_3') | v2_struct_0('#skF_3') | r1_waybel_0('#skF_1', '#skF_4', C_56) | ~l1_waybel_0('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_75])).
% 1.99/1.25  tff(c_80, plain, (![C_56]: (r2_waybel_0('#skF_1', '#skF_3', k6_subset_1(u1_struct_0('#skF_1'), C_56)) | v2_struct_0('#skF_3') | r1_waybel_0('#skF_1', '#skF_4', C_56) | v2_struct_0('#skF_4') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_65, c_26, c_24, c_22, c_77])).
% 1.99/1.25  tff(c_82, plain, (![C_58]: (r2_waybel_0('#skF_1', '#skF_3', k6_subset_1(u1_struct_0('#skF_1'), C_58)) | r1_waybel_0('#skF_1', '#skF_4', C_58))), inference(negUnitSimplification, [status(thm)], [c_32, c_48, c_28, c_80])).
% 1.99/1.25  tff(c_2, plain, (![A_1, B_5, C_7]: (~r2_waybel_0(A_1, B_5, k6_subset_1(u1_struct_0(A_1), C_7)) | ~r1_waybel_0(A_1, B_5, C_7) | ~l1_waybel_0(B_5, A_1) | v2_struct_0(B_5) | ~l1_struct_0(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.99/1.25  tff(c_87, plain, (![C_58]: (~r1_waybel_0('#skF_1', '#skF_3', C_58) | ~l1_waybel_0('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1') | r1_waybel_0('#skF_1', '#skF_4', C_58))), inference(resolution, [status(thm)], [c_82, c_2])).
% 1.99/1.25  tff(c_94, plain, (![C_58]: (~r1_waybel_0('#skF_1', '#skF_3', C_58) | v2_struct_0('#skF_3') | v2_struct_0('#skF_1') | r1_waybel_0('#skF_1', '#skF_4', C_58))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_22, c_87])).
% 1.99/1.25  tff(c_96, plain, (![C_59]: (~r1_waybel_0('#skF_1', '#skF_3', C_59) | r1_waybel_0('#skF_1', '#skF_4', C_59))), inference(negUnitSimplification, [status(thm)], [c_32, c_28, c_94])).
% 1.99/1.25  tff(c_99, plain, (r1_waybel_0('#skF_1', '#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_20, c_96])).
% 1.99/1.25  tff(c_103, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_99])).
% 1.99/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.25  
% 1.99/1.25  Inference rules
% 1.99/1.25  ----------------------
% 1.99/1.25  #Ref     : 0
% 1.99/1.25  #Sup     : 10
% 1.99/1.25  #Fact    : 0
% 1.99/1.25  #Define  : 0
% 1.99/1.25  #Split   : 0
% 1.99/1.25  #Chain   : 0
% 1.99/1.25  #Close   : 0
% 1.99/1.25  
% 1.99/1.25  Ordering : KBO
% 1.99/1.25  
% 1.99/1.25  Simplification rules
% 1.99/1.25  ----------------------
% 1.99/1.25  #Subsume      : 0
% 1.99/1.25  #Demod        : 24
% 1.99/1.25  #Tautology    : 1
% 1.99/1.25  #SimpNegUnit  : 8
% 1.99/1.25  #BackRed      : 0
% 1.99/1.25  
% 1.99/1.25  #Partial instantiations: 0
% 1.99/1.25  #Strategies tried      : 1
% 1.99/1.25  
% 1.99/1.25  Timing (in seconds)
% 1.99/1.25  ----------------------
% 1.99/1.26  Preprocessing        : 0.29
% 1.99/1.26  Parsing              : 0.17
% 1.99/1.26  CNF conversion       : 0.02
% 1.99/1.26  Main loop            : 0.15
% 1.99/1.26  Inferencing          : 0.06
% 1.99/1.26  Reduction            : 0.04
% 1.99/1.26  Demodulation         : 0.03
% 1.99/1.26  BG Simplification    : 0.01
% 1.99/1.26  Subsumption          : 0.03
% 1.99/1.26  Abstraction          : 0.01
% 1.99/1.26  MUC search           : 0.00
% 1.99/1.26  Cooper               : 0.00
% 1.99/1.26  Total                : 0.48
% 1.99/1.26  Index Insertion      : 0.00
% 1.99/1.26  Index Deletion       : 0.00
% 1.99/1.26  Index Matching       : 0.00
% 1.99/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
