%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:47 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   40 (  47 expanded)
%              Number of leaves         :   22 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   82 ( 138 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_0 > r1_waybel_0 > r1_xboole_0 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r2_waybel_0,type,(
    r2_waybel_0: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_orders_2(B)
              & v7_waybel_0(B)
              & l1_waybel_0(B,A) )
           => ! [C] :
                ( r1_waybel_0(A,B,C)
               => r2_waybel_0(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_yellow_6)).

tff(f_29,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_46,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r2_waybel_0(A,B,C)
            <=> ~ r1_waybel_0(A,B,k6_subset_1(u1_struct_0(A),C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_waybel_0)).

tff(f_27,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & l1_waybel_0(B,A) )
         => ! [C,D] :
              ~ ( r1_waybel_0(A,B,C)
                & r1_waybel_0(A,B,D)
                & r1_xboole_0(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_6)).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_22,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_24,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_16,plain,(
    l1_waybel_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_20,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_18,plain,(
    v7_waybel_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_14,plain,(
    r1_waybel_0('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4,plain,(
    ! [A_3,B_4] : k6_subset_1(A_3,B_4) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_5,B_9,C_11] :
      ( r2_waybel_0(A_5,B_9,C_11)
      | r1_waybel_0(A_5,B_9,k6_subset_1(u1_struct_0(A_5),C_11))
      | ~ l1_waybel_0(B_9,A_5)
      | v2_struct_0(B_9)
      | ~ l1_struct_0(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_27,plain,(
    ! [A_5,B_9,C_11] :
      ( r2_waybel_0(A_5,B_9,C_11)
      | r1_waybel_0(A_5,B_9,k4_xboole_0(u1_struct_0(A_5),C_11))
      | ~ l1_waybel_0(B_9,A_5)
      | v2_struct_0(B_9)
      | ~ l1_struct_0(A_5)
      | v2_struct_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_8])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_xboole_0(k4_xboole_0(A_1,B_2),B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_45,plain,(
    ! [C_37,D_38,A_39,B_40] :
      ( ~ r1_xboole_0(C_37,D_38)
      | ~ r1_waybel_0(A_39,B_40,D_38)
      | ~ r1_waybel_0(A_39,B_40,C_37)
      | ~ l1_waybel_0(B_40,A_39)
      | ~ v7_waybel_0(B_40)
      | ~ v4_orders_2(B_40)
      | v2_struct_0(B_40)
      | ~ l1_struct_0(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_49,plain,(
    ! [A_41,B_42,B_43,A_44] :
      ( ~ r1_waybel_0(A_41,B_42,B_43)
      | ~ r1_waybel_0(A_41,B_42,k4_xboole_0(A_44,B_43))
      | ~ l1_waybel_0(B_42,A_41)
      | ~ v7_waybel_0(B_42)
      | ~ v4_orders_2(B_42)
      | v2_struct_0(B_42)
      | ~ l1_struct_0(A_41)
      | v2_struct_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_2,c_45])).

tff(c_54,plain,(
    ! [A_45,B_46,C_47] :
      ( ~ r1_waybel_0(A_45,B_46,C_47)
      | ~ v7_waybel_0(B_46)
      | ~ v4_orders_2(B_46)
      | r2_waybel_0(A_45,B_46,C_47)
      | ~ l1_waybel_0(B_46,A_45)
      | v2_struct_0(B_46)
      | ~ l1_struct_0(A_45)
      | v2_struct_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_27,c_49])).

tff(c_12,plain,(
    ~ r2_waybel_0('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_57,plain,
    ( ~ r1_waybel_0('#skF_1','#skF_2','#skF_3')
    | ~ v7_waybel_0('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ l1_waybel_0('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_12])).

tff(c_60,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_16,c_20,c_18,c_14,c_57])).

tff(c_62,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_22,c_60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:52:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.14  
% 1.75/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.15  %$ r2_waybel_0 > r1_waybel_0 > r1_xboole_0 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1
% 1.75/1.15  
% 1.75/1.15  %Foreground sorts:
% 1.75/1.15  
% 1.75/1.15  
% 1.75/1.15  %Background operators:
% 1.75/1.15  
% 1.75/1.15  
% 1.75/1.15  %Foreground operators:
% 1.75/1.15  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.75/1.15  tff(r2_waybel_0, type, r2_waybel_0: ($i * $i * $i) > $o).
% 1.75/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.75/1.15  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 1.75/1.15  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 1.75/1.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.75/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.75/1.15  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.75/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.75/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.75/1.15  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 1.75/1.15  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.75/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.15  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 1.75/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.15  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.75/1.15  
% 1.75/1.16  tff(f_90, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (r1_waybel_0(A, B, C) => r2_waybel_0(A, B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_yellow_6)).
% 1.75/1.16  tff(f_29, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.75/1.16  tff(f_46, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> ~r1_waybel_0(A, B, k6_subset_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_waybel_0)).
% 1.75/1.16  tff(f_27, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 1.75/1.16  tff(f_69, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C, D]: ~((r1_waybel_0(A, B, C) & r1_waybel_0(A, B, D)) & r1_xboole_0(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_yellow_6)).
% 1.75/1.16  tff(c_26, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 1.75/1.16  tff(c_22, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 1.75/1.16  tff(c_24, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 1.75/1.16  tff(c_16, plain, (l1_waybel_0('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 1.75/1.16  tff(c_20, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 1.75/1.16  tff(c_18, plain, (v7_waybel_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 1.75/1.16  tff(c_14, plain, (r1_waybel_0('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 1.75/1.16  tff(c_4, plain, (![A_3, B_4]: (k6_subset_1(A_3, B_4)=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.75/1.16  tff(c_8, plain, (![A_5, B_9, C_11]: (r2_waybel_0(A_5, B_9, C_11) | r1_waybel_0(A_5, B_9, k6_subset_1(u1_struct_0(A_5), C_11)) | ~l1_waybel_0(B_9, A_5) | v2_struct_0(B_9) | ~l1_struct_0(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.75/1.16  tff(c_27, plain, (![A_5, B_9, C_11]: (r2_waybel_0(A_5, B_9, C_11) | r1_waybel_0(A_5, B_9, k4_xboole_0(u1_struct_0(A_5), C_11)) | ~l1_waybel_0(B_9, A_5) | v2_struct_0(B_9) | ~l1_struct_0(A_5) | v2_struct_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_8])).
% 1.75/1.16  tff(c_2, plain, (![A_1, B_2]: (r1_xboole_0(k4_xboole_0(A_1, B_2), B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.75/1.16  tff(c_45, plain, (![C_37, D_38, A_39, B_40]: (~r1_xboole_0(C_37, D_38) | ~r1_waybel_0(A_39, B_40, D_38) | ~r1_waybel_0(A_39, B_40, C_37) | ~l1_waybel_0(B_40, A_39) | ~v7_waybel_0(B_40) | ~v4_orders_2(B_40) | v2_struct_0(B_40) | ~l1_struct_0(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.75/1.16  tff(c_49, plain, (![A_41, B_42, B_43, A_44]: (~r1_waybel_0(A_41, B_42, B_43) | ~r1_waybel_0(A_41, B_42, k4_xboole_0(A_44, B_43)) | ~l1_waybel_0(B_42, A_41) | ~v7_waybel_0(B_42) | ~v4_orders_2(B_42) | v2_struct_0(B_42) | ~l1_struct_0(A_41) | v2_struct_0(A_41))), inference(resolution, [status(thm)], [c_2, c_45])).
% 1.75/1.16  tff(c_54, plain, (![A_45, B_46, C_47]: (~r1_waybel_0(A_45, B_46, C_47) | ~v7_waybel_0(B_46) | ~v4_orders_2(B_46) | r2_waybel_0(A_45, B_46, C_47) | ~l1_waybel_0(B_46, A_45) | v2_struct_0(B_46) | ~l1_struct_0(A_45) | v2_struct_0(A_45))), inference(resolution, [status(thm)], [c_27, c_49])).
% 1.75/1.16  tff(c_12, plain, (~r2_waybel_0('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 1.75/1.16  tff(c_57, plain, (~r1_waybel_0('#skF_1', '#skF_2', '#skF_3') | ~v7_waybel_0('#skF_2') | ~v4_orders_2('#skF_2') | ~l1_waybel_0('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_54, c_12])).
% 1.75/1.16  tff(c_60, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_16, c_20, c_18, c_14, c_57])).
% 1.75/1.16  tff(c_62, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_22, c_60])).
% 1.75/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.16  
% 1.75/1.16  Inference rules
% 1.75/1.16  ----------------------
% 1.75/1.16  #Ref     : 0
% 1.75/1.16  #Sup     : 6
% 1.75/1.16  #Fact    : 0
% 1.75/1.16  #Define  : 0
% 1.75/1.16  #Split   : 0
% 1.75/1.16  #Chain   : 0
% 1.75/1.16  #Close   : 0
% 1.75/1.16  
% 1.75/1.16  Ordering : KBO
% 1.75/1.16  
% 1.75/1.16  Simplification rules
% 1.75/1.16  ----------------------
% 1.75/1.16  #Subsume      : 0
% 1.75/1.16  #Demod        : 7
% 1.75/1.16  #Tautology    : 3
% 1.75/1.16  #SimpNegUnit  : 1
% 1.75/1.16  #BackRed      : 0
% 1.75/1.16  
% 1.75/1.16  #Partial instantiations: 0
% 1.75/1.16  #Strategies tried      : 1
% 1.75/1.16  
% 1.75/1.16  Timing (in seconds)
% 1.75/1.16  ----------------------
% 1.86/1.16  Preprocessing        : 0.29
% 1.86/1.16  Parsing              : 0.16
% 1.86/1.16  CNF conversion       : 0.02
% 1.86/1.16  Main loop            : 0.11
% 1.86/1.16  Inferencing          : 0.05
% 1.86/1.16  Reduction            : 0.03
% 1.86/1.16  Demodulation         : 0.02
% 1.86/1.16  BG Simplification    : 0.01
% 1.86/1.16  Subsumption          : 0.01
% 1.86/1.16  Abstraction          : 0.01
% 1.86/1.16  MUC search           : 0.00
% 1.86/1.16  Cooper               : 0.00
% 1.86/1.16  Total                : 0.42
% 1.86/1.16  Index Insertion      : 0.00
% 1.86/1.16  Index Deletion       : 0.00
% 1.86/1.16  Index Matching       : 0.00
% 1.86/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
