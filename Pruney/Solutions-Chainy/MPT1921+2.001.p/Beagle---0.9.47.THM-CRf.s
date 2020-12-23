%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:45 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   47 (  84 expanded)
%              Number of leaves         :   21 (  40 expanded)
%              Depth                    :    6
%              Number of atoms          :   77 ( 179 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_yellow_6 > r1_tarski > m1_yellow_0 > l1_waybel_0 > l1_struct_0 > l1_orders_2 > k2_partfun1 > u1_waybel_0 > #nlpp > u1_struct_0 > u1_orders_2 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(m1_yellow_0,type,(
    m1_yellow_0: ( $i * $i ) > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(u1_waybel_0,type,(
    u1_waybel_0: ( $i * $i ) > $i )).

tff(m1_yellow_6,type,(
    m1_yellow_6: ( $i * $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( l1_waybel_0(B,A)
           => ! [C] :
                ( m1_yellow_6(C,A,B)
               => r1_tarski(u1_struct_0(C),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_yellow_6)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

tff(f_36,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ( m1_yellow_0(B,A)
          <=> ( r1_tarski(u1_struct_0(B),u1_struct_0(A))
              & r1_tarski(u1_orders_2(B),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_yellow_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_waybel_0(B,A) )
     => ! [C] :
          ( m1_yellow_6(C,A,B)
         => l1_waybel_0(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_yellow_6)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => ! [C] :
              ( l1_waybel_0(C,A)
             => ( m1_yellow_6(C,A,B)
              <=> ( m1_yellow_0(C,B)
                  & u1_waybel_0(A,C) = k2_partfun1(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B),u1_struct_0(C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_yellow_6)).

tff(c_24,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_22,plain,(
    l1_waybel_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_25,plain,(
    ! [B_22,A_23] :
      ( l1_orders_2(B_22)
      | ~ l1_waybel_0(B_22,A_23)
      | ~ l1_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_28,plain,
    ( l1_orders_2('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_25])).

tff(c_31,plain,(
    l1_orders_2('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28])).

tff(c_32,plain,(
    ! [B_24,A_25] :
      ( r1_tarski(u1_struct_0(B_24),u1_struct_0(A_25))
      | ~ m1_yellow_0(B_24,A_25)
      | ~ l1_orders_2(B_24)
      | ~ l1_orders_2(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_36,plain,
    ( ~ m1_yellow_0('#skF_3','#skF_2')
    | ~ l1_orders_2('#skF_3')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_18])).

tff(c_38,plain,
    ( ~ m1_yellow_0('#skF_3','#skF_2')
    | ~ l1_orders_2('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_36])).

tff(c_39,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_20,plain,(
    m1_yellow_6('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_41,plain,(
    ! [C_28,A_29,B_30] :
      ( l1_waybel_0(C_28,A_29)
      | ~ m1_yellow_6(C_28,A_29,B_30)
      | ~ l1_waybel_0(B_30,A_29)
      | ~ l1_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_44,plain,
    ( l1_waybel_0('#skF_3','#skF_1')
    | ~ l1_waybel_0('#skF_2','#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_41])).

tff(c_47,plain,(
    l1_waybel_0('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_44])).

tff(c_8,plain,(
    ! [B_6,A_4] :
      ( l1_orders_2(B_6)
      | ~ l1_waybel_0(B_6,A_4)
      | ~ l1_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_50,plain,
    ( l1_orders_2('#skF_3')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_47,c_8])).

tff(c_53,plain,(
    l1_orders_2('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_50])).

tff(c_55,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_53])).

tff(c_56,plain,(
    ~ m1_yellow_0('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_59,plain,(
    ! [C_33,A_34,B_35] :
      ( l1_waybel_0(C_33,A_34)
      | ~ m1_yellow_6(C_33,A_34,B_35)
      | ~ l1_waybel_0(B_35,A_34)
      | ~ l1_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_62,plain,
    ( l1_waybel_0('#skF_3','#skF_1')
    | ~ l1_waybel_0('#skF_2','#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_59])).

tff(c_65,plain,(
    l1_waybel_0('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_62])).

tff(c_72,plain,(
    ! [C_36,B_37,A_38] :
      ( m1_yellow_0(C_36,B_37)
      | ~ m1_yellow_6(C_36,A_38,B_37)
      | ~ l1_waybel_0(C_36,A_38)
      | ~ l1_waybel_0(B_37,A_38)
      | ~ l1_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_75,plain,
    ( m1_yellow_0('#skF_3','#skF_2')
    | ~ l1_waybel_0('#skF_3','#skF_1')
    | ~ l1_waybel_0('#skF_2','#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_72])).

tff(c_78,plain,(
    m1_yellow_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_65,c_75])).

tff(c_80,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_78])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:36:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.15  
% 1.87/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.16  %$ m1_yellow_6 > r1_tarski > m1_yellow_0 > l1_waybel_0 > l1_struct_0 > l1_orders_2 > k2_partfun1 > u1_waybel_0 > #nlpp > u1_struct_0 > u1_orders_2 > #skF_2 > #skF_3 > #skF_1
% 1.87/1.16  
% 1.87/1.16  %Foreground sorts:
% 1.87/1.16  
% 1.87/1.16  
% 1.87/1.16  %Background operators:
% 1.87/1.16  
% 1.87/1.16  
% 1.87/1.16  %Foreground operators:
% 1.87/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.16  tff(m1_yellow_0, type, m1_yellow_0: ($i * $i) > $o).
% 1.87/1.16  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.87/1.16  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.87/1.16  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 1.87/1.16  tff(m1_yellow_6, type, m1_yellow_6: ($i * $i * $i) > $o).
% 1.87/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.16  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 1.87/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.16  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 1.87/1.16  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 1.87/1.16  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.87/1.16  
% 1.87/1.17  tff(f_77, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => (![C]: (m1_yellow_6(C, A, B) => r1_tarski(u1_struct_0(C), u1_struct_0(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_yellow_6)).
% 1.87/1.17  tff(f_43, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 1.87/1.17  tff(f_36, axiom, (![A]: (l1_orders_2(A) => (![B]: (l1_orders_2(B) => (m1_yellow_0(B, A) <=> (r1_tarski(u1_struct_0(B), u1_struct_0(A)) & r1_tarski(u1_orders_2(B), u1_orders_2(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_yellow_0)).
% 1.87/1.17  tff(f_66, axiom, (![A, B]: ((l1_struct_0(A) & l1_waybel_0(B, A)) => (![C]: (m1_yellow_6(C, A, B) => l1_waybel_0(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_yellow_6)).
% 1.87/1.17  tff(f_57, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => (![C]: (l1_waybel_0(C, A) => (m1_yellow_6(C, A, B) <=> (m1_yellow_0(C, B) & (u1_waybel_0(A, C) = k2_partfun1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B), u1_struct_0(C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_yellow_6)).
% 1.87/1.17  tff(c_24, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.87/1.17  tff(c_22, plain, (l1_waybel_0('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.87/1.17  tff(c_25, plain, (![B_22, A_23]: (l1_orders_2(B_22) | ~l1_waybel_0(B_22, A_23) | ~l1_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.87/1.17  tff(c_28, plain, (l1_orders_2('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_25])).
% 1.87/1.17  tff(c_31, plain, (l1_orders_2('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28])).
% 1.87/1.17  tff(c_32, plain, (![B_24, A_25]: (r1_tarski(u1_struct_0(B_24), u1_struct_0(A_25)) | ~m1_yellow_0(B_24, A_25) | ~l1_orders_2(B_24) | ~l1_orders_2(A_25))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.87/1.17  tff(c_18, plain, (~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.87/1.17  tff(c_36, plain, (~m1_yellow_0('#skF_3', '#skF_2') | ~l1_orders_2('#skF_3') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_32, c_18])).
% 1.87/1.17  tff(c_38, plain, (~m1_yellow_0('#skF_3', '#skF_2') | ~l1_orders_2('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_31, c_36])).
% 1.87/1.17  tff(c_39, plain, (~l1_orders_2('#skF_3')), inference(splitLeft, [status(thm)], [c_38])).
% 1.87/1.17  tff(c_20, plain, (m1_yellow_6('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.87/1.17  tff(c_41, plain, (![C_28, A_29, B_30]: (l1_waybel_0(C_28, A_29) | ~m1_yellow_6(C_28, A_29, B_30) | ~l1_waybel_0(B_30, A_29) | ~l1_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.87/1.17  tff(c_44, plain, (l1_waybel_0('#skF_3', '#skF_1') | ~l1_waybel_0('#skF_2', '#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_41])).
% 1.87/1.17  tff(c_47, plain, (l1_waybel_0('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_44])).
% 1.87/1.17  tff(c_8, plain, (![B_6, A_4]: (l1_orders_2(B_6) | ~l1_waybel_0(B_6, A_4) | ~l1_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.87/1.17  tff(c_50, plain, (l1_orders_2('#skF_3') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_47, c_8])).
% 1.87/1.17  tff(c_53, plain, (l1_orders_2('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_50])).
% 1.87/1.17  tff(c_55, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39, c_53])).
% 1.87/1.17  tff(c_56, plain, (~m1_yellow_0('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_38])).
% 1.87/1.17  tff(c_59, plain, (![C_33, A_34, B_35]: (l1_waybel_0(C_33, A_34) | ~m1_yellow_6(C_33, A_34, B_35) | ~l1_waybel_0(B_35, A_34) | ~l1_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.87/1.17  tff(c_62, plain, (l1_waybel_0('#skF_3', '#skF_1') | ~l1_waybel_0('#skF_2', '#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_59])).
% 1.87/1.17  tff(c_65, plain, (l1_waybel_0('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_62])).
% 1.87/1.17  tff(c_72, plain, (![C_36, B_37, A_38]: (m1_yellow_0(C_36, B_37) | ~m1_yellow_6(C_36, A_38, B_37) | ~l1_waybel_0(C_36, A_38) | ~l1_waybel_0(B_37, A_38) | ~l1_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.87/1.17  tff(c_75, plain, (m1_yellow_0('#skF_3', '#skF_2') | ~l1_waybel_0('#skF_3', '#skF_1') | ~l1_waybel_0('#skF_2', '#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_72])).
% 1.87/1.17  tff(c_78, plain, (m1_yellow_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_65, c_75])).
% 1.87/1.17  tff(c_80, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_78])).
% 1.87/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.17  
% 1.87/1.17  Inference rules
% 1.87/1.17  ----------------------
% 1.87/1.17  #Ref     : 0
% 1.87/1.17  #Sup     : 7
% 1.87/1.17  #Fact    : 0
% 1.87/1.17  #Define  : 0
% 1.87/1.17  #Split   : 1
% 1.87/1.17  #Chain   : 0
% 1.87/1.17  #Close   : 0
% 1.87/1.17  
% 1.87/1.17  Ordering : KBO
% 1.87/1.17  
% 1.87/1.17  Simplification rules
% 1.87/1.17  ----------------------
% 1.87/1.17  #Subsume      : 0
% 1.87/1.17  #Demod        : 12
% 1.87/1.17  #Tautology    : 1
% 1.87/1.17  #SimpNegUnit  : 2
% 1.87/1.17  #BackRed      : 0
% 1.87/1.17  
% 1.87/1.17  #Partial instantiations: 0
% 1.87/1.17  #Strategies tried      : 1
% 1.87/1.17  
% 1.87/1.17  Timing (in seconds)
% 1.87/1.17  ----------------------
% 1.87/1.17  Preprocessing        : 0.29
% 1.87/1.17  Parsing              : 0.16
% 1.87/1.17  CNF conversion       : 0.02
% 1.87/1.17  Main loop            : 0.12
% 1.87/1.17  Inferencing          : 0.05
% 1.87/1.17  Reduction            : 0.03
% 1.87/1.17  Demodulation         : 0.03
% 1.87/1.17  BG Simplification    : 0.01
% 1.87/1.17  Subsumption          : 0.02
% 1.87/1.17  Abstraction          : 0.00
% 1.87/1.18  MUC search           : 0.00
% 1.87/1.18  Cooper               : 0.00
% 1.87/1.18  Total                : 0.44
% 1.87/1.18  Index Insertion      : 0.00
% 1.87/1.18  Index Deletion       : 0.00
% 1.87/1.18  Index Matching       : 0.00
% 1.87/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
