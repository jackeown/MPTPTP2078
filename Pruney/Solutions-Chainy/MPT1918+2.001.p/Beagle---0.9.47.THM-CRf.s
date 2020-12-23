%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:44 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 102 expanded)
%              Number of leaves         :   17 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :  125 ( 277 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_yellow_0 > l1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(m1_yellow_0,type,(
    m1_yellow_0: ( $i * $i ) > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( m1_yellow_0(B,A)
           => ! [C] :
                ( m1_yellow_0(C,B)
               => m1_yellow_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_yellow_6)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_yellow_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_yellow_0)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ( m1_yellow_0(B,A)
          <=> ( r1_tarski(u1_struct_0(B),u1_struct_0(A))
              & r1_tarski(u1_orders_2(B),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_yellow_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_22,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20,plain,(
    m1_yellow_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_23,plain,(
    ! [B_16,A_17] :
      ( l1_orders_2(B_16)
      | ~ m1_yellow_0(B_16,A_17)
      | ~ l1_orders_2(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_29,plain,
    ( l1_orders_2('#skF_3')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_23])).

tff(c_33,plain,(
    l1_orders_2('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_29])).

tff(c_18,plain,(
    m1_yellow_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_30,plain,
    ( l1_orders_2('#skF_4')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_23])).

tff(c_36,plain,(
    l1_orders_2('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_30])).

tff(c_10,plain,(
    ! [B_8,A_6] :
      ( r1_tarski(u1_orders_2(B_8),u1_orders_2(A_6))
      | ~ m1_yellow_0(B_8,A_6)
      | ~ l1_orders_2(B_8)
      | ~ l1_orders_2(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_43,plain,(
    ! [C_22,B_23,A_24] :
      ( r2_hidden(C_22,B_23)
      | ~ r2_hidden(C_22,A_24)
      | ~ r1_tarski(A_24,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_48,plain,(
    ! [A_26,B_27,B_28] :
      ( r2_hidden('#skF_1'(A_26,B_27),B_28)
      | ~ r1_tarski(A_26,B_28)
      | r1_tarski(A_26,B_27) ) ),
    inference(resolution,[status(thm)],[c_6,c_43])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_59,plain,(
    ! [A_33,B_34,B_35,B_36] :
      ( r2_hidden('#skF_1'(A_33,B_34),B_35)
      | ~ r1_tarski(B_36,B_35)
      | ~ r1_tarski(A_33,B_36)
      | r1_tarski(A_33,B_34) ) ),
    inference(resolution,[status(thm)],[c_48,c_2])).

tff(c_103,plain,(
    ! [A_47,B_48,A_49,B_50] :
      ( r2_hidden('#skF_1'(A_47,B_48),u1_orders_2(A_49))
      | ~ r1_tarski(A_47,u1_orders_2(B_50))
      | r1_tarski(A_47,B_48)
      | ~ m1_yellow_0(B_50,A_49)
      | ~ l1_orders_2(B_50)
      | ~ l1_orders_2(A_49) ) ),
    inference(resolution,[status(thm)],[c_10,c_59])).

tff(c_159,plain,(
    ! [B_68,B_69,A_70,A_71] :
      ( r2_hidden('#skF_1'(u1_orders_2(B_68),B_69),u1_orders_2(A_70))
      | r1_tarski(u1_orders_2(B_68),B_69)
      | ~ m1_yellow_0(A_71,A_70)
      | ~ l1_orders_2(A_70)
      | ~ m1_yellow_0(B_68,A_71)
      | ~ l1_orders_2(B_68)
      | ~ l1_orders_2(A_71) ) ),
    inference(resolution,[status(thm)],[c_10,c_103])).

tff(c_165,plain,(
    ! [B_68,B_69] :
      ( r2_hidden('#skF_1'(u1_orders_2(B_68),B_69),u1_orders_2('#skF_2'))
      | r1_tarski(u1_orders_2(B_68),B_69)
      | ~ l1_orders_2('#skF_2')
      | ~ m1_yellow_0(B_68,'#skF_3')
      | ~ l1_orders_2(B_68)
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_159])).

tff(c_207,plain,(
    ! [B_74,B_75] :
      ( r2_hidden('#skF_1'(u1_orders_2(B_74),B_75),u1_orders_2('#skF_2'))
      | r1_tarski(u1_orders_2(B_74),B_75)
      | ~ m1_yellow_0(B_74,'#skF_3')
      | ~ l1_orders_2(B_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_22,c_165])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_215,plain,(
    ! [B_74] :
      ( r1_tarski(u1_orders_2(B_74),u1_orders_2('#skF_2'))
      | ~ m1_yellow_0(B_74,'#skF_3')
      | ~ l1_orders_2(B_74) ) ),
    inference(resolution,[status(thm)],[c_207,c_4])).

tff(c_12,plain,(
    ! [B_8,A_6] :
      ( r1_tarski(u1_struct_0(B_8),u1_struct_0(A_6))
      | ~ m1_yellow_0(B_8,A_6)
      | ~ l1_orders_2(B_8)
      | ~ l1_orders_2(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_86,plain,(
    ! [A_40,B_41,A_42,B_43] :
      ( r2_hidden('#skF_1'(A_40,B_41),u1_struct_0(A_42))
      | ~ r1_tarski(A_40,u1_struct_0(B_43))
      | r1_tarski(A_40,B_41)
      | ~ m1_yellow_0(B_43,A_42)
      | ~ l1_orders_2(B_43)
      | ~ l1_orders_2(A_42) ) ),
    inference(resolution,[status(thm)],[c_12,c_59])).

tff(c_136,plain,(
    ! [B_62,B_63,A_64,A_65] :
      ( r2_hidden('#skF_1'(u1_struct_0(B_62),B_63),u1_struct_0(A_64))
      | r1_tarski(u1_struct_0(B_62),B_63)
      | ~ m1_yellow_0(A_65,A_64)
      | ~ l1_orders_2(A_64)
      | ~ m1_yellow_0(B_62,A_65)
      | ~ l1_orders_2(B_62)
      | ~ l1_orders_2(A_65) ) ),
    inference(resolution,[status(thm)],[c_12,c_86])).

tff(c_142,plain,(
    ! [B_62,B_63] :
      ( r2_hidden('#skF_1'(u1_struct_0(B_62),B_63),u1_struct_0('#skF_2'))
      | r1_tarski(u1_struct_0(B_62),B_63)
      | ~ l1_orders_2('#skF_2')
      | ~ m1_yellow_0(B_62,'#skF_3')
      | ~ l1_orders_2(B_62)
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_136])).

tff(c_228,plain,(
    ! [B_77,B_78] :
      ( r2_hidden('#skF_1'(u1_struct_0(B_77),B_78),u1_struct_0('#skF_2'))
      | r1_tarski(u1_struct_0(B_77),B_78)
      | ~ m1_yellow_0(B_77,'#skF_3')
      | ~ l1_orders_2(B_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_22,c_142])).

tff(c_237,plain,(
    ! [B_79] :
      ( r1_tarski(u1_struct_0(B_79),u1_struct_0('#skF_2'))
      | ~ m1_yellow_0(B_79,'#skF_3')
      | ~ l1_orders_2(B_79) ) ),
    inference(resolution,[status(thm)],[c_228,c_4])).

tff(c_8,plain,(
    ! [B_8,A_6] :
      ( m1_yellow_0(B_8,A_6)
      | ~ r1_tarski(u1_orders_2(B_8),u1_orders_2(A_6))
      | ~ r1_tarski(u1_struct_0(B_8),u1_struct_0(A_6))
      | ~ l1_orders_2(B_8)
      | ~ l1_orders_2(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_244,plain,(
    ! [B_79] :
      ( m1_yellow_0(B_79,'#skF_2')
      | ~ r1_tarski(u1_orders_2(B_79),u1_orders_2('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ m1_yellow_0(B_79,'#skF_3')
      | ~ l1_orders_2(B_79) ) ),
    inference(resolution,[status(thm)],[c_237,c_8])).

tff(c_255,plain,(
    ! [B_80] :
      ( m1_yellow_0(B_80,'#skF_2')
      | ~ r1_tarski(u1_orders_2(B_80),u1_orders_2('#skF_2'))
      | ~ m1_yellow_0(B_80,'#skF_3')
      | ~ l1_orders_2(B_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_244])).

tff(c_284,plain,(
    ! [B_83] :
      ( m1_yellow_0(B_83,'#skF_2')
      | ~ m1_yellow_0(B_83,'#skF_3')
      | ~ l1_orders_2(B_83) ) ),
    inference(resolution,[status(thm)],[c_215,c_255])).

tff(c_16,plain,(
    ~ m1_yellow_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_294,plain,
    ( ~ m1_yellow_0('#skF_4','#skF_3')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_284,c_16])).

tff(c_307,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_18,c_294])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:06:19 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.29  
% 2.12/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.29  %$ r2_hidden > r1_tarski > m1_yellow_0 > l1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.12/1.29  
% 2.12/1.29  %Foreground sorts:
% 2.12/1.29  
% 2.12/1.29  
% 2.12/1.29  %Background operators:
% 2.12/1.29  
% 2.12/1.29  
% 2.12/1.29  %Foreground operators:
% 2.12/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.12/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.12/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.12/1.29  tff(m1_yellow_0, type, m1_yellow_0: ($i * $i) > $o).
% 2.12/1.29  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.12/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.12/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.29  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.12/1.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.12/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.12/1.30  
% 2.12/1.31  tff(f_61, negated_conjecture, ~(![A]: (l1_orders_2(A) => (![B]: (m1_yellow_0(B, A) => (![C]: (m1_yellow_0(C, B) => m1_yellow_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_yellow_6)).
% 2.12/1.31  tff(f_50, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_yellow_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_yellow_0)).
% 2.12/1.31  tff(f_43, axiom, (![A]: (l1_orders_2(A) => (![B]: (l1_orders_2(B) => (m1_yellow_0(B, A) <=> (r1_tarski(u1_struct_0(B), u1_struct_0(A)) & r1_tarski(u1_orders_2(B), u1_orders_2(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_yellow_0)).
% 2.12/1.31  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.12/1.31  tff(c_22, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.12/1.31  tff(c_20, plain, (m1_yellow_0('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.12/1.31  tff(c_23, plain, (![B_16, A_17]: (l1_orders_2(B_16) | ~m1_yellow_0(B_16, A_17) | ~l1_orders_2(A_17))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.12/1.31  tff(c_29, plain, (l1_orders_2('#skF_3') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_20, c_23])).
% 2.12/1.31  tff(c_33, plain, (l1_orders_2('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_29])).
% 2.12/1.31  tff(c_18, plain, (m1_yellow_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.12/1.31  tff(c_30, plain, (l1_orders_2('#skF_4') | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_18, c_23])).
% 2.12/1.31  tff(c_36, plain, (l1_orders_2('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_33, c_30])).
% 2.12/1.31  tff(c_10, plain, (![B_8, A_6]: (r1_tarski(u1_orders_2(B_8), u1_orders_2(A_6)) | ~m1_yellow_0(B_8, A_6) | ~l1_orders_2(B_8) | ~l1_orders_2(A_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.12/1.31  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.12/1.31  tff(c_43, plain, (![C_22, B_23, A_24]: (r2_hidden(C_22, B_23) | ~r2_hidden(C_22, A_24) | ~r1_tarski(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.12/1.31  tff(c_48, plain, (![A_26, B_27, B_28]: (r2_hidden('#skF_1'(A_26, B_27), B_28) | ~r1_tarski(A_26, B_28) | r1_tarski(A_26, B_27))), inference(resolution, [status(thm)], [c_6, c_43])).
% 2.12/1.31  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.12/1.31  tff(c_59, plain, (![A_33, B_34, B_35, B_36]: (r2_hidden('#skF_1'(A_33, B_34), B_35) | ~r1_tarski(B_36, B_35) | ~r1_tarski(A_33, B_36) | r1_tarski(A_33, B_34))), inference(resolution, [status(thm)], [c_48, c_2])).
% 2.12/1.31  tff(c_103, plain, (![A_47, B_48, A_49, B_50]: (r2_hidden('#skF_1'(A_47, B_48), u1_orders_2(A_49)) | ~r1_tarski(A_47, u1_orders_2(B_50)) | r1_tarski(A_47, B_48) | ~m1_yellow_0(B_50, A_49) | ~l1_orders_2(B_50) | ~l1_orders_2(A_49))), inference(resolution, [status(thm)], [c_10, c_59])).
% 2.12/1.31  tff(c_159, plain, (![B_68, B_69, A_70, A_71]: (r2_hidden('#skF_1'(u1_orders_2(B_68), B_69), u1_orders_2(A_70)) | r1_tarski(u1_orders_2(B_68), B_69) | ~m1_yellow_0(A_71, A_70) | ~l1_orders_2(A_70) | ~m1_yellow_0(B_68, A_71) | ~l1_orders_2(B_68) | ~l1_orders_2(A_71))), inference(resolution, [status(thm)], [c_10, c_103])).
% 2.12/1.31  tff(c_165, plain, (![B_68, B_69]: (r2_hidden('#skF_1'(u1_orders_2(B_68), B_69), u1_orders_2('#skF_2')) | r1_tarski(u1_orders_2(B_68), B_69) | ~l1_orders_2('#skF_2') | ~m1_yellow_0(B_68, '#skF_3') | ~l1_orders_2(B_68) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_159])).
% 2.12/1.31  tff(c_207, plain, (![B_74, B_75]: (r2_hidden('#skF_1'(u1_orders_2(B_74), B_75), u1_orders_2('#skF_2')) | r1_tarski(u1_orders_2(B_74), B_75) | ~m1_yellow_0(B_74, '#skF_3') | ~l1_orders_2(B_74))), inference(demodulation, [status(thm), theory('equality')], [c_33, c_22, c_165])).
% 2.12/1.31  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.12/1.31  tff(c_215, plain, (![B_74]: (r1_tarski(u1_orders_2(B_74), u1_orders_2('#skF_2')) | ~m1_yellow_0(B_74, '#skF_3') | ~l1_orders_2(B_74))), inference(resolution, [status(thm)], [c_207, c_4])).
% 2.12/1.31  tff(c_12, plain, (![B_8, A_6]: (r1_tarski(u1_struct_0(B_8), u1_struct_0(A_6)) | ~m1_yellow_0(B_8, A_6) | ~l1_orders_2(B_8) | ~l1_orders_2(A_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.12/1.31  tff(c_86, plain, (![A_40, B_41, A_42, B_43]: (r2_hidden('#skF_1'(A_40, B_41), u1_struct_0(A_42)) | ~r1_tarski(A_40, u1_struct_0(B_43)) | r1_tarski(A_40, B_41) | ~m1_yellow_0(B_43, A_42) | ~l1_orders_2(B_43) | ~l1_orders_2(A_42))), inference(resolution, [status(thm)], [c_12, c_59])).
% 2.12/1.31  tff(c_136, plain, (![B_62, B_63, A_64, A_65]: (r2_hidden('#skF_1'(u1_struct_0(B_62), B_63), u1_struct_0(A_64)) | r1_tarski(u1_struct_0(B_62), B_63) | ~m1_yellow_0(A_65, A_64) | ~l1_orders_2(A_64) | ~m1_yellow_0(B_62, A_65) | ~l1_orders_2(B_62) | ~l1_orders_2(A_65))), inference(resolution, [status(thm)], [c_12, c_86])).
% 2.12/1.31  tff(c_142, plain, (![B_62, B_63]: (r2_hidden('#skF_1'(u1_struct_0(B_62), B_63), u1_struct_0('#skF_2')) | r1_tarski(u1_struct_0(B_62), B_63) | ~l1_orders_2('#skF_2') | ~m1_yellow_0(B_62, '#skF_3') | ~l1_orders_2(B_62) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_136])).
% 2.12/1.31  tff(c_228, plain, (![B_77, B_78]: (r2_hidden('#skF_1'(u1_struct_0(B_77), B_78), u1_struct_0('#skF_2')) | r1_tarski(u1_struct_0(B_77), B_78) | ~m1_yellow_0(B_77, '#skF_3') | ~l1_orders_2(B_77))), inference(demodulation, [status(thm), theory('equality')], [c_33, c_22, c_142])).
% 2.12/1.31  tff(c_237, plain, (![B_79]: (r1_tarski(u1_struct_0(B_79), u1_struct_0('#skF_2')) | ~m1_yellow_0(B_79, '#skF_3') | ~l1_orders_2(B_79))), inference(resolution, [status(thm)], [c_228, c_4])).
% 2.12/1.31  tff(c_8, plain, (![B_8, A_6]: (m1_yellow_0(B_8, A_6) | ~r1_tarski(u1_orders_2(B_8), u1_orders_2(A_6)) | ~r1_tarski(u1_struct_0(B_8), u1_struct_0(A_6)) | ~l1_orders_2(B_8) | ~l1_orders_2(A_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.12/1.31  tff(c_244, plain, (![B_79]: (m1_yellow_0(B_79, '#skF_2') | ~r1_tarski(u1_orders_2(B_79), u1_orders_2('#skF_2')) | ~l1_orders_2('#skF_2') | ~m1_yellow_0(B_79, '#skF_3') | ~l1_orders_2(B_79))), inference(resolution, [status(thm)], [c_237, c_8])).
% 2.12/1.31  tff(c_255, plain, (![B_80]: (m1_yellow_0(B_80, '#skF_2') | ~r1_tarski(u1_orders_2(B_80), u1_orders_2('#skF_2')) | ~m1_yellow_0(B_80, '#skF_3') | ~l1_orders_2(B_80))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_244])).
% 2.12/1.31  tff(c_284, plain, (![B_83]: (m1_yellow_0(B_83, '#skF_2') | ~m1_yellow_0(B_83, '#skF_3') | ~l1_orders_2(B_83))), inference(resolution, [status(thm)], [c_215, c_255])).
% 2.12/1.31  tff(c_16, plain, (~m1_yellow_0('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.12/1.31  tff(c_294, plain, (~m1_yellow_0('#skF_4', '#skF_3') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_284, c_16])).
% 2.12/1.31  tff(c_307, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_18, c_294])).
% 2.12/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.31  
% 2.12/1.31  Inference rules
% 2.12/1.31  ----------------------
% 2.12/1.31  #Ref     : 0
% 2.12/1.31  #Sup     : 58
% 2.12/1.31  #Fact    : 0
% 2.12/1.31  #Define  : 0
% 2.12/1.31  #Split   : 2
% 2.12/1.31  #Chain   : 0
% 2.12/1.31  #Close   : 0
% 2.12/1.31  
% 2.12/1.31  Ordering : KBO
% 2.12/1.31  
% 2.12/1.31  Simplification rules
% 2.12/1.31  ----------------------
% 2.12/1.31  #Subsume      : 8
% 2.12/1.31  #Demod        : 25
% 2.12/1.31  #Tautology    : 6
% 2.12/1.31  #SimpNegUnit  : 0
% 2.12/1.31  #BackRed      : 0
% 2.12/1.31  
% 2.12/1.31  #Partial instantiations: 0
% 2.12/1.31  #Strategies tried      : 1
% 2.12/1.31  
% 2.12/1.31  Timing (in seconds)
% 2.12/1.31  ----------------------
% 2.12/1.31  Preprocessing        : 0.27
% 2.12/1.31  Parsing              : 0.15
% 2.12/1.31  CNF conversion       : 0.02
% 2.12/1.31  Main loop            : 0.27
% 2.12/1.31  Inferencing          : 0.11
% 2.12/1.31  Reduction            : 0.06
% 2.12/1.31  Demodulation         : 0.04
% 2.12/1.31  BG Simplification    : 0.02
% 2.12/1.31  Subsumption          : 0.07
% 2.12/1.31  Abstraction          : 0.01
% 2.12/1.31  MUC search           : 0.00
% 2.12/1.31  Cooper               : 0.00
% 2.12/1.31  Total                : 0.57
% 2.12/1.31  Index Insertion      : 0.00
% 2.12/1.31  Index Deletion       : 0.00
% 2.12/1.31  Index Matching       : 0.00
% 2.12/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
