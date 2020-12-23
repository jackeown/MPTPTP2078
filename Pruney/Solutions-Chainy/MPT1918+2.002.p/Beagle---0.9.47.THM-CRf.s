%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:44 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   44 (  83 expanded)
%              Number of leaves         :   15 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :  106 ( 218 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_yellow_0 > l1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > #skF_2 > #skF_3 > #skF_1

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

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( m1_yellow_0(B,A)
           => ! [C] :
                ( m1_yellow_0(C,B)
               => m1_yellow_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_yellow_6)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_yellow_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_0)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ( m1_yellow_0(B,A)
          <=> ( r1_tarski(u1_struct_0(B),u1_struct_0(A))
              & r1_tarski(u1_orders_2(B),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_yellow_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_12,plain,(
    ~ m1_yellow_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16,plain,(
    m1_yellow_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_19,plain,(
    ! [B_14,A_15] :
      ( l1_orders_2(B_14)
      | ~ m1_yellow_0(B_14,A_15)
      | ~ l1_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_25,plain,
    ( l1_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_19])).

tff(c_29,plain,(
    l1_orders_2('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_25])).

tff(c_14,plain,(
    m1_yellow_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_26,plain,
    ( l1_orders_2('#skF_3')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_19])).

tff(c_32,plain,(
    l1_orders_2('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_26])).

tff(c_6,plain,(
    ! [B_6,A_4] :
      ( r1_tarski(u1_orders_2(B_6),u1_orders_2(A_4))
      | ~ m1_yellow_0(B_6,A_4)
      | ~ l1_orders_2(B_6)
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_33,plain,(
    ! [B_19,A_20] :
      ( r1_tarski(u1_orders_2(B_19),u1_orders_2(A_20))
      | ~ m1_yellow_0(B_19,A_20)
      | ~ l1_orders_2(B_19)
      | ~ l1_orders_2(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_41,plain,(
    ! [A_23,A_24,B_25] :
      ( r1_tarski(A_23,u1_orders_2(A_24))
      | ~ r1_tarski(A_23,u1_orders_2(B_25))
      | ~ m1_yellow_0(B_25,A_24)
      | ~ l1_orders_2(B_25)
      | ~ l1_orders_2(A_24) ) ),
    inference(resolution,[status(thm)],[c_33,c_2])).

tff(c_80,plain,(
    ! [B_35,A_36,A_37] :
      ( r1_tarski(u1_orders_2(B_35),u1_orders_2(A_36))
      | ~ m1_yellow_0(A_37,A_36)
      | ~ l1_orders_2(A_36)
      | ~ m1_yellow_0(B_35,A_37)
      | ~ l1_orders_2(B_35)
      | ~ l1_orders_2(A_37) ) ),
    inference(resolution,[status(thm)],[c_6,c_41])).

tff(c_84,plain,(
    ! [B_35] :
      ( r1_tarski(u1_orders_2(B_35),u1_orders_2('#skF_1'))
      | ~ l1_orders_2('#skF_1')
      | ~ m1_yellow_0(B_35,'#skF_2')
      | ~ l1_orders_2(B_35)
      | ~ l1_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_80])).

tff(c_90,plain,(
    ! [B_35] :
      ( r1_tarski(u1_orders_2(B_35),u1_orders_2('#skF_1'))
      | ~ m1_yellow_0(B_35,'#skF_2')
      | ~ l1_orders_2(B_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_18,c_84])).

tff(c_8,plain,(
    ! [B_6,A_4] :
      ( r1_tarski(u1_struct_0(B_6),u1_struct_0(A_4))
      | ~ m1_yellow_0(B_6,A_4)
      | ~ l1_orders_2(B_6)
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_37,plain,(
    ! [B_21,A_22] :
      ( r1_tarski(u1_struct_0(B_21),u1_struct_0(A_22))
      | ~ m1_yellow_0(B_21,A_22)
      | ~ l1_orders_2(B_21)
      | ~ l1_orders_2(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_45,plain,(
    ! [A_26,A_27,B_28] :
      ( r1_tarski(A_26,u1_struct_0(A_27))
      | ~ r1_tarski(A_26,u1_struct_0(B_28))
      | ~ m1_yellow_0(B_28,A_27)
      | ~ l1_orders_2(B_28)
      | ~ l1_orders_2(A_27) ) ),
    inference(resolution,[status(thm)],[c_37,c_2])).

tff(c_54,plain,(
    ! [B_31,A_32,A_33] :
      ( r1_tarski(u1_struct_0(B_31),u1_struct_0(A_32))
      | ~ m1_yellow_0(A_33,A_32)
      | ~ l1_orders_2(A_32)
      | ~ m1_yellow_0(B_31,A_33)
      | ~ l1_orders_2(B_31)
      | ~ l1_orders_2(A_33) ) ),
    inference(resolution,[status(thm)],[c_8,c_45])).

tff(c_58,plain,(
    ! [B_31] :
      ( r1_tarski(u1_struct_0(B_31),u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1')
      | ~ m1_yellow_0(B_31,'#skF_2')
      | ~ l1_orders_2(B_31)
      | ~ l1_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_54])).

tff(c_91,plain,(
    ! [B_38] :
      ( r1_tarski(u1_struct_0(B_38),u1_struct_0('#skF_1'))
      | ~ m1_yellow_0(B_38,'#skF_2')
      | ~ l1_orders_2(B_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_18,c_58])).

tff(c_4,plain,(
    ! [B_6,A_4] :
      ( m1_yellow_0(B_6,A_4)
      | ~ r1_tarski(u1_orders_2(B_6),u1_orders_2(A_4))
      | ~ r1_tarski(u1_struct_0(B_6),u1_struct_0(A_4))
      | ~ l1_orders_2(B_6)
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_94,plain,(
    ! [B_38] :
      ( m1_yellow_0(B_38,'#skF_1')
      | ~ r1_tarski(u1_orders_2(B_38),u1_orders_2('#skF_1'))
      | ~ l1_orders_2('#skF_1')
      | ~ m1_yellow_0(B_38,'#skF_2')
      | ~ l1_orders_2(B_38) ) ),
    inference(resolution,[status(thm)],[c_91,c_4])).

tff(c_138,plain,(
    ! [B_43] :
      ( m1_yellow_0(B_43,'#skF_1')
      | ~ r1_tarski(u1_orders_2(B_43),u1_orders_2('#skF_1'))
      | ~ m1_yellow_0(B_43,'#skF_2')
      | ~ l1_orders_2(B_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_94])).

tff(c_150,plain,(
    ! [B_44] :
      ( m1_yellow_0(B_44,'#skF_1')
      | ~ m1_yellow_0(B_44,'#skF_2')
      | ~ l1_orders_2(B_44) ) ),
    inference(resolution,[status(thm)],[c_90,c_138])).

tff(c_153,plain,
    ( m1_yellow_0('#skF_3','#skF_1')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_150])).

tff(c_156,plain,(
    m1_yellow_0('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_153])).

tff(c_158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_156])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:51:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.20  
% 1.90/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.20  %$ r1_tarski > m1_yellow_0 > l1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > #skF_2 > #skF_3 > #skF_1
% 1.90/1.20  
% 1.90/1.20  %Foreground sorts:
% 1.90/1.20  
% 1.90/1.20  
% 1.90/1.20  %Background operators:
% 1.90/1.20  
% 1.90/1.20  
% 1.90/1.20  %Foreground operators:
% 1.90/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.90/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.90/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.90/1.20  tff(m1_yellow_0, type, m1_yellow_0: ($i * $i) > $o).
% 1.90/1.20  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.90/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.20  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 1.90/1.20  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.90/1.20  
% 1.97/1.22  tff(f_60, negated_conjecture, ~(![A]: (l1_orders_2(A) => (![B]: (m1_yellow_0(B, A) => (![C]: (m1_yellow_0(C, B) => m1_yellow_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_yellow_6)).
% 1.97/1.22  tff(f_49, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_yellow_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_yellow_0)).
% 1.97/1.22  tff(f_42, axiom, (![A]: (l1_orders_2(A) => (![B]: (l1_orders_2(B) => (m1_yellow_0(B, A) <=> (r1_tarski(u1_struct_0(B), u1_struct_0(A)) & r1_tarski(u1_orders_2(B), u1_orders_2(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_yellow_0)).
% 1.97/1.22  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.97/1.22  tff(c_12, plain, (~m1_yellow_0('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.97/1.22  tff(c_18, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.97/1.22  tff(c_16, plain, (m1_yellow_0('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.97/1.22  tff(c_19, plain, (![B_14, A_15]: (l1_orders_2(B_14) | ~m1_yellow_0(B_14, A_15) | ~l1_orders_2(A_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.97/1.22  tff(c_25, plain, (l1_orders_2('#skF_2') | ~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_16, c_19])).
% 1.97/1.22  tff(c_29, plain, (l1_orders_2('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_25])).
% 1.97/1.22  tff(c_14, plain, (m1_yellow_0('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.97/1.22  tff(c_26, plain, (l1_orders_2('#skF_3') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_14, c_19])).
% 1.97/1.22  tff(c_32, plain, (l1_orders_2('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_29, c_26])).
% 1.97/1.22  tff(c_6, plain, (![B_6, A_4]: (r1_tarski(u1_orders_2(B_6), u1_orders_2(A_4)) | ~m1_yellow_0(B_6, A_4) | ~l1_orders_2(B_6) | ~l1_orders_2(A_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.97/1.22  tff(c_33, plain, (![B_19, A_20]: (r1_tarski(u1_orders_2(B_19), u1_orders_2(A_20)) | ~m1_yellow_0(B_19, A_20) | ~l1_orders_2(B_19) | ~l1_orders_2(A_20))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.97/1.22  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.97/1.22  tff(c_41, plain, (![A_23, A_24, B_25]: (r1_tarski(A_23, u1_orders_2(A_24)) | ~r1_tarski(A_23, u1_orders_2(B_25)) | ~m1_yellow_0(B_25, A_24) | ~l1_orders_2(B_25) | ~l1_orders_2(A_24))), inference(resolution, [status(thm)], [c_33, c_2])).
% 1.97/1.22  tff(c_80, plain, (![B_35, A_36, A_37]: (r1_tarski(u1_orders_2(B_35), u1_orders_2(A_36)) | ~m1_yellow_0(A_37, A_36) | ~l1_orders_2(A_36) | ~m1_yellow_0(B_35, A_37) | ~l1_orders_2(B_35) | ~l1_orders_2(A_37))), inference(resolution, [status(thm)], [c_6, c_41])).
% 1.97/1.22  tff(c_84, plain, (![B_35]: (r1_tarski(u1_orders_2(B_35), u1_orders_2('#skF_1')) | ~l1_orders_2('#skF_1') | ~m1_yellow_0(B_35, '#skF_2') | ~l1_orders_2(B_35) | ~l1_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_80])).
% 1.97/1.22  tff(c_90, plain, (![B_35]: (r1_tarski(u1_orders_2(B_35), u1_orders_2('#skF_1')) | ~m1_yellow_0(B_35, '#skF_2') | ~l1_orders_2(B_35))), inference(demodulation, [status(thm), theory('equality')], [c_29, c_18, c_84])).
% 1.97/1.22  tff(c_8, plain, (![B_6, A_4]: (r1_tarski(u1_struct_0(B_6), u1_struct_0(A_4)) | ~m1_yellow_0(B_6, A_4) | ~l1_orders_2(B_6) | ~l1_orders_2(A_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.97/1.22  tff(c_37, plain, (![B_21, A_22]: (r1_tarski(u1_struct_0(B_21), u1_struct_0(A_22)) | ~m1_yellow_0(B_21, A_22) | ~l1_orders_2(B_21) | ~l1_orders_2(A_22))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.97/1.22  tff(c_45, plain, (![A_26, A_27, B_28]: (r1_tarski(A_26, u1_struct_0(A_27)) | ~r1_tarski(A_26, u1_struct_0(B_28)) | ~m1_yellow_0(B_28, A_27) | ~l1_orders_2(B_28) | ~l1_orders_2(A_27))), inference(resolution, [status(thm)], [c_37, c_2])).
% 1.97/1.22  tff(c_54, plain, (![B_31, A_32, A_33]: (r1_tarski(u1_struct_0(B_31), u1_struct_0(A_32)) | ~m1_yellow_0(A_33, A_32) | ~l1_orders_2(A_32) | ~m1_yellow_0(B_31, A_33) | ~l1_orders_2(B_31) | ~l1_orders_2(A_33))), inference(resolution, [status(thm)], [c_8, c_45])).
% 1.97/1.22  tff(c_58, plain, (![B_31]: (r1_tarski(u1_struct_0(B_31), u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1') | ~m1_yellow_0(B_31, '#skF_2') | ~l1_orders_2(B_31) | ~l1_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_54])).
% 1.97/1.22  tff(c_91, plain, (![B_38]: (r1_tarski(u1_struct_0(B_38), u1_struct_0('#skF_1')) | ~m1_yellow_0(B_38, '#skF_2') | ~l1_orders_2(B_38))), inference(demodulation, [status(thm), theory('equality')], [c_29, c_18, c_58])).
% 1.97/1.22  tff(c_4, plain, (![B_6, A_4]: (m1_yellow_0(B_6, A_4) | ~r1_tarski(u1_orders_2(B_6), u1_orders_2(A_4)) | ~r1_tarski(u1_struct_0(B_6), u1_struct_0(A_4)) | ~l1_orders_2(B_6) | ~l1_orders_2(A_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.97/1.22  tff(c_94, plain, (![B_38]: (m1_yellow_0(B_38, '#skF_1') | ~r1_tarski(u1_orders_2(B_38), u1_orders_2('#skF_1')) | ~l1_orders_2('#skF_1') | ~m1_yellow_0(B_38, '#skF_2') | ~l1_orders_2(B_38))), inference(resolution, [status(thm)], [c_91, c_4])).
% 1.97/1.22  tff(c_138, plain, (![B_43]: (m1_yellow_0(B_43, '#skF_1') | ~r1_tarski(u1_orders_2(B_43), u1_orders_2('#skF_1')) | ~m1_yellow_0(B_43, '#skF_2') | ~l1_orders_2(B_43))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_94])).
% 1.97/1.22  tff(c_150, plain, (![B_44]: (m1_yellow_0(B_44, '#skF_1') | ~m1_yellow_0(B_44, '#skF_2') | ~l1_orders_2(B_44))), inference(resolution, [status(thm)], [c_90, c_138])).
% 1.97/1.22  tff(c_153, plain, (m1_yellow_0('#skF_3', '#skF_1') | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_14, c_150])).
% 1.97/1.22  tff(c_156, plain, (m1_yellow_0('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_153])).
% 1.97/1.22  tff(c_158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_156])).
% 1.97/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.22  
% 1.97/1.22  Inference rules
% 1.97/1.22  ----------------------
% 1.97/1.22  #Ref     : 0
% 1.97/1.22  #Sup     : 27
% 1.97/1.22  #Fact    : 0
% 1.97/1.22  #Define  : 0
% 1.97/1.22  #Split   : 0
% 1.97/1.22  #Chain   : 0
% 1.97/1.22  #Close   : 0
% 1.97/1.22  
% 1.97/1.22  Ordering : KBO
% 1.97/1.22  
% 1.97/1.22  Simplification rules
% 1.97/1.22  ----------------------
% 1.97/1.22  #Subsume      : 2
% 1.97/1.22  #Demod        : 20
% 1.97/1.22  #Tautology    : 2
% 1.97/1.22  #SimpNegUnit  : 1
% 1.97/1.22  #BackRed      : 0
% 1.97/1.22  
% 1.97/1.22  #Partial instantiations: 0
% 1.97/1.22  #Strategies tried      : 1
% 1.97/1.22  
% 1.97/1.22  Timing (in seconds)
% 1.97/1.22  ----------------------
% 1.97/1.22  Preprocessing        : 0.26
% 1.97/1.22  Parsing              : 0.15
% 1.97/1.22  CNF conversion       : 0.02
% 1.97/1.22  Main loop            : 0.19
% 1.97/1.22  Inferencing          : 0.08
% 1.97/1.22  Reduction            : 0.05
% 1.97/1.22  Demodulation         : 0.03
% 1.97/1.22  BG Simplification    : 0.01
% 1.97/1.22  Subsumption          : 0.05
% 1.97/1.22  Abstraction          : 0.01
% 1.97/1.22  MUC search           : 0.00
% 1.97/1.22  Cooper               : 0.00
% 1.97/1.22  Total                : 0.48
% 1.97/1.22  Index Insertion      : 0.00
% 1.97/1.22  Index Deletion       : 0.00
% 1.97/1.22  Index Matching       : 0.00
% 1.97/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
