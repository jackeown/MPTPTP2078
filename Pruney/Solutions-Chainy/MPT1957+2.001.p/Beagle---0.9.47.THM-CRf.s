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
% DateTime   : Thu Dec  3 10:30:56 EST 2020

% Result     : Theorem 1.44s
% Output     : CNFRefutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   18 (  18 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    3
%              Number of atoms          :    9 (   9 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ #nlpp > u1_struct_0 > u1_orders_2 > k9_setfam_1 > k3_yellow_1 > k2_yellow_1 > k1_yellow_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_31,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_29,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_34,negated_conjecture,(
    ~ ! [A] : u1_struct_0(k3_yellow_1(A)) = k9_setfam_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_waybel_7)).

tff(c_18,plain,(
    ! [A_4] : k2_yellow_1(k9_setfam_1(A_4)) = k3_yellow_1(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1] : u1_struct_0(k2_yellow_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ! [A_4] : u1_struct_0(k3_yellow_1(A_4)) = k9_setfam_1(A_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2])).

tff(c_8,plain,(
    u1_struct_0(k3_yellow_1('#skF_1')) != k9_setfam_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_44,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:46:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.44/1.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.44/1.04  
% 1.44/1.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.44/1.04  %$ #nlpp > u1_struct_0 > u1_orders_2 > k9_setfam_1 > k3_yellow_1 > k2_yellow_1 > k1_yellow_1 > #skF_1
% 1.44/1.04  
% 1.44/1.04  %Foreground sorts:
% 1.44/1.04  
% 1.44/1.04  
% 1.44/1.04  %Background operators:
% 1.44/1.04  
% 1.44/1.04  
% 1.44/1.04  %Foreground operators:
% 1.44/1.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.44/1.04  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 1.44/1.04  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 1.44/1.04  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 1.44/1.04  tff('#skF_1', type, '#skF_1': $i).
% 1.44/1.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.44/1.04  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 1.44/1.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.44/1.04  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 1.44/1.04  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.44/1.04  
% 1.44/1.05  tff(f_31, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_yellow_1)).
% 1.44/1.05  tff(f_29, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 1.44/1.05  tff(f_34, negated_conjecture, ~(![A]: (u1_struct_0(k3_yellow_1(A)) = k9_setfam_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_waybel_7)).
% 1.44/1.05  tff(c_18, plain, (![A_4]: (k2_yellow_1(k9_setfam_1(A_4))=k3_yellow_1(A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.44/1.05  tff(c_2, plain, (![A_1]: (u1_struct_0(k2_yellow_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.44/1.05  tff(c_24, plain, (![A_4]: (u1_struct_0(k3_yellow_1(A_4))=k9_setfam_1(A_4))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2])).
% 1.44/1.05  tff(c_8, plain, (u1_struct_0(k3_yellow_1('#skF_1'))!=k9_setfam_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.44/1.05  tff(c_44, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_8])).
% 1.44/1.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.44/1.05  
% 1.44/1.05  Inference rules
% 1.44/1.05  ----------------------
% 1.44/1.05  #Ref     : 0
% 1.44/1.05  #Sup     : 8
% 1.44/1.05  #Fact    : 0
% 1.44/1.05  #Define  : 0
% 1.44/1.05  #Split   : 0
% 1.44/1.05  #Chain   : 0
% 1.44/1.05  #Close   : 0
% 1.44/1.05  
% 1.44/1.05  Ordering : KBO
% 1.44/1.05  
% 1.44/1.05  Simplification rules
% 1.44/1.05  ----------------------
% 1.44/1.05  #Subsume      : 0
% 1.44/1.05  #Demod        : 1
% 1.44/1.05  #Tautology    : 6
% 1.44/1.05  #SimpNegUnit  : 0
% 1.44/1.05  #BackRed      : 1
% 1.44/1.05  
% 1.44/1.05  #Partial instantiations: 0
% 1.44/1.05  #Strategies tried      : 1
% 1.44/1.05  
% 1.44/1.05  Timing (in seconds)
% 1.44/1.05  ----------------------
% 1.44/1.05  Preprocessing        : 0.23
% 1.44/1.05  Parsing              : 0.12
% 1.44/1.05  CNF conversion       : 0.01
% 1.44/1.05  Main loop            : 0.06
% 1.44/1.05  Inferencing          : 0.03
% 1.44/1.05  Reduction            : 0.02
% 1.44/1.05  Demodulation         : 0.01
% 1.44/1.05  BG Simplification    : 0.01
% 1.44/1.05  Subsumption          : 0.00
% 1.44/1.05  Abstraction          : 0.00
% 1.44/1.05  MUC search           : 0.00
% 1.44/1.05  Cooper               : 0.00
% 1.44/1.05  Total                : 0.31
% 1.44/1.05  Index Insertion      : 0.00
% 1.44/1.05  Index Deletion       : 0.00
% 1.44/1.05  Index Matching       : 0.00
% 1.44/1.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
