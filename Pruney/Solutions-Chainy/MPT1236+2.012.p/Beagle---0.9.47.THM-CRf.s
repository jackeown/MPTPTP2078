%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:36 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   26 (  29 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :   35 (  40 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > k1_struct_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_50,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => k1_tops_1(A,k1_struct_0(A)) = k1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tops_1)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => v1_xboole_0(k1_tops_1(A,k1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_tops_1)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => v1_xboole_0(k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_struct_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(c_12,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [A_3] :
      ( l1_struct_0(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_5] :
      ( v1_xboole_0(k1_tops_1(A_5,k1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_4] :
      ( v1_xboole_0(k1_struct_0(A_4))
      | ~ l1_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_15,plain,(
    ! [B_8,A_9] :
      ( ~ v1_xboole_0(B_8)
      | B_8 = A_9
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_23,plain,(
    ! [A_11,A_12] :
      ( k1_struct_0(A_11) = A_12
      | ~ v1_xboole_0(A_12)
      | ~ l1_struct_0(A_11) ) ),
    inference(resolution,[status(thm)],[c_6,c_15])).

tff(c_55,plain,(
    ! [A_22,A_23] :
      ( k1_tops_1(A_22,k1_struct_0(A_22)) = k1_struct_0(A_23)
      | ~ l1_struct_0(A_23)
      | ~ l1_pre_topc(A_22) ) ),
    inference(resolution,[status(thm)],[c_8,c_23])).

tff(c_59,plain,(
    ! [A_24,A_25] :
      ( k1_tops_1(A_24,k1_struct_0(A_24)) = k1_struct_0(A_25)
      | ~ l1_pre_topc(A_24)
      | ~ l1_pre_topc(A_25) ) ),
    inference(resolution,[status(thm)],[c_4,c_55])).

tff(c_111,plain,(
    ! [A_29] :
      ( k1_tops_1(A_29,k1_struct_0(A_29)) = k1_struct_0('#skF_1')
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_12,c_59])).

tff(c_10,plain,(
    k1_tops_1('#skF_1',k1_struct_0('#skF_1')) != k1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_129,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_10])).

tff(c_144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_129])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:44:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.13  
% 1.62/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.14  %$ v1_xboole_0 > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > k1_struct_0 > #skF_1
% 1.62/1.14  
% 1.62/1.14  %Foreground sorts:
% 1.62/1.14  
% 1.62/1.14  
% 1.62/1.14  %Background operators:
% 1.62/1.14  
% 1.62/1.14  
% 1.62/1.14  %Foreground operators:
% 1.62/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.14  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.62/1.14  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 1.62/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.14  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.62/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.14  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 1.62/1.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.62/1.14  
% 1.62/1.14  tff(f_50, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (k1_tops_1(A, k1_struct_0(A)) = k1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_tops_1)).
% 1.62/1.14  tff(f_37, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 1.62/1.14  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => v1_xboole_0(k1_tops_1(A, k1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_tops_1)).
% 1.62/1.14  tff(f_41, axiom, (![A]: (l1_struct_0(A) => v1_xboole_0(k1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_struct_0)).
% 1.62/1.14  tff(f_33, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 1.62/1.14  tff(c_12, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.62/1.14  tff(c_4, plain, (![A_3]: (l1_struct_0(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.62/1.14  tff(c_8, plain, (![A_5]: (v1_xboole_0(k1_tops_1(A_5, k1_struct_0(A_5))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.62/1.14  tff(c_6, plain, (![A_4]: (v1_xboole_0(k1_struct_0(A_4)) | ~l1_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.62/1.14  tff(c_15, plain, (![B_8, A_9]: (~v1_xboole_0(B_8) | B_8=A_9 | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.62/1.14  tff(c_23, plain, (![A_11, A_12]: (k1_struct_0(A_11)=A_12 | ~v1_xboole_0(A_12) | ~l1_struct_0(A_11))), inference(resolution, [status(thm)], [c_6, c_15])).
% 1.62/1.14  tff(c_55, plain, (![A_22, A_23]: (k1_tops_1(A_22, k1_struct_0(A_22))=k1_struct_0(A_23) | ~l1_struct_0(A_23) | ~l1_pre_topc(A_22))), inference(resolution, [status(thm)], [c_8, c_23])).
% 1.62/1.14  tff(c_59, plain, (![A_24, A_25]: (k1_tops_1(A_24, k1_struct_0(A_24))=k1_struct_0(A_25) | ~l1_pre_topc(A_24) | ~l1_pre_topc(A_25))), inference(resolution, [status(thm)], [c_4, c_55])).
% 1.62/1.14  tff(c_111, plain, (![A_29]: (k1_tops_1(A_29, k1_struct_0(A_29))=k1_struct_0('#skF_1') | ~l1_pre_topc(A_29))), inference(resolution, [status(thm)], [c_12, c_59])).
% 1.62/1.14  tff(c_10, plain, (k1_tops_1('#skF_1', k1_struct_0('#skF_1'))!=k1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.62/1.14  tff(c_129, plain, (~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_111, c_10])).
% 1.62/1.14  tff(c_144, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_129])).
% 1.62/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.14  
% 1.62/1.14  Inference rules
% 1.62/1.14  ----------------------
% 1.62/1.14  #Ref     : 0
% 1.62/1.14  #Sup     : 35
% 1.62/1.14  #Fact    : 0
% 1.62/1.14  #Define  : 0
% 1.62/1.14  #Split   : 0
% 1.62/1.14  #Chain   : 0
% 1.62/1.14  #Close   : 0
% 1.62/1.14  
% 1.62/1.14  Ordering : KBO
% 1.62/1.14  
% 1.62/1.14  Simplification rules
% 1.62/1.14  ----------------------
% 1.62/1.14  #Subsume      : 16
% 1.62/1.14  #Demod        : 3
% 1.62/1.14  #Tautology    : 2
% 1.62/1.14  #SimpNegUnit  : 0
% 1.62/1.14  #BackRed      : 0
% 1.62/1.14  
% 1.62/1.14  #Partial instantiations: 0
% 1.62/1.14  #Strategies tried      : 1
% 1.62/1.14  
% 1.62/1.14  Timing (in seconds)
% 1.62/1.14  ----------------------
% 1.62/1.15  Preprocessing        : 0.24
% 1.62/1.15  Parsing              : 0.14
% 1.62/1.15  CNF conversion       : 0.01
% 1.62/1.15  Main loop            : 0.15
% 1.62/1.15  Inferencing          : 0.07
% 1.62/1.15  Reduction            : 0.03
% 1.62/1.15  Demodulation         : 0.02
% 1.62/1.15  BG Simplification    : 0.01
% 1.62/1.15  Subsumption          : 0.03
% 1.62/1.15  Abstraction          : 0.01
% 1.62/1.15  MUC search           : 0.00
% 1.62/1.15  Cooper               : 0.00
% 1.62/1.15  Total                : 0.41
% 1.62/1.15  Index Insertion      : 0.00
% 1.62/1.15  Index Deletion       : 0.00
% 1.62/1.15  Index Matching       : 0.00
% 1.62/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
