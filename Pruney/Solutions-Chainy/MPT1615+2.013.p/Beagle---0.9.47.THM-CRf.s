%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:36 EST 2020

% Result     : Theorem 1.57s
% Output     : CNFRefutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   32 (  44 expanded)
%              Number of leaves         :   17 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   39 (  73 expanded)
%              Number of equality atoms :    4 (  12 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_pre_topc > k3_yellow_0 > k2_yellow_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_53,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k3_yellow_0(k2_yellow_1(u1_pre_topc(A))) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow_1)).

tff(f_36,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_pre_topc)).

tff(f_43,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k1_xboole_0,A)
       => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(c_12,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [A_3] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(A_3))
      | ~ l1_pre_topc(A_3)
      | ~ v2_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_22,plain,(
    ! [A_9] :
      ( k3_yellow_0(k2_yellow_1(A_9)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    k3_yellow_0(k2_yellow_1(u1_pre_topc('#skF_1'))) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_33,plain,
    ( ~ r2_hidden(k1_xboole_0,u1_pre_topc('#skF_1'))
    | v1_xboole_0(u1_pre_topc('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_8])).

tff(c_35,plain,(
    ~ r2_hidden(k1_xboole_0,u1_pre_topc('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_33])).

tff(c_38,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_35])).

tff(c_42,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_38])).

tff(c_43,plain,(
    v1_xboole_0(u1_pre_topc('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_33])).

tff(c_16,plain,(
    ! [A_7] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(A_7))
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_20,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(u1_pre_topc(A_7))
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7) ) ),
    inference(resolution,[status(thm)],[c_16,c_2])).

tff(c_47,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_43,c_20])).

tff(c_51,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:01:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.57/1.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.07  
% 1.57/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.07  %$ r2_hidden > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_pre_topc > k3_yellow_0 > k2_yellow_1 > k1_xboole_0 > #skF_1
% 1.57/1.07  
% 1.57/1.07  %Foreground sorts:
% 1.57/1.07  
% 1.57/1.07  
% 1.57/1.07  %Background operators:
% 1.57/1.07  
% 1.57/1.07  
% 1.57/1.07  %Foreground operators:
% 1.57/1.07  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.57/1.07  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 1.57/1.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.57/1.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.57/1.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.57/1.07  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 1.57/1.07  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 1.57/1.07  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.57/1.07  tff('#skF_1', type, '#skF_1': $i).
% 1.57/1.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.57/1.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.57/1.07  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.57/1.07  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.57/1.07  
% 1.57/1.08  tff(f_53, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (k3_yellow_0(k2_yellow_1(u1_pre_topc(A))) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_yellow_1)).
% 1.57/1.08  tff(f_36, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => r2_hidden(k1_xboole_0, u1_pre_topc(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_pre_topc)).
% 1.57/1.08  tff(f_43, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_yellow_1)).
% 1.57/1.08  tff(f_30, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 1.57/1.08  tff(c_12, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.57/1.08  tff(c_10, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.57/1.08  tff(c_4, plain, (![A_3]: (r2_hidden(k1_xboole_0, u1_pre_topc(A_3)) | ~l1_pre_topc(A_3) | ~v2_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.57/1.08  tff(c_22, plain, (![A_9]: (k3_yellow_0(k2_yellow_1(A_9))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.57/1.08  tff(c_8, plain, (k3_yellow_0(k2_yellow_1(u1_pre_topc('#skF_1')))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.57/1.08  tff(c_33, plain, (~r2_hidden(k1_xboole_0, u1_pre_topc('#skF_1')) | v1_xboole_0(u1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_22, c_8])).
% 1.57/1.08  tff(c_35, plain, (~r2_hidden(k1_xboole_0, u1_pre_topc('#skF_1'))), inference(splitLeft, [status(thm)], [c_33])).
% 1.57/1.08  tff(c_38, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4, c_35])).
% 1.57/1.08  tff(c_42, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_10, c_38])).
% 1.57/1.08  tff(c_43, plain, (v1_xboole_0(u1_pre_topc('#skF_1'))), inference(splitRight, [status(thm)], [c_33])).
% 1.57/1.08  tff(c_16, plain, (![A_7]: (r2_hidden(k1_xboole_0, u1_pre_topc(A_7)) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.57/1.08  tff(c_2, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.57/1.08  tff(c_20, plain, (![A_7]: (~v1_xboole_0(u1_pre_topc(A_7)) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7))), inference(resolution, [status(thm)], [c_16, c_2])).
% 1.57/1.08  tff(c_47, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_43, c_20])).
% 1.57/1.08  tff(c_51, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_10, c_47])).
% 1.57/1.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.08  
% 1.57/1.08  Inference rules
% 1.57/1.08  ----------------------
% 1.57/1.08  #Ref     : 0
% 1.57/1.08  #Sup     : 6
% 1.57/1.08  #Fact    : 0
% 1.57/1.08  #Define  : 0
% 1.57/1.08  #Split   : 1
% 1.57/1.08  #Chain   : 0
% 1.57/1.08  #Close   : 0
% 1.57/1.08  
% 1.57/1.08  Ordering : KBO
% 1.57/1.08  
% 1.57/1.08  Simplification rules
% 1.57/1.08  ----------------------
% 1.57/1.08  #Subsume      : 0
% 1.57/1.08  #Demod        : 4
% 1.57/1.08  #Tautology    : 2
% 1.57/1.08  #SimpNegUnit  : 0
% 1.57/1.08  #BackRed      : 0
% 1.57/1.08  
% 1.57/1.08  #Partial instantiations: 0
% 1.57/1.08  #Strategies tried      : 1
% 1.57/1.08  
% 1.57/1.08  Timing (in seconds)
% 1.57/1.08  ----------------------
% 1.64/1.08  Preprocessing        : 0.24
% 1.64/1.08  Parsing              : 0.14
% 1.64/1.08  CNF conversion       : 0.01
% 1.64/1.08  Main loop            : 0.09
% 1.64/1.08  Inferencing          : 0.04
% 1.64/1.08  Reduction            : 0.02
% 1.64/1.08  Demodulation         : 0.02
% 1.64/1.08  BG Simplification    : 0.01
% 1.64/1.08  Subsumption          : 0.02
% 1.64/1.08  Abstraction          : 0.00
% 1.64/1.08  MUC search           : 0.00
% 1.64/1.08  Cooper               : 0.00
% 1.64/1.08  Total                : 0.35
% 1.64/1.08  Index Insertion      : 0.00
% 1.64/1.08  Index Deletion       : 0.00
% 1.64/1.08  Index Matching       : 0.00
% 1.64/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
