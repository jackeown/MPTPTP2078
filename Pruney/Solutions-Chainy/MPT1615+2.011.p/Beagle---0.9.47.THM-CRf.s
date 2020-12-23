%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:35 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   30 (  41 expanded)
%              Number of leaves         :   17 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   35 (  66 expanded)
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

tff(f_55,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k3_yellow_0(k2_yellow_1(u1_pre_topc(A))) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_yellow_1)).

tff(f_38,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_pre_topc)).

tff(f_45,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k1_xboole_0,A)
       => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_32,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ~ v1_xboole_0(u1_pre_topc(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_pre_topc)).

tff(c_12,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4,plain,(
    ! [A_2] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(A_2))
      | ~ l1_pre_topc(A_2)
      | ~ v2_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_17,plain,(
    ! [A_6] :
      ( k3_yellow_0(k2_yellow_1(A_6)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,A_6)
      | v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    k3_yellow_0(k2_yellow_1(u1_pre_topc('#skF_1'))) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,
    ( ~ r2_hidden(k1_xboole_0,u1_pre_topc('#skF_1'))
    | v1_xboole_0(u1_pre_topc('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_17,c_8])).

tff(c_30,plain,(
    ~ r2_hidden(k1_xboole_0,u1_pre_topc('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_33,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_30])).

tff(c_37,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_33])).

tff(c_38,plain,(
    v1_xboole_0(u1_pre_topc('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_2,plain,(
    ! [A_1] :
      ( ~ v1_xboole_0(u1_pre_topc(A_1))
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_42,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_2])).

tff(c_46,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:18:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.15  
% 1.63/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.16  %$ r2_hidden > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_pre_topc > k3_yellow_0 > k2_yellow_1 > k1_xboole_0 > #skF_1
% 1.63/1.16  
% 1.63/1.16  %Foreground sorts:
% 1.63/1.16  
% 1.63/1.16  
% 1.63/1.16  %Background operators:
% 1.63/1.16  
% 1.63/1.16  
% 1.63/1.16  %Foreground operators:
% 1.63/1.16  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.63/1.16  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 1.63/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.63/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.63/1.16  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 1.63/1.16  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 1.63/1.16  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.63/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.16  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.63/1.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.63/1.16  
% 1.79/1.17  tff(f_55, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (k3_yellow_0(k2_yellow_1(u1_pre_topc(A))) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_yellow_1)).
% 1.79/1.17  tff(f_38, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => r2_hidden(k1_xboole_0, u1_pre_topc(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_pre_topc)).
% 1.79/1.17  tff(f_45, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow_1)).
% 1.79/1.17  tff(f_32, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => ~v1_xboole_0(u1_pre_topc(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_pre_topc)).
% 1.79/1.17  tff(c_12, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.79/1.17  tff(c_10, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.79/1.17  tff(c_4, plain, (![A_2]: (r2_hidden(k1_xboole_0, u1_pre_topc(A_2)) | ~l1_pre_topc(A_2) | ~v2_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.79/1.17  tff(c_17, plain, (![A_6]: (k3_yellow_0(k2_yellow_1(A_6))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, A_6) | v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.79/1.17  tff(c_8, plain, (k3_yellow_0(k2_yellow_1(u1_pre_topc('#skF_1')))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.79/1.17  tff(c_28, plain, (~r2_hidden(k1_xboole_0, u1_pre_topc('#skF_1')) | v1_xboole_0(u1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_17, c_8])).
% 1.79/1.17  tff(c_30, plain, (~r2_hidden(k1_xboole_0, u1_pre_topc('#skF_1'))), inference(splitLeft, [status(thm)], [c_28])).
% 1.79/1.17  tff(c_33, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4, c_30])).
% 1.79/1.17  tff(c_37, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_10, c_33])).
% 1.79/1.17  tff(c_38, plain, (v1_xboole_0(u1_pre_topc('#skF_1'))), inference(splitRight, [status(thm)], [c_28])).
% 1.79/1.17  tff(c_2, plain, (![A_1]: (~v1_xboole_0(u1_pre_topc(A_1)) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.79/1.17  tff(c_42, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_2])).
% 1.79/1.17  tff(c_46, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_10, c_42])).
% 1.79/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.17  
% 1.79/1.17  Inference rules
% 1.79/1.17  ----------------------
% 1.79/1.17  #Ref     : 0
% 1.79/1.17  #Sup     : 5
% 1.79/1.17  #Fact    : 0
% 1.79/1.17  #Define  : 0
% 1.79/1.17  #Split   : 1
% 1.79/1.17  #Chain   : 0
% 1.79/1.17  #Close   : 0
% 1.79/1.17  
% 1.79/1.17  Ordering : KBO
% 1.79/1.17  
% 1.79/1.17  Simplification rules
% 1.79/1.17  ----------------------
% 1.79/1.17  #Subsume      : 0
% 1.79/1.17  #Demod        : 4
% 1.79/1.17  #Tautology    : 2
% 1.79/1.17  #SimpNegUnit  : 0
% 1.79/1.17  #BackRed      : 0
% 1.79/1.17  
% 1.79/1.17  #Partial instantiations: 0
% 1.79/1.17  #Strategies tried      : 1
% 1.79/1.17  
% 1.79/1.17  Timing (in seconds)
% 1.79/1.17  ----------------------
% 1.79/1.17  Preprocessing        : 0.27
% 1.79/1.17  Parsing              : 0.15
% 1.79/1.17  CNF conversion       : 0.02
% 1.79/1.17  Main loop            : 0.09
% 1.79/1.17  Inferencing          : 0.04
% 1.79/1.17  Reduction            : 0.02
% 1.79/1.17  Demodulation         : 0.02
% 1.79/1.17  BG Simplification    : 0.01
% 1.79/1.17  Subsumption          : 0.01
% 1.79/1.17  Abstraction          : 0.00
% 1.79/1.17  MUC search           : 0.00
% 1.79/1.17  Cooper               : 0.00
% 1.79/1.17  Total                : 0.39
% 1.79/1.17  Index Insertion      : 0.00
% 1.79/1.17  Index Deletion       : 0.00
% 1.79/1.17  Index Matching       : 0.00
% 1.79/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
