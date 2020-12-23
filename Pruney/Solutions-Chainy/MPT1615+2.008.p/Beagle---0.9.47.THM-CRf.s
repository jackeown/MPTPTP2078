%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:35 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   33 (  45 expanded)
%              Number of leaves         :   18 (  25 expanded)
%              Depth                    :    5
%              Number of atoms          :   39 (  73 expanded)
%              Number of equality atoms :    4 (  12 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_pre_topc > k3_yellow_0 > k2_yellow_1 > k1_xboole_0 > #skF_1 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_54,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k3_yellow_0(k2_yellow_1(u1_pre_topc(A))) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_yellow_1)).

tff(f_37,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_pre_topc)).

tff(f_44,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k1_xboole_0,A)
       => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_14,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [A_5] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(A_5))
      | ~ l1_pre_topc(A_5)
      | ~ v2_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_29,plain,(
    ! [A_12] :
      ( k3_yellow_0(k2_yellow_1(A_12)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,A_12)
      | v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10,plain,(
    k3_yellow_0(k2_yellow_1(u1_pre_topc('#skF_2'))) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_40,plain,
    ( ~ r2_hidden(k1_xboole_0,u1_pre_topc('#skF_2'))
    | v1_xboole_0(u1_pre_topc('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_29,c_10])).

tff(c_42,plain,(
    ~ r2_hidden(k1_xboole_0,u1_pre_topc('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_45,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_42])).

tff(c_49,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_45])).

tff(c_50,plain,(
    v1_xboole_0(u1_pre_topc('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_23,plain,(
    ! [A_10] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(A_10))
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_27,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(u1_pre_topc(A_10))
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10) ) ),
    inference(resolution,[status(thm)],[c_23,c_2])).

tff(c_54,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_27])).

tff(c_58,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:23:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.16  
% 1.75/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.16  %$ r2_hidden > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_pre_topc > k3_yellow_0 > k2_yellow_1 > k1_xboole_0 > #skF_1 > #skF_2
% 1.75/1.16  
% 1.75/1.16  %Foreground sorts:
% 1.75/1.16  
% 1.75/1.16  
% 1.75/1.16  %Background operators:
% 1.75/1.16  
% 1.75/1.16  
% 1.75/1.16  %Foreground operators:
% 1.75/1.16  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.75/1.16  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 1.75/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.75/1.16  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.75/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.75/1.16  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 1.75/1.16  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 1.75/1.16  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.75/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.75/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.16  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.75/1.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.75/1.16  
% 1.75/1.17  tff(f_54, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (k3_yellow_0(k2_yellow_1(u1_pre_topc(A))) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_yellow_1)).
% 1.75/1.17  tff(f_37, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => r2_hidden(k1_xboole_0, u1_pre_topc(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_pre_topc)).
% 1.75/1.17  tff(f_44, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow_1)).
% 1.75/1.17  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.75/1.17  tff(c_14, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.75/1.17  tff(c_12, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.75/1.17  tff(c_6, plain, (![A_5]: (r2_hidden(k1_xboole_0, u1_pre_topc(A_5)) | ~l1_pre_topc(A_5) | ~v2_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.75/1.17  tff(c_29, plain, (![A_12]: (k3_yellow_0(k2_yellow_1(A_12))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, A_12) | v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.75/1.17  tff(c_10, plain, (k3_yellow_0(k2_yellow_1(u1_pre_topc('#skF_2')))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.75/1.17  tff(c_40, plain, (~r2_hidden(k1_xboole_0, u1_pre_topc('#skF_2')) | v1_xboole_0(u1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_29, c_10])).
% 1.75/1.17  tff(c_42, plain, (~r2_hidden(k1_xboole_0, u1_pre_topc('#skF_2'))), inference(splitLeft, [status(thm)], [c_40])).
% 1.75/1.17  tff(c_45, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_42])).
% 1.75/1.17  tff(c_49, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_45])).
% 1.75/1.17  tff(c_50, plain, (v1_xboole_0(u1_pre_topc('#skF_2'))), inference(splitRight, [status(thm)], [c_40])).
% 1.75/1.17  tff(c_23, plain, (![A_10]: (r2_hidden(k1_xboole_0, u1_pre_topc(A_10)) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.75/1.17  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.75/1.17  tff(c_27, plain, (![A_10]: (~v1_xboole_0(u1_pre_topc(A_10)) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10))), inference(resolution, [status(thm)], [c_23, c_2])).
% 1.75/1.17  tff(c_54, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_27])).
% 1.75/1.17  tff(c_58, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_54])).
% 1.75/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.17  
% 1.75/1.17  Inference rules
% 1.75/1.17  ----------------------
% 1.75/1.17  #Ref     : 0
% 1.75/1.17  #Sup     : 7
% 1.75/1.17  #Fact    : 0
% 1.75/1.17  #Define  : 0
% 1.75/1.17  #Split   : 1
% 1.75/1.17  #Chain   : 0
% 1.75/1.17  #Close   : 0
% 1.75/1.17  
% 1.75/1.17  Ordering : KBO
% 1.75/1.17  
% 1.75/1.17  Simplification rules
% 1.75/1.17  ----------------------
% 1.75/1.17  #Subsume      : 0
% 1.75/1.17  #Demod        : 4
% 1.75/1.17  #Tautology    : 3
% 1.75/1.17  #SimpNegUnit  : 0
% 1.75/1.17  #BackRed      : 0
% 1.75/1.17  
% 1.75/1.17  #Partial instantiations: 0
% 1.75/1.17  #Strategies tried      : 1
% 1.75/1.17  
% 1.75/1.17  Timing (in seconds)
% 1.75/1.17  ----------------------
% 1.75/1.17  Preprocessing        : 0.26
% 1.75/1.17  Parsing              : 0.15
% 1.75/1.17  CNF conversion       : 0.02
% 1.75/1.17  Main loop            : 0.10
% 1.75/1.17  Inferencing          : 0.04
% 1.75/1.17  Reduction            : 0.02
% 1.75/1.17  Demodulation         : 0.02
% 1.75/1.17  BG Simplification    : 0.01
% 1.75/1.17  Subsumption          : 0.02
% 1.75/1.17  Abstraction          : 0.00
% 1.75/1.17  MUC search           : 0.00
% 1.75/1.17  Cooper               : 0.00
% 1.75/1.17  Total                : 0.38
% 1.75/1.17  Index Insertion      : 0.00
% 1.75/1.17  Index Deletion       : 0.00
% 1.75/1.17  Index Matching       : 0.00
% 1.75/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
