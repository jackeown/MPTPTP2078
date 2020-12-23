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
% DateTime   : Thu Dec  3 10:05:52 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   42 (  46 expanded)
%              Number of leaves         :   24 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   63 (  83 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v5_relat_1(C,A)
          & v1_funct_1(C) )
       => ( r2_hidden(B,k1_relat_1(C))
         => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_36,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_38,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_32,plain,(
    r2_hidden('#skF_4',k1_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_28,plain,(
    ! [B_14,A_13] :
      ( r2_hidden(k1_funct_1(B_14,A_13),k2_relat_1(B_14))
      | ~ r2_hidden(A_13,k1_relat_1(B_14))
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_48,plain,(
    ! [B_27,A_28] :
      ( r1_tarski(k2_relat_1(B_27),A_28)
      | ~ v5_relat_1(B_27,A_28)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_70,plain,(
    ! [B_32,A_33] :
      ( k3_xboole_0(k2_relat_1(B_32),A_33) = k2_relat_1(B_32)
      | ~ v5_relat_1(B_32,A_33)
      | ~ v1_relat_1(B_32) ) ),
    inference(resolution,[status(thm)],[c_48,c_20])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_97,plain,(
    ! [D_39,A_40,B_41] :
      ( r2_hidden(D_39,A_40)
      | ~ r2_hidden(D_39,k2_relat_1(B_41))
      | ~ v5_relat_1(B_41,A_40)
      | ~ v1_relat_1(B_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_4])).

tff(c_651,plain,(
    ! [B_102,A_103,A_104] :
      ( r2_hidden(k1_funct_1(B_102,A_103),A_104)
      | ~ v5_relat_1(B_102,A_104)
      | ~ r2_hidden(A_103,k1_relat_1(B_102))
      | ~ v1_funct_1(B_102)
      | ~ v1_relat_1(B_102) ) ),
    inference(resolution,[status(thm)],[c_28,c_97])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_670,plain,(
    ! [B_105,A_106,A_107] :
      ( m1_subset_1(k1_funct_1(B_105,A_106),A_107)
      | ~ v5_relat_1(B_105,A_107)
      | ~ r2_hidden(A_106,k1_relat_1(B_105))
      | ~ v1_funct_1(B_105)
      | ~ v1_relat_1(B_105) ) ),
    inference(resolution,[status(thm)],[c_651,c_22])).

tff(c_717,plain,(
    ! [A_107] :
      ( m1_subset_1(k1_funct_1('#skF_5','#skF_4'),A_107)
      | ~ v5_relat_1('#skF_5',A_107)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_32,c_670])).

tff(c_736,plain,(
    ! [A_108] :
      ( m1_subset_1(k1_funct_1('#skF_5','#skF_4'),A_108)
      | ~ v5_relat_1('#skF_5',A_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_717])).

tff(c_30,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_5','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_739,plain,(
    ~ v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_736,c_30])).

tff(c_743,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_739])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:45:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.43  
% 2.68/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.43  %$ v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 2.68/1.43  
% 2.68/1.43  %Foreground sorts:
% 2.68/1.43  
% 2.68/1.43  
% 2.68/1.43  %Background operators:
% 2.68/1.43  
% 2.68/1.43  
% 2.68/1.43  %Foreground operators:
% 2.68/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.68/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.68/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.68/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.68/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.68/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.68/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.68/1.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.68/1.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.68/1.43  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.68/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.68/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.68/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.68/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.68/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.68/1.43  
% 2.68/1.44  tff(f_67, negated_conjecture, ~(![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_1)).
% 2.68/1.44  tff(f_56, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 2.68/1.44  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.68/1.44  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.68/1.44  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.68/1.44  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.68/1.44  tff(c_36, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.68/1.44  tff(c_38, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.68/1.44  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.68/1.44  tff(c_32, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.68/1.44  tff(c_28, plain, (![B_14, A_13]: (r2_hidden(k1_funct_1(B_14, A_13), k2_relat_1(B_14)) | ~r2_hidden(A_13, k1_relat_1(B_14)) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.68/1.44  tff(c_48, plain, (![B_27, A_28]: (r1_tarski(k2_relat_1(B_27), A_28) | ~v5_relat_1(B_27, A_28) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.68/1.44  tff(c_20, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.68/1.44  tff(c_70, plain, (![B_32, A_33]: (k3_xboole_0(k2_relat_1(B_32), A_33)=k2_relat_1(B_32) | ~v5_relat_1(B_32, A_33) | ~v1_relat_1(B_32))), inference(resolution, [status(thm)], [c_48, c_20])).
% 2.68/1.44  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.68/1.44  tff(c_97, plain, (![D_39, A_40, B_41]: (r2_hidden(D_39, A_40) | ~r2_hidden(D_39, k2_relat_1(B_41)) | ~v5_relat_1(B_41, A_40) | ~v1_relat_1(B_41))), inference(superposition, [status(thm), theory('equality')], [c_70, c_4])).
% 2.68/1.44  tff(c_651, plain, (![B_102, A_103, A_104]: (r2_hidden(k1_funct_1(B_102, A_103), A_104) | ~v5_relat_1(B_102, A_104) | ~r2_hidden(A_103, k1_relat_1(B_102)) | ~v1_funct_1(B_102) | ~v1_relat_1(B_102))), inference(resolution, [status(thm)], [c_28, c_97])).
% 2.68/1.44  tff(c_22, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.68/1.44  tff(c_670, plain, (![B_105, A_106, A_107]: (m1_subset_1(k1_funct_1(B_105, A_106), A_107) | ~v5_relat_1(B_105, A_107) | ~r2_hidden(A_106, k1_relat_1(B_105)) | ~v1_funct_1(B_105) | ~v1_relat_1(B_105))), inference(resolution, [status(thm)], [c_651, c_22])).
% 2.68/1.44  tff(c_717, plain, (![A_107]: (m1_subset_1(k1_funct_1('#skF_5', '#skF_4'), A_107) | ~v5_relat_1('#skF_5', A_107) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_32, c_670])).
% 2.68/1.44  tff(c_736, plain, (![A_108]: (m1_subset_1(k1_funct_1('#skF_5', '#skF_4'), A_108) | ~v5_relat_1('#skF_5', A_108))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_717])).
% 2.68/1.44  tff(c_30, plain, (~m1_subset_1(k1_funct_1('#skF_5', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.68/1.44  tff(c_739, plain, (~v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_736, c_30])).
% 2.68/1.44  tff(c_743, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_739])).
% 2.68/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.44  
% 2.68/1.44  Inference rules
% 2.68/1.44  ----------------------
% 2.68/1.44  #Ref     : 0
% 2.68/1.44  #Sup     : 147
% 2.68/1.44  #Fact    : 0
% 2.68/1.44  #Define  : 0
% 2.68/1.44  #Split   : 0
% 2.68/1.44  #Chain   : 0
% 2.68/1.44  #Close   : 0
% 2.68/1.44  
% 2.68/1.44  Ordering : KBO
% 2.68/1.44  
% 2.68/1.44  Simplification rules
% 2.68/1.44  ----------------------
% 2.68/1.44  #Subsume      : 19
% 2.68/1.44  #Demod        : 21
% 2.68/1.44  #Tautology    : 28
% 2.68/1.44  #SimpNegUnit  : 0
% 2.68/1.44  #BackRed      : 0
% 2.68/1.44  
% 2.68/1.44  #Partial instantiations: 0
% 2.68/1.44  #Strategies tried      : 1
% 2.68/1.44  
% 2.68/1.44  Timing (in seconds)
% 2.68/1.44  ----------------------
% 2.68/1.45  Preprocessing        : 0.29
% 2.68/1.45  Parsing              : 0.15
% 2.68/1.45  CNF conversion       : 0.02
% 2.68/1.45  Main loop            : 0.40
% 2.68/1.45  Inferencing          : 0.17
% 2.68/1.45  Reduction            : 0.08
% 2.68/1.45  Demodulation         : 0.06
% 2.68/1.45  BG Simplification    : 0.03
% 2.68/1.45  Subsumption          : 0.10
% 2.68/1.45  Abstraction          : 0.02
% 2.68/1.45  MUC search           : 0.00
% 2.68/1.45  Cooper               : 0.00
% 2.68/1.45  Total                : 0.71
% 2.68/1.45  Index Insertion      : 0.00
% 2.68/1.45  Index Deletion       : 0.00
% 2.68/1.45  Index Matching       : 0.00
% 2.68/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
