%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:29 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   48 (  63 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   66 ( 129 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > v5_ordinal1 > v3_ordinal1 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v3_ordinal1(k1_relat_1(A))
         => ( v1_relat_1(A)
            & v5_relat_1(A,k2_relat_1(A))
            & v1_funct_1(A)
            & v5_ordinal1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_ordinal1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v5_ordinal1(A)
    <=> v3_ordinal1(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_ordinal1)).

tff(c_38,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_12,plain,(
    ! [A_5] : v4_relat_1(k6_relat_1(A_5),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_6] : v1_relat_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    ! [A_6] : v1_funct_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ! [A_7] :
      ( k1_relat_1(k6_relat_1(A_7)) = A_7
      | ~ v1_funct_1(k6_relat_1(A_7))
      | ~ v1_relat_1(k6_relat_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_42,plain,(
    ! [A_7] :
      ( k1_relat_1(k6_relat_1(A_7)) = A_7
      | ~ v1_relat_1(k6_relat_1(A_7)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_26])).

tff(c_46,plain,(
    ! [A_7] : k1_relat_1(k6_relat_1(A_7)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_42])).

tff(c_96,plain,(
    ! [B_26,A_27] :
      ( r1_tarski(k1_relat_1(B_26),A_27)
      | ~ v4_relat_1(B_26,A_27)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_99,plain,(
    ! [A_7,A_27] :
      ( r1_tarski(A_7,A_27)
      | ~ v4_relat_1(k6_relat_1(A_7),A_27)
      | ~ v1_relat_1(k6_relat_1(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_96])).

tff(c_102,plain,(
    ! [A_28,A_29] :
      ( r1_tarski(A_28,A_29)
      | ~ v4_relat_1(k6_relat_1(A_28),A_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_99])).

tff(c_112,plain,(
    ! [A_32] : r1_tarski(A_32,A_32) ),
    inference(resolution,[status(thm)],[c_12,c_102])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( v5_relat_1(B_4,A_3)
      | ~ r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_118,plain,(
    ! [B_33] :
      ( v5_relat_1(B_33,k2_relat_1(B_33))
      | ~ v1_relat_1(B_33) ) ),
    inference(resolution,[status(thm)],[c_112,c_6])).

tff(c_36,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_32,plain,
    ( ~ v5_ordinal1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v5_relat_1('#skF_2',k2_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_40,plain,
    ( ~ v5_ordinal1('#skF_2')
    | ~ v5_relat_1('#skF_2',k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_32])).

tff(c_67,plain,(
    ~ v5_relat_1('#skF_2',k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_121,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_118,c_67])).

tff(c_125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_121])).

tff(c_126,plain,(
    ~ v5_ordinal1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_34,plain,(
    v3_ordinal1(k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_128,plain,(
    ! [A_34] :
      ( v5_ordinal1(A_34)
      | ~ v3_ordinal1(k1_relat_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_137,plain,(
    v5_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_128])).

tff(c_142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_137])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:05:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.71  
% 2.49/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.72  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > v5_ordinal1 > v3_ordinal1 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.49/1.72  
% 2.49/1.72  %Foreground sorts:
% 2.49/1.72  
% 2.49/1.72  
% 2.49/1.72  %Background operators:
% 2.49/1.72  
% 2.49/1.72  
% 2.49/1.72  %Foreground operators:
% 2.49/1.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.49/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.49/1.72  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 2.49/1.72  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.72  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.49/1.72  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.49/1.72  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.49/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.49/1.72  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.49/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.72  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.49/1.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.49/1.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.49/1.72  
% 2.49/1.76  tff(f_79, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v3_ordinal1(k1_relat_1(A)) => (((v1_relat_1(A) & v5_relat_1(A, k2_relat_1(A))) & v1_funct_1(A)) & v5_ordinal1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_ordinal1)).
% 2.49/1.76  tff(f_43, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc24_relat_1)).
% 2.49/1.76  tff(f_47, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.49/1.76  tff(f_60, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 2.49/1.76  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.49/1.76  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.49/1.76  tff(f_64, axiom, (![A]: (v5_ordinal1(A) <=> v3_ordinal1(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_ordinal1)).
% 2.49/1.76  tff(c_38, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.49/1.76  tff(c_12, plain, (![A_5]: (v4_relat_1(k6_relat_1(A_5), A_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.49/1.76  tff(c_16, plain, (![A_6]: (v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.49/1.76  tff(c_18, plain, (![A_6]: (v1_funct_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.49/1.76  tff(c_26, plain, (![A_7]: (k1_relat_1(k6_relat_1(A_7))=A_7 | ~v1_funct_1(k6_relat_1(A_7)) | ~v1_relat_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.49/1.76  tff(c_42, plain, (![A_7]: (k1_relat_1(k6_relat_1(A_7))=A_7 | ~v1_relat_1(k6_relat_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_26])).
% 2.49/1.76  tff(c_46, plain, (![A_7]: (k1_relat_1(k6_relat_1(A_7))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_42])).
% 2.49/1.76  tff(c_96, plain, (![B_26, A_27]: (r1_tarski(k1_relat_1(B_26), A_27) | ~v4_relat_1(B_26, A_27) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.49/1.76  tff(c_99, plain, (![A_7, A_27]: (r1_tarski(A_7, A_27) | ~v4_relat_1(k6_relat_1(A_7), A_27) | ~v1_relat_1(k6_relat_1(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_96])).
% 2.49/1.76  tff(c_102, plain, (![A_28, A_29]: (r1_tarski(A_28, A_29) | ~v4_relat_1(k6_relat_1(A_28), A_29))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_99])).
% 2.49/1.76  tff(c_112, plain, (![A_32]: (r1_tarski(A_32, A_32))), inference(resolution, [status(thm)], [c_12, c_102])).
% 2.49/1.76  tff(c_6, plain, (![B_4, A_3]: (v5_relat_1(B_4, A_3) | ~r1_tarski(k2_relat_1(B_4), A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.49/1.76  tff(c_118, plain, (![B_33]: (v5_relat_1(B_33, k2_relat_1(B_33)) | ~v1_relat_1(B_33))), inference(resolution, [status(thm)], [c_112, c_6])).
% 2.49/1.76  tff(c_36, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.49/1.76  tff(c_32, plain, (~v5_ordinal1('#skF_2') | ~v1_funct_1('#skF_2') | ~v5_relat_1('#skF_2', k2_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.49/1.76  tff(c_40, plain, (~v5_ordinal1('#skF_2') | ~v5_relat_1('#skF_2', k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_32])).
% 2.49/1.76  tff(c_67, plain, (~v5_relat_1('#skF_2', k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_40])).
% 2.49/1.76  tff(c_121, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_118, c_67])).
% 2.49/1.76  tff(c_125, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_121])).
% 2.49/1.76  tff(c_126, plain, (~v5_ordinal1('#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 2.49/1.76  tff(c_34, plain, (v3_ordinal1(k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.49/1.76  tff(c_128, plain, (![A_34]: (v5_ordinal1(A_34) | ~v3_ordinal1(k1_relat_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.49/1.76  tff(c_137, plain, (v5_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_34, c_128])).
% 2.49/1.76  tff(c_142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126, c_137])).
% 2.49/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.76  
% 2.49/1.76  Inference rules
% 2.49/1.76  ----------------------
% 2.49/1.76  #Ref     : 0
% 2.49/1.76  #Sup     : 17
% 2.49/1.76  #Fact    : 0
% 2.49/1.76  #Define  : 0
% 2.49/1.76  #Split   : 1
% 2.49/1.76  #Chain   : 0
% 2.49/1.76  #Close   : 0
% 2.49/1.76  
% 2.49/1.76  Ordering : KBO
% 2.49/1.76  
% 2.49/1.76  Simplification rules
% 2.49/1.76  ----------------------
% 2.49/1.76  #Subsume      : 0
% 2.49/1.76  #Demod        : 9
% 2.49/1.76  #Tautology    : 9
% 2.49/1.76  #SimpNegUnit  : 1
% 2.49/1.76  #BackRed      : 0
% 2.49/1.76  
% 2.49/1.76  #Partial instantiations: 0
% 2.49/1.76  #Strategies tried      : 1
% 2.49/1.76  
% 2.49/1.76  Timing (in seconds)
% 2.49/1.76  ----------------------
% 2.49/1.76  Preprocessing        : 0.54
% 2.49/1.76  Parsing              : 0.28
% 2.49/1.76  CNF conversion       : 0.03
% 2.49/1.76  Main loop            : 0.25
% 2.49/1.76  Inferencing          : 0.09
% 2.49/1.76  Reduction            : 0.07
% 2.49/1.76  Demodulation         : 0.05
% 2.49/1.76  BG Simplification    : 0.03
% 2.49/1.76  Subsumption          : 0.04
% 2.49/1.76  Abstraction          : 0.01
% 2.49/1.76  MUC search           : 0.00
% 2.49/1.76  Cooper               : 0.00
% 2.49/1.76  Total                : 0.86
% 2.49/1.76  Index Insertion      : 0.00
% 2.49/1.76  Index Deletion       : 0.00
% 2.49/1.76  Index Matching       : 0.00
% 2.49/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
