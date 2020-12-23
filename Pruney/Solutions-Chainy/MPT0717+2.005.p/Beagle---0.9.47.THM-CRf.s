%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:41 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   37 (  69 expanded)
%              Number of leaves         :   22 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 ( 152 expanded)
%              Number of equality atoms :    7 (  17 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k8_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v5_relat_1(B,A)
          & v1_funct_1(B) )
       => ! [C] :
            ( r2_hidden(C,k1_relat_1(B))
           => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( B = k8_relat_1(A,C)
          <=> ( ! [D] :
                  ( r2_hidden(D,k1_relat_1(B))
                <=> ( r2_hidden(D,k1_relat_1(C))
                    & r2_hidden(k1_funct_1(C,D),A) ) )
              & ! [D] :
                  ( r2_hidden(D,k1_relat_1(B))
                 => k1_funct_1(B,D) = k1_funct_1(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_1)).

tff(c_46,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_52,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_50,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_61,plain,(
    ! [A_34,B_35] :
      ( k8_relat_1(A_34,B_35) = B_35
      | ~ r1_tarski(k2_relat_1(B_35),A_34)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_66,plain,(
    ! [A_36,B_37] :
      ( k8_relat_1(A_36,B_37) = B_37
      | ~ v5_relat_1(B_37,A_36)
      | ~ v1_relat_1(B_37) ) ),
    inference(resolution,[status(thm)],[c_4,c_61])).

tff(c_69,plain,
    ( k8_relat_1('#skF_4','#skF_5') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_66])).

tff(c_72,plain,(
    k8_relat_1('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_69])).

tff(c_48,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_93,plain,(
    ! [C_41,D_42,A_43] :
      ( r2_hidden(k1_funct_1(C_41,D_42),A_43)
      | ~ r2_hidden(D_42,k1_relat_1(k8_relat_1(A_43,C_41)))
      | ~ v1_funct_1(C_41)
      | ~ v1_relat_1(C_41)
      | ~ v1_funct_1(k8_relat_1(A_43,C_41))
      | ~ v1_relat_1(k8_relat_1(A_43,C_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_96,plain,(
    ! [D_42] :
      ( r2_hidden(k1_funct_1('#skF_5',D_42),'#skF_4')
      | ~ r2_hidden(D_42,k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_funct_1(k8_relat_1('#skF_4','#skF_5'))
      | ~ v1_relat_1(k8_relat_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_93])).

tff(c_99,plain,(
    ! [D_44] :
      ( r2_hidden(k1_funct_1('#skF_5',D_44),'#skF_4')
      | ~ r2_hidden(D_44,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_72,c_48,c_72,c_52,c_48,c_96])).

tff(c_44,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_6'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_102,plain,(
    ~ r2_hidden('#skF_6',k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_99,c_44])).

tff(c_106,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_102])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:15:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.27  
% 2.18/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.27  %$ v5_relat_1 > r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k8_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.18/1.27  
% 2.18/1.27  %Foreground sorts:
% 2.18/1.27  
% 2.18/1.27  
% 2.18/1.27  %Background operators:
% 2.18/1.27  
% 2.18/1.27  
% 2.18/1.27  %Foreground operators:
% 2.18/1.27  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.18/1.27  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.18/1.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.18/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.18/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.18/1.27  tff('#skF_6', type, '#skF_6': $i).
% 2.18/1.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.18/1.27  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.18/1.27  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.18/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.18/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.18/1.27  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.18/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.18/1.27  
% 2.18/1.28  tff(f_80, negated_conjecture, ~(![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 2.18/1.28  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.18/1.28  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 2.18/1.28  tff(f_68, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((B = k8_relat_1(A, C)) <=> ((![D]: (r2_hidden(D, k1_relat_1(B)) <=> (r2_hidden(D, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, D), A)))) & (![D]: (r2_hidden(D, k1_relat_1(B)) => (k1_funct_1(B, D) = k1_funct_1(C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_funct_1)).
% 2.18/1.28  tff(c_46, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.18/1.28  tff(c_52, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.18/1.28  tff(c_50, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.18/1.28  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.18/1.28  tff(c_61, plain, (![A_34, B_35]: (k8_relat_1(A_34, B_35)=B_35 | ~r1_tarski(k2_relat_1(B_35), A_34) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.18/1.28  tff(c_66, plain, (![A_36, B_37]: (k8_relat_1(A_36, B_37)=B_37 | ~v5_relat_1(B_37, A_36) | ~v1_relat_1(B_37))), inference(resolution, [status(thm)], [c_4, c_61])).
% 2.18/1.28  tff(c_69, plain, (k8_relat_1('#skF_4', '#skF_5')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_66])).
% 2.18/1.28  tff(c_72, plain, (k8_relat_1('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_69])).
% 2.18/1.28  tff(c_48, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.18/1.28  tff(c_93, plain, (![C_41, D_42, A_43]: (r2_hidden(k1_funct_1(C_41, D_42), A_43) | ~r2_hidden(D_42, k1_relat_1(k8_relat_1(A_43, C_41))) | ~v1_funct_1(C_41) | ~v1_relat_1(C_41) | ~v1_funct_1(k8_relat_1(A_43, C_41)) | ~v1_relat_1(k8_relat_1(A_43, C_41)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.18/1.28  tff(c_96, plain, (![D_42]: (r2_hidden(k1_funct_1('#skF_5', D_42), '#skF_4') | ~r2_hidden(D_42, k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1(k8_relat_1('#skF_4', '#skF_5')) | ~v1_relat_1(k8_relat_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_72, c_93])).
% 2.18/1.28  tff(c_99, plain, (![D_44]: (r2_hidden(k1_funct_1('#skF_5', D_44), '#skF_4') | ~r2_hidden(D_44, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_72, c_48, c_72, c_52, c_48, c_96])).
% 2.18/1.28  tff(c_44, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_6'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.18/1.28  tff(c_102, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_99, c_44])).
% 2.18/1.28  tff(c_106, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_102])).
% 2.18/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.28  
% 2.18/1.28  Inference rules
% 2.18/1.28  ----------------------
% 2.18/1.28  #Ref     : 0
% 2.18/1.28  #Sup     : 10
% 2.18/1.28  #Fact    : 0
% 2.18/1.28  #Define  : 0
% 2.18/1.28  #Split   : 0
% 2.18/1.28  #Chain   : 0
% 2.18/1.28  #Close   : 0
% 2.18/1.28  
% 2.18/1.28  Ordering : KBO
% 2.18/1.28  
% 2.18/1.28  Simplification rules
% 2.18/1.28  ----------------------
% 2.18/1.28  #Subsume      : 0
% 2.18/1.28  #Demod        : 20
% 2.18/1.28  #Tautology    : 6
% 2.18/1.28  #SimpNegUnit  : 0
% 2.18/1.28  #BackRed      : 0
% 2.18/1.28  
% 2.18/1.28  #Partial instantiations: 0
% 2.18/1.28  #Strategies tried      : 1
% 2.18/1.28  
% 2.18/1.28  Timing (in seconds)
% 2.18/1.28  ----------------------
% 2.18/1.28  Preprocessing        : 0.33
% 2.18/1.28  Parsing              : 0.17
% 2.18/1.28  CNF conversion       : 0.03
% 2.18/1.28  Main loop            : 0.14
% 2.18/1.28  Inferencing          : 0.04
% 2.18/1.28  Reduction            : 0.04
% 2.18/1.28  Demodulation         : 0.03
% 2.18/1.28  BG Simplification    : 0.02
% 2.18/1.28  Subsumption          : 0.04
% 2.18/1.28  Abstraction          : 0.01
% 2.18/1.28  MUC search           : 0.00
% 2.18/1.28  Cooper               : 0.00
% 2.18/1.28  Total                : 0.49
% 2.18/1.28  Index Insertion      : 0.00
% 2.18/1.28  Index Deletion       : 0.00
% 2.18/1.28  Index Matching       : 0.00
% 2.18/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
