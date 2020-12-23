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
% DateTime   : Thu Dec  3 10:05:53 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   41 (  73 expanded)
%              Number of leaves         :   24 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   60 ( 158 expanded)
%              Number of equality atoms :    7 (  17 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v5_relat_1(C,A)
          & v1_funct_1(C) )
       => ( r2_hidden(B,k1_relat_1(C))
         => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_72,axiom,(
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

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_46,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_6','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_48,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_54,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_52,plain,(
    v5_relat_1('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_68,plain,(
    ! [A_37,B_38] :
      ( k8_relat_1(A_37,B_38) = B_38
      | ~ r1_tarski(k2_relat_1(B_38),A_37)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_73,plain,(
    ! [A_39,B_40] :
      ( k8_relat_1(A_39,B_40) = B_40
      | ~ v5_relat_1(B_40,A_39)
      | ~ v1_relat_1(B_40) ) ),
    inference(resolution,[status(thm)],[c_6,c_68])).

tff(c_76,plain,
    ( k8_relat_1('#skF_4','#skF_6') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_73])).

tff(c_79,plain,(
    k8_relat_1('#skF_4','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_76])).

tff(c_50,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_100,plain,(
    ! [C_44,D_45,A_46] :
      ( r2_hidden(k1_funct_1(C_44,D_45),A_46)
      | ~ r2_hidden(D_45,k1_relat_1(k8_relat_1(A_46,C_44)))
      | ~ v1_funct_1(C_44)
      | ~ v1_relat_1(C_44)
      | ~ v1_funct_1(k8_relat_1(A_46,C_44))
      | ~ v1_relat_1(k8_relat_1(A_46,C_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_103,plain,(
    ! [D_45] :
      ( r2_hidden(k1_funct_1('#skF_6',D_45),'#skF_4')
      | ~ r2_hidden(D_45,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ v1_funct_1(k8_relat_1('#skF_4','#skF_6'))
      | ~ v1_relat_1(k8_relat_1('#skF_4','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_100])).

tff(c_106,plain,(
    ! [D_47] :
      ( r2_hidden(k1_funct_1('#skF_6',D_47),'#skF_4')
      | ~ r2_hidden(D_47,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_79,c_50,c_79,c_54,c_50,c_103])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_111,plain,(
    ! [D_48] :
      ( m1_subset_1(k1_funct_1('#skF_6',D_48),'#skF_4')
      | ~ r2_hidden(D_48,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_106,c_2])).

tff(c_114,plain,(
    m1_subset_1(k1_funct_1('#skF_6','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_111])).

tff(c_118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_114])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:26:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.20  
% 2.02/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.20  %$ v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.02/1.20  
% 2.02/1.20  %Foreground sorts:
% 2.02/1.20  
% 2.02/1.20  
% 2.02/1.20  %Background operators:
% 2.02/1.20  
% 2.02/1.20  
% 2.02/1.20  %Foreground operators:
% 2.02/1.20  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.02/1.20  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.02/1.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.02/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.02/1.20  tff('#skF_5', type, '#skF_5': $i).
% 2.02/1.20  tff('#skF_6', type, '#skF_6': $i).
% 2.02/1.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.02/1.20  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.02/1.20  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.02/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.02/1.20  tff('#skF_4', type, '#skF_4': $i).
% 2.02/1.20  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.02/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.02/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.02/1.20  
% 2.02/1.21  tff(f_83, negated_conjecture, ~(![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_1)).
% 2.02/1.21  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.02/1.21  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 2.02/1.21  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((B = k8_relat_1(A, C)) <=> ((![D]: (r2_hidden(D, k1_relat_1(B)) <=> (r2_hidden(D, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, D), A)))) & (![D]: (r2_hidden(D, k1_relat_1(B)) => (k1_funct_1(B, D) = k1_funct_1(C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_funct_1)).
% 2.02/1.21  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.02/1.21  tff(c_46, plain, (~m1_subset_1(k1_funct_1('#skF_6', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.02/1.21  tff(c_48, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.02/1.21  tff(c_54, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.02/1.21  tff(c_52, plain, (v5_relat_1('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.02/1.21  tff(c_6, plain, (![B_4, A_3]: (r1_tarski(k2_relat_1(B_4), A_3) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.02/1.21  tff(c_68, plain, (![A_37, B_38]: (k8_relat_1(A_37, B_38)=B_38 | ~r1_tarski(k2_relat_1(B_38), A_37) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.02/1.21  tff(c_73, plain, (![A_39, B_40]: (k8_relat_1(A_39, B_40)=B_40 | ~v5_relat_1(B_40, A_39) | ~v1_relat_1(B_40))), inference(resolution, [status(thm)], [c_6, c_68])).
% 2.02/1.21  tff(c_76, plain, (k8_relat_1('#skF_4', '#skF_6')='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_73])).
% 2.02/1.21  tff(c_79, plain, (k8_relat_1('#skF_4', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_76])).
% 2.02/1.21  tff(c_50, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.02/1.21  tff(c_100, plain, (![C_44, D_45, A_46]: (r2_hidden(k1_funct_1(C_44, D_45), A_46) | ~r2_hidden(D_45, k1_relat_1(k8_relat_1(A_46, C_44))) | ~v1_funct_1(C_44) | ~v1_relat_1(C_44) | ~v1_funct_1(k8_relat_1(A_46, C_44)) | ~v1_relat_1(k8_relat_1(A_46, C_44)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.02/1.21  tff(c_103, plain, (![D_45]: (r2_hidden(k1_funct_1('#skF_6', D_45), '#skF_4') | ~r2_hidden(D_45, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1(k8_relat_1('#skF_4', '#skF_6')) | ~v1_relat_1(k8_relat_1('#skF_4', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_79, c_100])).
% 2.02/1.21  tff(c_106, plain, (![D_47]: (r2_hidden(k1_funct_1('#skF_6', D_47), '#skF_4') | ~r2_hidden(D_47, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_79, c_50, c_79, c_54, c_50, c_103])).
% 2.02/1.21  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.02/1.21  tff(c_111, plain, (![D_48]: (m1_subset_1(k1_funct_1('#skF_6', D_48), '#skF_4') | ~r2_hidden(D_48, k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_106, c_2])).
% 2.02/1.21  tff(c_114, plain, (m1_subset_1(k1_funct_1('#skF_6', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_48, c_111])).
% 2.02/1.21  tff(c_118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_114])).
% 2.02/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.21  
% 2.02/1.21  Inference rules
% 2.02/1.21  ----------------------
% 2.02/1.21  #Ref     : 0
% 2.02/1.21  #Sup     : 12
% 2.02/1.21  #Fact    : 0
% 2.02/1.21  #Define  : 0
% 2.02/1.21  #Split   : 0
% 2.02/1.21  #Chain   : 0
% 2.02/1.21  #Close   : 0
% 2.02/1.21  
% 2.02/1.21  Ordering : KBO
% 2.02/1.21  
% 2.02/1.21  Simplification rules
% 2.02/1.21  ----------------------
% 2.02/1.21  #Subsume      : 0
% 2.02/1.21  #Demod        : 19
% 2.02/1.21  #Tautology    : 6
% 2.02/1.21  #SimpNegUnit  : 1
% 2.02/1.21  #BackRed      : 0
% 2.02/1.21  
% 2.02/1.21  #Partial instantiations: 0
% 2.02/1.21  #Strategies tried      : 1
% 2.02/1.21  
% 2.02/1.21  Timing (in seconds)
% 2.02/1.21  ----------------------
% 2.02/1.21  Preprocessing        : 0.31
% 2.02/1.21  Parsing              : 0.16
% 2.02/1.21  CNF conversion       : 0.02
% 2.02/1.21  Main loop            : 0.15
% 2.02/1.21  Inferencing          : 0.04
% 2.02/1.21  Reduction            : 0.04
% 2.02/1.21  Demodulation         : 0.03
% 2.02/1.22  BG Simplification    : 0.02
% 2.02/1.22  Subsumption          : 0.04
% 2.02/1.22  Abstraction          : 0.01
% 2.02/1.22  MUC search           : 0.00
% 2.02/1.22  Cooper               : 0.00
% 2.02/1.22  Total                : 0.48
% 2.02/1.22  Index Insertion      : 0.00
% 2.02/1.22  Index Deletion       : 0.00
% 2.02/1.22  Index Matching       : 0.00
% 2.02/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
