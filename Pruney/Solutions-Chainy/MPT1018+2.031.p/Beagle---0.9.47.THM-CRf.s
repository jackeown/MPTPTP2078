%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:49 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   33 (  40 expanded)
%              Number of leaves         :   19 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   52 ( 108 expanded)
%              Number of equality atoms :   14 (  28 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
         => ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v2_funct_1(B)
      <=> ! [C,D] :
            ( ( r2_hidden(C,A)
              & r2_hidden(D,A)
              & k1_funct_1(B,C) = k1_funct_1(B,D) )
           => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).

tff(c_12,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_24,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_26,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_20,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14,plain,(
    k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_62,plain,(
    ! [D_19,C_20,B_21,A_22] :
      ( D_19 = C_20
      | k1_funct_1(B_21,D_19) != k1_funct_1(B_21,C_20)
      | ~ r2_hidden(D_19,A_22)
      | ~ r2_hidden(C_20,A_22)
      | ~ v2_funct_1(B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_22,A_22)))
      | ~ v1_funct_2(B_21,A_22,A_22)
      | ~ v1_funct_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_64,plain,(
    ! [C_20,A_22] :
      ( C_20 = '#skF_5'
      | k1_funct_1('#skF_4',C_20) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden('#skF_5',A_22)
      | ~ r2_hidden(C_20,A_22)
      | ~ v2_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_22,A_22)))
      | ~ v1_funct_2('#skF_4',A_22,A_22)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_62])).

tff(c_71,plain,(
    ! [C_23,A_24] :
      ( C_23 = '#skF_5'
      | k1_funct_1('#skF_4',C_23) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden('#skF_5',A_24)
      | ~ r2_hidden(C_23,A_24)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_24,A_24)))
      | ~ v1_funct_2('#skF_4',A_24,A_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_20,c_64])).

tff(c_73,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r2_hidden('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_71])).

tff(c_78,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_18,c_73])).

tff(c_80,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_78])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:32:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.16  
% 1.71/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.16  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.80/1.16  
% 1.80/1.16  %Foreground sorts:
% 1.80/1.16  
% 1.80/1.16  
% 1.80/1.16  %Background operators:
% 1.80/1.16  
% 1.80/1.16  
% 1.80/1.16  %Foreground operators:
% 1.80/1.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.80/1.16  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.80/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.80/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.80/1.16  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.80/1.16  tff('#skF_6', type, '#skF_6': $i).
% 1.80/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.80/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.80/1.16  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.80/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.80/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.80/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.80/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.80/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.80/1.16  
% 1.80/1.17  tff(f_60, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) => (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_funct_2)).
% 1.80/1.17  tff(f_42, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) <=> (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_funct_2)).
% 1.80/1.17  tff(c_12, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.80/1.17  tff(c_24, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.80/1.17  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.80/1.17  tff(c_18, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.80/1.17  tff(c_16, plain, (r2_hidden('#skF_6', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.80/1.17  tff(c_26, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.80/1.17  tff(c_20, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.80/1.17  tff(c_14, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.80/1.17  tff(c_62, plain, (![D_19, C_20, B_21, A_22]: (D_19=C_20 | k1_funct_1(B_21, D_19)!=k1_funct_1(B_21, C_20) | ~r2_hidden(D_19, A_22) | ~r2_hidden(C_20, A_22) | ~v2_funct_1(B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))) | ~v1_funct_2(B_21, A_22, A_22) | ~v1_funct_1(B_21))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.80/1.17  tff(c_64, plain, (![C_20, A_22]: (C_20='#skF_5' | k1_funct_1('#skF_4', C_20)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden('#skF_5', A_22) | ~r2_hidden(C_20, A_22) | ~v2_funct_1('#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))) | ~v1_funct_2('#skF_4', A_22, A_22) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_62])).
% 1.80/1.17  tff(c_71, plain, (![C_23, A_24]: (C_23='#skF_5' | k1_funct_1('#skF_4', C_23)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden('#skF_5', A_24) | ~r2_hidden(C_23, A_24) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))) | ~v1_funct_2('#skF_4', A_24, A_24))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_20, c_64])).
% 1.80/1.17  tff(c_73, plain, ('#skF_5'='#skF_6' | ~r2_hidden('#skF_5', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_16, c_71])).
% 1.80/1.17  tff(c_78, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_18, c_73])).
% 1.80/1.17  tff(c_80, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_78])).
% 1.80/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.17  
% 1.80/1.17  Inference rules
% 1.80/1.17  ----------------------
% 1.80/1.17  #Ref     : 1
% 1.80/1.17  #Sup     : 10
% 1.80/1.17  #Fact    : 0
% 1.80/1.17  #Define  : 0
% 1.80/1.17  #Split   : 0
% 1.80/1.17  #Chain   : 0
% 1.80/1.17  #Close   : 0
% 1.80/1.17  
% 1.80/1.17  Ordering : KBO
% 1.80/1.17  
% 1.80/1.17  Simplification rules
% 1.80/1.17  ----------------------
% 1.80/1.17  #Subsume      : 0
% 1.80/1.17  #Demod        : 19
% 1.80/1.17  #Tautology    : 7
% 1.80/1.17  #SimpNegUnit  : 1
% 1.80/1.17  #BackRed      : 0
% 1.80/1.17  
% 1.80/1.17  #Partial instantiations: 0
% 1.80/1.17  #Strategies tried      : 1
% 1.80/1.17  
% 1.80/1.17  Timing (in seconds)
% 1.80/1.17  ----------------------
% 1.80/1.17  Preprocessing        : 0.26
% 1.80/1.17  Parsing              : 0.14
% 1.80/1.17  CNF conversion       : 0.02
% 1.80/1.17  Main loop            : 0.10
% 1.80/1.17  Inferencing          : 0.04
% 1.80/1.17  Reduction            : 0.03
% 1.80/1.17  Demodulation         : 0.02
% 1.80/1.17  BG Simplification    : 0.01
% 1.80/1.17  Subsumption          : 0.01
% 1.80/1.18  Abstraction          : 0.01
% 1.80/1.18  MUC search           : 0.00
% 1.80/1.18  Cooper               : 0.00
% 1.80/1.18  Total                : 0.39
% 1.80/1.18  Index Insertion      : 0.00
% 1.80/1.18  Index Deletion       : 0.00
% 1.80/1.18  Index Matching       : 0.00
% 1.80/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
