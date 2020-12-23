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
% DateTime   : Thu Dec  3 10:18:06 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   35 (  48 expanded)
%              Number of leaves         :   19 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 ( 106 expanded)
%              Number of equality atoms :    7 (  16 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
          & ! [E] :
              ~ ( r2_hidden(E,A)
                & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_10,plain,(
    r2_hidden('#skF_2',k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_23,plain,(
    ! [A_13,B_14,C_15,D_16] :
      ( r2_hidden('#skF_1'(A_13,B_14,C_15,D_16),A_13)
      | ~ r2_hidden(C_15,k2_relset_1(A_13,B_14,D_16))
      | ~ m1_subset_1(D_16,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_2(D_16,A_13,B_14)
      | ~ v1_funct_1(D_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_25,plain,(
    ! [C_15] :
      ( r2_hidden('#skF_1'('#skF_3','#skF_4',C_15,'#skF_5'),'#skF_3')
      | ~ r2_hidden(C_15,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_12,c_23])).

tff(c_29,plain,(
    ! [C_17] :
      ( r2_hidden('#skF_1'('#skF_3','#skF_4',C_17,'#skF_5'),'#skF_3')
      | ~ r2_hidden(C_17,k2_relset_1('#skF_3','#skF_4','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_25])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_34,plain,(
    ! [C_18] :
      ( m1_subset_1('#skF_1'('#skF_3','#skF_4',C_18,'#skF_5'),'#skF_3')
      | ~ r2_hidden(C_18,k2_relset_1('#skF_3','#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_29,c_2])).

tff(c_38,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_2','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_34])).

tff(c_8,plain,(
    ! [E_9] :
      ( k1_funct_1('#skF_5',E_9) != '#skF_2'
      | ~ m1_subset_1(E_9,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_42,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_4','#skF_2','#skF_5')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_8])).

tff(c_43,plain,(
    ! [D_19,A_20,B_21,C_22] :
      ( k1_funct_1(D_19,'#skF_1'(A_20,B_21,C_22,D_19)) = C_22
      | ~ r2_hidden(C_22,k2_relset_1(A_20,B_21,D_19))
      | ~ m1_subset_1(D_19,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21)))
      | ~ v1_funct_2(D_19,A_20,B_21)
      | ~ v1_funct_1(D_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_45,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_4','#skF_2','#skF_5')) = '#skF_2'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_43])).

tff(c_48,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_4','#skF_2','#skF_5')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_12,c_45])).

tff(c_50,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:12:55 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.13  
% 1.63/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.13  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.63/1.13  
% 1.63/1.13  %Foreground sorts:
% 1.63/1.13  
% 1.63/1.13  
% 1.63/1.13  %Background operators:
% 1.63/1.13  
% 1.63/1.13  
% 1.63/1.13  %Foreground operators:
% 1.63/1.13  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 1.63/1.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.63/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.63/1.13  tff('#skF_5', type, '#skF_5': $i).
% 1.63/1.13  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.63/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.63/1.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.63/1.13  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.63/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.63/1.13  tff('#skF_4', type, '#skF_4': $i).
% 1.63/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.13  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 1.63/1.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.76/1.13  
% 1.76/1.14  tff(f_60, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 1.76/1.14  tff(f_44, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_funct_2)).
% 1.76/1.14  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 1.76/1.14  tff(c_10, plain, (r2_hidden('#skF_2', k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.76/1.14  tff(c_16, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.76/1.14  tff(c_14, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.76/1.14  tff(c_12, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.76/1.14  tff(c_23, plain, (![A_13, B_14, C_15, D_16]: (r2_hidden('#skF_1'(A_13, B_14, C_15, D_16), A_13) | ~r2_hidden(C_15, k2_relset_1(A_13, B_14, D_16)) | ~m1_subset_1(D_16, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_2(D_16, A_13, B_14) | ~v1_funct_1(D_16))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.76/1.14  tff(c_25, plain, (![C_15]: (r2_hidden('#skF_1'('#skF_3', '#skF_4', C_15, '#skF_5'), '#skF_3') | ~r2_hidden(C_15, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_12, c_23])).
% 1.76/1.14  tff(c_29, plain, (![C_17]: (r2_hidden('#skF_1'('#skF_3', '#skF_4', C_17, '#skF_5'), '#skF_3') | ~r2_hidden(C_17, k2_relset_1('#skF_3', '#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_25])).
% 1.76/1.14  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.76/1.14  tff(c_34, plain, (![C_18]: (m1_subset_1('#skF_1'('#skF_3', '#skF_4', C_18, '#skF_5'), '#skF_3') | ~r2_hidden(C_18, k2_relset_1('#skF_3', '#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_29, c_2])).
% 1.76/1.14  tff(c_38, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_4', '#skF_2', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_10, c_34])).
% 1.76/1.14  tff(c_8, plain, (![E_9]: (k1_funct_1('#skF_5', E_9)!='#skF_2' | ~m1_subset_1(E_9, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.76/1.14  tff(c_42, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_2', '#skF_5'))!='#skF_2'), inference(resolution, [status(thm)], [c_38, c_8])).
% 1.76/1.14  tff(c_43, plain, (![D_19, A_20, B_21, C_22]: (k1_funct_1(D_19, '#skF_1'(A_20, B_21, C_22, D_19))=C_22 | ~r2_hidden(C_22, k2_relset_1(A_20, B_21, D_19)) | ~m1_subset_1(D_19, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))) | ~v1_funct_2(D_19, A_20, B_21) | ~v1_funct_1(D_19))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.76/1.14  tff(c_45, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_2', '#skF_5'))='#skF_2' | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_10, c_43])).
% 1.76/1.14  tff(c_48, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_2', '#skF_5'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_12, c_45])).
% 1.76/1.14  tff(c_50, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_48])).
% 1.76/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.14  
% 1.76/1.14  Inference rules
% 1.76/1.14  ----------------------
% 1.76/1.14  #Ref     : 0
% 1.76/1.14  #Sup     : 6
% 1.76/1.14  #Fact    : 0
% 1.76/1.14  #Define  : 0
% 1.76/1.14  #Split   : 0
% 1.76/1.14  #Chain   : 0
% 1.76/1.14  #Close   : 0
% 1.76/1.14  
% 1.76/1.14  Ordering : KBO
% 1.76/1.14  
% 1.76/1.14  Simplification rules
% 1.76/1.14  ----------------------
% 1.76/1.14  #Subsume      : 0
% 1.76/1.14  #Demod        : 5
% 1.76/1.14  #Tautology    : 0
% 1.76/1.14  #SimpNegUnit  : 1
% 1.76/1.14  #BackRed      : 0
% 1.76/1.14  
% 1.76/1.14  #Partial instantiations: 0
% 1.76/1.14  #Strategies tried      : 1
% 1.76/1.14  
% 1.76/1.14  Timing (in seconds)
% 1.76/1.14  ----------------------
% 1.76/1.15  Preprocessing        : 0.27
% 1.76/1.15  Parsing              : 0.15
% 1.76/1.15  CNF conversion       : 0.02
% 1.76/1.15  Main loop            : 0.10
% 1.76/1.15  Inferencing          : 0.05
% 1.76/1.15  Reduction            : 0.03
% 1.76/1.15  Demodulation         : 0.02
% 1.76/1.15  BG Simplification    : 0.01
% 1.76/1.15  Subsumption          : 0.02
% 1.76/1.15  Abstraction          : 0.00
% 1.76/1.15  MUC search           : 0.00
% 1.76/1.15  Cooper               : 0.00
% 1.76/1.15  Total                : 0.39
% 1.76/1.15  Index Insertion      : 0.00
% 1.76/1.15  Index Deletion       : 0.00
% 1.76/1.15  Index Matching       : 0.00
% 1.76/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
