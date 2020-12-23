%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:07 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   35 (  40 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   59 (  89 expanded)
%              Number of equality atoms :    9 (  14 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_10,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [A_5,B_6,C_7] :
      ( m1_subset_1(k2_relset_1(A_5,B_6,C_7),k1_zfmisc_1(B_6))
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_25,plain,(
    ! [D_19,C_20,A_21,B_22] :
      ( r2_hidden(k1_funct_1(D_19,C_20),k2_relset_1(A_21,B_22,D_19))
      | k1_xboole_0 = B_22
      | ~ r2_hidden(C_20,A_21)
      | ~ m1_subset_1(D_19,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ v1_funct_2(D_19,A_21,B_22)
      | ~ v1_funct_1(D_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_29,plain,(
    ! [B_25,A_23,A_27,D_26,C_24] :
      ( r2_hidden(k1_funct_1(D_26,C_24),A_27)
      | ~ m1_subset_1(k2_relset_1(A_23,B_25,D_26),k1_zfmisc_1(A_27))
      | k1_xboole_0 = B_25
      | ~ r2_hidden(C_24,A_23)
      | ~ m1_subset_1(D_26,k1_zfmisc_1(k2_zfmisc_1(A_23,B_25)))
      | ~ v1_funct_2(D_26,A_23,B_25)
      | ~ v1_funct_1(D_26) ) ),
    inference(resolution,[status(thm)],[c_25,c_2])).

tff(c_33,plain,(
    ! [C_28,C_29,B_30,A_31] :
      ( r2_hidden(k1_funct_1(C_28,C_29),B_30)
      | k1_xboole_0 = B_30
      | ~ r2_hidden(C_29,A_31)
      | ~ v1_funct_2(C_28,A_31,B_30)
      | ~ v1_funct_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_31,B_30))) ) ),
    inference(resolution,[status(thm)],[c_4,c_29])).

tff(c_40,plain,(
    ! [C_32,B_33] :
      ( r2_hidden(k1_funct_1(C_32,'#skF_3'),B_33)
      | k1_xboole_0 = B_33
      | ~ v1_funct_2(C_32,'#skF_1',B_33)
      | ~ v1_funct_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_33))) ) ),
    inference(resolution,[status(thm)],[c_12,c_33])).

tff(c_47,plain,
    ( r2_hidden(k1_funct_1('#skF_4','#skF_3'),'#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_40])).

tff(c_51,plain,
    ( r2_hidden(k1_funct_1('#skF_4','#skF_3'),'#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_47])).

tff(c_53,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_8,c_51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:44:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.18  
% 1.75/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.19  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.75/1.19  
% 1.75/1.19  %Foreground sorts:
% 1.75/1.19  
% 1.75/1.19  
% 1.75/1.19  %Background operators:
% 1.75/1.19  
% 1.75/1.19  
% 1.75/1.19  %Foreground operators:
% 1.75/1.19  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 1.75/1.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.75/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.75/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.75/1.19  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.75/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.75/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.75/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.75/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.75/1.19  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.75/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.75/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.75/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.75/1.19  
% 1.88/1.20  tff(f_61, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 1.88/1.20  tff(f_36, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 1.88/1.20  tff(f_48, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 1.88/1.20  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 1.88/1.20  tff(c_10, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.88/1.20  tff(c_8, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.88/1.20  tff(c_18, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.88/1.20  tff(c_16, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.88/1.20  tff(c_14, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.88/1.20  tff(c_12, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.88/1.20  tff(c_4, plain, (![A_5, B_6, C_7]: (m1_subset_1(k2_relset_1(A_5, B_6, C_7), k1_zfmisc_1(B_6)) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.88/1.20  tff(c_25, plain, (![D_19, C_20, A_21, B_22]: (r2_hidden(k1_funct_1(D_19, C_20), k2_relset_1(A_21, B_22, D_19)) | k1_xboole_0=B_22 | ~r2_hidden(C_20, A_21) | ~m1_subset_1(D_19, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~v1_funct_2(D_19, A_21, B_22) | ~v1_funct_1(D_19))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.88/1.20  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.88/1.20  tff(c_29, plain, (![B_25, A_23, A_27, D_26, C_24]: (r2_hidden(k1_funct_1(D_26, C_24), A_27) | ~m1_subset_1(k2_relset_1(A_23, B_25, D_26), k1_zfmisc_1(A_27)) | k1_xboole_0=B_25 | ~r2_hidden(C_24, A_23) | ~m1_subset_1(D_26, k1_zfmisc_1(k2_zfmisc_1(A_23, B_25))) | ~v1_funct_2(D_26, A_23, B_25) | ~v1_funct_1(D_26))), inference(resolution, [status(thm)], [c_25, c_2])).
% 1.88/1.20  tff(c_33, plain, (![C_28, C_29, B_30, A_31]: (r2_hidden(k1_funct_1(C_28, C_29), B_30) | k1_xboole_0=B_30 | ~r2_hidden(C_29, A_31) | ~v1_funct_2(C_28, A_31, B_30) | ~v1_funct_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_31, B_30))))), inference(resolution, [status(thm)], [c_4, c_29])).
% 1.88/1.20  tff(c_40, plain, (![C_32, B_33]: (r2_hidden(k1_funct_1(C_32, '#skF_3'), B_33) | k1_xboole_0=B_33 | ~v1_funct_2(C_32, '#skF_1', B_33) | ~v1_funct_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_33))))), inference(resolution, [status(thm)], [c_12, c_33])).
% 1.88/1.20  tff(c_47, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_3'), '#skF_2') | k1_xboole_0='#skF_2' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_40])).
% 1.88/1.20  tff(c_51, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_3'), '#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_47])).
% 1.88/1.20  tff(c_53, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_8, c_51])).
% 1.88/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.20  
% 1.88/1.20  Inference rules
% 1.88/1.20  ----------------------
% 1.88/1.20  #Ref     : 0
% 1.88/1.20  #Sup     : 7
% 1.88/1.20  #Fact    : 0
% 1.88/1.20  #Define  : 0
% 1.88/1.20  #Split   : 0
% 1.88/1.20  #Chain   : 0
% 1.88/1.20  #Close   : 0
% 1.88/1.20  
% 1.88/1.20  Ordering : KBO
% 1.88/1.20  
% 1.88/1.20  Simplification rules
% 1.88/1.20  ----------------------
% 1.88/1.20  #Subsume      : 0
% 1.88/1.20  #Demod        : 2
% 1.88/1.20  #Tautology    : 0
% 1.88/1.20  #SimpNegUnit  : 1
% 1.88/1.20  #BackRed      : 0
% 1.88/1.20  
% 1.88/1.20  #Partial instantiations: 0
% 1.88/1.20  #Strategies tried      : 1
% 1.88/1.20  
% 1.88/1.20  Timing (in seconds)
% 1.88/1.20  ----------------------
% 1.88/1.20  Preprocessing        : 0.27
% 1.88/1.20  Parsing              : 0.14
% 1.88/1.20  CNF conversion       : 0.02
% 1.88/1.20  Main loop            : 0.11
% 1.88/1.20  Inferencing          : 0.05
% 1.88/1.20  Reduction            : 0.03
% 1.88/1.20  Demodulation         : 0.02
% 1.88/1.20  BG Simplification    : 0.01
% 1.88/1.20  Subsumption          : 0.02
% 1.88/1.20  Abstraction          : 0.01
% 1.88/1.20  MUC search           : 0.00
% 1.88/1.20  Cooper               : 0.00
% 1.88/1.20  Total                : 0.41
% 1.88/1.20  Index Insertion      : 0.00
% 1.88/1.20  Index Deletion       : 0.00
% 1.88/1.20  Index Matching       : 0.00
% 1.88/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
