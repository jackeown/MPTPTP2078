%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:05 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   37 (  84 expanded)
%              Number of leaves         :   21 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   34 ( 127 expanded)
%              Number of equality atoms :   13 (  31 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_32,axiom,(
    ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_14,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_32,plain,(
    ! [C_13,A_14,B_15] :
      ( v1_xboole_0(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15)))
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_35,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_32])).

tff(c_38,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_35])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_42,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_4])).

tff(c_6,plain,(
    ! [A_2] : k10_relat_1(k1_xboole_0,A_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_45,plain,(
    ! [A_2] : k10_relat_1('#skF_3',A_2) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_6])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_14])).

tff(c_73,plain,(
    ! [A_18,B_19,C_20,D_21] :
      ( k8_relset_1(A_18,B_19,C_20,D_21) = k10_relat_1(C_20,D_21)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_75,plain,(
    ! [D_21] : k8_relset_1('#skF_3','#skF_1','#skF_3',D_21) = k10_relat_1('#skF_3',D_21) ),
    inference(resolution,[status(thm)],[c_44,c_73])).

tff(c_77,plain,(
    ! [D_21] : k8_relset_1('#skF_3','#skF_1','#skF_3',D_21) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_75])).

tff(c_12,plain,(
    k8_relset_1(k1_xboole_0,'#skF_1','#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_43,plain,(
    k8_relset_1('#skF_3','#skF_1','#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_12])).

tff(c_80,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:07:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.12  
% 1.66/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.12  %$ v1_funct_2 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.66/1.12  
% 1.66/1.12  %Foreground sorts:
% 1.66/1.12  
% 1.66/1.12  
% 1.66/1.12  %Background operators:
% 1.66/1.12  
% 1.66/1.12  
% 1.66/1.12  %Foreground operators:
% 1.66/1.12  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.66/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.12  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.66/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.66/1.12  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.66/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.66/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.66/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.12  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.66/1.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.66/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.66/1.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.66/1.12  
% 1.66/1.14  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.66/1.14  tff(f_52, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_funct_2)).
% 1.66/1.14  tff(f_39, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 1.66/1.14  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.66/1.14  tff(f_32, axiom, (![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 1.66/1.14  tff(f_43, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 1.66/1.14  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.66/1.14  tff(c_14, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.66/1.14  tff(c_32, plain, (![C_13, A_14, B_15]: (v1_xboole_0(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))) | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.66/1.14  tff(c_35, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_32])).
% 1.66/1.14  tff(c_38, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_35])).
% 1.66/1.14  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.66/1.14  tff(c_42, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_38, c_4])).
% 1.66/1.14  tff(c_6, plain, (![A_2]: (k10_relat_1(k1_xboole_0, A_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.66/1.14  tff(c_45, plain, (![A_2]: (k10_relat_1('#skF_3', A_2)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_6])).
% 1.66/1.14  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_14])).
% 1.66/1.14  tff(c_73, plain, (![A_18, B_19, C_20, D_21]: (k8_relset_1(A_18, B_19, C_20, D_21)=k10_relat_1(C_20, D_21) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.66/1.14  tff(c_75, plain, (![D_21]: (k8_relset_1('#skF_3', '#skF_1', '#skF_3', D_21)=k10_relat_1('#skF_3', D_21))), inference(resolution, [status(thm)], [c_44, c_73])).
% 1.66/1.14  tff(c_77, plain, (![D_21]: (k8_relset_1('#skF_3', '#skF_1', '#skF_3', D_21)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_45, c_75])).
% 1.66/1.14  tff(c_12, plain, (k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.66/1.14  tff(c_43, plain, (k8_relset_1('#skF_3', '#skF_1', '#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_12])).
% 1.66/1.14  tff(c_80, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_43])).
% 1.66/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.14  
% 1.66/1.14  Inference rules
% 1.66/1.14  ----------------------
% 1.66/1.14  #Ref     : 0
% 1.66/1.14  #Sup     : 12
% 1.66/1.14  #Fact    : 0
% 1.66/1.14  #Define  : 0
% 1.66/1.14  #Split   : 0
% 1.66/1.14  #Chain   : 0
% 1.66/1.14  #Close   : 0
% 1.66/1.14  
% 1.66/1.14  Ordering : KBO
% 1.66/1.14  
% 1.66/1.14  Simplification rules
% 1.66/1.14  ----------------------
% 1.66/1.14  #Subsume      : 0
% 1.66/1.14  #Demod        : 14
% 1.66/1.14  #Tautology    : 10
% 1.66/1.14  #SimpNegUnit  : 0
% 1.66/1.14  #BackRed      : 7
% 1.66/1.14  
% 1.66/1.14  #Partial instantiations: 0
% 1.66/1.14  #Strategies tried      : 1
% 1.66/1.14  
% 1.66/1.14  Timing (in seconds)
% 1.66/1.14  ----------------------
% 1.66/1.14  Preprocessing        : 0.29
% 1.66/1.14  Parsing              : 0.15
% 1.66/1.14  CNF conversion       : 0.02
% 1.66/1.14  Main loop            : 0.10
% 1.66/1.14  Inferencing          : 0.04
% 1.66/1.14  Reduction            : 0.03
% 1.66/1.14  Demodulation         : 0.03
% 1.66/1.14  BG Simplification    : 0.01
% 1.66/1.14  Subsumption          : 0.01
% 1.66/1.14  Abstraction          : 0.01
% 1.66/1.14  MUC search           : 0.00
% 1.66/1.14  Cooper               : 0.00
% 1.66/1.14  Total                : 0.41
% 1.66/1.14  Index Insertion      : 0.00
% 1.66/1.14  Index Deletion       : 0.00
% 1.66/1.14  Index Matching       : 0.00
% 1.66/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
