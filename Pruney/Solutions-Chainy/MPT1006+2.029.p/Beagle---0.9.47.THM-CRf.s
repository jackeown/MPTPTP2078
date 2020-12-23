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
% DateTime   : Thu Dec  3 10:14:06 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 100 expanded)
%              Number of leaves         :   24 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :   41 ( 149 expanded)
%              Number of equality atoms :   18 (  55 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_35,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_30])).

tff(c_70,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(A_25,B_26)
      | ~ m1_subset_1(A_25,k1_zfmisc_1(B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_81,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_35,c_70])).

tff(c_84,plain,(
    ! [B_27,A_28] :
      ( B_27 = A_28
      | ~ r1_tarski(B_27,A_28)
      | ~ r1_tarski(A_28,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_86,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_81,c_84])).

tff(c_93,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_86])).

tff(c_24,plain,(
    ! [A_12] : k10_relat_1(k1_xboole_0,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_103,plain,(
    ! [A_12] : k10_relat_1('#skF_3',A_12) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_93,c_24])).

tff(c_16,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_105,plain,(
    ! [A_6] : m1_subset_1('#skF_3',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_16])).

tff(c_188,plain,(
    ! [A_45,B_46,C_47,D_48] :
      ( k8_relset_1(A_45,B_46,C_47,D_48) = k10_relat_1(C_47,D_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_195,plain,(
    ! [A_45,B_46,D_48] : k8_relset_1(A_45,B_46,'#skF_3',D_48) = k10_relat_1('#skF_3',D_48) ),
    inference(resolution,[status(thm)],[c_105,c_188])).

tff(c_200,plain,(
    ! [A_45,B_46,D_48] : k8_relset_1(A_45,B_46,'#skF_3',D_48) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_195])).

tff(c_28,plain,(
    k8_relset_1(k1_xboole_0,'#skF_1','#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_100,plain,(
    k8_relset_1('#skF_3','#skF_1','#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_93,c_28])).

tff(c_204,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_100])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:41:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.29  
% 2.00/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.30  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.00/1.30  
% 2.00/1.30  %Foreground sorts:
% 2.00/1.30  
% 2.00/1.30  
% 2.00/1.30  %Background operators:
% 2.00/1.30  
% 2.00/1.30  
% 2.00/1.30  %Foreground operators:
% 2.00/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.00/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.00/1.30  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.00/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.00/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.00/1.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.00/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.00/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.00/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.30  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.00/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.00/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.00/1.30  
% 2.16/1.31  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.16/1.31  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.16/1.31  tff(f_66, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_2)).
% 2.16/1.31  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.16/1.31  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.16/1.31  tff(f_53, axiom, (![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 2.16/1.31  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.16/1.31  tff(f_57, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.16/1.31  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.16/1.31  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.16/1.31  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.16/1.31  tff(c_35, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_30])).
% 2.16/1.31  tff(c_70, plain, (![A_25, B_26]: (r1_tarski(A_25, B_26) | ~m1_subset_1(A_25, k1_zfmisc_1(B_26)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.16/1.31  tff(c_81, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_35, c_70])).
% 2.16/1.31  tff(c_84, plain, (![B_27, A_28]: (B_27=A_28 | ~r1_tarski(B_27, A_28) | ~r1_tarski(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.16/1.31  tff(c_86, plain, (k1_xboole_0='#skF_3' | ~r1_tarski(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_81, c_84])).
% 2.16/1.31  tff(c_93, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_86])).
% 2.16/1.31  tff(c_24, plain, (![A_12]: (k10_relat_1(k1_xboole_0, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.16/1.31  tff(c_103, plain, (![A_12]: (k10_relat_1('#skF_3', A_12)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_93, c_24])).
% 2.16/1.31  tff(c_16, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.16/1.31  tff(c_105, plain, (![A_6]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_16])).
% 2.16/1.31  tff(c_188, plain, (![A_45, B_46, C_47, D_48]: (k8_relset_1(A_45, B_46, C_47, D_48)=k10_relat_1(C_47, D_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.16/1.31  tff(c_195, plain, (![A_45, B_46, D_48]: (k8_relset_1(A_45, B_46, '#skF_3', D_48)=k10_relat_1('#skF_3', D_48))), inference(resolution, [status(thm)], [c_105, c_188])).
% 2.16/1.31  tff(c_200, plain, (![A_45, B_46, D_48]: (k8_relset_1(A_45, B_46, '#skF_3', D_48)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_195])).
% 2.16/1.31  tff(c_28, plain, (k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.16/1.31  tff(c_100, plain, (k8_relset_1('#skF_3', '#skF_1', '#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_93, c_93, c_28])).
% 2.16/1.31  tff(c_204, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_200, c_100])).
% 2.16/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.31  
% 2.16/1.31  Inference rules
% 2.16/1.31  ----------------------
% 2.16/1.31  #Ref     : 0
% 2.16/1.31  #Sup     : 36
% 2.16/1.31  #Fact    : 0
% 2.16/1.31  #Define  : 0
% 2.16/1.31  #Split   : 0
% 2.16/1.31  #Chain   : 0
% 2.16/1.31  #Close   : 0
% 2.16/1.31  
% 2.16/1.31  Ordering : KBO
% 2.16/1.31  
% 2.16/1.31  Simplification rules
% 2.16/1.31  ----------------------
% 2.16/1.31  #Subsume      : 1
% 2.16/1.31  #Demod        : 28
% 2.16/1.31  #Tautology    : 29
% 2.16/1.31  #SimpNegUnit  : 0
% 2.16/1.31  #BackRed      : 10
% 2.16/1.31  
% 2.16/1.31  #Partial instantiations: 0
% 2.16/1.31  #Strategies tried      : 1
% 2.16/1.31  
% 2.16/1.31  Timing (in seconds)
% 2.16/1.31  ----------------------
% 2.16/1.31  Preprocessing        : 0.31
% 2.16/1.31  Parsing              : 0.17
% 2.16/1.31  CNF conversion       : 0.02
% 2.16/1.31  Main loop            : 0.14
% 2.16/1.31  Inferencing          : 0.05
% 2.16/1.31  Reduction            : 0.05
% 2.16/1.31  Demodulation         : 0.04
% 2.16/1.31  BG Simplification    : 0.01
% 2.16/1.31  Subsumption          : 0.02
% 2.16/1.31  Abstraction          : 0.01
% 2.16/1.31  MUC search           : 0.00
% 2.16/1.31  Cooper               : 0.00
% 2.16/1.31  Total                : 0.48
% 2.16/1.31  Index Insertion      : 0.00
% 2.16/1.31  Index Deletion       : 0.00
% 2.16/1.31  Index Matching       : 0.00
% 2.16/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
