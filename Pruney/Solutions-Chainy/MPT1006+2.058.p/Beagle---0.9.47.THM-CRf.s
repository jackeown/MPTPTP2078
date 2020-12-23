%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:10 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   42 (  95 expanded)
%              Number of leaves         :   24 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :   35 ( 119 expanded)
%              Number of equality atoms :   22 (  75 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_36,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_55,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_35,axiom,(
    ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(f_46,axiom,(
    ! [A,B] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A,B))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relset_1)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_8,plain,(
    ! [A_3] : k9_relat_1(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_27,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_22])).

tff(c_85,plain,(
    ! [A_21,B_22] :
      ( k9_relat_1(k6_relat_1(A_21),B_22) = B_22
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_94,plain,(
    k9_relat_1(k6_relat_1(k1_xboole_0),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_27,c_85])).

tff(c_99,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_12,c_94])).

tff(c_10,plain,(
    ! [A_4] : k10_relat_1(k1_xboole_0,A_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_107,plain,(
    ! [A_4] : k10_relat_1('#skF_3',A_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_99,c_10])).

tff(c_18,plain,(
    ! [A_11,B_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_167,plain,(
    ! [A_31,B_32] : m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_18])).

tff(c_16,plain,(
    ! [A_7,B_8,C_9,D_10] :
      ( k8_relset_1(A_7,B_8,C_9,D_10) = k10_relat_1(C_9,D_10)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_169,plain,(
    ! [A_31,B_32,D_10] : k8_relset_1(A_31,B_32,'#skF_3',D_10) = k10_relat_1('#skF_3',D_10) ),
    inference(resolution,[status(thm)],[c_167,c_16])).

tff(c_178,plain,(
    ! [A_31,B_32,D_10] : k8_relset_1(A_31,B_32,'#skF_3',D_10) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_169])).

tff(c_20,plain,(
    k8_relset_1(k1_xboole_0,'#skF_1','#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_102,plain,(
    k8_relset_1('#skF_3','#skF_1','#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_99,c_20])).

tff(c_184,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_102])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:01:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.16  
% 1.68/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.16  %$ v1_funct_2 > m1_subset_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.68/1.16  
% 1.68/1.16  %Foreground sorts:
% 1.68/1.16  
% 1.68/1.16  
% 1.68/1.16  %Background operators:
% 1.68/1.16  
% 1.68/1.16  
% 1.68/1.16  %Foreground operators:
% 1.68/1.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.68/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.16  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.68/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.68/1.16  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.68/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.16  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.68/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.68/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.68/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.16  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.68/1.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.68/1.16  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.68/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.68/1.16  
% 1.68/1.17  tff(f_33, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.68/1.17  tff(f_36, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 1.68/1.17  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.68/1.17  tff(f_55, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_2)).
% 1.68/1.17  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 1.68/1.17  tff(f_35, axiom, (![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 1.68/1.17  tff(f_46, axiom, (![A, B]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relset_1)).
% 1.68/1.17  tff(f_44, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 1.68/1.17  tff(c_8, plain, (![A_3]: (k9_relat_1(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.68/1.17  tff(c_12, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.68/1.17  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.68/1.17  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.68/1.17  tff(c_27, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_22])).
% 1.68/1.17  tff(c_85, plain, (![A_21, B_22]: (k9_relat_1(k6_relat_1(A_21), B_22)=B_22 | ~m1_subset_1(B_22, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.68/1.17  tff(c_94, plain, (k9_relat_1(k6_relat_1(k1_xboole_0), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_27, c_85])).
% 1.68/1.17  tff(c_99, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_12, c_94])).
% 1.68/1.17  tff(c_10, plain, (![A_4]: (k10_relat_1(k1_xboole_0, A_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.68/1.17  tff(c_107, plain, (![A_4]: (k10_relat_1('#skF_3', A_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_99, c_10])).
% 1.68/1.17  tff(c_18, plain, (![A_11, B_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.68/1.17  tff(c_167, plain, (![A_31, B_32]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_18])).
% 1.68/1.17  tff(c_16, plain, (![A_7, B_8, C_9, D_10]: (k8_relset_1(A_7, B_8, C_9, D_10)=k10_relat_1(C_9, D_10) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.68/1.17  tff(c_169, plain, (![A_31, B_32, D_10]: (k8_relset_1(A_31, B_32, '#skF_3', D_10)=k10_relat_1('#skF_3', D_10))), inference(resolution, [status(thm)], [c_167, c_16])).
% 1.68/1.17  tff(c_178, plain, (![A_31, B_32, D_10]: (k8_relset_1(A_31, B_32, '#skF_3', D_10)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_169])).
% 1.68/1.17  tff(c_20, plain, (k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.68/1.17  tff(c_102, plain, (k8_relset_1('#skF_3', '#skF_1', '#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_99, c_99, c_20])).
% 1.68/1.17  tff(c_184, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_178, c_102])).
% 1.68/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.17  
% 1.68/1.17  Inference rules
% 1.68/1.17  ----------------------
% 1.68/1.17  #Ref     : 0
% 1.68/1.17  #Sup     : 40
% 1.68/1.17  #Fact    : 0
% 1.68/1.17  #Define  : 0
% 1.68/1.17  #Split   : 0
% 1.68/1.17  #Chain   : 0
% 1.68/1.17  #Close   : 0
% 1.68/1.17  
% 1.68/1.17  Ordering : KBO
% 1.68/1.17  
% 1.68/1.17  Simplification rules
% 1.68/1.17  ----------------------
% 1.68/1.17  #Subsume      : 0
% 1.68/1.17  #Demod        : 33
% 1.68/1.17  #Tautology    : 34
% 1.68/1.17  #SimpNegUnit  : 0
% 1.68/1.17  #BackRed      : 12
% 1.68/1.17  
% 1.68/1.17  #Partial instantiations: 0
% 1.68/1.17  #Strategies tried      : 1
% 1.68/1.17  
% 1.68/1.17  Timing (in seconds)
% 1.68/1.17  ----------------------
% 1.68/1.17  Preprocessing        : 0.29
% 1.68/1.17  Parsing              : 0.15
% 1.68/1.17  CNF conversion       : 0.02
% 1.68/1.17  Main loop            : 0.12
% 1.68/1.17  Inferencing          : 0.04
% 1.68/1.17  Reduction            : 0.05
% 1.68/1.17  Demodulation         : 0.04
% 1.68/1.17  BG Simplification    : 0.01
% 1.68/1.17  Subsumption          : 0.02
% 1.68/1.17  Abstraction          : 0.01
% 1.68/1.17  MUC search           : 0.00
% 1.68/1.17  Cooper               : 0.00
% 1.68/1.17  Total                : 0.44
% 1.68/1.17  Index Insertion      : 0.00
% 1.68/1.17  Index Deletion       : 0.00
% 1.68/1.17  Index Matching       : 0.00
% 1.68/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
