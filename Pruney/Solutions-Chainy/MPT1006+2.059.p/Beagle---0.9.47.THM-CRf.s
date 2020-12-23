%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:10 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   43 (  96 expanded)
%              Number of leaves         :   25 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :   35 ( 119 expanded)
%              Number of equality atoms :   22 (  75 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_41,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_44,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_43,axiom,(
    ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_12,plain,(
    ! [A_7] : k9_relat_1(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_29,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_24])).

tff(c_82,plain,(
    ! [A_22,B_23] :
      ( k9_relat_1(k6_relat_1(A_22),B_23) = B_23
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_85,plain,(
    k9_relat_1(k6_relat_1(k1_xboole_0),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_29,c_82])).

tff(c_90,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16,c_85])).

tff(c_14,plain,(
    ! [A_8] : k10_relat_1(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_99,plain,(
    ! [A_8] : k10_relat_1('#skF_3',A_8) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_90,c_14])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_95,plain,(
    ! [A_3] : m1_subset_1('#skF_3',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_8])).

tff(c_176,plain,(
    ! [A_33,B_34,C_35,D_36] :
      ( k8_relset_1(A_33,B_34,C_35,D_36) = k10_relat_1(C_35,D_36)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_179,plain,(
    ! [A_33,B_34,D_36] : k8_relset_1(A_33,B_34,'#skF_3',D_36) = k10_relat_1('#skF_3',D_36) ),
    inference(resolution,[status(thm)],[c_95,c_176])).

tff(c_185,plain,(
    ! [A_33,B_34,D_36] : k8_relset_1(A_33,B_34,'#skF_3',D_36) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_179])).

tff(c_22,plain,(
    k8_relset_1(k1_xboole_0,'#skF_1','#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_93,plain,(
    k8_relset_1('#skF_3','#skF_1','#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_90,c_22])).

tff(c_189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_93])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:45:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.16  
% 1.66/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.16  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k8_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.66/1.16  
% 1.66/1.16  %Foreground sorts:
% 1.66/1.16  
% 1.66/1.16  
% 1.66/1.16  %Background operators:
% 1.66/1.16  
% 1.66/1.16  
% 1.66/1.16  %Foreground operators:
% 1.66/1.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.66/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.66/1.16  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.66/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.66/1.16  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.66/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.16  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.66/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.66/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.66/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.16  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.66/1.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.66/1.16  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.66/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.66/1.16  
% 1.66/1.17  tff(f_41, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.66/1.17  tff(f_44, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 1.66/1.17  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.66/1.17  tff(f_61, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_2)).
% 1.66/1.17  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 1.66/1.17  tff(f_43, axiom, (![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 1.66/1.17  tff(f_33, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 1.66/1.17  tff(f_52, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 1.66/1.17  tff(c_12, plain, (![A_7]: (k9_relat_1(k1_xboole_0, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.66/1.17  tff(c_16, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.66/1.17  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.66/1.17  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.66/1.17  tff(c_29, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_24])).
% 1.66/1.17  tff(c_82, plain, (![A_22, B_23]: (k9_relat_1(k6_relat_1(A_22), B_23)=B_23 | ~m1_subset_1(B_23, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.66/1.17  tff(c_85, plain, (k9_relat_1(k6_relat_1(k1_xboole_0), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_29, c_82])).
% 1.66/1.17  tff(c_90, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16, c_85])).
% 1.66/1.17  tff(c_14, plain, (![A_8]: (k10_relat_1(k1_xboole_0, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.66/1.17  tff(c_99, plain, (![A_8]: (k10_relat_1('#skF_3', A_8)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_90, c_14])).
% 1.66/1.17  tff(c_8, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.66/1.17  tff(c_95, plain, (![A_3]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_8])).
% 1.66/1.17  tff(c_176, plain, (![A_33, B_34, C_35, D_36]: (k8_relset_1(A_33, B_34, C_35, D_36)=k10_relat_1(C_35, D_36) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.66/1.17  tff(c_179, plain, (![A_33, B_34, D_36]: (k8_relset_1(A_33, B_34, '#skF_3', D_36)=k10_relat_1('#skF_3', D_36))), inference(resolution, [status(thm)], [c_95, c_176])).
% 1.66/1.17  tff(c_185, plain, (![A_33, B_34, D_36]: (k8_relset_1(A_33, B_34, '#skF_3', D_36)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_179])).
% 1.66/1.17  tff(c_22, plain, (k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.66/1.17  tff(c_93, plain, (k8_relset_1('#skF_3', '#skF_1', '#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_90, c_22])).
% 1.66/1.17  tff(c_189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_185, c_93])).
% 1.66/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.17  
% 1.66/1.17  Inference rules
% 1.66/1.17  ----------------------
% 1.66/1.17  #Ref     : 0
% 1.66/1.17  #Sup     : 40
% 1.66/1.17  #Fact    : 0
% 1.66/1.17  #Define  : 0
% 1.66/1.17  #Split   : 0
% 1.66/1.17  #Chain   : 0
% 1.66/1.17  #Close   : 0
% 1.66/1.17  
% 1.66/1.17  Ordering : KBO
% 1.66/1.17  
% 1.66/1.17  Simplification rules
% 1.66/1.17  ----------------------
% 1.66/1.17  #Subsume      : 0
% 1.66/1.17  #Demod        : 30
% 1.66/1.17  #Tautology    : 34
% 1.66/1.17  #SimpNegUnit  : 0
% 1.66/1.17  #BackRed      : 11
% 1.66/1.17  
% 1.66/1.17  #Partial instantiations: 0
% 1.66/1.17  #Strategies tried      : 1
% 1.66/1.17  
% 1.66/1.17  Timing (in seconds)
% 1.66/1.17  ----------------------
% 1.91/1.18  Preprocessing        : 0.29
% 1.91/1.18  Parsing              : 0.16
% 1.91/1.18  CNF conversion       : 0.02
% 1.91/1.18  Main loop            : 0.12
% 1.91/1.18  Inferencing          : 0.04
% 1.91/1.18  Reduction            : 0.04
% 1.91/1.18  Demodulation         : 0.03
% 1.91/1.18  BG Simplification    : 0.01
% 1.91/1.18  Subsumption          : 0.02
% 1.91/1.18  Abstraction          : 0.01
% 1.91/1.18  MUC search           : 0.00
% 1.91/1.18  Cooper               : 0.00
% 1.91/1.18  Total                : 0.44
% 1.91/1.18  Index Insertion      : 0.00
% 1.91/1.18  Index Deletion       : 0.00
% 1.91/1.18  Index Matching       : 0.00
% 1.91/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
