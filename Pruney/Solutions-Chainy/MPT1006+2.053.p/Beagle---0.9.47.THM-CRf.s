%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:09 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 101 expanded)
%              Number of leaves         :   25 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :   41 ( 149 expanded)
%              Number of equality atoms :   17 (  50 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_57,axiom,(
    ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_29,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_24])).

tff(c_72,plain,(
    ! [C_24,B_25,A_26] :
      ( ~ v1_xboole_0(C_24)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(C_24))
      | ~ r2_hidden(A_26,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_74,plain,(
    ! [A_26] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_26,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_29,c_72])).

tff(c_81,plain,(
    ! [A_27] : ~ r2_hidden(A_27,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_74])).

tff(c_86,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4,c_81])).

tff(c_18,plain,(
    ! [A_12] : k10_relat_1(k1_xboole_0,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_91,plain,(
    ! [A_12] : k10_relat_1('#skF_4',A_12) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_86,c_18])).

tff(c_12,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_94,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_12])).

tff(c_155,plain,(
    ! [A_36,B_37,C_38,D_39] :
      ( k8_relset_1(A_36,B_37,C_38,D_39) = k10_relat_1(C_38,D_39)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_160,plain,(
    ! [A_36,B_37,D_39] : k8_relset_1(A_36,B_37,'#skF_4',D_39) = k10_relat_1('#skF_4',D_39) ),
    inference(resolution,[status(thm)],[c_94,c_155])).

tff(c_164,plain,(
    ! [A_36,B_37,D_39] : k8_relset_1(A_36,B_37,'#skF_4',D_39) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_160])).

tff(c_22,plain,(
    k8_relset_1(k1_xboole_0,'#skF_2','#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_89,plain,(
    k8_relset_1('#skF_4','#skF_2','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_86,c_22])).

tff(c_167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_89])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:56:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.34  
% 2.06/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.34  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.06/1.34  
% 2.06/1.34  %Foreground sorts:
% 2.06/1.34  
% 2.06/1.34  
% 2.06/1.34  %Background operators:
% 2.06/1.34  
% 2.06/1.34  
% 2.06/1.34  %Foreground operators:
% 2.06/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.06/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.34  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.06/1.34  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.06/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.06/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.06/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.34  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.06/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.06/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.06/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.06/1.34  
% 2.06/1.35  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.06/1.35  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.06/1.35  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.06/1.35  tff(f_70, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_2)).
% 2.06/1.35  tff(f_55, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.06/1.35  tff(f_57, axiom, (![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 2.06/1.35  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.06/1.35  tff(f_61, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.06/1.35  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.06/1.35  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.06/1.35  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.06/1.35  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.06/1.35  tff(c_29, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_24])).
% 2.06/1.35  tff(c_72, plain, (![C_24, B_25, A_26]: (~v1_xboole_0(C_24) | ~m1_subset_1(B_25, k1_zfmisc_1(C_24)) | ~r2_hidden(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.06/1.35  tff(c_74, plain, (![A_26]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_26, '#skF_4'))), inference(resolution, [status(thm)], [c_29, c_72])).
% 2.06/1.35  tff(c_81, plain, (![A_27]: (~r2_hidden(A_27, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_74])).
% 2.06/1.35  tff(c_86, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4, c_81])).
% 2.06/1.35  tff(c_18, plain, (![A_12]: (k10_relat_1(k1_xboole_0, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.06/1.35  tff(c_91, plain, (![A_12]: (k10_relat_1('#skF_4', A_12)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_86, c_18])).
% 2.06/1.35  tff(c_12, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.06/1.35  tff(c_94, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_12])).
% 2.06/1.35  tff(c_155, plain, (![A_36, B_37, C_38, D_39]: (k8_relset_1(A_36, B_37, C_38, D_39)=k10_relat_1(C_38, D_39) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.06/1.35  tff(c_160, plain, (![A_36, B_37, D_39]: (k8_relset_1(A_36, B_37, '#skF_4', D_39)=k10_relat_1('#skF_4', D_39))), inference(resolution, [status(thm)], [c_94, c_155])).
% 2.06/1.35  tff(c_164, plain, (![A_36, B_37, D_39]: (k8_relset_1(A_36, B_37, '#skF_4', D_39)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_160])).
% 2.06/1.35  tff(c_22, plain, (k8_relset_1(k1_xboole_0, '#skF_2', '#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.06/1.35  tff(c_89, plain, (k8_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_86, c_22])).
% 2.06/1.35  tff(c_167, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_164, c_89])).
% 2.06/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.35  
% 2.06/1.35  Inference rules
% 2.06/1.35  ----------------------
% 2.06/1.35  #Ref     : 0
% 2.06/1.35  #Sup     : 31
% 2.06/1.35  #Fact    : 0
% 2.06/1.35  #Define  : 0
% 2.06/1.35  #Split   : 0
% 2.06/1.35  #Chain   : 0
% 2.06/1.35  #Close   : 0
% 2.06/1.35  
% 2.06/1.35  Ordering : KBO
% 2.06/1.35  
% 2.06/1.35  Simplification rules
% 2.06/1.35  ----------------------
% 2.06/1.35  #Subsume      : 5
% 2.06/1.35  #Demod        : 23
% 2.06/1.35  #Tautology    : 22
% 2.06/1.35  #SimpNegUnit  : 0
% 2.06/1.35  #BackRed      : 11
% 2.06/1.35  
% 2.06/1.35  #Partial instantiations: 0
% 2.06/1.35  #Strategies tried      : 1
% 2.06/1.35  
% 2.06/1.35  Timing (in seconds)
% 2.06/1.35  ----------------------
% 2.06/1.35  Preprocessing        : 0.32
% 2.06/1.35  Parsing              : 0.16
% 2.06/1.35  CNF conversion       : 0.02
% 2.06/1.35  Main loop            : 0.13
% 2.06/1.35  Inferencing          : 0.04
% 2.06/1.35  Reduction            : 0.05
% 2.06/1.35  Demodulation         : 0.03
% 2.06/1.35  BG Simplification    : 0.01
% 2.06/1.35  Subsumption          : 0.02
% 2.06/1.35  Abstraction          : 0.01
% 2.06/1.35  MUC search           : 0.00
% 2.06/1.35  Cooper               : 0.00
% 2.06/1.36  Total                : 0.47
% 2.06/1.36  Index Insertion      : 0.00
% 2.06/1.36  Index Deletion       : 0.00
% 2.06/1.36  Index Matching       : 0.00
% 2.06/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
