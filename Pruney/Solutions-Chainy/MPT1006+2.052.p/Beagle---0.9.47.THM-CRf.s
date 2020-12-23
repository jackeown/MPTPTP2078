%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:09 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 102 expanded)
%              Number of leaves         :   26 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :   46 ( 174 expanded)
%              Number of equality atoms :   17 (  50 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_72,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_mcart_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_49,axiom,(
    ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(f_34,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_22,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_1'(A_15),A_15)
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_8,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_31,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_26])).

tff(c_74,plain,(
    ! [C_40,B_41,A_42] :
      ( ~ v1_xboole_0(C_40)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(C_40))
      | ~ r2_hidden(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_76,plain,(
    ! [A_42] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_42,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_31,c_74])).

tff(c_83,plain,(
    ! [A_43] : ~ r2_hidden(A_43,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_76])).

tff(c_88,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22,c_83])).

tff(c_16,plain,(
    ! [A_10] : k10_relat_1(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_93,plain,(
    ! [A_10] : k10_relat_1('#skF_4',A_10) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_88,c_16])).

tff(c_10,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_96,plain,(
    ! [A_3] : m1_subset_1('#skF_4',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_10])).

tff(c_149,plain,(
    ! [A_52,B_53,C_54,D_55] :
      ( k8_relset_1(A_52,B_53,C_54,D_55) = k10_relat_1(C_54,D_55)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_156,plain,(
    ! [A_52,B_53,D_55] : k8_relset_1(A_52,B_53,'#skF_4',D_55) = k10_relat_1('#skF_4',D_55) ),
    inference(resolution,[status(thm)],[c_96,c_149])).

tff(c_158,plain,(
    ! [A_52,B_53,D_55] : k8_relset_1(A_52,B_53,'#skF_4',D_55) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_156])).

tff(c_24,plain,(
    k8_relset_1(k1_xboole_0,'#skF_2','#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_90,plain,(
    k8_relset_1('#skF_4','#skF_2','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_88,c_24])).

tff(c_161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_90])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:04:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.26  
% 1.93/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.27  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 1.93/1.27  
% 1.93/1.27  %Foreground sorts:
% 1.93/1.27  
% 1.93/1.27  
% 1.93/1.27  %Background operators:
% 1.93/1.27  
% 1.93/1.27  
% 1.93/1.27  %Foreground operators:
% 1.93/1.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.93/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.27  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.93/1.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.93/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.93/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.93/1.27  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.27  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.93/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.27  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.93/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.93/1.27  tff('#skF_4', type, '#skF_4': $i).
% 1.93/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.93/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.93/1.27  
% 1.93/1.28  tff(f_72, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_mcart_1)).
% 1.93/1.28  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.93/1.28  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.93/1.28  tff(f_81, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_2)).
% 1.93/1.28  tff(f_47, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 1.93/1.28  tff(f_49, axiom, (![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 1.93/1.28  tff(f_34, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 1.93/1.28  tff(f_53, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 1.93/1.28  tff(c_22, plain, (![A_15]: (r2_hidden('#skF_1'(A_15), A_15) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.93/1.28  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.93/1.28  tff(c_8, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.93/1.28  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.93/1.28  tff(c_31, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_26])).
% 1.93/1.28  tff(c_74, plain, (![C_40, B_41, A_42]: (~v1_xboole_0(C_40) | ~m1_subset_1(B_41, k1_zfmisc_1(C_40)) | ~r2_hidden(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.93/1.28  tff(c_76, plain, (![A_42]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_42, '#skF_4'))), inference(resolution, [status(thm)], [c_31, c_74])).
% 1.93/1.28  tff(c_83, plain, (![A_43]: (~r2_hidden(A_43, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_76])).
% 1.93/1.28  tff(c_88, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_22, c_83])).
% 1.93/1.28  tff(c_16, plain, (![A_10]: (k10_relat_1(k1_xboole_0, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.93/1.28  tff(c_93, plain, (![A_10]: (k10_relat_1('#skF_4', A_10)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_88, c_16])).
% 1.93/1.28  tff(c_10, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.93/1.28  tff(c_96, plain, (![A_3]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_10])).
% 1.93/1.28  tff(c_149, plain, (![A_52, B_53, C_54, D_55]: (k8_relset_1(A_52, B_53, C_54, D_55)=k10_relat_1(C_54, D_55) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.93/1.28  tff(c_156, plain, (![A_52, B_53, D_55]: (k8_relset_1(A_52, B_53, '#skF_4', D_55)=k10_relat_1('#skF_4', D_55))), inference(resolution, [status(thm)], [c_96, c_149])).
% 1.93/1.28  tff(c_158, plain, (![A_52, B_53, D_55]: (k8_relset_1(A_52, B_53, '#skF_4', D_55)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_156])).
% 1.93/1.28  tff(c_24, plain, (k8_relset_1(k1_xboole_0, '#skF_2', '#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.93/1.28  tff(c_90, plain, (k8_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_88, c_24])).
% 1.93/1.28  tff(c_161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_158, c_90])).
% 1.93/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.28  
% 1.93/1.28  Inference rules
% 1.93/1.28  ----------------------
% 1.93/1.28  #Ref     : 0
% 1.93/1.28  #Sup     : 29
% 1.93/1.28  #Fact    : 0
% 1.93/1.28  #Define  : 0
% 1.93/1.28  #Split   : 0
% 1.93/1.28  #Chain   : 0
% 1.93/1.28  #Close   : 0
% 1.93/1.28  
% 1.93/1.28  Ordering : KBO
% 1.93/1.28  
% 1.93/1.28  Simplification rules
% 1.93/1.28  ----------------------
% 1.93/1.28  #Subsume      : 3
% 1.93/1.28  #Demod        : 22
% 1.93/1.28  #Tautology    : 22
% 1.93/1.28  #SimpNegUnit  : 0
% 1.93/1.28  #BackRed      : 11
% 1.93/1.28  
% 1.93/1.28  #Partial instantiations: 0
% 1.93/1.28  #Strategies tried      : 1
% 1.93/1.28  
% 1.93/1.28  Timing (in seconds)
% 1.93/1.28  ----------------------
% 1.93/1.28  Preprocessing        : 0.32
% 1.93/1.28  Parsing              : 0.17
% 1.93/1.28  CNF conversion       : 0.02
% 1.93/1.28  Main loop            : 0.13
% 1.93/1.28  Inferencing          : 0.05
% 1.93/1.28  Reduction            : 0.04
% 1.93/1.28  Demodulation         : 0.03
% 1.93/1.28  BG Simplification    : 0.01
% 1.93/1.28  Subsumption          : 0.02
% 1.93/1.28  Abstraction          : 0.01
% 1.93/1.28  MUC search           : 0.00
% 1.93/1.28  Cooper               : 0.00
% 1.93/1.28  Total                : 0.47
% 1.93/1.28  Index Insertion      : 0.00
% 1.93/1.28  Index Deletion       : 0.00
% 1.93/1.28  Index Matching       : 0.00
% 1.93/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
