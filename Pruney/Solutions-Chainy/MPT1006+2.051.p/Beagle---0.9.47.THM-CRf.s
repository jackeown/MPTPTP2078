%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:09 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 102 expanded)
%              Number of leaves         :   26 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :   44 ( 164 expanded)
%              Number of equality atoms :   17 (  50 expanded)
%              Maximal formula depth    :   11 (   3 average)
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

tff(f_68,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_mcart_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_77,negated_conjecture,(
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
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_8,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_31,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_26])).

tff(c_74,plain,(
    ! [C_32,B_33,A_34] :
      ( ~ v1_xboole_0(C_32)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(C_32))
      | ~ r2_hidden(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_76,plain,(
    ! [A_34] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_34,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_31,c_74])).

tff(c_83,plain,(
    ! [A_35] : ~ r2_hidden(A_35,'#skF_4') ),
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

tff(c_172,plain,(
    ! [A_51,B_52,C_53,D_54] :
      ( k8_relset_1(A_51,B_52,C_53,D_54) = k10_relat_1(C_53,D_54)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_179,plain,(
    ! [A_51,B_52,D_54] : k8_relset_1(A_51,B_52,'#skF_4',D_54) = k10_relat_1('#skF_4',D_54) ),
    inference(resolution,[status(thm)],[c_96,c_172])).

tff(c_181,plain,(
    ! [A_51,B_52,D_54] : k8_relset_1(A_51,B_52,'#skF_4',D_54) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_179])).

tff(c_24,plain,(
    k8_relset_1(k1_xboole_0,'#skF_2','#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_90,plain,(
    k8_relset_1('#skF_4','#skF_2','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_88,c_24])).

tff(c_190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_90])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:41:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.14  
% 1.72/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.14  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 1.72/1.14  
% 1.72/1.14  %Foreground sorts:
% 1.72/1.14  
% 1.72/1.14  
% 1.72/1.14  %Background operators:
% 1.72/1.14  
% 1.72/1.14  
% 1.72/1.14  %Foreground operators:
% 1.72/1.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.72/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.72/1.14  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.72/1.14  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.72/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.72/1.14  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.72/1.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.72/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.72/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.72/1.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.72/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.14  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.72/1.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.72/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.72/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.72/1.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.72/1.14  
% 1.72/1.15  tff(f_68, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ((r2_hidden(C, D) & r2_hidden(D, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_mcart_1)).
% 1.72/1.15  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.72/1.15  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.72/1.15  tff(f_77, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_2)).
% 1.72/1.15  tff(f_47, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 1.72/1.15  tff(f_49, axiom, (![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 1.72/1.15  tff(f_34, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 1.72/1.15  tff(f_53, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 1.72/1.15  tff(c_22, plain, (![A_15]: (r2_hidden('#skF_1'(A_15), A_15) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.72/1.15  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.72/1.15  tff(c_8, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.72/1.15  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.72/1.15  tff(c_31, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_26])).
% 1.72/1.15  tff(c_74, plain, (![C_32, B_33, A_34]: (~v1_xboole_0(C_32) | ~m1_subset_1(B_33, k1_zfmisc_1(C_32)) | ~r2_hidden(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.72/1.15  tff(c_76, plain, (![A_34]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_34, '#skF_4'))), inference(resolution, [status(thm)], [c_31, c_74])).
% 1.72/1.15  tff(c_83, plain, (![A_35]: (~r2_hidden(A_35, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_76])).
% 1.72/1.15  tff(c_88, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_22, c_83])).
% 1.72/1.15  tff(c_16, plain, (![A_10]: (k10_relat_1(k1_xboole_0, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.72/1.15  tff(c_93, plain, (![A_10]: (k10_relat_1('#skF_4', A_10)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_88, c_16])).
% 1.72/1.15  tff(c_10, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.72/1.15  tff(c_96, plain, (![A_3]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_10])).
% 1.72/1.15  tff(c_172, plain, (![A_51, B_52, C_53, D_54]: (k8_relset_1(A_51, B_52, C_53, D_54)=k10_relat_1(C_53, D_54) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.72/1.15  tff(c_179, plain, (![A_51, B_52, D_54]: (k8_relset_1(A_51, B_52, '#skF_4', D_54)=k10_relat_1('#skF_4', D_54))), inference(resolution, [status(thm)], [c_96, c_172])).
% 1.72/1.15  tff(c_181, plain, (![A_51, B_52, D_54]: (k8_relset_1(A_51, B_52, '#skF_4', D_54)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_179])).
% 1.72/1.15  tff(c_24, plain, (k8_relset_1(k1_xboole_0, '#skF_2', '#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.72/1.15  tff(c_90, plain, (k8_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_88, c_24])).
% 1.72/1.15  tff(c_190, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_181, c_90])).
% 1.72/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.15  
% 1.72/1.15  Inference rules
% 1.72/1.15  ----------------------
% 1.72/1.15  #Ref     : 0
% 1.72/1.15  #Sup     : 34
% 1.72/1.15  #Fact    : 0
% 1.72/1.15  #Define  : 0
% 1.72/1.15  #Split   : 0
% 1.72/1.15  #Chain   : 0
% 1.72/1.15  #Close   : 0
% 1.72/1.15  
% 1.72/1.15  Ordering : KBO
% 1.72/1.15  
% 1.72/1.15  Simplification rules
% 1.72/1.15  ----------------------
% 1.72/1.15  #Subsume      : 3
% 1.72/1.15  #Demod        : 24
% 1.72/1.15  #Tautology    : 24
% 1.72/1.15  #SimpNegUnit  : 0
% 1.72/1.15  #BackRed      : 11
% 1.72/1.15  
% 1.72/1.15  #Partial instantiations: 0
% 1.72/1.15  #Strategies tried      : 1
% 1.72/1.15  
% 1.72/1.15  Timing (in seconds)
% 1.72/1.15  ----------------------
% 1.72/1.15  Preprocessing        : 0.30
% 1.72/1.15  Parsing              : 0.16
% 1.72/1.15  CNF conversion       : 0.02
% 1.72/1.15  Main loop            : 0.13
% 1.72/1.15  Inferencing          : 0.05
% 1.72/1.15  Reduction            : 0.05
% 1.72/1.15  Demodulation         : 0.03
% 1.72/1.15  BG Simplification    : 0.01
% 1.72/1.15  Subsumption          : 0.02
% 1.72/1.15  Abstraction          : 0.01
% 1.72/1.15  MUC search           : 0.00
% 1.72/1.15  Cooper               : 0.00
% 1.72/1.15  Total                : 0.46
% 1.72/1.15  Index Insertion      : 0.00
% 1.72/1.15  Index Deletion       : 0.00
% 1.72/1.15  Index Matching       : 0.00
% 1.72/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
