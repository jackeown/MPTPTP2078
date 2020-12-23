%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:09 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 137 expanded)
%              Number of leaves         :   25 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :   45 ( 237 expanded)
%              Number of equality atoms :   20 (  84 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(f_61,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_41,axiom,(
    ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_16,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_1'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_8,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_29,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_24])).

tff(c_71,plain,(
    ! [C_27,B_28,A_29] :
      ( ~ v1_xboole_0(C_27)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(C_27))
      | ~ r2_hidden(A_29,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_73,plain,(
    ! [A_29] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_29,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_29,c_71])).

tff(c_77,plain,(
    ! [A_30] : ~ r2_hidden(A_30,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_73])).

tff(c_82,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_16,c_77])).

tff(c_12,plain,(
    ! [A_6] : k10_relat_1(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_86,plain,(
    ! [A_6] : k10_relat_1('#skF_4',A_6) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_82,c_12])).

tff(c_88,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_29])).

tff(c_89,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_4',B_2) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_82,c_8])).

tff(c_159,plain,(
    ! [A_45,B_46,C_47,D_48] :
      ( k8_relset_1(A_45,B_46,C_47,D_48) = k10_relat_1(C_47,D_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_177,plain,(
    ! [B_56,C_57,D_58] :
      ( k8_relset_1('#skF_4',B_56,C_57,D_58) = k10_relat_1(C_57,D_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_159])).

tff(c_179,plain,(
    ! [B_56,D_58] : k8_relset_1('#skF_4',B_56,'#skF_4',D_58) = k10_relat_1('#skF_4',D_58) ),
    inference(resolution,[status(thm)],[c_88,c_177])).

tff(c_181,plain,(
    ! [B_56,D_58] : k8_relset_1('#skF_4',B_56,'#skF_4',D_58) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_179])).

tff(c_22,plain,(
    k8_relset_1(k1_xboole_0,'#skF_2','#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_84,plain,(
    k8_relset_1('#skF_4','#skF_2','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_82,c_22])).

tff(c_184,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_84])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n025.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:15:05 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.15  
% 1.71/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.15  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 1.71/1.15  
% 1.71/1.15  %Foreground sorts:
% 1.71/1.15  
% 1.71/1.15  
% 1.71/1.15  %Background operators:
% 1.71/1.15  
% 1.71/1.15  
% 1.71/1.15  %Foreground operators:
% 1.71/1.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.71/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.71/1.15  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.71/1.15  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.71/1.15  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.71/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.71/1.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.71/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.71/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.71/1.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.71/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.15  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.71/1.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.71/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.71/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.71/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.71/1.15  
% 1.71/1.16  tff(f_61, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 1.71/1.16  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.71/1.16  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.71/1.16  tff(f_70, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_funct_2)).
% 1.71/1.16  tff(f_39, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 1.71/1.16  tff(f_41, axiom, (![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 1.71/1.16  tff(f_45, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 1.71/1.16  tff(c_16, plain, (![A_11]: (r2_hidden('#skF_1'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.71/1.16  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.71/1.16  tff(c_8, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.71/1.16  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.71/1.16  tff(c_29, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_24])).
% 1.71/1.16  tff(c_71, plain, (![C_27, B_28, A_29]: (~v1_xboole_0(C_27) | ~m1_subset_1(B_28, k1_zfmisc_1(C_27)) | ~r2_hidden(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.71/1.16  tff(c_73, plain, (![A_29]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_29, '#skF_4'))), inference(resolution, [status(thm)], [c_29, c_71])).
% 1.71/1.16  tff(c_77, plain, (![A_30]: (~r2_hidden(A_30, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_73])).
% 1.71/1.16  tff(c_82, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_16, c_77])).
% 1.71/1.16  tff(c_12, plain, (![A_6]: (k10_relat_1(k1_xboole_0, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.71/1.16  tff(c_86, plain, (![A_6]: (k10_relat_1('#skF_4', A_6)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_82, c_12])).
% 1.71/1.16  tff(c_88, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_29])).
% 1.71/1.16  tff(c_89, plain, (![B_2]: (k2_zfmisc_1('#skF_4', B_2)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_82, c_8])).
% 1.71/1.16  tff(c_159, plain, (![A_45, B_46, C_47, D_48]: (k8_relset_1(A_45, B_46, C_47, D_48)=k10_relat_1(C_47, D_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.71/1.16  tff(c_177, plain, (![B_56, C_57, D_58]: (k8_relset_1('#skF_4', B_56, C_57, D_58)=k10_relat_1(C_57, D_58) | ~m1_subset_1(C_57, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_89, c_159])).
% 1.71/1.16  tff(c_179, plain, (![B_56, D_58]: (k8_relset_1('#skF_4', B_56, '#skF_4', D_58)=k10_relat_1('#skF_4', D_58))), inference(resolution, [status(thm)], [c_88, c_177])).
% 1.71/1.16  tff(c_181, plain, (![B_56, D_58]: (k8_relset_1('#skF_4', B_56, '#skF_4', D_58)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_179])).
% 1.71/1.16  tff(c_22, plain, (k8_relset_1(k1_xboole_0, '#skF_2', '#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.71/1.16  tff(c_84, plain, (k8_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_82, c_22])).
% 1.71/1.16  tff(c_184, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_181, c_84])).
% 1.71/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.16  
% 1.71/1.16  Inference rules
% 1.71/1.16  ----------------------
% 1.71/1.16  #Ref     : 0
% 1.71/1.16  #Sup     : 34
% 1.71/1.16  #Fact    : 0
% 1.71/1.16  #Define  : 0
% 1.71/1.16  #Split   : 0
% 1.71/1.16  #Chain   : 0
% 1.71/1.16  #Close   : 0
% 1.71/1.16  
% 1.71/1.16  Ordering : KBO
% 1.71/1.16  
% 1.71/1.16  Simplification rules
% 1.71/1.16  ----------------------
% 1.71/1.16  #Subsume      : 1
% 1.71/1.16  #Demod        : 23
% 1.71/1.16  #Tautology    : 25
% 1.71/1.16  #SimpNegUnit  : 0
% 1.71/1.16  #BackRed      : 10
% 1.71/1.16  
% 1.71/1.16  #Partial instantiations: 0
% 1.71/1.16  #Strategies tried      : 1
% 1.71/1.16  
% 1.71/1.16  Timing (in seconds)
% 1.71/1.16  ----------------------
% 1.71/1.17  Preprocessing        : 0.29
% 1.71/1.17  Parsing              : 0.15
% 1.71/1.17  CNF conversion       : 0.02
% 1.71/1.17  Main loop            : 0.13
% 1.71/1.17  Inferencing          : 0.05
% 1.71/1.17  Reduction            : 0.04
% 1.71/1.17  Demodulation         : 0.03
% 1.71/1.17  BG Simplification    : 0.01
% 1.71/1.17  Subsumption          : 0.02
% 1.71/1.17  Abstraction          : 0.01
% 1.71/1.17  MUC search           : 0.00
% 1.71/1.17  Cooper               : 0.00
% 1.71/1.17  Total                : 0.44
% 1.71/1.17  Index Insertion      : 0.00
% 1.71/1.17  Index Deletion       : 0.00
% 1.71/1.17  Index Matching       : 0.00
% 1.71/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
