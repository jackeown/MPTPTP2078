%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:32 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   40 (  50 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   43 (  59 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_57,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k5_relset_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    ! [B_22,A_23] :
      ( v1_relat_1(B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_23))
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_21,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_18])).

tff(c_24,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_21])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_7,A_6)),A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_26,plain,(
    ! [A_26,B_27,C_28,D_29] :
      ( k5_relset_1(A_26,B_27,C_28,D_29) = k7_relat_1(C_28,D_29)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_29,plain,(
    ! [D_29] : k5_relset_1('#skF_1','#skF_3','#skF_4',D_29) = k7_relat_1('#skF_4',D_29) ),
    inference(resolution,[status(thm)],[c_16,c_26])).

tff(c_40,plain,(
    ! [A_31,B_32,C_33,D_34] :
      ( m1_subset_1(k5_relset_1(A_31,B_32,C_33,D_34),k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_48,plain,(
    ! [D_29] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_29),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29,c_40])).

tff(c_54,plain,(
    ! [D_29] : m1_subset_1(k7_relat_1('#skF_4',D_29),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_48])).

tff(c_93,plain,(
    ! [D_45,B_46,C_47,A_48] :
      ( m1_subset_1(D_45,k1_zfmisc_1(k2_zfmisc_1(B_46,C_47)))
      | ~ r1_tarski(k1_relat_1(D_45),B_46)
      | ~ m1_subset_1(D_45,k1_zfmisc_1(k2_zfmisc_1(A_48,C_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_139,plain,(
    ! [D_61,B_62] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_61),k1_zfmisc_1(k2_zfmisc_1(B_62,'#skF_3')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4',D_61)),B_62) ) ),
    inference(resolution,[status(thm)],[c_54,c_93])).

tff(c_14,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_1','#skF_3','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_14])).

tff(c_154,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_139,c_30])).

tff(c_161,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_154])).

tff(c_165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_161])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n025.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 20:55:36 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.16/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.51  
% 2.32/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.52  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.32/1.52  
% 2.32/1.52  %Foreground sorts:
% 2.32/1.52  
% 2.32/1.52  
% 2.32/1.52  %Background operators:
% 2.32/1.52  
% 2.32/1.52  
% 2.32/1.52  %Foreground operators:
% 2.32/1.52  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.32/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.52  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.32/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.32/1.52  tff('#skF_2', type, '#skF_2': $i).
% 2.32/1.52  tff('#skF_3', type, '#skF_3': $i).
% 2.32/1.52  tff('#skF_1', type, '#skF_1': $i).
% 2.32/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.32/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.32/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.32/1.52  tff('#skF_4', type, '#skF_4': $i).
% 2.32/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.32/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.32/1.52  
% 2.32/1.53  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.32/1.53  tff(f_57, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_relset_1)).
% 2.32/1.53  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.32/1.53  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.32/1.53  tff(f_46, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.32/1.53  tff(f_42, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k5_relset_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relset_1)).
% 2.32/1.53  tff(f_52, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 2.32/1.53  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.32/1.53  tff(c_16, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.32/1.53  tff(c_18, plain, (![B_22, A_23]: (v1_relat_1(B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(A_23)) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.32/1.53  tff(c_21, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_18])).
% 2.32/1.53  tff(c_24, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_21])).
% 2.32/1.53  tff(c_6, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(k7_relat_1(B_7, A_6)), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.32/1.53  tff(c_26, plain, (![A_26, B_27, C_28, D_29]: (k5_relset_1(A_26, B_27, C_28, D_29)=k7_relat_1(C_28, D_29) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.32/1.53  tff(c_29, plain, (![D_29]: (k5_relset_1('#skF_1', '#skF_3', '#skF_4', D_29)=k7_relat_1('#skF_4', D_29))), inference(resolution, [status(thm)], [c_16, c_26])).
% 2.32/1.53  tff(c_40, plain, (![A_31, B_32, C_33, D_34]: (m1_subset_1(k5_relset_1(A_31, B_32, C_33, D_34), k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.32/1.53  tff(c_48, plain, (![D_29]: (m1_subset_1(k7_relat_1('#skF_4', D_29), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_29, c_40])).
% 2.32/1.53  tff(c_54, plain, (![D_29]: (m1_subset_1(k7_relat_1('#skF_4', D_29), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_48])).
% 2.32/1.53  tff(c_93, plain, (![D_45, B_46, C_47, A_48]: (m1_subset_1(D_45, k1_zfmisc_1(k2_zfmisc_1(B_46, C_47))) | ~r1_tarski(k1_relat_1(D_45), B_46) | ~m1_subset_1(D_45, k1_zfmisc_1(k2_zfmisc_1(A_48, C_47))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.32/1.53  tff(c_139, plain, (![D_61, B_62]: (m1_subset_1(k7_relat_1('#skF_4', D_61), k1_zfmisc_1(k2_zfmisc_1(B_62, '#skF_3'))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', D_61)), B_62))), inference(resolution, [status(thm)], [c_54, c_93])).
% 2.32/1.53  tff(c_14, plain, (~m1_subset_1(k5_relset_1('#skF_1', '#skF_3', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.32/1.53  tff(c_30, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_29, c_14])).
% 2.32/1.53  tff(c_154, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(resolution, [status(thm)], [c_139, c_30])).
% 2.32/1.53  tff(c_161, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6, c_154])).
% 2.32/1.53  tff(c_165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_161])).
% 2.32/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.53  
% 2.32/1.53  Inference rules
% 2.32/1.53  ----------------------
% 2.32/1.54  #Ref     : 0
% 2.32/1.54  #Sup     : 32
% 2.32/1.54  #Fact    : 0
% 2.32/1.54  #Define  : 0
% 2.32/1.54  #Split   : 0
% 2.32/1.54  #Chain   : 0
% 2.32/1.54  #Close   : 0
% 2.32/1.54  
% 2.32/1.54  Ordering : KBO
% 2.32/1.54  
% 2.32/1.54  Simplification rules
% 2.32/1.54  ----------------------
% 2.32/1.54  #Subsume      : 2
% 2.32/1.54  #Demod        : 16
% 2.32/1.54  #Tautology    : 8
% 2.32/1.54  #SimpNegUnit  : 0
% 2.32/1.54  #BackRed      : 2
% 2.32/1.54  
% 2.32/1.54  #Partial instantiations: 0
% 2.32/1.54  #Strategies tried      : 1
% 2.32/1.54  
% 2.32/1.54  Timing (in seconds)
% 2.32/1.54  ----------------------
% 2.39/1.54  Preprocessing        : 0.46
% 2.39/1.54  Parsing              : 0.24
% 2.39/1.54  CNF conversion       : 0.03
% 2.39/1.54  Main loop            : 0.25
% 2.39/1.54  Inferencing          : 0.11
% 2.39/1.54  Reduction            : 0.08
% 2.39/1.54  Demodulation         : 0.06
% 2.39/1.54  BG Simplification    : 0.02
% 2.39/1.54  Subsumption          : 0.04
% 2.39/1.54  Abstraction          : 0.02
% 2.39/1.54  MUC search           : 0.00
% 2.39/1.54  Cooper               : 0.00
% 2.39/1.54  Total                : 0.75
% 2.39/1.54  Index Insertion      : 0.00
% 2.39/1.54  Index Deletion       : 0.00
% 2.39/1.54  Index Matching       : 0.00
% 2.39/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
