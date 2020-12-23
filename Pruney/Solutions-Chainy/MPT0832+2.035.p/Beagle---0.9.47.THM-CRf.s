%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:45 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
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
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k6_relset_1,type,(
    k6_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_57,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => m1_subset_1(k6_relset_1(C,A,B,D),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_relset_1)).

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
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k6_relset_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    ! [B_22,A_23] :
      ( v1_relat_1(B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_23))
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_21,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_16,c_18])).

tff(c_24,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_21])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_6,B_7)),A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_26,plain,(
    ! [A_26,B_27,C_28,D_29] :
      ( k6_relset_1(A_26,B_27,C_28,D_29) = k8_relat_1(C_28,D_29)
      | ~ m1_subset_1(D_29,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_29,plain,(
    ! [C_28] : k6_relset_1('#skF_3','#skF_1',C_28,'#skF_4') = k8_relat_1(C_28,'#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_26])).

tff(c_40,plain,(
    ! [A_31,B_32,C_33,D_34] :
      ( m1_subset_1(k6_relset_1(A_31,B_32,C_33,D_34),k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ m1_subset_1(D_34,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_48,plain,(
    ! [C_28] :
      ( m1_subset_1(k8_relat_1(C_28,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29,c_40])).

tff(c_54,plain,(
    ! [C_28] : m1_subset_1(k8_relat_1(C_28,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_48])).

tff(c_93,plain,(
    ! [D_45,C_46,B_47,A_48] :
      ( m1_subset_1(D_45,k1_zfmisc_1(k2_zfmisc_1(C_46,B_47)))
      | ~ r1_tarski(k2_relat_1(D_45),B_47)
      | ~ m1_subset_1(D_45,k1_zfmisc_1(k2_zfmisc_1(C_46,A_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_139,plain,(
    ! [C_61,B_62] :
      ( m1_subset_1(k8_relat_1(C_61,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_62)))
      | ~ r1_tarski(k2_relat_1(k8_relat_1(C_61,'#skF_4')),B_62) ) ),
    inference(resolution,[status(thm)],[c_54,c_93])).

tff(c_14,plain,(
    ~ m1_subset_1(k6_relset_1('#skF_3','#skF_1','#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    ~ m1_subset_1(k8_relat_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_14])).

tff(c_154,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_139,c_30])).

tff(c_161,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_154])).

tff(c_165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_161])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:27:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.33  
% 2.08/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.33  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.08/1.33  
% 2.08/1.33  %Foreground sorts:
% 2.08/1.33  
% 2.08/1.33  
% 2.08/1.33  %Background operators:
% 2.08/1.33  
% 2.08/1.33  
% 2.08/1.33  %Foreground operators:
% 2.08/1.33  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.08/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.08/1.33  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.08/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.08/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.08/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.08/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.08/1.33  
% 2.08/1.34  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.08/1.34  tff(f_57, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => m1_subset_1(k6_relset_1(C, A, B, D), k1_zfmisc_1(k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_relset_1)).
% 2.08/1.34  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.08/1.34  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_relat_1)).
% 2.08/1.34  tff(f_46, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.08/1.34  tff(f_42, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k6_relset_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relset_1)).
% 2.08/1.34  tff(f_52, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 2.08/1.34  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.08/1.34  tff(c_16, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.08/1.34  tff(c_18, plain, (![B_22, A_23]: (v1_relat_1(B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(A_23)) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.08/1.34  tff(c_21, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_16, c_18])).
% 2.08/1.34  tff(c_24, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_21])).
% 2.08/1.34  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k2_relat_1(k8_relat_1(A_6, B_7)), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.08/1.34  tff(c_26, plain, (![A_26, B_27, C_28, D_29]: (k6_relset_1(A_26, B_27, C_28, D_29)=k8_relat_1(C_28, D_29) | ~m1_subset_1(D_29, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.08/1.34  tff(c_29, plain, (![C_28]: (k6_relset_1('#skF_3', '#skF_1', C_28, '#skF_4')=k8_relat_1(C_28, '#skF_4'))), inference(resolution, [status(thm)], [c_16, c_26])).
% 2.08/1.34  tff(c_40, plain, (![A_31, B_32, C_33, D_34]: (m1_subset_1(k6_relset_1(A_31, B_32, C_33, D_34), k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~m1_subset_1(D_34, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.08/1.34  tff(c_48, plain, (![C_28]: (m1_subset_1(k8_relat_1(C_28, '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_29, c_40])).
% 2.08/1.34  tff(c_54, plain, (![C_28]: (m1_subset_1(k8_relat_1(C_28, '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_48])).
% 2.08/1.34  tff(c_93, plain, (![D_45, C_46, B_47, A_48]: (m1_subset_1(D_45, k1_zfmisc_1(k2_zfmisc_1(C_46, B_47))) | ~r1_tarski(k2_relat_1(D_45), B_47) | ~m1_subset_1(D_45, k1_zfmisc_1(k2_zfmisc_1(C_46, A_48))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.08/1.34  tff(c_139, plain, (![C_61, B_62]: (m1_subset_1(k8_relat_1(C_61, '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_62))) | ~r1_tarski(k2_relat_1(k8_relat_1(C_61, '#skF_4')), B_62))), inference(resolution, [status(thm)], [c_54, c_93])).
% 2.08/1.34  tff(c_14, plain, (~m1_subset_1(k6_relset_1('#skF_3', '#skF_1', '#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.08/1.34  tff(c_30, plain, (~m1_subset_1(k8_relat_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_29, c_14])).
% 2.08/1.34  tff(c_154, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2')), inference(resolution, [status(thm)], [c_139, c_30])).
% 2.08/1.34  tff(c_161, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6, c_154])).
% 2.08/1.34  tff(c_165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_161])).
% 2.08/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.34  
% 2.08/1.34  Inference rules
% 2.08/1.34  ----------------------
% 2.08/1.34  #Ref     : 0
% 2.08/1.34  #Sup     : 32
% 2.08/1.34  #Fact    : 0
% 2.08/1.34  #Define  : 0
% 2.08/1.34  #Split   : 0
% 2.08/1.34  #Chain   : 0
% 2.08/1.34  #Close   : 0
% 2.08/1.34  
% 2.08/1.34  Ordering : KBO
% 2.08/1.34  
% 2.08/1.34  Simplification rules
% 2.08/1.34  ----------------------
% 2.08/1.34  #Subsume      : 2
% 2.08/1.34  #Demod        : 16
% 2.08/1.34  #Tautology    : 8
% 2.08/1.34  #SimpNegUnit  : 0
% 2.08/1.34  #BackRed      : 2
% 2.08/1.34  
% 2.08/1.34  #Partial instantiations: 0
% 2.08/1.34  #Strategies tried      : 1
% 2.08/1.34  
% 2.08/1.34  Timing (in seconds)
% 2.08/1.34  ----------------------
% 2.08/1.34  Preprocessing        : 0.35
% 2.08/1.34  Parsing              : 0.19
% 2.08/1.34  CNF conversion       : 0.02
% 2.08/1.34  Main loop            : 0.16
% 2.08/1.34  Inferencing          : 0.07
% 2.08/1.34  Reduction            : 0.05
% 2.08/1.34  Demodulation         : 0.04
% 2.08/1.34  BG Simplification    : 0.01
% 2.08/1.34  Subsumption          : 0.02
% 2.08/1.34  Abstraction          : 0.01
% 2.08/1.34  MUC search           : 0.00
% 2.08/1.34  Cooper               : 0.00
% 2.08/1.35  Total                : 0.54
% 2.08/1.35  Index Insertion      : 0.00
% 2.08/1.35  Index Deletion       : 0.00
% 2.08/1.35  Index Matching       : 0.00
% 2.08/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
