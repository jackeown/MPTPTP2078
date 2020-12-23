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
% DateTime   : Thu Dec  3 10:07:45 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   43 (  56 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   56 (  78 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   10 (   4 average)
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

tff(f_63,negated_conjecture,(
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

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ( r1_tarski(A,D)
       => m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_18,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_21,plain,(
    ! [B_26,A_27] :
      ( v1_relat_1(B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_27))
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_24,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_18,c_21])).

tff(c_27,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_24])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_6,B_7)),A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(k8_relat_1(A_8,B_9),B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_43,plain,(
    ! [A_35,B_36,C_37,D_38] :
      ( m1_subset_1(A_35,k1_zfmisc_1(k2_zfmisc_1(B_36,C_37)))
      | ~ r1_tarski(A_35,D_38)
      | ~ m1_subset_1(D_38,k1_zfmisc_1(k2_zfmisc_1(B_36,C_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_68,plain,(
    ! [A_46,B_47,B_48,C_49] :
      ( m1_subset_1(k8_relat_1(A_46,B_47),k1_zfmisc_1(k2_zfmisc_1(B_48,C_49)))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(k2_zfmisc_1(B_48,C_49)))
      | ~ v1_relat_1(B_47) ) ),
    inference(resolution,[status(thm)],[c_8,c_43])).

tff(c_12,plain,(
    ! [D_17,C_16,B_15,A_14] :
      ( m1_subset_1(D_17,k1_zfmisc_1(k2_zfmisc_1(C_16,B_15)))
      | ~ r1_tarski(k2_relat_1(D_17),B_15)
      | ~ m1_subset_1(D_17,k1_zfmisc_1(k2_zfmisc_1(C_16,A_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_215,plain,(
    ! [A_99,B_95,B_96,B_97,C_98] :
      ( m1_subset_1(k8_relat_1(A_99,B_95),k1_zfmisc_1(k2_zfmisc_1(B_96,B_97)))
      | ~ r1_tarski(k2_relat_1(k8_relat_1(A_99,B_95)),B_97)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(k2_zfmisc_1(B_96,C_98)))
      | ~ v1_relat_1(B_95) ) ),
    inference(resolution,[status(thm)],[c_68,c_12])).

tff(c_223,plain,(
    ! [A_99,B_97] :
      ( m1_subset_1(k8_relat_1(A_99,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_97)))
      | ~ r1_tarski(k2_relat_1(k8_relat_1(A_99,'#skF_4')),B_97)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_215])).

tff(c_232,plain,(
    ! [A_100,B_101] :
      ( m1_subset_1(k8_relat_1(A_100,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_101)))
      | ~ r1_tarski(k2_relat_1(k8_relat_1(A_100,'#skF_4')),B_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_223])).

tff(c_29,plain,(
    ! [A_30,B_31,C_32,D_33] :
      ( k6_relset_1(A_30,B_31,C_32,D_33) = k8_relat_1(C_32,D_33)
      | ~ m1_subset_1(D_33,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_32,plain,(
    ! [C_32] : k6_relset_1('#skF_3','#skF_1',C_32,'#skF_4') = k8_relat_1(C_32,'#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_29])).

tff(c_16,plain,(
    ~ m1_subset_1(k6_relset_1('#skF_3','#skF_1','#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_33,plain,(
    ~ m1_subset_1(k8_relat_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_16])).

tff(c_275,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_232,c_33])).

tff(c_282,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_275])).

tff(c_286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_282])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 20:22:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.35  
% 2.31/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.35  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.31/1.35  
% 2.31/1.35  %Foreground sorts:
% 2.31/1.35  
% 2.31/1.35  
% 2.31/1.35  %Background operators:
% 2.31/1.35  
% 2.31/1.35  
% 2.31/1.35  %Foreground operators:
% 2.31/1.35  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.31/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.31/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.31/1.35  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.31/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.31/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.31/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.31/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.31/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.31/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.31/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.31/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.31/1.35  
% 2.52/1.36  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.52/1.36  tff(f_63, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => m1_subset_1(k6_relset_1(C, A, B, D), k1_zfmisc_1(k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_relset_1)).
% 2.52/1.36  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.52/1.36  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_relat_1)).
% 2.52/1.36  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 2.52/1.36  tff(f_58, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => (r1_tarski(A, D) => m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_relset_1)).
% 2.52/1.36  tff(f_52, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 2.52/1.36  tff(f_46, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.52/1.36  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.52/1.36  tff(c_18, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.52/1.36  tff(c_21, plain, (![B_26, A_27]: (v1_relat_1(B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(A_27)) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.52/1.36  tff(c_24, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_18, c_21])).
% 2.52/1.36  tff(c_27, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_24])).
% 2.52/1.36  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k2_relat_1(k8_relat_1(A_6, B_7)), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.52/1.36  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(k8_relat_1(A_8, B_9), B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.52/1.36  tff(c_43, plain, (![A_35, B_36, C_37, D_38]: (m1_subset_1(A_35, k1_zfmisc_1(k2_zfmisc_1(B_36, C_37))) | ~r1_tarski(A_35, D_38) | ~m1_subset_1(D_38, k1_zfmisc_1(k2_zfmisc_1(B_36, C_37))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.52/1.36  tff(c_68, plain, (![A_46, B_47, B_48, C_49]: (m1_subset_1(k8_relat_1(A_46, B_47), k1_zfmisc_1(k2_zfmisc_1(B_48, C_49))) | ~m1_subset_1(B_47, k1_zfmisc_1(k2_zfmisc_1(B_48, C_49))) | ~v1_relat_1(B_47))), inference(resolution, [status(thm)], [c_8, c_43])).
% 2.52/1.36  tff(c_12, plain, (![D_17, C_16, B_15, A_14]: (m1_subset_1(D_17, k1_zfmisc_1(k2_zfmisc_1(C_16, B_15))) | ~r1_tarski(k2_relat_1(D_17), B_15) | ~m1_subset_1(D_17, k1_zfmisc_1(k2_zfmisc_1(C_16, A_14))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.52/1.36  tff(c_215, plain, (![A_99, B_95, B_96, B_97, C_98]: (m1_subset_1(k8_relat_1(A_99, B_95), k1_zfmisc_1(k2_zfmisc_1(B_96, B_97))) | ~r1_tarski(k2_relat_1(k8_relat_1(A_99, B_95)), B_97) | ~m1_subset_1(B_95, k1_zfmisc_1(k2_zfmisc_1(B_96, C_98))) | ~v1_relat_1(B_95))), inference(resolution, [status(thm)], [c_68, c_12])).
% 2.52/1.36  tff(c_223, plain, (![A_99, B_97]: (m1_subset_1(k8_relat_1(A_99, '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_97))) | ~r1_tarski(k2_relat_1(k8_relat_1(A_99, '#skF_4')), B_97) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_215])).
% 2.52/1.36  tff(c_232, plain, (![A_100, B_101]: (m1_subset_1(k8_relat_1(A_100, '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_101))) | ~r1_tarski(k2_relat_1(k8_relat_1(A_100, '#skF_4')), B_101))), inference(demodulation, [status(thm), theory('equality')], [c_27, c_223])).
% 2.52/1.36  tff(c_29, plain, (![A_30, B_31, C_32, D_33]: (k6_relset_1(A_30, B_31, C_32, D_33)=k8_relat_1(C_32, D_33) | ~m1_subset_1(D_33, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.52/1.36  tff(c_32, plain, (![C_32]: (k6_relset_1('#skF_3', '#skF_1', C_32, '#skF_4')=k8_relat_1(C_32, '#skF_4'))), inference(resolution, [status(thm)], [c_18, c_29])).
% 2.52/1.36  tff(c_16, plain, (~m1_subset_1(k6_relset_1('#skF_3', '#skF_1', '#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.52/1.36  tff(c_33, plain, (~m1_subset_1(k8_relat_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_16])).
% 2.52/1.36  tff(c_275, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2')), inference(resolution, [status(thm)], [c_232, c_33])).
% 2.52/1.36  tff(c_282, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6, c_275])).
% 2.52/1.36  tff(c_286, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27, c_282])).
% 2.52/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.36  
% 2.52/1.36  Inference rules
% 2.52/1.36  ----------------------
% 2.52/1.36  #Ref     : 0
% 2.52/1.36  #Sup     : 60
% 2.52/1.36  #Fact    : 0
% 2.52/1.36  #Define  : 0
% 2.52/1.36  #Split   : 0
% 2.52/1.36  #Chain   : 0
% 2.52/1.36  #Close   : 0
% 2.52/1.36  
% 2.52/1.36  Ordering : KBO
% 2.52/1.36  
% 2.52/1.36  Simplification rules
% 2.52/1.36  ----------------------
% 2.52/1.36  #Subsume      : 5
% 2.52/1.36  #Demod        : 31
% 2.52/1.36  #Tautology    : 9
% 2.52/1.36  #SimpNegUnit  : 0
% 2.52/1.36  #BackRed      : 1
% 2.52/1.36  
% 2.52/1.36  #Partial instantiations: 0
% 2.52/1.36  #Strategies tried      : 1
% 2.52/1.36  
% 2.52/1.36  Timing (in seconds)
% 2.52/1.36  ----------------------
% 2.52/1.37  Preprocessing        : 0.28
% 2.52/1.37  Parsing              : 0.14
% 2.52/1.37  CNF conversion       : 0.02
% 2.52/1.37  Main loop            : 0.24
% 2.52/1.37  Inferencing          : 0.09
% 2.52/1.37  Reduction            : 0.07
% 2.52/1.37  Demodulation         : 0.05
% 2.52/1.37  BG Simplification    : 0.01
% 2.52/1.37  Subsumption          : 0.05
% 2.52/1.37  Abstraction          : 0.02
% 2.52/1.37  MUC search           : 0.00
% 2.52/1.37  Cooper               : 0.00
% 2.52/1.37  Total                : 0.55
% 2.52/1.37  Index Insertion      : 0.00
% 2.52/1.37  Index Deletion       : 0.00
% 2.52/1.37  Index Matching       : 0.00
% 2.52/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
