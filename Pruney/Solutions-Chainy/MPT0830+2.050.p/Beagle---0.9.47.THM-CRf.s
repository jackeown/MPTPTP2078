%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:32 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ( r1_tarski(A,D)
       => m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_18,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_21,plain,(
    ! [B_26,A_27] :
      ( v1_relat_1(B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_27))
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_24,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_21])).

tff(c_27,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_24])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_7,A_6)),A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k7_relat_1(B_9,A_8),B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_43,plain,(
    ! [A_35,B_36,C_37,D_38] :
      ( m1_subset_1(A_35,k1_zfmisc_1(k2_zfmisc_1(B_36,C_37)))
      | ~ r1_tarski(A_35,D_38)
      | ~ m1_subset_1(D_38,k1_zfmisc_1(k2_zfmisc_1(B_36,C_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_68,plain,(
    ! [B_46,A_47,B_48,C_49] :
      ( m1_subset_1(k7_relat_1(B_46,A_47),k1_zfmisc_1(k2_zfmisc_1(B_48,C_49)))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(k2_zfmisc_1(B_48,C_49)))
      | ~ v1_relat_1(B_46) ) ),
    inference(resolution,[status(thm)],[c_8,c_43])).

tff(c_12,plain,(
    ! [D_17,B_15,C_16,A_14] :
      ( m1_subset_1(D_17,k1_zfmisc_1(k2_zfmisc_1(B_15,C_16)))
      | ~ r1_tarski(k1_relat_1(D_17),B_15)
      | ~ m1_subset_1(D_17,k1_zfmisc_1(k2_zfmisc_1(A_14,C_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_215,plain,(
    ! [C_99,B_98,A_95,B_96,B_97] :
      ( m1_subset_1(k7_relat_1(B_96,A_95),k1_zfmisc_1(k2_zfmisc_1(B_98,C_99)))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_96,A_95)),B_98)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(k2_zfmisc_1(B_97,C_99)))
      | ~ v1_relat_1(B_96) ) ),
    inference(resolution,[status(thm)],[c_68,c_12])).

tff(c_223,plain,(
    ! [A_95,B_98] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_95),k1_zfmisc_1(k2_zfmisc_1(B_98,'#skF_3')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_95)),B_98)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_215])).

tff(c_232,plain,(
    ! [A_100,B_101] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_100),k1_zfmisc_1(k2_zfmisc_1(B_101,'#skF_3')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_100)),B_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_223])).

tff(c_29,plain,(
    ! [A_30,B_31,C_32,D_33] :
      ( k5_relset_1(A_30,B_31,C_32,D_33) = k7_relat_1(C_32,D_33)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_32,plain,(
    ! [D_33] : k5_relset_1('#skF_1','#skF_3','#skF_4',D_33) = k7_relat_1('#skF_4',D_33) ),
    inference(resolution,[status(thm)],[c_18,c_29])).

tff(c_16,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_1','#skF_3','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_33,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_16])).

tff(c_275,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_232,c_33])).

tff(c_282,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_275])).

tff(c_286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_282])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.18/0.33  % CPULimit   : 60
% 0.18/0.33  % DateTime   : Tue Dec  1 20:41:04 EST 2020
% 0.18/0.34  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.44  
% 2.18/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.44  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.18/1.44  
% 2.18/1.44  %Foreground sorts:
% 2.18/1.44  
% 2.18/1.44  
% 2.18/1.44  %Background operators:
% 2.18/1.44  
% 2.18/1.44  
% 2.18/1.44  %Foreground operators:
% 2.18/1.44  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.18/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.44  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.18/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.18/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.18/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.18/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.18/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.44  
% 2.18/1.45  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.18/1.45  tff(f_63, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_relset_1)).
% 2.18/1.45  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.18/1.45  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.18/1.45  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 2.18/1.45  tff(f_58, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => (r1_tarski(A, D) => m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_relset_1)).
% 2.18/1.45  tff(f_52, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 2.18/1.45  tff(f_46, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.18/1.45  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.18/1.45  tff(c_18, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.18/1.45  tff(c_21, plain, (![B_26, A_27]: (v1_relat_1(B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(A_27)) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.18/1.45  tff(c_24, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_21])).
% 2.18/1.45  tff(c_27, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_24])).
% 2.18/1.45  tff(c_6, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(k7_relat_1(B_7, A_6)), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.18/1.45  tff(c_8, plain, (![B_9, A_8]: (r1_tarski(k7_relat_1(B_9, A_8), B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.18/1.45  tff(c_43, plain, (![A_35, B_36, C_37, D_38]: (m1_subset_1(A_35, k1_zfmisc_1(k2_zfmisc_1(B_36, C_37))) | ~r1_tarski(A_35, D_38) | ~m1_subset_1(D_38, k1_zfmisc_1(k2_zfmisc_1(B_36, C_37))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.18/1.45  tff(c_68, plain, (![B_46, A_47, B_48, C_49]: (m1_subset_1(k7_relat_1(B_46, A_47), k1_zfmisc_1(k2_zfmisc_1(B_48, C_49))) | ~m1_subset_1(B_46, k1_zfmisc_1(k2_zfmisc_1(B_48, C_49))) | ~v1_relat_1(B_46))), inference(resolution, [status(thm)], [c_8, c_43])).
% 2.18/1.45  tff(c_12, plain, (![D_17, B_15, C_16, A_14]: (m1_subset_1(D_17, k1_zfmisc_1(k2_zfmisc_1(B_15, C_16))) | ~r1_tarski(k1_relat_1(D_17), B_15) | ~m1_subset_1(D_17, k1_zfmisc_1(k2_zfmisc_1(A_14, C_16))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.18/1.45  tff(c_215, plain, (![C_99, B_98, A_95, B_96, B_97]: (m1_subset_1(k7_relat_1(B_96, A_95), k1_zfmisc_1(k2_zfmisc_1(B_98, C_99))) | ~r1_tarski(k1_relat_1(k7_relat_1(B_96, A_95)), B_98) | ~m1_subset_1(B_96, k1_zfmisc_1(k2_zfmisc_1(B_97, C_99))) | ~v1_relat_1(B_96))), inference(resolution, [status(thm)], [c_68, c_12])).
% 2.18/1.45  tff(c_223, plain, (![A_95, B_98]: (m1_subset_1(k7_relat_1('#skF_4', A_95), k1_zfmisc_1(k2_zfmisc_1(B_98, '#skF_3'))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_95)), B_98) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_215])).
% 2.18/1.45  tff(c_232, plain, (![A_100, B_101]: (m1_subset_1(k7_relat_1('#skF_4', A_100), k1_zfmisc_1(k2_zfmisc_1(B_101, '#skF_3'))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_100)), B_101))), inference(demodulation, [status(thm), theory('equality')], [c_27, c_223])).
% 2.18/1.45  tff(c_29, plain, (![A_30, B_31, C_32, D_33]: (k5_relset_1(A_30, B_31, C_32, D_33)=k7_relat_1(C_32, D_33) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.18/1.45  tff(c_32, plain, (![D_33]: (k5_relset_1('#skF_1', '#skF_3', '#skF_4', D_33)=k7_relat_1('#skF_4', D_33))), inference(resolution, [status(thm)], [c_18, c_29])).
% 2.18/1.45  tff(c_16, plain, (~m1_subset_1(k5_relset_1('#skF_1', '#skF_3', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.18/1.45  tff(c_33, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_16])).
% 2.18/1.45  tff(c_275, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(resolution, [status(thm)], [c_232, c_33])).
% 2.18/1.45  tff(c_282, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6, c_275])).
% 2.18/1.45  tff(c_286, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27, c_282])).
% 2.18/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.45  
% 2.18/1.45  Inference rules
% 2.18/1.45  ----------------------
% 2.18/1.45  #Ref     : 0
% 2.18/1.45  #Sup     : 60
% 2.18/1.45  #Fact    : 0
% 2.18/1.45  #Define  : 0
% 2.18/1.45  #Split   : 0
% 2.18/1.45  #Chain   : 0
% 2.18/1.45  #Close   : 0
% 2.18/1.45  
% 2.18/1.45  Ordering : KBO
% 2.18/1.45  
% 2.18/1.45  Simplification rules
% 2.18/1.45  ----------------------
% 2.18/1.45  #Subsume      : 5
% 2.18/1.45  #Demod        : 31
% 2.18/1.45  #Tautology    : 9
% 2.18/1.45  #SimpNegUnit  : 0
% 2.18/1.45  #BackRed      : 1
% 2.18/1.45  
% 2.18/1.45  #Partial instantiations: 0
% 2.18/1.45  #Strategies tried      : 1
% 2.18/1.45  
% 2.18/1.45  Timing (in seconds)
% 2.18/1.45  ----------------------
% 2.18/1.45  Preprocessing        : 0.34
% 2.18/1.46  Parsing              : 0.17
% 2.18/1.46  CNF conversion       : 0.03
% 2.18/1.46  Main loop            : 0.26
% 2.18/1.46  Inferencing          : 0.10
% 2.18/1.46  Reduction            : 0.07
% 2.18/1.46  Demodulation         : 0.05
% 2.18/1.46  BG Simplification    : 0.02
% 2.18/1.46  Subsumption          : 0.05
% 2.18/1.46  Abstraction          : 0.02
% 2.18/1.46  MUC search           : 0.00
% 2.18/1.46  Cooper               : 0.00
% 2.18/1.46  Total                : 0.63
% 2.18/1.46  Index Insertion      : 0.00
% 2.18/1.46  Index Deletion       : 0.00
% 2.18/1.46  Index Matching       : 0.00
% 2.18/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
