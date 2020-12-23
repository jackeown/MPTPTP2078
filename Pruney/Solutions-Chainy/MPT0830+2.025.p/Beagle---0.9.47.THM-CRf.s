%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:29 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   40 (  50 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 (  66 expanded)
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

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ( r1_tarski(A,D)
       => m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_16,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_19,plain,(
    ! [C_24,A_25,B_26] :
      ( v1_relat_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_23,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_19])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_2,A_1)),A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k7_relat_1(B_4,A_3),B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,(
    ! [A_32,B_33,C_34,D_35] :
      ( m1_subset_1(A_32,k1_zfmisc_1(k2_zfmisc_1(B_33,C_34)))
      | ~ r1_tarski(A_32,D_35)
      | ~ m1_subset_1(D_35,k1_zfmisc_1(k2_zfmisc_1(B_33,C_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_62,plain,(
    ! [B_43,A_44,B_45,C_46] :
      ( m1_subset_1(k7_relat_1(B_43,A_44),k1_zfmisc_1(k2_zfmisc_1(B_45,C_46)))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k2_zfmisc_1(B_45,C_46)))
      | ~ v1_relat_1(B_43) ) ),
    inference(resolution,[status(thm)],[c_4,c_38])).

tff(c_10,plain,(
    ! [D_15,B_13,C_14,A_12] :
      ( m1_subset_1(D_15,k1_zfmisc_1(k2_zfmisc_1(B_13,C_14)))
      | ~ r1_tarski(k1_relat_1(D_15),B_13)
      | ~ m1_subset_1(D_15,k1_zfmisc_1(k2_zfmisc_1(A_12,C_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_225,plain,(
    ! [C_99,B_98,A_101,B_97,B_100] :
      ( m1_subset_1(k7_relat_1(B_98,A_101),k1_zfmisc_1(k2_zfmisc_1(B_97,C_99)))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_98,A_101)),B_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(k2_zfmisc_1(B_100,C_99)))
      | ~ v1_relat_1(B_98) ) ),
    inference(resolution,[status(thm)],[c_62,c_10])).

tff(c_233,plain,(
    ! [A_101,B_97] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_101),k1_zfmisc_1(k2_zfmisc_1(B_97,'#skF_3')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_101)),B_97)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_225])).

tff(c_244,plain,(
    ! [A_104,B_105] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_104),k1_zfmisc_1(k2_zfmisc_1(B_105,'#skF_3')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_104)),B_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23,c_233])).

tff(c_24,plain,(
    ! [A_27,B_28,C_29,D_30] :
      ( k5_relset_1(A_27,B_28,C_29,D_30) = k7_relat_1(C_29,D_30)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_27,plain,(
    ! [D_30] : k5_relset_1('#skF_1','#skF_3','#skF_4',D_30) = k7_relat_1('#skF_4',D_30) ),
    inference(resolution,[status(thm)],[c_16,c_24])).

tff(c_14,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_1','#skF_3','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_28,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_14])).

tff(c_290,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_244,c_28])).

tff(c_296,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2,c_290])).

tff(c_300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_23,c_296])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 15:38:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.29  
% 2.09/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.30  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.09/1.30  
% 2.09/1.30  %Foreground sorts:
% 2.09/1.30  
% 2.09/1.30  
% 2.09/1.30  %Background operators:
% 2.09/1.30  
% 2.09/1.30  
% 2.09/1.30  %Foreground operators:
% 2.09/1.30  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.09/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.30  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.09/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.09/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.09/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.09/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.09/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.09/1.30  
% 2.09/1.31  tff(f_58, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_relset_1)).
% 2.09/1.31  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.09/1.31  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.09/1.31  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 2.09/1.31  tff(f_53, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => (r1_tarski(A, D) => m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_relset_1)).
% 2.09/1.31  tff(f_47, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 2.09/1.31  tff(f_41, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.09/1.31  tff(c_16, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.09/1.31  tff(c_19, plain, (![C_24, A_25, B_26]: (v1_relat_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.09/1.31  tff(c_23, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_19])).
% 2.09/1.31  tff(c_2, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(k7_relat_1(B_2, A_1)), A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.09/1.31  tff(c_4, plain, (![B_4, A_3]: (r1_tarski(k7_relat_1(B_4, A_3), B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.09/1.31  tff(c_38, plain, (![A_32, B_33, C_34, D_35]: (m1_subset_1(A_32, k1_zfmisc_1(k2_zfmisc_1(B_33, C_34))) | ~r1_tarski(A_32, D_35) | ~m1_subset_1(D_35, k1_zfmisc_1(k2_zfmisc_1(B_33, C_34))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.09/1.31  tff(c_62, plain, (![B_43, A_44, B_45, C_46]: (m1_subset_1(k7_relat_1(B_43, A_44), k1_zfmisc_1(k2_zfmisc_1(B_45, C_46))) | ~m1_subset_1(B_43, k1_zfmisc_1(k2_zfmisc_1(B_45, C_46))) | ~v1_relat_1(B_43))), inference(resolution, [status(thm)], [c_4, c_38])).
% 2.09/1.31  tff(c_10, plain, (![D_15, B_13, C_14, A_12]: (m1_subset_1(D_15, k1_zfmisc_1(k2_zfmisc_1(B_13, C_14))) | ~r1_tarski(k1_relat_1(D_15), B_13) | ~m1_subset_1(D_15, k1_zfmisc_1(k2_zfmisc_1(A_12, C_14))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.09/1.31  tff(c_225, plain, (![C_99, B_98, A_101, B_97, B_100]: (m1_subset_1(k7_relat_1(B_98, A_101), k1_zfmisc_1(k2_zfmisc_1(B_97, C_99))) | ~r1_tarski(k1_relat_1(k7_relat_1(B_98, A_101)), B_97) | ~m1_subset_1(B_98, k1_zfmisc_1(k2_zfmisc_1(B_100, C_99))) | ~v1_relat_1(B_98))), inference(resolution, [status(thm)], [c_62, c_10])).
% 2.09/1.31  tff(c_233, plain, (![A_101, B_97]: (m1_subset_1(k7_relat_1('#skF_4', A_101), k1_zfmisc_1(k2_zfmisc_1(B_97, '#skF_3'))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_101)), B_97) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_16, c_225])).
% 2.09/1.31  tff(c_244, plain, (![A_104, B_105]: (m1_subset_1(k7_relat_1('#skF_4', A_104), k1_zfmisc_1(k2_zfmisc_1(B_105, '#skF_3'))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_104)), B_105))), inference(demodulation, [status(thm), theory('equality')], [c_23, c_233])).
% 2.09/1.31  tff(c_24, plain, (![A_27, B_28, C_29, D_30]: (k5_relset_1(A_27, B_28, C_29, D_30)=k7_relat_1(C_29, D_30) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.09/1.31  tff(c_27, plain, (![D_30]: (k5_relset_1('#skF_1', '#skF_3', '#skF_4', D_30)=k7_relat_1('#skF_4', D_30))), inference(resolution, [status(thm)], [c_16, c_24])).
% 2.09/1.31  tff(c_14, plain, (~m1_subset_1(k5_relset_1('#skF_1', '#skF_3', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.09/1.31  tff(c_28, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_27, c_14])).
% 2.09/1.31  tff(c_290, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(resolution, [status(thm)], [c_244, c_28])).
% 2.09/1.31  tff(c_296, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2, c_290])).
% 2.09/1.31  tff(c_300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_23, c_296])).
% 2.09/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.31  
% 2.09/1.31  Inference rules
% 2.09/1.31  ----------------------
% 2.09/1.31  #Ref     : 0
% 2.09/1.31  #Sup     : 67
% 2.09/1.31  #Fact    : 0
% 2.09/1.31  #Define  : 0
% 2.09/1.31  #Split   : 0
% 2.09/1.31  #Chain   : 0
% 2.09/1.31  #Close   : 0
% 2.09/1.31  
% 2.09/1.31  Ordering : KBO
% 2.09/1.31  
% 2.09/1.31  Simplification rules
% 2.09/1.31  ----------------------
% 2.09/1.31  #Subsume      : 6
% 2.09/1.31  #Demod        : 26
% 2.09/1.31  #Tautology    : 11
% 2.09/1.31  #SimpNegUnit  : 0
% 2.09/1.31  #BackRed      : 1
% 2.09/1.31  
% 2.09/1.31  #Partial instantiations: 0
% 2.09/1.31  #Strategies tried      : 1
% 2.09/1.31  
% 2.09/1.31  Timing (in seconds)
% 2.09/1.31  ----------------------
% 2.09/1.31  Preprocessing        : 0.28
% 2.09/1.31  Parsing              : 0.15
% 2.09/1.31  CNF conversion       : 0.02
% 2.09/1.31  Main loop            : 0.25
% 2.09/1.31  Inferencing          : 0.10
% 2.09/1.31  Reduction            : 0.07
% 2.09/1.31  Demodulation         : 0.05
% 2.09/1.31  BG Simplification    : 0.01
% 2.09/1.31  Subsumption          : 0.05
% 2.09/1.32  Abstraction          : 0.02
% 2.09/1.32  MUC search           : 0.00
% 2.09/1.32  Cooper               : 0.00
% 2.09/1.32  Total                : 0.57
% 2.09/1.32  Index Insertion      : 0.00
% 2.09/1.32  Index Deletion       : 0.00
% 2.09/1.32  Index Matching       : 0.00
% 2.09/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
