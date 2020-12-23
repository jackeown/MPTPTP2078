%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:42 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.74s
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

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => m1_subset_1(k6_relset_1(C,A,B,D),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_relset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ( r1_tarski(A,D)
       => m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(c_16,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
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
    ! [A_1,B_2] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_1,B_2)),A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(k8_relat_1(A_3,B_4),B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,(
    ! [A_32,B_33,C_34,D_35] :
      ( m1_subset_1(A_32,k1_zfmisc_1(k2_zfmisc_1(B_33,C_34)))
      | ~ r1_tarski(A_32,D_35)
      | ~ m1_subset_1(D_35,k1_zfmisc_1(k2_zfmisc_1(B_33,C_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_62,plain,(
    ! [A_43,B_44,B_45,C_46] :
      ( m1_subset_1(k8_relat_1(A_43,B_44),k1_zfmisc_1(k2_zfmisc_1(B_45,C_46)))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(k2_zfmisc_1(B_45,C_46)))
      | ~ v1_relat_1(B_44) ) ),
    inference(resolution,[status(thm)],[c_4,c_38])).

tff(c_10,plain,(
    ! [D_15,C_14,B_13,A_12] :
      ( m1_subset_1(D_15,k1_zfmisc_1(k2_zfmisc_1(C_14,B_13)))
      | ~ r1_tarski(k2_relat_1(D_15),B_13)
      | ~ m1_subset_1(D_15,k1_zfmisc_1(k2_zfmisc_1(C_14,A_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_225,plain,(
    ! [A_99,B_101,B_97,B_100,C_98] :
      ( m1_subset_1(k8_relat_1(A_99,B_100),k1_zfmisc_1(k2_zfmisc_1(B_101,B_97)))
      | ~ r1_tarski(k2_relat_1(k8_relat_1(A_99,B_100)),B_97)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(k2_zfmisc_1(B_101,C_98)))
      | ~ v1_relat_1(B_100) ) ),
    inference(resolution,[status(thm)],[c_62,c_10])).

tff(c_233,plain,(
    ! [A_99,B_97] :
      ( m1_subset_1(k8_relat_1(A_99,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_97)))
      | ~ r1_tarski(k2_relat_1(k8_relat_1(A_99,'#skF_4')),B_97)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_225])).

tff(c_244,plain,(
    ! [A_104,B_105] :
      ( m1_subset_1(k8_relat_1(A_104,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_105)))
      | ~ r1_tarski(k2_relat_1(k8_relat_1(A_104,'#skF_4')),B_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23,c_233])).

tff(c_24,plain,(
    ! [A_27,B_28,C_29,D_30] :
      ( k6_relset_1(A_27,B_28,C_29,D_30) = k8_relat_1(C_29,D_30)
      | ~ m1_subset_1(D_30,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_27,plain,(
    ! [C_29] : k6_relset_1('#skF_3','#skF_1',C_29,'#skF_4') = k8_relat_1(C_29,'#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_24])).

tff(c_14,plain,(
    ~ m1_subset_1(k6_relset_1('#skF_3','#skF_1','#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_28,plain,(
    ~ m1_subset_1(k8_relat_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_14])).

tff(c_290,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_244,c_28])).

tff(c_296,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2,c_290])).

tff(c_300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_23,c_296])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:30:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.68  
% 2.74/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.68  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.74/1.68  
% 2.74/1.68  %Foreground sorts:
% 2.74/1.68  
% 2.74/1.68  
% 2.74/1.68  %Background operators:
% 2.74/1.68  
% 2.74/1.68  
% 2.74/1.68  %Foreground operators:
% 2.74/1.68  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.74/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.74/1.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.74/1.68  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.74/1.68  tff('#skF_2', type, '#skF_2': $i).
% 2.74/1.68  tff('#skF_3', type, '#skF_3': $i).
% 2.74/1.68  tff('#skF_1', type, '#skF_1': $i).
% 2.74/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.74/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.74/1.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.74/1.68  tff('#skF_4', type, '#skF_4': $i).
% 2.74/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.74/1.68  
% 2.74/1.70  tff(f_58, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => m1_subset_1(k6_relset_1(C, A, B, D), k1_zfmisc_1(k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_relset_1)).
% 2.74/1.70  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.74/1.70  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_relat_1)).
% 2.74/1.70  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 2.74/1.70  tff(f_53, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => (r1_tarski(A, D) => m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_relset_1)).
% 2.74/1.70  tff(f_47, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 2.74/1.70  tff(f_41, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.74/1.70  tff(c_16, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.74/1.70  tff(c_19, plain, (![C_24, A_25, B_26]: (v1_relat_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.74/1.70  tff(c_23, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_19])).
% 2.74/1.70  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k2_relat_1(k8_relat_1(A_1, B_2)), A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.74/1.70  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k8_relat_1(A_3, B_4), B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.74/1.70  tff(c_38, plain, (![A_32, B_33, C_34, D_35]: (m1_subset_1(A_32, k1_zfmisc_1(k2_zfmisc_1(B_33, C_34))) | ~r1_tarski(A_32, D_35) | ~m1_subset_1(D_35, k1_zfmisc_1(k2_zfmisc_1(B_33, C_34))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.74/1.70  tff(c_62, plain, (![A_43, B_44, B_45, C_46]: (m1_subset_1(k8_relat_1(A_43, B_44), k1_zfmisc_1(k2_zfmisc_1(B_45, C_46))) | ~m1_subset_1(B_44, k1_zfmisc_1(k2_zfmisc_1(B_45, C_46))) | ~v1_relat_1(B_44))), inference(resolution, [status(thm)], [c_4, c_38])).
% 2.74/1.70  tff(c_10, plain, (![D_15, C_14, B_13, A_12]: (m1_subset_1(D_15, k1_zfmisc_1(k2_zfmisc_1(C_14, B_13))) | ~r1_tarski(k2_relat_1(D_15), B_13) | ~m1_subset_1(D_15, k1_zfmisc_1(k2_zfmisc_1(C_14, A_12))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.74/1.70  tff(c_225, plain, (![A_99, B_101, B_97, B_100, C_98]: (m1_subset_1(k8_relat_1(A_99, B_100), k1_zfmisc_1(k2_zfmisc_1(B_101, B_97))) | ~r1_tarski(k2_relat_1(k8_relat_1(A_99, B_100)), B_97) | ~m1_subset_1(B_100, k1_zfmisc_1(k2_zfmisc_1(B_101, C_98))) | ~v1_relat_1(B_100))), inference(resolution, [status(thm)], [c_62, c_10])).
% 2.74/1.70  tff(c_233, plain, (![A_99, B_97]: (m1_subset_1(k8_relat_1(A_99, '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_97))) | ~r1_tarski(k2_relat_1(k8_relat_1(A_99, '#skF_4')), B_97) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_16, c_225])).
% 2.74/1.70  tff(c_244, plain, (![A_104, B_105]: (m1_subset_1(k8_relat_1(A_104, '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_105))) | ~r1_tarski(k2_relat_1(k8_relat_1(A_104, '#skF_4')), B_105))), inference(demodulation, [status(thm), theory('equality')], [c_23, c_233])).
% 2.74/1.70  tff(c_24, plain, (![A_27, B_28, C_29, D_30]: (k6_relset_1(A_27, B_28, C_29, D_30)=k8_relat_1(C_29, D_30) | ~m1_subset_1(D_30, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.74/1.70  tff(c_27, plain, (![C_29]: (k6_relset_1('#skF_3', '#skF_1', C_29, '#skF_4')=k8_relat_1(C_29, '#skF_4'))), inference(resolution, [status(thm)], [c_16, c_24])).
% 2.74/1.70  tff(c_14, plain, (~m1_subset_1(k6_relset_1('#skF_3', '#skF_1', '#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.74/1.70  tff(c_28, plain, (~m1_subset_1(k8_relat_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_27, c_14])).
% 2.74/1.70  tff(c_290, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2')), inference(resolution, [status(thm)], [c_244, c_28])).
% 2.74/1.70  tff(c_296, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2, c_290])).
% 2.74/1.70  tff(c_300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_23, c_296])).
% 2.74/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.70  
% 2.74/1.70  Inference rules
% 2.74/1.70  ----------------------
% 2.74/1.70  #Ref     : 0
% 2.74/1.70  #Sup     : 67
% 2.74/1.70  #Fact    : 0
% 2.74/1.70  #Define  : 0
% 2.74/1.70  #Split   : 0
% 2.74/1.70  #Chain   : 0
% 2.74/1.70  #Close   : 0
% 2.74/1.70  
% 2.74/1.70  Ordering : KBO
% 2.74/1.70  
% 2.74/1.70  Simplification rules
% 2.74/1.70  ----------------------
% 2.74/1.70  #Subsume      : 6
% 2.74/1.70  #Demod        : 26
% 2.74/1.70  #Tautology    : 11
% 2.74/1.70  #SimpNegUnit  : 0
% 2.74/1.70  #BackRed      : 1
% 2.74/1.70  
% 2.74/1.70  #Partial instantiations: 0
% 2.74/1.70  #Strategies tried      : 1
% 2.74/1.70  
% 2.74/1.70  Timing (in seconds)
% 2.74/1.70  ----------------------
% 2.74/1.70  Preprocessing        : 0.43
% 2.74/1.70  Parsing              : 0.23
% 2.74/1.70  CNF conversion       : 0.03
% 2.74/1.70  Main loop            : 0.38
% 2.74/1.70  Inferencing          : 0.15
% 2.74/1.70  Reduction            : 0.10
% 2.74/1.70  Demodulation         : 0.07
% 2.74/1.70  BG Simplification    : 0.02
% 2.74/1.70  Subsumption          : 0.08
% 2.74/1.70  Abstraction          : 0.03
% 2.74/1.70  MUC search           : 0.00
% 2.74/1.70  Cooper               : 0.00
% 2.74/1.70  Total                : 0.85
% 2.74/1.70  Index Insertion      : 0.00
% 2.74/1.70  Index Deletion       : 0.00
% 2.74/1.70  Index Matching       : 0.00
% 2.74/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
