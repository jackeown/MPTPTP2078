%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:42 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   47 (  81 expanded)
%              Number of leaves         :   23 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 ( 122 expanded)
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

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => m1_subset_1(k6_relset_1(C,A,B,D),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(c_20,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_32,plain,(
    ! [C_27,A_28,B_29] :
      ( v1_relat_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_41,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_32])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_6,B_7)),A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(k8_relat_1(A_8,B_9),B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ m1_subset_1(A_23,k1_zfmisc_1(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_20,c_22])).

tff(c_63,plain,(
    ! [A_35,C_36,B_37] :
      ( r1_tarski(A_35,C_36)
      | ~ r1_tarski(B_37,C_36)
      | ~ r1_tarski(A_35,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    ! [A_35] :
      ( r1_tarski(A_35,k2_zfmisc_1('#skF_3','#skF_1'))
      | ~ r1_tarski(A_35,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_63])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_157,plain,(
    ! [D_61,C_62,B_63,A_64] :
      ( m1_subset_1(D_61,k1_zfmisc_1(k2_zfmisc_1(C_62,B_63)))
      | ~ r1_tarski(k2_relat_1(D_61),B_63)
      | ~ m1_subset_1(D_61,k1_zfmisc_1(k2_zfmisc_1(C_62,A_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_375,plain,(
    ! [A_100,C_101,B_102,A_103] :
      ( m1_subset_1(A_100,k1_zfmisc_1(k2_zfmisc_1(C_101,B_102)))
      | ~ r1_tarski(k2_relat_1(A_100),B_102)
      | ~ r1_tarski(A_100,k2_zfmisc_1(C_101,A_103)) ) ),
    inference(resolution,[status(thm)],[c_6,c_157])).

tff(c_408,plain,(
    ! [A_104,B_105] :
      ( m1_subset_1(A_104,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_105)))
      | ~ r1_tarski(k2_relat_1(A_104),B_105)
      | ~ r1_tarski(A_104,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_72,c_375])).

tff(c_96,plain,(
    ! [A_42,B_43,C_44,D_45] :
      ( k6_relset_1(A_42,B_43,C_44,D_45) = k8_relat_1(C_44,D_45)
      | ~ m1_subset_1(D_45,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_103,plain,(
    ! [C_44] : k6_relset_1('#skF_3','#skF_1',C_44,'#skF_4') = k8_relat_1(C_44,'#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_96])).

tff(c_18,plain,(
    ~ m1_subset_1(k6_relset_1('#skF_3','#skF_1','#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_104,plain,(
    ~ m1_subset_1(k8_relat_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_18])).

tff(c_423,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2')
    | ~ r1_tarski(k8_relat_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_408,c_104])).

tff(c_427,plain,(
    ~ r1_tarski(k8_relat_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_423])).

tff(c_430,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_427])).

tff(c_434,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_430])).

tff(c_435,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_423])).

tff(c_454,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_435])).

tff(c_458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_454])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:03:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.41  
% 2.42/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.41  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.42/1.41  
% 2.42/1.41  %Foreground sorts:
% 2.42/1.41  
% 2.42/1.41  
% 2.42/1.41  %Background operators:
% 2.42/1.41  
% 2.42/1.41  
% 2.42/1.41  %Foreground operators:
% 2.42/1.41  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.42/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.42/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.42/1.41  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.42/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.42/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.42/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.42/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.42/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.42/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.42/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.42/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.42/1.41  
% 2.42/1.42  tff(f_62, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => m1_subset_1(k6_relset_1(C, A, B, D), k1_zfmisc_1(k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_relset_1)).
% 2.42/1.42  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.42/1.42  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 2.42/1.42  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_relat_1)).
% 2.42/1.42  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.42/1.42  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.42/1.42  tff(f_57, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relset_1)).
% 2.42/1.42  tff(f_51, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.42/1.42  tff(c_20, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.42/1.42  tff(c_32, plain, (![C_27, A_28, B_29]: (v1_relat_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.42/1.42  tff(c_41, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_32])).
% 2.42/1.42  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(k2_relat_1(k8_relat_1(A_6, B_7)), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.42/1.42  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(k8_relat_1(A_8, B_9), B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.42/1.42  tff(c_22, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | ~m1_subset_1(A_23, k1_zfmisc_1(B_24)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.42/1.42  tff(c_30, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_20, c_22])).
% 2.42/1.42  tff(c_63, plain, (![A_35, C_36, B_37]: (r1_tarski(A_35, C_36) | ~r1_tarski(B_37, C_36) | ~r1_tarski(A_35, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.42/1.42  tff(c_72, plain, (![A_35]: (r1_tarski(A_35, k2_zfmisc_1('#skF_3', '#skF_1')) | ~r1_tarski(A_35, '#skF_4'))), inference(resolution, [status(thm)], [c_30, c_63])).
% 2.42/1.42  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.42/1.42  tff(c_157, plain, (![D_61, C_62, B_63, A_64]: (m1_subset_1(D_61, k1_zfmisc_1(k2_zfmisc_1(C_62, B_63))) | ~r1_tarski(k2_relat_1(D_61), B_63) | ~m1_subset_1(D_61, k1_zfmisc_1(k2_zfmisc_1(C_62, A_64))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.42/1.42  tff(c_375, plain, (![A_100, C_101, B_102, A_103]: (m1_subset_1(A_100, k1_zfmisc_1(k2_zfmisc_1(C_101, B_102))) | ~r1_tarski(k2_relat_1(A_100), B_102) | ~r1_tarski(A_100, k2_zfmisc_1(C_101, A_103)))), inference(resolution, [status(thm)], [c_6, c_157])).
% 2.42/1.42  tff(c_408, plain, (![A_104, B_105]: (m1_subset_1(A_104, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_105))) | ~r1_tarski(k2_relat_1(A_104), B_105) | ~r1_tarski(A_104, '#skF_4'))), inference(resolution, [status(thm)], [c_72, c_375])).
% 2.42/1.42  tff(c_96, plain, (![A_42, B_43, C_44, D_45]: (k6_relset_1(A_42, B_43, C_44, D_45)=k8_relat_1(C_44, D_45) | ~m1_subset_1(D_45, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.42/1.42  tff(c_103, plain, (![C_44]: (k6_relset_1('#skF_3', '#skF_1', C_44, '#skF_4')=k8_relat_1(C_44, '#skF_4'))), inference(resolution, [status(thm)], [c_20, c_96])).
% 2.42/1.42  tff(c_18, plain, (~m1_subset_1(k6_relset_1('#skF_3', '#skF_1', '#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.42/1.42  tff(c_104, plain, (~m1_subset_1(k8_relat_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_18])).
% 2.42/1.42  tff(c_423, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2') | ~r1_tarski(k8_relat_1('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_408, c_104])).
% 2.42/1.42  tff(c_427, plain, (~r1_tarski(k8_relat_1('#skF_2', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_423])).
% 2.42/1.42  tff(c_430, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_427])).
% 2.42/1.42  tff(c_434, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_41, c_430])).
% 2.42/1.42  tff(c_435, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2')), inference(splitRight, [status(thm)], [c_423])).
% 2.42/1.42  tff(c_454, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8, c_435])).
% 2.42/1.42  tff(c_458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_41, c_454])).
% 2.42/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.42  
% 2.42/1.42  Inference rules
% 2.42/1.42  ----------------------
% 2.42/1.42  #Ref     : 0
% 2.42/1.42  #Sup     : 96
% 2.42/1.42  #Fact    : 0
% 2.42/1.42  #Define  : 0
% 2.42/1.42  #Split   : 2
% 2.42/1.42  #Chain   : 0
% 2.42/1.42  #Close   : 0
% 2.42/1.42  
% 2.42/1.42  Ordering : KBO
% 2.42/1.42  
% 2.42/1.42  Simplification rules
% 2.42/1.42  ----------------------
% 2.42/1.42  #Subsume      : 9
% 2.42/1.42  #Demod        : 18
% 2.42/1.42  #Tautology    : 11
% 2.42/1.42  #SimpNegUnit  : 0
% 2.42/1.42  #BackRed      : 1
% 2.42/1.42  
% 2.42/1.42  #Partial instantiations: 0
% 2.42/1.42  #Strategies tried      : 1
% 2.42/1.42  
% 2.42/1.42  Timing (in seconds)
% 2.42/1.42  ----------------------
% 2.42/1.42  Preprocessing        : 0.32
% 2.42/1.42  Parsing              : 0.16
% 2.42/1.42  CNF conversion       : 0.02
% 2.42/1.42  Main loop            : 0.33
% 2.42/1.42  Inferencing          : 0.13
% 2.42/1.42  Reduction            : 0.08
% 2.42/1.43  Demodulation         : 0.06
% 2.42/1.43  BG Simplification    : 0.02
% 2.42/1.43  Subsumption          : 0.07
% 2.42/1.43  Abstraction          : 0.02
% 2.42/1.43  MUC search           : 0.00
% 2.42/1.43  Cooper               : 0.00
% 2.42/1.43  Total                : 0.68
% 2.42/1.43  Index Insertion      : 0.00
% 2.42/1.43  Index Deletion       : 0.00
% 2.42/1.43  Index Matching       : 0.00
% 2.42/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
