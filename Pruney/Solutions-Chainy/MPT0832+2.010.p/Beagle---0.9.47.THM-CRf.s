%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:41 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   44 (  54 expanded)
%              Number of leaves         :   24 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   44 (  60 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => m1_subset_1(k6_relset_1(C,A,B,D),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_relset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k6_relset_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

tff(c_18,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_69,plain,(
    ! [C_28,A_29,B_30] :
      ( v1_relat_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_73,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_69])).

tff(c_74,plain,(
    ! [B_31,A_32] :
      ( k3_xboole_0(k2_relat_1(B_31),A_32) = k2_relat_1(k8_relat_1(A_32,B_31))
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [B_24,A_25] : k3_xboole_0(B_24,A_25) = k3_xboole_0(A_25,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_35,plain,(
    ! [B_24,A_25] : r1_tarski(k3_xboole_0(B_24,A_25),A_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4])).

tff(c_80,plain,(
    ! [A_32,B_31] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_32,B_31)),A_32)
      | ~ v1_relat_1(B_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_35])).

tff(c_103,plain,(
    ! [A_33,B_34,C_35,D_36] :
      ( k6_relset_1(A_33,B_34,C_35,D_36) = k8_relat_1(C_35,D_36)
      | ~ m1_subset_1(D_36,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_106,plain,(
    ! [C_35] : k6_relset_1('#skF_3','#skF_1',C_35,'#skF_4') = k8_relat_1(C_35,'#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_103])).

tff(c_260,plain,(
    ! [A_53,B_54,C_55,D_56] :
      ( m1_subset_1(k6_relset_1(A_53,B_54,C_55,D_56),k1_zfmisc_1(k2_zfmisc_1(A_53,B_54)))
      | ~ m1_subset_1(D_56,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_270,plain,(
    ! [C_35] :
      ( m1_subset_1(k8_relat_1(C_35,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_260])).

tff(c_276,plain,(
    ! [C_57] : m1_subset_1(k8_relat_1(C_57,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_270])).

tff(c_14,plain,(
    ! [D_21,C_20,B_19,A_18] :
      ( m1_subset_1(D_21,k1_zfmisc_1(k2_zfmisc_1(C_20,B_19)))
      | ~ r1_tarski(k2_relat_1(D_21),B_19)
      | ~ m1_subset_1(D_21,k1_zfmisc_1(k2_zfmisc_1(C_20,A_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_337,plain,(
    ! [C_76,B_77] :
      ( m1_subset_1(k8_relat_1(C_76,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_77)))
      | ~ r1_tarski(k2_relat_1(k8_relat_1(C_76,'#skF_4')),B_77) ) ),
    inference(resolution,[status(thm)],[c_276,c_14])).

tff(c_16,plain,(
    ~ m1_subset_1(k6_relset_1('#skF_3','#skF_1','#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_107,plain,(
    ~ m1_subset_1(k8_relat_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_16])).

tff(c_352,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_337,c_107])).

tff(c_379,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_352])).

tff(c_383,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_379])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:57:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.26  
% 2.22/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.26  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.22/1.26  
% 2.22/1.26  %Foreground sorts:
% 2.22/1.26  
% 2.22/1.26  
% 2.22/1.26  %Background operators:
% 2.22/1.26  
% 2.22/1.26  
% 2.22/1.26  %Foreground operators:
% 2.22/1.26  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.22/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.22/1.26  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.22/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.22/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.22/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.22/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.22/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.22/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.22/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.22/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.22/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.22/1.26  
% 2.22/1.27  tff(f_56, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => m1_subset_1(k6_relset_1(C, A, B, D), k1_zfmisc_1(k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_relset_1)).
% 2.22/1.27  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.22/1.27  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_relat_1)).
% 2.22/1.27  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.22/1.27  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.22/1.27  tff(f_45, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.22/1.27  tff(f_41, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k6_relset_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relset_1)).
% 2.22/1.27  tff(f_51, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 2.22/1.27  tff(c_18, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.22/1.27  tff(c_69, plain, (![C_28, A_29, B_30]: (v1_relat_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.22/1.27  tff(c_73, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_69])).
% 2.22/1.27  tff(c_74, plain, (![B_31, A_32]: (k3_xboole_0(k2_relat_1(B_31), A_32)=k2_relat_1(k8_relat_1(A_32, B_31)) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.22/1.27  tff(c_20, plain, (![B_24, A_25]: (k3_xboole_0(B_24, A_25)=k3_xboole_0(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.22/1.27  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.22/1.27  tff(c_35, plain, (![B_24, A_25]: (r1_tarski(k3_xboole_0(B_24, A_25), A_25))), inference(superposition, [status(thm), theory('equality')], [c_20, c_4])).
% 2.22/1.27  tff(c_80, plain, (![A_32, B_31]: (r1_tarski(k2_relat_1(k8_relat_1(A_32, B_31)), A_32) | ~v1_relat_1(B_31))), inference(superposition, [status(thm), theory('equality')], [c_74, c_35])).
% 2.22/1.27  tff(c_103, plain, (![A_33, B_34, C_35, D_36]: (k6_relset_1(A_33, B_34, C_35, D_36)=k8_relat_1(C_35, D_36) | ~m1_subset_1(D_36, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.22/1.27  tff(c_106, plain, (![C_35]: (k6_relset_1('#skF_3', '#skF_1', C_35, '#skF_4')=k8_relat_1(C_35, '#skF_4'))), inference(resolution, [status(thm)], [c_18, c_103])).
% 2.22/1.27  tff(c_260, plain, (![A_53, B_54, C_55, D_56]: (m1_subset_1(k6_relset_1(A_53, B_54, C_55, D_56), k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))) | ~m1_subset_1(D_56, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.22/1.27  tff(c_270, plain, (![C_35]: (m1_subset_1(k8_relat_1(C_35, '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_106, c_260])).
% 2.22/1.27  tff(c_276, plain, (![C_57]: (m1_subset_1(k8_relat_1(C_57, '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_270])).
% 2.22/1.27  tff(c_14, plain, (![D_21, C_20, B_19, A_18]: (m1_subset_1(D_21, k1_zfmisc_1(k2_zfmisc_1(C_20, B_19))) | ~r1_tarski(k2_relat_1(D_21), B_19) | ~m1_subset_1(D_21, k1_zfmisc_1(k2_zfmisc_1(C_20, A_18))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.22/1.27  tff(c_337, plain, (![C_76, B_77]: (m1_subset_1(k8_relat_1(C_76, '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_77))) | ~r1_tarski(k2_relat_1(k8_relat_1(C_76, '#skF_4')), B_77))), inference(resolution, [status(thm)], [c_276, c_14])).
% 2.22/1.27  tff(c_16, plain, (~m1_subset_1(k6_relset_1('#skF_3', '#skF_1', '#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.22/1.27  tff(c_107, plain, (~m1_subset_1(k8_relat_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_16])).
% 2.22/1.27  tff(c_352, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2')), inference(resolution, [status(thm)], [c_337, c_107])).
% 2.22/1.27  tff(c_379, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_352])).
% 2.22/1.27  tff(c_383, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_379])).
% 2.22/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.27  
% 2.22/1.27  Inference rules
% 2.22/1.27  ----------------------
% 2.22/1.27  #Ref     : 0
% 2.22/1.27  #Sup     : 94
% 2.22/1.27  #Fact    : 0
% 2.22/1.27  #Define  : 0
% 2.22/1.27  #Split   : 0
% 2.22/1.27  #Chain   : 0
% 2.22/1.27  #Close   : 0
% 2.22/1.27  
% 2.22/1.27  Ordering : KBO
% 2.22/1.27  
% 2.22/1.27  Simplification rules
% 2.22/1.27  ----------------------
% 2.22/1.27  #Subsume      : 16
% 2.22/1.27  #Demod        : 18
% 2.22/1.27  #Tautology    : 32
% 2.22/1.27  #SimpNegUnit  : 0
% 2.22/1.27  #BackRed      : 2
% 2.22/1.27  
% 2.22/1.27  #Partial instantiations: 0
% 2.22/1.27  #Strategies tried      : 1
% 2.22/1.27  
% 2.22/1.27  Timing (in seconds)
% 2.22/1.27  ----------------------
% 2.22/1.27  Preprocessing        : 0.29
% 2.22/1.27  Parsing              : 0.16
% 2.22/1.27  CNF conversion       : 0.02
% 2.22/1.27  Main loop            : 0.24
% 2.22/1.27  Inferencing          : 0.10
% 2.22/1.27  Reduction            : 0.07
% 2.22/1.27  Demodulation         : 0.06
% 2.22/1.27  BG Simplification    : 0.01
% 2.22/1.27  Subsumption          : 0.04
% 2.22/1.27  Abstraction          : 0.02
% 2.22/1.27  MUC search           : 0.00
% 2.22/1.28  Cooper               : 0.00
% 2.22/1.28  Total                : 0.55
% 2.22/1.28  Index Insertion      : 0.00
% 2.22/1.28  Index Deletion       : 0.00
% 2.22/1.28  Index Matching       : 0.00
% 2.22/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
