%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:53 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   49 (  62 expanded)
%              Number of leaves         :   28 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   57 (  83 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => r1_tarski(k8_relset_1(A,B,D,C),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_2)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_12,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_35,plain,(
    ! [B_31,A_32] :
      ( v1_relat_1(B_31)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_32))
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_38,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_35])).

tff(c_41,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_38])).

tff(c_57,plain,(
    ! [C_40,A_41,B_42] :
      ( v4_relat_1(C_40,A_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_61,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_57])).

tff(c_10,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(B_10),A_9)
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_30,plain,(
    ! [B_29,A_30] :
      ( r1_tarski(k10_relat_1(B_29,A_30),k1_relat_1(B_29))
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_88,plain,(
    ! [B_50,A_51] :
      ( k2_xboole_0(k10_relat_1(B_50,A_51),k1_relat_1(B_50)) = k1_relat_1(B_50)
      | ~ v1_relat_1(B_50) ) ),
    inference(resolution,[status(thm)],[c_30,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_100,plain,(
    ! [B_52,A_53,C_54] :
      ( r1_tarski(k10_relat_1(B_52,A_53),C_54)
      | ~ r1_tarski(k1_relat_1(B_52),C_54)
      | ~ v1_relat_1(B_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_2])).

tff(c_62,plain,(
    ! [A_43,B_44,C_45,D_46] :
      ( k8_relset_1(A_43,B_44,C_45,D_46) = k10_relat_1(C_45,D_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_65,plain,(
    ! [D_46] : k8_relset_1('#skF_1','#skF_2','#skF_4',D_46) = k10_relat_1('#skF_4',D_46) ),
    inference(resolution,[status(thm)],[c_24,c_62])).

tff(c_22,plain,(
    ~ r1_tarski(k8_relset_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_66,plain,(
    ~ r1_tarski(k10_relat_1('#skF_4','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_22])).

tff(c_103,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_66])).

tff(c_109,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_103])).

tff(c_113,plain,
    ( ~ v4_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_109])).

tff(c_117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_61,c_113])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:50:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.16  
% 1.68/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.16  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.68/1.16  
% 1.68/1.16  %Foreground sorts:
% 1.68/1.16  
% 1.68/1.16  
% 1.68/1.16  %Background operators:
% 1.68/1.16  
% 1.68/1.16  
% 1.68/1.16  %Foreground operators:
% 1.68/1.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.68/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.16  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.68/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.68/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.68/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.16  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.68/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.68/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.16  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.68/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.68/1.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.68/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.68/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.16  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.68/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.68/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.68/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.68/1.16  
% 1.68/1.17  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.68/1.17  tff(f_69, negated_conjecture, ~(![A, B, C, D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r1_tarski(k8_relset_1(A, B, D, C), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_funct_2)).
% 1.68/1.17  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.68/1.17  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.68/1.17  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 1.68/1.17  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 1.68/1.17  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.68/1.17  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.68/1.17  tff(f_62, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 1.68/1.17  tff(c_12, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.68/1.17  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.68/1.17  tff(c_35, plain, (![B_31, A_32]: (v1_relat_1(B_31) | ~m1_subset_1(B_31, k1_zfmisc_1(A_32)) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.68/1.17  tff(c_38, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_35])).
% 1.68/1.17  tff(c_41, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_38])).
% 1.68/1.17  tff(c_57, plain, (![C_40, A_41, B_42]: (v4_relat_1(C_40, A_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.68/1.17  tff(c_61, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_24, c_57])).
% 1.68/1.17  tff(c_10, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(B_10), A_9) | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.68/1.17  tff(c_30, plain, (![B_29, A_30]: (r1_tarski(k10_relat_1(B_29, A_30), k1_relat_1(B_29)) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.68/1.17  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.68/1.17  tff(c_88, plain, (![B_50, A_51]: (k2_xboole_0(k10_relat_1(B_50, A_51), k1_relat_1(B_50))=k1_relat_1(B_50) | ~v1_relat_1(B_50))), inference(resolution, [status(thm)], [c_30, c_4])).
% 1.68/1.17  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.68/1.17  tff(c_100, plain, (![B_52, A_53, C_54]: (r1_tarski(k10_relat_1(B_52, A_53), C_54) | ~r1_tarski(k1_relat_1(B_52), C_54) | ~v1_relat_1(B_52))), inference(superposition, [status(thm), theory('equality')], [c_88, c_2])).
% 1.68/1.17  tff(c_62, plain, (![A_43, B_44, C_45, D_46]: (k8_relset_1(A_43, B_44, C_45, D_46)=k10_relat_1(C_45, D_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.68/1.17  tff(c_65, plain, (![D_46]: (k8_relset_1('#skF_1', '#skF_2', '#skF_4', D_46)=k10_relat_1('#skF_4', D_46))), inference(resolution, [status(thm)], [c_24, c_62])).
% 1.68/1.17  tff(c_22, plain, (~r1_tarski(k8_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.68/1.17  tff(c_66, plain, (~r1_tarski(k10_relat_1('#skF_4', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_22])).
% 1.68/1.17  tff(c_103, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_100, c_66])).
% 1.68/1.17  tff(c_109, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_41, c_103])).
% 1.68/1.17  tff(c_113, plain, (~v4_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_109])).
% 1.68/1.17  tff(c_117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_41, c_61, c_113])).
% 1.68/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.17  
% 1.68/1.17  Inference rules
% 1.68/1.17  ----------------------
% 1.68/1.17  #Ref     : 0
% 1.68/1.17  #Sup     : 18
% 1.68/1.17  #Fact    : 0
% 1.68/1.17  #Define  : 0
% 1.68/1.17  #Split   : 0
% 1.68/1.17  #Chain   : 0
% 1.68/1.17  #Close   : 0
% 1.68/1.17  
% 1.68/1.17  Ordering : KBO
% 1.68/1.17  
% 1.68/1.17  Simplification rules
% 1.68/1.17  ----------------------
% 1.68/1.17  #Subsume      : 0
% 1.68/1.17  #Demod        : 5
% 1.68/1.17  #Tautology    : 7
% 1.68/1.17  #SimpNegUnit  : 0
% 1.68/1.17  #BackRed      : 1
% 1.68/1.17  
% 1.68/1.17  #Partial instantiations: 0
% 1.68/1.17  #Strategies tried      : 1
% 1.68/1.17  
% 1.68/1.17  Timing (in seconds)
% 1.68/1.17  ----------------------
% 1.68/1.18  Preprocessing        : 0.29
% 1.68/1.18  Parsing              : 0.16
% 1.68/1.18  CNF conversion       : 0.02
% 1.68/1.18  Main loop            : 0.13
% 1.68/1.18  Inferencing          : 0.06
% 1.68/1.18  Reduction            : 0.04
% 1.68/1.18  Demodulation         : 0.03
% 1.68/1.18  BG Simplification    : 0.01
% 1.68/1.18  Subsumption          : 0.01
% 1.68/1.18  Abstraction          : 0.01
% 1.68/1.18  MUC search           : 0.00
% 1.68/1.18  Cooper               : 0.00
% 1.68/1.18  Total                : 0.44
% 1.68/1.18  Index Insertion      : 0.00
% 1.68/1.18  Index Deletion       : 0.00
% 1.68/1.18  Index Matching       : 0.00
% 1.68/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
