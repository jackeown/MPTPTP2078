%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:53 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   45 (  52 expanded)
%              Number of leaves         :   25 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   49 (  64 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => r1_tarski(k8_relset_1(A,B,D,C),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_2)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

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

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_20,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_33,plain,(
    ! [C_25,A_26,B_27] :
      ( v1_relat_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_42,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_33])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k10_relat_1(B_7,A_6),k1_relat_1(B_7))
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_78,plain,(
    ! [A_43,B_44,C_45] :
      ( k1_relset_1(A_43,B_44,C_45) = k1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_87,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_78])).

tff(c_119,plain,(
    ! [A_54,B_55,C_56] :
      ( m1_subset_1(k1_relset_1(A_54,B_55,C_56),k1_zfmisc_1(A_54))
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_133,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_119])).

tff(c_138,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_133])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_142,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_138,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_149,plain,(
    ! [A_57] :
      ( r1_tarski(A_57,'#skF_1')
      | ~ r1_tarski(A_57,k1_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_142,c_2])).

tff(c_153,plain,(
    ! [A_6] :
      ( r1_tarski(k10_relat_1('#skF_4',A_6),'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8,c_149])).

tff(c_156,plain,(
    ! [A_6] : r1_tarski(k10_relat_1('#skF_4',A_6),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_153])).

tff(c_157,plain,(
    ! [A_58,B_59,C_60,D_61] :
      ( k8_relset_1(A_58,B_59,C_60,D_61) = k10_relat_1(C_60,D_61)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_168,plain,(
    ! [D_61] : k8_relset_1('#skF_1','#skF_2','#skF_4',D_61) = k10_relat_1('#skF_4',D_61) ),
    inference(resolution,[status(thm)],[c_20,c_157])).

tff(c_18,plain,(
    ~ r1_tarski(k8_relset_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_176,plain,(
    ~ r1_tarski(k10_relat_1('#skF_4','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_18])).

tff(c_179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_176])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:55:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.17  
% 1.95/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.18  %$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.95/1.18  
% 1.95/1.18  %Foreground sorts:
% 1.95/1.18  
% 1.95/1.18  
% 1.95/1.18  %Background operators:
% 1.95/1.18  
% 1.95/1.18  
% 1.95/1.18  %Foreground operators:
% 1.95/1.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.95/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.18  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.95/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.18  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.95/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.95/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.18  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.95/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.95/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.95/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.95/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.95/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.95/1.18  
% 1.95/1.19  tff(f_62, negated_conjecture, ~(![A, B, C, D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r1_tarski(k8_relset_1(A, B, D, C), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_funct_2)).
% 1.95/1.19  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.95/1.19  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 1.95/1.19  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 1.95/1.19  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 1.95/1.19  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.95/1.19  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.95/1.19  tff(f_55, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 1.95/1.19  tff(c_20, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.95/1.19  tff(c_33, plain, (![C_25, A_26, B_27]: (v1_relat_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.95/1.19  tff(c_42, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_33])).
% 1.95/1.19  tff(c_8, plain, (![B_7, A_6]: (r1_tarski(k10_relat_1(B_7, A_6), k1_relat_1(B_7)) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.95/1.19  tff(c_78, plain, (![A_43, B_44, C_45]: (k1_relset_1(A_43, B_44, C_45)=k1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.95/1.19  tff(c_87, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_78])).
% 1.95/1.19  tff(c_119, plain, (![A_54, B_55, C_56]: (m1_subset_1(k1_relset_1(A_54, B_55, C_56), k1_zfmisc_1(A_54)) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.95/1.19  tff(c_133, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_87, c_119])).
% 1.95/1.19  tff(c_138, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_133])).
% 1.95/1.19  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.95/1.19  tff(c_142, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(resolution, [status(thm)], [c_138, c_4])).
% 1.95/1.19  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.95/1.19  tff(c_149, plain, (![A_57]: (r1_tarski(A_57, '#skF_1') | ~r1_tarski(A_57, k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_142, c_2])).
% 1.95/1.19  tff(c_153, plain, (![A_6]: (r1_tarski(k10_relat_1('#skF_4', A_6), '#skF_1') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_8, c_149])).
% 1.95/1.19  tff(c_156, plain, (![A_6]: (r1_tarski(k10_relat_1('#skF_4', A_6), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_153])).
% 1.95/1.19  tff(c_157, plain, (![A_58, B_59, C_60, D_61]: (k8_relset_1(A_58, B_59, C_60, D_61)=k10_relat_1(C_60, D_61) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.95/1.19  tff(c_168, plain, (![D_61]: (k8_relset_1('#skF_1', '#skF_2', '#skF_4', D_61)=k10_relat_1('#skF_4', D_61))), inference(resolution, [status(thm)], [c_20, c_157])).
% 1.95/1.19  tff(c_18, plain, (~r1_tarski(k8_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.95/1.19  tff(c_176, plain, (~r1_tarski(k10_relat_1('#skF_4', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_18])).
% 1.95/1.19  tff(c_179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_156, c_176])).
% 1.95/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.19  
% 1.95/1.19  Inference rules
% 1.95/1.19  ----------------------
% 1.95/1.19  #Ref     : 0
% 1.95/1.19  #Sup     : 35
% 1.95/1.19  #Fact    : 0
% 1.95/1.19  #Define  : 0
% 1.95/1.19  #Split   : 0
% 1.95/1.19  #Chain   : 0
% 1.95/1.19  #Close   : 0
% 1.95/1.19  
% 1.95/1.19  Ordering : KBO
% 1.95/1.19  
% 1.95/1.19  Simplification rules
% 1.95/1.19  ----------------------
% 1.95/1.19  #Subsume      : 2
% 1.95/1.19  #Demod        : 7
% 1.95/1.19  #Tautology    : 6
% 1.95/1.19  #SimpNegUnit  : 0
% 1.95/1.19  #BackRed      : 1
% 1.95/1.19  
% 1.95/1.19  #Partial instantiations: 0
% 1.95/1.19  #Strategies tried      : 1
% 1.95/1.19  
% 1.95/1.19  Timing (in seconds)
% 1.95/1.19  ----------------------
% 1.95/1.19  Preprocessing        : 0.28
% 1.95/1.19  Parsing              : 0.15
% 1.95/1.19  CNF conversion       : 0.02
% 1.95/1.19  Main loop            : 0.16
% 1.95/1.19  Inferencing          : 0.07
% 1.95/1.19  Reduction            : 0.04
% 1.95/1.19  Demodulation         : 0.03
% 1.95/1.19  BG Simplification    : 0.01
% 1.95/1.19  Subsumption          : 0.03
% 1.95/1.19  Abstraction          : 0.01
% 1.95/1.19  MUC search           : 0.00
% 1.95/1.19  Cooper               : 0.00
% 1.95/1.19  Total                : 0.47
% 1.95/1.19  Index Insertion      : 0.00
% 1.95/1.19  Index Deletion       : 0.00
% 1.95/1.19  Index Matching       : 0.00
% 1.95/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
