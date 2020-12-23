%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:09 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :   51 (  70 expanded)
%              Number of leaves         :   23 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   66 ( 127 expanded)
%              Number of equality atoms :   22 (  25 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_22,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_28,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_780,plain,(
    ! [B_60,A_61] :
      ( k9_relat_1(B_60,k10_relat_1(B_60,A_61)) = A_61
      | ~ r1_tarski(A_61,k2_relat_1(B_60))
      | ~ v1_funct_1(B_60)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_800,plain,
    ( k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_780])).

tff(c_819,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_800])).

tff(c_997,plain,(
    ! [C_69,A_70,B_71] :
      ( k3_xboole_0(k10_relat_1(C_69,A_70),k10_relat_1(C_69,B_71)) = k10_relat_1(C_69,k3_xboole_0(A_70,B_71))
      | ~ v1_funct_1(C_69)
      | ~ v1_relat_1(C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_26,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_96,plain,(
    k3_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k10_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_12])).

tff(c_1015,plain,
    ( k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k10_relat_1('#skF_3','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_997,c_96])).

tff(c_1068,plain,(
    k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k10_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_1015])).

tff(c_392,plain,(
    ! [A_43,C_44,B_45] :
      ( r1_tarski(A_43,C_44)
      | ~ r1_tarski(B_45,C_44)
      | ~ r1_tarski(A_43,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_406,plain,(
    ! [A_43] :
      ( r1_tarski(A_43,k2_relat_1('#skF_3'))
      | ~ r1_tarski(A_43,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_392])).

tff(c_792,plain,(
    ! [A_43] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_43)) = A_43
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(A_43,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_406,c_780])).

tff(c_2822,plain,(
    ! [A_99] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_99)) = A_99
      | ~ r1_tarski(A_99,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_792])).

tff(c_2850,plain,
    ( k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = k3_xboole_0('#skF_1','#skF_2')
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1068,c_2822])).

tff(c_2870,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_819,c_2850])).

tff(c_14,plain,(
    ! [B_11,A_10] : k2_tarski(B_11,A_10) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_105,plain,(
    ! [A_27,B_28] : k1_setfam_1(k2_tarski(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_120,plain,(
    ! [B_29,A_30] : k1_setfam_1(k2_tarski(B_29,A_30)) = k3_xboole_0(A_30,B_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_105])).

tff(c_16,plain,(
    ! [A_12,B_13] : k1_setfam_1(k2_tarski(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_143,plain,(
    ! [B_31,A_32] : k3_xboole_0(B_31,A_32) = k3_xboole_0(A_32,B_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_16])).

tff(c_158,plain,(
    ! [B_31,A_32] : r1_tarski(k3_xboole_0(B_31,A_32),A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_8])).

tff(c_2934,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2870,c_158])).

tff(c_2957,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_2934])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n023.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:06:05 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.74/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.67  
% 3.74/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.67  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 3.74/1.67  
% 3.74/1.67  %Foreground sorts:
% 3.74/1.67  
% 3.74/1.67  
% 3.74/1.67  %Background operators:
% 3.74/1.67  
% 3.74/1.67  
% 3.74/1.67  %Foreground operators:
% 3.74/1.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.74/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.74/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.74/1.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.74/1.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.74/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.74/1.67  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.74/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.74/1.67  tff('#skF_1', type, '#skF_1': $i).
% 3.74/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.74/1.67  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.74/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.74/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.74/1.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.74/1.67  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.74/1.67  
% 3.74/1.68  tff(f_72, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 3.74/1.68  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.74/1.68  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 3.74/1.68  tff(f_53, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_funct_1)).
% 3.74/1.68  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.74/1.68  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.74/1.68  tff(f_45, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.74/1.68  tff(f_47, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.74/1.68  tff(c_22, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.74/1.68  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.74/1.68  tff(c_30, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.74/1.68  tff(c_28, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.74/1.68  tff(c_24, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.74/1.68  tff(c_780, plain, (![B_60, A_61]: (k9_relat_1(B_60, k10_relat_1(B_60, A_61))=A_61 | ~r1_tarski(A_61, k2_relat_1(B_60)) | ~v1_funct_1(B_60) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.74/1.68  tff(c_800, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_780])).
% 3.74/1.68  tff(c_819, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_800])).
% 3.74/1.68  tff(c_997, plain, (![C_69, A_70, B_71]: (k3_xboole_0(k10_relat_1(C_69, A_70), k10_relat_1(C_69, B_71))=k10_relat_1(C_69, k3_xboole_0(A_70, B_71)) | ~v1_funct_1(C_69) | ~v1_relat_1(C_69))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.74/1.68  tff(c_26, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.74/1.68  tff(c_12, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.74/1.68  tff(c_96, plain, (k3_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k10_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_26, c_12])).
% 3.74/1.68  tff(c_1015, plain, (k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k10_relat_1('#skF_3', '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_997, c_96])).
% 3.74/1.68  tff(c_1068, plain, (k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k10_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_1015])).
% 3.74/1.68  tff(c_392, plain, (![A_43, C_44, B_45]: (r1_tarski(A_43, C_44) | ~r1_tarski(B_45, C_44) | ~r1_tarski(A_43, B_45))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.74/1.68  tff(c_406, plain, (![A_43]: (r1_tarski(A_43, k2_relat_1('#skF_3')) | ~r1_tarski(A_43, '#skF_1'))), inference(resolution, [status(thm)], [c_24, c_392])).
% 3.74/1.68  tff(c_792, plain, (![A_43]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_43))=A_43 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~r1_tarski(A_43, '#skF_1'))), inference(resolution, [status(thm)], [c_406, c_780])).
% 3.74/1.68  tff(c_2822, plain, (![A_99]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_99))=A_99 | ~r1_tarski(A_99, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_792])).
% 3.74/1.68  tff(c_2850, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))=k3_xboole_0('#skF_1', '#skF_2') | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1068, c_2822])).
% 3.74/1.68  tff(c_2870, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_819, c_2850])).
% 3.74/1.68  tff(c_14, plain, (![B_11, A_10]: (k2_tarski(B_11, A_10)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.74/1.68  tff(c_105, plain, (![A_27, B_28]: (k1_setfam_1(k2_tarski(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.74/1.68  tff(c_120, plain, (![B_29, A_30]: (k1_setfam_1(k2_tarski(B_29, A_30))=k3_xboole_0(A_30, B_29))), inference(superposition, [status(thm), theory('equality')], [c_14, c_105])).
% 3.74/1.68  tff(c_16, plain, (![A_12, B_13]: (k1_setfam_1(k2_tarski(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.74/1.68  tff(c_143, plain, (![B_31, A_32]: (k3_xboole_0(B_31, A_32)=k3_xboole_0(A_32, B_31))), inference(superposition, [status(thm), theory('equality')], [c_120, c_16])).
% 3.74/1.68  tff(c_158, plain, (![B_31, A_32]: (r1_tarski(k3_xboole_0(B_31, A_32), A_32))), inference(superposition, [status(thm), theory('equality')], [c_143, c_8])).
% 3.74/1.68  tff(c_2934, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2870, c_158])).
% 3.74/1.68  tff(c_2957, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_2934])).
% 3.74/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.68  
% 3.74/1.68  Inference rules
% 3.74/1.68  ----------------------
% 3.74/1.68  #Ref     : 0
% 3.74/1.68  #Sup     : 724
% 3.74/1.68  #Fact    : 0
% 3.74/1.68  #Define  : 0
% 3.74/1.68  #Split   : 2
% 3.74/1.68  #Chain   : 0
% 3.74/1.68  #Close   : 0
% 3.74/1.68  
% 3.74/1.68  Ordering : KBO
% 3.74/1.68  
% 3.74/1.68  Simplification rules
% 3.74/1.68  ----------------------
% 3.74/1.68  #Subsume      : 88
% 3.74/1.68  #Demod        : 621
% 3.74/1.68  #Tautology    : 440
% 3.74/1.68  #SimpNegUnit  : 1
% 3.74/1.68  #BackRed      : 0
% 3.74/1.68  
% 3.74/1.68  #Partial instantiations: 0
% 3.74/1.68  #Strategies tried      : 1
% 3.74/1.68  
% 3.74/1.68  Timing (in seconds)
% 3.74/1.68  ----------------------
% 3.74/1.68  Preprocessing        : 0.29
% 3.74/1.68  Parsing              : 0.16
% 3.74/1.68  CNF conversion       : 0.02
% 3.74/1.68  Main loop            : 0.64
% 3.74/1.68  Inferencing          : 0.20
% 3.74/1.68  Reduction            : 0.28
% 3.74/1.68  Demodulation         : 0.23
% 3.74/1.68  BG Simplification    : 0.02
% 3.74/1.68  Subsumption          : 0.11
% 3.74/1.68  Abstraction          : 0.03
% 3.74/1.68  MUC search           : 0.00
% 3.74/1.68  Cooper               : 0.00
% 3.74/1.68  Total                : 0.96
% 3.74/1.68  Index Insertion      : 0.00
% 3.74/1.68  Index Deletion       : 0.00
% 3.74/1.68  Index Matching       : 0.00
% 3.74/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
