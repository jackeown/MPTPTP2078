%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:10 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 135 expanded)
%              Number of leaves         :   23 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :   39 ( 195 expanded)
%              Number of equality atoms :   22 (  98 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k8_relset_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
    ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_10,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_27,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_22])).

tff(c_65,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ m1_subset_1(A_19,k1_zfmisc_1(B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_73,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_27,c_65])).

tff(c_74,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = A_21
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_78,plain,(
    k3_xboole_0('#skF_3',k1_xboole_0) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_73,c_74])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_81,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_4])).

tff(c_16,plain,(
    ! [A_8] : k10_relat_1(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_91,plain,(
    ! [A_8] : k10_relat_1('#skF_3',A_8) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_81,c_16])).

tff(c_93,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_27])).

tff(c_94,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_81,c_10])).

tff(c_160,plain,(
    ! [A_29,B_30,C_31,D_32] :
      ( k8_relset_1(A_29,B_30,C_31,D_32) = k10_relat_1(C_31,D_32)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_190,plain,(
    ! [B_41,C_42,D_43] :
      ( k8_relset_1('#skF_3',B_41,C_42,D_43) = k10_relat_1(C_42,D_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_160])).

tff(c_192,plain,(
    ! [B_41,D_43] : k8_relset_1('#skF_3',B_41,'#skF_3',D_43) = k10_relat_1('#skF_3',D_43) ),
    inference(resolution,[status(thm)],[c_93,c_190])).

tff(c_197,plain,(
    ! [B_41,D_43] : k8_relset_1('#skF_3',B_41,'#skF_3',D_43) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_192])).

tff(c_20,plain,(
    k8_relset_1(k1_xboole_0,'#skF_1','#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_89,plain,(
    k8_relset_1('#skF_3','#skF_1','#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_81,c_20])).

tff(c_201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_89])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:52:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.16  
% 1.65/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.16  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k8_relset_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.65/1.16  
% 1.65/1.16  %Foreground sorts:
% 1.65/1.16  
% 1.65/1.16  
% 1.65/1.16  %Background operators:
% 1.65/1.16  
% 1.65/1.16  
% 1.65/1.16  %Foreground operators:
% 1.65/1.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.65/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.16  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.65/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.65/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.65/1.16  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.65/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.65/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.65/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.16  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.65/1.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.65/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.65/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.65/1.16  
% 1.65/1.17  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.65/1.17  tff(f_56, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_funct_2)).
% 1.65/1.17  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.65/1.17  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.65/1.17  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.65/1.17  tff(f_43, axiom, (![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 1.65/1.17  tff(f_47, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 1.65/1.17  tff(c_10, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.65/1.17  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.65/1.17  tff(c_27, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_22])).
% 1.65/1.17  tff(c_65, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | ~m1_subset_1(A_19, k1_zfmisc_1(B_20)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.65/1.17  tff(c_73, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_27, c_65])).
% 1.65/1.17  tff(c_74, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=A_21 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.65/1.17  tff(c_78, plain, (k3_xboole_0('#skF_3', k1_xboole_0)='#skF_3'), inference(resolution, [status(thm)], [c_73, c_74])).
% 1.65/1.17  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.65/1.17  tff(c_81, plain, (k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_78, c_4])).
% 1.65/1.17  tff(c_16, plain, (![A_8]: (k10_relat_1(k1_xboole_0, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.65/1.17  tff(c_91, plain, (![A_8]: (k10_relat_1('#skF_3', A_8)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_81, c_16])).
% 1.65/1.17  tff(c_93, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_27])).
% 1.65/1.17  tff(c_94, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_81, c_10])).
% 1.65/1.17  tff(c_160, plain, (![A_29, B_30, C_31, D_32]: (k8_relset_1(A_29, B_30, C_31, D_32)=k10_relat_1(C_31, D_32) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.65/1.17  tff(c_190, plain, (![B_41, C_42, D_43]: (k8_relset_1('#skF_3', B_41, C_42, D_43)=k10_relat_1(C_42, D_43) | ~m1_subset_1(C_42, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_94, c_160])).
% 1.65/1.17  tff(c_192, plain, (![B_41, D_43]: (k8_relset_1('#skF_3', B_41, '#skF_3', D_43)=k10_relat_1('#skF_3', D_43))), inference(resolution, [status(thm)], [c_93, c_190])).
% 1.65/1.17  tff(c_197, plain, (![B_41, D_43]: (k8_relset_1('#skF_3', B_41, '#skF_3', D_43)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_192])).
% 1.65/1.17  tff(c_20, plain, (k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.65/1.17  tff(c_89, plain, (k8_relset_1('#skF_3', '#skF_1', '#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_81, c_81, c_20])).
% 1.65/1.17  tff(c_201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_197, c_89])).
% 1.65/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.17  
% 1.65/1.17  Inference rules
% 1.65/1.17  ----------------------
% 1.65/1.17  #Ref     : 0
% 1.65/1.17  #Sup     : 43
% 1.65/1.17  #Fact    : 0
% 1.65/1.17  #Define  : 0
% 1.65/1.17  #Split   : 0
% 1.65/1.17  #Chain   : 0
% 1.65/1.17  #Close   : 0
% 1.65/1.17  
% 1.65/1.17  Ordering : KBO
% 1.65/1.17  
% 1.65/1.17  Simplification rules
% 1.65/1.17  ----------------------
% 1.65/1.17  #Subsume      : 0
% 1.65/1.17  #Demod        : 27
% 1.65/1.17  #Tautology    : 34
% 1.65/1.17  #SimpNegUnit  : 0
% 1.65/1.17  #BackRed      : 10
% 1.65/1.17  
% 1.65/1.17  #Partial instantiations: 0
% 1.65/1.17  #Strategies tried      : 1
% 1.65/1.17  
% 1.65/1.17  Timing (in seconds)
% 1.65/1.17  ----------------------
% 1.65/1.18  Preprocessing        : 0.28
% 1.65/1.18  Parsing              : 0.15
% 1.65/1.18  CNF conversion       : 0.02
% 1.65/1.18  Main loop            : 0.13
% 1.65/1.18  Inferencing          : 0.05
% 1.65/1.18  Reduction            : 0.05
% 1.65/1.18  Demodulation         : 0.03
% 1.65/1.18  BG Simplification    : 0.01
% 1.65/1.18  Subsumption          : 0.02
% 1.65/1.18  Abstraction          : 0.01
% 1.65/1.18  MUC search           : 0.00
% 1.65/1.18  Cooper               : 0.00
% 1.65/1.18  Total                : 0.44
% 1.90/1.18  Index Insertion      : 0.00
% 1.90/1.18  Index Deletion       : 0.00
% 1.90/1.18  Index Matching       : 0.00
% 1.90/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
