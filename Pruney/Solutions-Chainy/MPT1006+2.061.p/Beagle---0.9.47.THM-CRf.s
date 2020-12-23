%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:10 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 119 expanded)
%              Number of leaves         :   21 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :   40 ( 185 expanded)
%              Number of equality atoms :   20 (  78 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_25,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_20])).

tff(c_57,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ m1_subset_1(A_17,k1_zfmisc_1(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_65,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_25,c_57])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_69,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_65,c_2])).

tff(c_14,plain,(
    ! [A_6] : k10_relat_1(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_73,plain,(
    ! [A_6] : k10_relat_1('#skF_3',A_6) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_69,c_14])).

tff(c_70,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_65])).

tff(c_76,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_3',B_3) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_69,c_8])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_134,plain,(
    ! [A_25,B_26,C_27,D_28] :
      ( k8_relset_1(A_25,B_26,C_27,D_28) = k10_relat_1(C_27,D_28)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_164,plain,(
    ! [A_37,B_38,A_39,D_40] :
      ( k8_relset_1(A_37,B_38,A_39,D_40) = k10_relat_1(A_39,D_40)
      | ~ r1_tarski(A_39,k2_zfmisc_1(A_37,B_38)) ) ),
    inference(resolution,[status(thm)],[c_12,c_134])).

tff(c_169,plain,(
    ! [B_41,A_42,D_43] :
      ( k8_relset_1('#skF_3',B_41,A_42,D_43) = k10_relat_1(A_42,D_43)
      | ~ r1_tarski(A_42,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_164])).

tff(c_171,plain,(
    ! [B_41,D_43] : k8_relset_1('#skF_3',B_41,'#skF_3',D_43) = k10_relat_1('#skF_3',D_43) ),
    inference(resolution,[status(thm)],[c_70,c_169])).

tff(c_173,plain,(
    ! [B_41,D_43] : k8_relset_1('#skF_3',B_41,'#skF_3',D_43) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_171])).

tff(c_18,plain,(
    k8_relset_1(k1_xboole_0,'#skF_1','#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_71,plain,(
    k8_relset_1('#skF_3','#skF_1','#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_69,c_18])).

tff(c_176,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_71])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:46:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.15  
% 1.79/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.16  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.79/1.16  
% 1.79/1.16  %Foreground sorts:
% 1.79/1.16  
% 1.79/1.16  
% 1.79/1.16  %Background operators:
% 1.79/1.16  
% 1.79/1.16  
% 1.79/1.16  %Foreground operators:
% 1.79/1.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.79/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.16  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.79/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.79/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.79/1.16  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.79/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.79/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.79/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.79/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.79/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.16  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.79/1.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.79/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.79/1.16  
% 1.79/1.17  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.79/1.17  tff(f_54, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_funct_2)).
% 1.79/1.17  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.79/1.17  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.79/1.17  tff(f_41, axiom, (![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 1.79/1.17  tff(f_45, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 1.79/1.17  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.79/1.17  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.79/1.17  tff(c_25, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_20])).
% 1.79/1.17  tff(c_57, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~m1_subset_1(A_17, k1_zfmisc_1(B_18)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.79/1.17  tff(c_65, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_25, c_57])).
% 1.79/1.17  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.79/1.17  tff(c_69, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_65, c_2])).
% 1.79/1.17  tff(c_14, plain, (![A_6]: (k10_relat_1(k1_xboole_0, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.79/1.17  tff(c_73, plain, (![A_6]: (k10_relat_1('#skF_3', A_6)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_69, c_14])).
% 1.79/1.17  tff(c_70, plain, (r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_65])).
% 1.79/1.17  tff(c_76, plain, (![B_3]: (k2_zfmisc_1('#skF_3', B_3)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_69, c_8])).
% 1.79/1.17  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.79/1.17  tff(c_134, plain, (![A_25, B_26, C_27, D_28]: (k8_relset_1(A_25, B_26, C_27, D_28)=k10_relat_1(C_27, D_28) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.79/1.17  tff(c_164, plain, (![A_37, B_38, A_39, D_40]: (k8_relset_1(A_37, B_38, A_39, D_40)=k10_relat_1(A_39, D_40) | ~r1_tarski(A_39, k2_zfmisc_1(A_37, B_38)))), inference(resolution, [status(thm)], [c_12, c_134])).
% 1.79/1.17  tff(c_169, plain, (![B_41, A_42, D_43]: (k8_relset_1('#skF_3', B_41, A_42, D_43)=k10_relat_1(A_42, D_43) | ~r1_tarski(A_42, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_164])).
% 1.79/1.17  tff(c_171, plain, (![B_41, D_43]: (k8_relset_1('#skF_3', B_41, '#skF_3', D_43)=k10_relat_1('#skF_3', D_43))), inference(resolution, [status(thm)], [c_70, c_169])).
% 1.79/1.17  tff(c_173, plain, (![B_41, D_43]: (k8_relset_1('#skF_3', B_41, '#skF_3', D_43)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_171])).
% 1.79/1.17  tff(c_18, plain, (k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.79/1.17  tff(c_71, plain, (k8_relset_1('#skF_3', '#skF_1', '#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_69, c_69, c_18])).
% 1.79/1.17  tff(c_176, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_173, c_71])).
% 1.79/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.17  
% 1.79/1.17  Inference rules
% 1.79/1.17  ----------------------
% 1.79/1.17  #Ref     : 0
% 1.79/1.17  #Sup     : 36
% 1.79/1.17  #Fact    : 0
% 1.79/1.17  #Define  : 0
% 1.79/1.17  #Split   : 0
% 1.79/1.17  #Chain   : 0
% 1.79/1.17  #Close   : 0
% 1.79/1.17  
% 1.79/1.17  Ordering : KBO
% 1.79/1.17  
% 1.79/1.17  Simplification rules
% 1.79/1.17  ----------------------
% 1.79/1.17  #Subsume      : 1
% 1.79/1.17  #Demod        : 23
% 1.79/1.17  #Tautology    : 26
% 1.79/1.17  #SimpNegUnit  : 0
% 1.79/1.17  #BackRed      : 9
% 1.79/1.17  
% 1.79/1.17  #Partial instantiations: 0
% 1.79/1.17  #Strategies tried      : 1
% 1.79/1.17  
% 1.79/1.17  Timing (in seconds)
% 1.79/1.17  ----------------------
% 1.79/1.17  Preprocessing        : 0.28
% 1.79/1.17  Parsing              : 0.15
% 1.79/1.17  CNF conversion       : 0.02
% 1.79/1.17  Main loop            : 0.13
% 1.79/1.17  Inferencing          : 0.05
% 1.79/1.17  Reduction            : 0.05
% 1.79/1.17  Demodulation         : 0.03
% 1.79/1.17  BG Simplification    : 0.01
% 1.79/1.17  Subsumption          : 0.02
% 1.79/1.17  Abstraction          : 0.01
% 1.79/1.17  MUC search           : 0.00
% 1.79/1.17  Cooper               : 0.00
% 1.79/1.17  Total                : 0.44
% 1.79/1.17  Index Insertion      : 0.00
% 1.79/1.17  Index Deletion       : 0.00
% 1.79/1.17  Index Matching       : 0.00
% 1.79/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
