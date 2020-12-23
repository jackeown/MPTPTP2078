%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:02 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.94s
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
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k7_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

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
    ! [A_6] : k9_relat_1(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_73,plain,(
    ! [A_6] : k9_relat_1('#skF_3',A_6) = '#skF_3' ),
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
      ( k7_relset_1(A_25,B_26,C_27,D_28) = k9_relat_1(C_27,D_28)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_164,plain,(
    ! [A_37,B_38,A_39,D_40] :
      ( k7_relset_1(A_37,B_38,A_39,D_40) = k9_relat_1(A_39,D_40)
      | ~ r1_tarski(A_39,k2_zfmisc_1(A_37,B_38)) ) ),
    inference(resolution,[status(thm)],[c_12,c_134])).

tff(c_169,plain,(
    ! [B_41,A_42,D_43] :
      ( k7_relset_1('#skF_3',B_41,A_42,D_43) = k9_relat_1(A_42,D_43)
      | ~ r1_tarski(A_42,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_164])).

tff(c_171,plain,(
    ! [B_41,D_43] : k7_relset_1('#skF_3',B_41,'#skF_3',D_43) = k9_relat_1('#skF_3',D_43) ),
    inference(resolution,[status(thm)],[c_70,c_169])).

tff(c_173,plain,(
    ! [B_41,D_43] : k7_relset_1('#skF_3',B_41,'#skF_3',D_43) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_171])).

tff(c_18,plain,(
    k7_relset_1(k1_xboole_0,'#skF_1','#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_71,plain,(
    k7_relset_1('#skF_3','#skF_1','#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_69,c_18])).

tff(c_176,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_71])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:29:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.17  
% 1.85/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.17  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.94/1.17  
% 1.94/1.17  %Foreground sorts:
% 1.94/1.17  
% 1.94/1.17  
% 1.94/1.17  %Background operators:
% 1.94/1.17  
% 1.94/1.17  
% 1.94/1.17  %Foreground operators:
% 1.94/1.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.94/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.17  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 1.94/1.17  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.94/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.17  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.94/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.94/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.94/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.94/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.94/1.17  
% 1.94/1.18  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.94/1.18  tff(f_54, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k7_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_2)).
% 1.94/1.18  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.94/1.18  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.94/1.18  tff(f_41, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.94/1.18  tff(f_45, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 1.94/1.18  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.94/1.18  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.94/1.18  tff(c_25, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_20])).
% 1.94/1.18  tff(c_57, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~m1_subset_1(A_17, k1_zfmisc_1(B_18)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.94/1.18  tff(c_65, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_25, c_57])).
% 1.94/1.18  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.94/1.18  tff(c_69, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_65, c_2])).
% 1.94/1.18  tff(c_14, plain, (![A_6]: (k9_relat_1(k1_xboole_0, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.94/1.18  tff(c_73, plain, (![A_6]: (k9_relat_1('#skF_3', A_6)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_69, c_14])).
% 1.94/1.18  tff(c_70, plain, (r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_65])).
% 1.94/1.18  tff(c_76, plain, (![B_3]: (k2_zfmisc_1('#skF_3', B_3)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_69, c_8])).
% 1.94/1.18  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.94/1.18  tff(c_134, plain, (![A_25, B_26, C_27, D_28]: (k7_relset_1(A_25, B_26, C_27, D_28)=k9_relat_1(C_27, D_28) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.94/1.18  tff(c_164, plain, (![A_37, B_38, A_39, D_40]: (k7_relset_1(A_37, B_38, A_39, D_40)=k9_relat_1(A_39, D_40) | ~r1_tarski(A_39, k2_zfmisc_1(A_37, B_38)))), inference(resolution, [status(thm)], [c_12, c_134])).
% 1.94/1.18  tff(c_169, plain, (![B_41, A_42, D_43]: (k7_relset_1('#skF_3', B_41, A_42, D_43)=k9_relat_1(A_42, D_43) | ~r1_tarski(A_42, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_164])).
% 1.94/1.18  tff(c_171, plain, (![B_41, D_43]: (k7_relset_1('#skF_3', B_41, '#skF_3', D_43)=k9_relat_1('#skF_3', D_43))), inference(resolution, [status(thm)], [c_70, c_169])).
% 1.94/1.18  tff(c_173, plain, (![B_41, D_43]: (k7_relset_1('#skF_3', B_41, '#skF_3', D_43)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_171])).
% 1.94/1.18  tff(c_18, plain, (k7_relset_1(k1_xboole_0, '#skF_1', '#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.94/1.18  tff(c_71, plain, (k7_relset_1('#skF_3', '#skF_1', '#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_69, c_69, c_18])).
% 1.94/1.18  tff(c_176, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_173, c_71])).
% 1.94/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.18  
% 1.94/1.18  Inference rules
% 1.94/1.18  ----------------------
% 1.94/1.18  #Ref     : 0
% 1.94/1.18  #Sup     : 36
% 1.94/1.18  #Fact    : 0
% 1.94/1.18  #Define  : 0
% 1.94/1.18  #Split   : 0
% 1.94/1.18  #Chain   : 0
% 1.94/1.18  #Close   : 0
% 1.94/1.18  
% 1.94/1.18  Ordering : KBO
% 1.94/1.18  
% 1.94/1.18  Simplification rules
% 1.94/1.18  ----------------------
% 1.94/1.18  #Subsume      : 1
% 1.94/1.18  #Demod        : 23
% 1.94/1.18  #Tautology    : 26
% 1.94/1.18  #SimpNegUnit  : 0
% 1.94/1.18  #BackRed      : 9
% 1.94/1.18  
% 1.94/1.18  #Partial instantiations: 0
% 1.94/1.18  #Strategies tried      : 1
% 1.94/1.18  
% 1.94/1.19  Timing (in seconds)
% 1.94/1.19  ----------------------
% 1.94/1.19  Preprocessing        : 0.29
% 1.94/1.19  Parsing              : 0.15
% 1.94/1.19  CNF conversion       : 0.02
% 1.94/1.19  Main loop            : 0.14
% 1.94/1.19  Inferencing          : 0.05
% 1.94/1.19  Reduction            : 0.05
% 1.94/1.19  Demodulation         : 0.04
% 1.94/1.19  BG Simplification    : 0.01
% 1.94/1.19  Subsumption          : 0.02
% 1.94/1.19  Abstraction          : 0.01
% 1.94/1.19  MUC search           : 0.00
% 1.94/1.19  Cooper               : 0.00
% 1.94/1.19  Total                : 0.46
% 1.94/1.19  Index Insertion      : 0.00
% 1.94/1.19  Index Deletion       : 0.00
% 1.94/1.19  Index Matching       : 0.00
% 1.94/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
