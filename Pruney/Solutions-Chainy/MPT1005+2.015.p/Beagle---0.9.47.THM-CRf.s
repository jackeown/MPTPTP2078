%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:01 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 102 expanded)
%              Number of leaves         :   22 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :   43 ( 155 expanded)
%              Number of equality atoms :   19 (  56 expanded)
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

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k7_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_31,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_26])).

tff(c_64,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_68,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_31,c_64])).

tff(c_85,plain,(
    ! [B_24,A_25] :
      ( B_24 = A_25
      | ~ r1_tarski(B_24,A_25)
      | ~ r1_tarski(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_87,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_85])).

tff(c_94,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_87])).

tff(c_20,plain,(
    ! [A_8] : k9_relat_1(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_104,plain,(
    ! [A_8] : k9_relat_1('#skF_3',A_8) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_94,c_20])).

tff(c_108,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_8])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_114,plain,(
    ! [A_26,B_27,C_28,D_29] :
      ( k7_relset_1(A_26,B_27,C_28,D_29) = k9_relat_1(C_28,D_29)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_175,plain,(
    ! [A_35,B_36,A_37,D_38] :
      ( k7_relset_1(A_35,B_36,A_37,D_38) = k9_relat_1(A_37,D_38)
      | ~ r1_tarski(A_37,k2_zfmisc_1(A_35,B_36)) ) ),
    inference(resolution,[status(thm)],[c_18,c_114])).

tff(c_182,plain,(
    ! [A_35,B_36,D_38] : k7_relset_1(A_35,B_36,'#skF_3',D_38) = k9_relat_1('#skF_3',D_38) ),
    inference(resolution,[status(thm)],[c_108,c_175])).

tff(c_187,plain,(
    ! [A_35,B_36,D_38] : k7_relset_1(A_35,B_36,'#skF_3',D_38) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_182])).

tff(c_24,plain,(
    k7_relset_1(k1_xboole_0,'#skF_1','#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_102,plain,(
    k7_relset_1('#skF_3','#skF_1','#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_94,c_24])).

tff(c_191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_102])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:35:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.16  
% 1.65/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.17  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.65/1.17  
% 1.65/1.17  %Foreground sorts:
% 1.65/1.17  
% 1.65/1.17  
% 1.65/1.17  %Background operators:
% 1.65/1.17  
% 1.65/1.17  
% 1.65/1.17  %Foreground operators:
% 1.65/1.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.65/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.65/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.65/1.17  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 1.65/1.17  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.65/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.17  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.65/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.65/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.65/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.65/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.65/1.17  
% 1.84/1.18  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.84/1.18  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.84/1.18  tff(f_58, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k7_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_2)).
% 1.84/1.18  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.84/1.18  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.84/1.18  tff(f_45, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 1.84/1.18  tff(f_49, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 1.84/1.18  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.84/1.18  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.84/1.18  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.84/1.18  tff(c_31, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_26])).
% 1.84/1.18  tff(c_64, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | ~m1_subset_1(A_18, k1_zfmisc_1(B_19)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.84/1.18  tff(c_68, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_31, c_64])).
% 1.84/1.18  tff(c_85, plain, (![B_24, A_25]: (B_24=A_25 | ~r1_tarski(B_24, A_25) | ~r1_tarski(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.84/1.18  tff(c_87, plain, (k1_xboole_0='#skF_3' | ~r1_tarski(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_68, c_85])).
% 1.84/1.18  tff(c_94, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_87])).
% 1.84/1.18  tff(c_20, plain, (![A_8]: (k9_relat_1(k1_xboole_0, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.84/1.18  tff(c_104, plain, (![A_8]: (k9_relat_1('#skF_3', A_8)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_94, c_20])).
% 1.84/1.18  tff(c_108, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_8])).
% 1.84/1.18  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.84/1.18  tff(c_114, plain, (![A_26, B_27, C_28, D_29]: (k7_relset_1(A_26, B_27, C_28, D_29)=k9_relat_1(C_28, D_29) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.84/1.18  tff(c_175, plain, (![A_35, B_36, A_37, D_38]: (k7_relset_1(A_35, B_36, A_37, D_38)=k9_relat_1(A_37, D_38) | ~r1_tarski(A_37, k2_zfmisc_1(A_35, B_36)))), inference(resolution, [status(thm)], [c_18, c_114])).
% 1.84/1.18  tff(c_182, plain, (![A_35, B_36, D_38]: (k7_relset_1(A_35, B_36, '#skF_3', D_38)=k9_relat_1('#skF_3', D_38))), inference(resolution, [status(thm)], [c_108, c_175])).
% 1.84/1.18  tff(c_187, plain, (![A_35, B_36, D_38]: (k7_relset_1(A_35, B_36, '#skF_3', D_38)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_182])).
% 1.84/1.18  tff(c_24, plain, (k7_relset_1(k1_xboole_0, '#skF_1', '#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.84/1.18  tff(c_102, plain, (k7_relset_1('#skF_3', '#skF_1', '#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_94, c_24])).
% 1.84/1.18  tff(c_191, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_187, c_102])).
% 1.84/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.18  
% 1.84/1.18  Inference rules
% 1.84/1.18  ----------------------
% 1.84/1.18  #Ref     : 0
% 1.84/1.18  #Sup     : 36
% 1.84/1.18  #Fact    : 0
% 1.84/1.18  #Define  : 0
% 1.84/1.18  #Split   : 0
% 1.84/1.18  #Chain   : 0
% 1.84/1.18  #Close   : 0
% 1.84/1.18  
% 1.84/1.18  Ordering : KBO
% 1.84/1.18  
% 1.84/1.18  Simplification rules
% 1.84/1.18  ----------------------
% 1.84/1.18  #Subsume      : 1
% 1.84/1.18  #Demod        : 25
% 1.84/1.18  #Tautology    : 27
% 1.84/1.18  #SimpNegUnit  : 0
% 1.84/1.18  #BackRed      : 10
% 1.84/1.18  
% 1.84/1.18  #Partial instantiations: 0
% 1.84/1.18  #Strategies tried      : 1
% 1.84/1.18  
% 1.84/1.18  Timing (in seconds)
% 1.84/1.18  ----------------------
% 1.84/1.18  Preprocessing        : 0.27
% 1.84/1.18  Parsing              : 0.14
% 1.84/1.18  CNF conversion       : 0.02
% 1.84/1.18  Main loop            : 0.13
% 1.84/1.18  Inferencing          : 0.04
% 1.84/1.18  Reduction            : 0.04
% 1.84/1.18  Demodulation         : 0.03
% 1.84/1.18  BG Simplification    : 0.01
% 1.84/1.18  Subsumption          : 0.02
% 1.84/1.18  Abstraction          : 0.01
% 1.84/1.18  MUC search           : 0.00
% 1.84/1.18  Cooper               : 0.00
% 1.84/1.18  Total                : 0.43
% 1.84/1.18  Index Insertion      : 0.00
% 1.84/1.18  Index Deletion       : 0.00
% 1.84/1.18  Index Matching       : 0.00
% 1.84/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
