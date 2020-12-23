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
% DateTime   : Thu Dec  3 10:14:01 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   37 (  84 expanded)
%              Number of leaves         :   21 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   34 ( 127 expanded)
%              Number of equality atoms :   13 (  31 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k7_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_32,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_14,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_32,plain,(
    ! [C_13,A_14,B_15] :
      ( v1_xboole_0(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15)))
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_35,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_32])).

tff(c_38,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_35])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_42,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_4])).

tff(c_6,plain,(
    ! [A_2] : k9_relat_1(k1_xboole_0,A_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_45,plain,(
    ! [A_2] : k9_relat_1('#skF_3',A_2) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_6])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_14])).

tff(c_73,plain,(
    ! [A_18,B_19,C_20,D_21] :
      ( k7_relset_1(A_18,B_19,C_20,D_21) = k9_relat_1(C_20,D_21)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_75,plain,(
    ! [D_21] : k7_relset_1('#skF_3','#skF_1','#skF_3',D_21) = k9_relat_1('#skF_3',D_21) ),
    inference(resolution,[status(thm)],[c_44,c_73])).

tff(c_77,plain,(
    ! [D_21] : k7_relset_1('#skF_3','#skF_1','#skF_3',D_21) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_75])).

tff(c_12,plain,(
    k7_relset_1(k1_xboole_0,'#skF_1','#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_43,plain,(
    k7_relset_1('#skF_3','#skF_1','#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_12])).

tff(c_80,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:02:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.49  
% 2.04/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.50  %$ v1_funct_2 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.04/1.50  
% 2.04/1.50  %Foreground sorts:
% 2.04/1.50  
% 2.04/1.50  
% 2.04/1.50  %Background operators:
% 2.04/1.50  
% 2.04/1.50  
% 2.04/1.50  %Foreground operators:
% 2.04/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.04/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.04/1.50  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.04/1.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.04/1.50  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.50  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.04/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.04/1.50  tff('#skF_1', type, '#skF_1': $i).
% 2.04/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.04/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.04/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.04/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.04/1.50  
% 2.04/1.51  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.04/1.51  tff(f_52, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k7_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_2)).
% 2.04/1.51  tff(f_39, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 2.04/1.51  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.04/1.51  tff(f_32, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 2.04/1.51  tff(f_43, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.04/1.51  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.04/1.51  tff(c_14, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.04/1.51  tff(c_32, plain, (![C_13, A_14, B_15]: (v1_xboole_0(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))) | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.04/1.51  tff(c_35, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_32])).
% 2.04/1.51  tff(c_38, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_35])).
% 2.04/1.51  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.04/1.51  tff(c_42, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_38, c_4])).
% 2.04/1.51  tff(c_6, plain, (![A_2]: (k9_relat_1(k1_xboole_0, A_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.04/1.51  tff(c_45, plain, (![A_2]: (k9_relat_1('#skF_3', A_2)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_6])).
% 2.04/1.51  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_14])).
% 2.04/1.51  tff(c_73, plain, (![A_18, B_19, C_20, D_21]: (k7_relset_1(A_18, B_19, C_20, D_21)=k9_relat_1(C_20, D_21) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.04/1.51  tff(c_75, plain, (![D_21]: (k7_relset_1('#skF_3', '#skF_1', '#skF_3', D_21)=k9_relat_1('#skF_3', D_21))), inference(resolution, [status(thm)], [c_44, c_73])).
% 2.04/1.51  tff(c_77, plain, (![D_21]: (k7_relset_1('#skF_3', '#skF_1', '#skF_3', D_21)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_45, c_75])).
% 2.04/1.51  tff(c_12, plain, (k7_relset_1(k1_xboole_0, '#skF_1', '#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.04/1.51  tff(c_43, plain, (k7_relset_1('#skF_3', '#skF_1', '#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_12])).
% 2.04/1.51  tff(c_80, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_43])).
% 2.04/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.51  
% 2.04/1.51  Inference rules
% 2.04/1.51  ----------------------
% 2.04/1.51  #Ref     : 0
% 2.04/1.51  #Sup     : 12
% 2.04/1.51  #Fact    : 0
% 2.04/1.51  #Define  : 0
% 2.04/1.51  #Split   : 0
% 2.04/1.51  #Chain   : 0
% 2.04/1.51  #Close   : 0
% 2.04/1.51  
% 2.04/1.51  Ordering : KBO
% 2.04/1.51  
% 2.04/1.51  Simplification rules
% 2.04/1.51  ----------------------
% 2.04/1.51  #Subsume      : 0
% 2.04/1.51  #Demod        : 14
% 2.04/1.51  #Tautology    : 10
% 2.04/1.51  #SimpNegUnit  : 0
% 2.04/1.51  #BackRed      : 7
% 2.04/1.51  
% 2.04/1.52  #Partial instantiations: 0
% 2.04/1.52  #Strategies tried      : 1
% 2.04/1.52  
% 2.04/1.52  Timing (in seconds)
% 2.04/1.52  ----------------------
% 2.04/1.52  Preprocessing        : 0.44
% 2.04/1.52  Parsing              : 0.23
% 2.04/1.52  CNF conversion       : 0.03
% 2.04/1.52  Main loop            : 0.15
% 2.04/1.52  Inferencing          : 0.06
% 2.04/1.52  Reduction            : 0.05
% 2.04/1.52  Demodulation         : 0.04
% 2.04/1.52  BG Simplification    : 0.01
% 2.04/1.52  Subsumption          : 0.02
% 2.04/1.52  Abstraction          : 0.01
% 2.04/1.52  MUC search           : 0.00
% 2.04/1.52  Cooper               : 0.00
% 2.04/1.52  Total                : 0.63
% 2.04/1.52  Index Insertion      : 0.00
% 2.04/1.52  Index Deletion       : 0.00
% 2.04/1.52  Index Matching       : 0.00
% 2.04/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
