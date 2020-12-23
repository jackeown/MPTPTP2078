%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:02 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 127 expanded)
%              Number of leaves         :   21 (  56 expanded)
%              Depth                    :    9
%              Number of atoms          :   34 ( 174 expanded)
%              Number of equality atoms :   22 ( 112 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_34,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_51,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k7_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_8,plain,(
    ! [A_3] : k9_relat_1(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_23,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_18])).

tff(c_68,plain,(
    ! [A_15,B_16] :
      ( k9_relat_1(k6_relat_1(A_15),B_16) = B_16
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_71,plain,(
    k9_relat_1(k6_relat_1(k1_xboole_0),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_23,c_68])).

tff(c_73,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10,c_71])).

tff(c_78,plain,(
    ! [A_3] : k9_relat_1('#skF_3',A_3) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_73,c_8])).

tff(c_79,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_23])).

tff(c_105,plain,(
    ! [B_22] : k2_zfmisc_1('#skF_3',B_22) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_73,c_6])).

tff(c_14,plain,(
    ! [A_6,B_7,C_8,D_9] :
      ( k7_relset_1(A_6,B_7,C_8,D_9) = k9_relat_1(C_8,D_9)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_141,plain,(
    ! [B_26,C_27,D_28] :
      ( k7_relset_1('#skF_3',B_26,C_27,D_28) = k9_relat_1(C_27,D_28)
      | ~ m1_subset_1(C_27,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_14])).

tff(c_143,plain,(
    ! [B_26,D_28] : k7_relset_1('#skF_3',B_26,'#skF_3',D_28) = k9_relat_1('#skF_3',D_28) ),
    inference(resolution,[status(thm)],[c_79,c_141])).

tff(c_145,plain,(
    ! [B_26,D_28] : k7_relset_1('#skF_3',B_26,'#skF_3',D_28) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_143])).

tff(c_16,plain,(
    k7_relset_1(k1_xboole_0,'#skF_1','#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_75,plain,(
    k7_relset_1('#skF_3','#skF_1','#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_73,c_16])).

tff(c_148,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_75])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:55:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.25  
% 1.88/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.25  %$ v1_funct_2 > m1_subset_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.88/1.25  
% 1.88/1.25  %Foreground sorts:
% 1.88/1.25  
% 1.88/1.25  
% 1.88/1.25  %Background operators:
% 1.88/1.25  
% 1.88/1.25  
% 1.88/1.25  %Foreground operators:
% 1.88/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.88/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.88/1.25  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 1.88/1.25  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.88/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.25  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.88/1.25  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.88/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.88/1.25  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.88/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.88/1.25  
% 1.88/1.26  tff(f_33, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.88/1.26  tff(f_34, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 1.88/1.26  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.88/1.26  tff(f_51, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k7_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_2)).
% 1.88/1.26  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 1.88/1.26  tff(f_42, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 1.88/1.26  tff(c_8, plain, (![A_3]: (k9_relat_1(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.88/1.26  tff(c_10, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.88/1.26  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.88/1.26  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.88/1.26  tff(c_23, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_18])).
% 1.88/1.26  tff(c_68, plain, (![A_15, B_16]: (k9_relat_1(k6_relat_1(A_15), B_16)=B_16 | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.88/1.26  tff(c_71, plain, (k9_relat_1(k6_relat_1(k1_xboole_0), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_23, c_68])).
% 1.88/1.26  tff(c_73, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10, c_71])).
% 1.88/1.26  tff(c_78, plain, (![A_3]: (k9_relat_1('#skF_3', A_3)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_73, c_8])).
% 1.88/1.26  tff(c_79, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_23])).
% 1.88/1.26  tff(c_105, plain, (![B_22]: (k2_zfmisc_1('#skF_3', B_22)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_73, c_6])).
% 1.88/1.26  tff(c_14, plain, (![A_6, B_7, C_8, D_9]: (k7_relset_1(A_6, B_7, C_8, D_9)=k9_relat_1(C_8, D_9) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.88/1.26  tff(c_141, plain, (![B_26, C_27, D_28]: (k7_relset_1('#skF_3', B_26, C_27, D_28)=k9_relat_1(C_27, D_28) | ~m1_subset_1(C_27, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_105, c_14])).
% 1.88/1.26  tff(c_143, plain, (![B_26, D_28]: (k7_relset_1('#skF_3', B_26, '#skF_3', D_28)=k9_relat_1('#skF_3', D_28))), inference(resolution, [status(thm)], [c_79, c_141])).
% 1.88/1.26  tff(c_145, plain, (![B_26, D_28]: (k7_relset_1('#skF_3', B_26, '#skF_3', D_28)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_143])).
% 1.88/1.26  tff(c_16, plain, (k7_relset_1(k1_xboole_0, '#skF_1', '#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.88/1.26  tff(c_75, plain, (k7_relset_1('#skF_3', '#skF_1', '#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_73, c_73, c_16])).
% 1.88/1.26  tff(c_148, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_145, c_75])).
% 1.88/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.26  
% 1.88/1.26  Inference rules
% 1.88/1.26  ----------------------
% 1.88/1.26  #Ref     : 0
% 1.88/1.26  #Sup     : 31
% 1.88/1.26  #Fact    : 0
% 1.88/1.26  #Define  : 0
% 1.88/1.26  #Split   : 0
% 1.88/1.26  #Chain   : 0
% 1.88/1.26  #Close   : 0
% 1.88/1.26  
% 1.88/1.26  Ordering : KBO
% 1.88/1.26  
% 1.88/1.26  Simplification rules
% 1.88/1.26  ----------------------
% 1.88/1.26  #Subsume      : 0
% 1.88/1.26  #Demod        : 22
% 1.88/1.26  #Tautology    : 27
% 1.88/1.26  #SimpNegUnit  : 0
% 1.88/1.26  #BackRed      : 9
% 1.88/1.26  
% 1.88/1.26  #Partial instantiations: 0
% 1.88/1.26  #Strategies tried      : 1
% 1.88/1.26  
% 1.88/1.26  Timing (in seconds)
% 1.88/1.26  ----------------------
% 1.88/1.26  Preprocessing        : 0.38
% 1.88/1.26  Parsing              : 0.19
% 1.88/1.26  CNF conversion       : 0.02
% 1.88/1.26  Main loop            : 0.11
% 1.88/1.26  Inferencing          : 0.04
% 1.88/1.26  Reduction            : 0.04
% 1.88/1.26  Demodulation         : 0.03
% 1.88/1.26  BG Simplification    : 0.01
% 1.88/1.26  Subsumption          : 0.01
% 1.88/1.26  Abstraction          : 0.01
% 1.88/1.26  MUC search           : 0.00
% 1.88/1.26  Cooper               : 0.00
% 1.88/1.26  Total                : 0.51
% 1.88/1.27  Index Insertion      : 0.00
% 1.88/1.27  Index Deletion       : 0.00
% 1.88/1.27  Index Matching       : 0.00
% 1.88/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
