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
% DateTime   : Thu Dec  3 10:08:41 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   44 (  55 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 (  73 expanded)
%              Number of equality atoms :   15 (  20 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => ( r1_xboole_0(B,C)
         => k5_relset_1(C,A,D,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_18,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_21,plain,(
    ! [B_18,A_19] :
      ( r1_xboole_0(B_18,A_19)
      | ~ r1_xboole_0(A_19,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_21])).

tff(c_20,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_29,plain,(
    ! [C_20,A_21,B_22] :
      ( v1_relat_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_33,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_29])).

tff(c_34,plain,(
    ! [C_23,A_24,B_25] :
      ( v4_relat_1(C_23,A_24)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_38,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_34])).

tff(c_39,plain,(
    ! [B_26,A_27] :
      ( k7_relat_1(B_26,A_27) = B_26
      | ~ v4_relat_1(B_26,A_27)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_42,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_39])).

tff(c_45,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_42])).

tff(c_55,plain,(
    ! [C_31,A_32,B_33] :
      ( k7_relat_1(k7_relat_1(C_31,A_32),B_33) = k1_xboole_0
      | ~ r1_xboole_0(A_32,B_33)
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_70,plain,(
    ! [B_33] :
      ( k7_relat_1('#skF_4',B_33) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_33)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_55])).

tff(c_75,plain,(
    ! [B_34] :
      ( k7_relat_1('#skF_4',B_34) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_70])).

tff(c_79,plain,(
    k7_relat_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_75])).

tff(c_80,plain,(
    ! [A_35,B_36,C_37,D_38] :
      ( k5_relset_1(A_35,B_36,C_37,D_38) = k7_relat_1(C_37,D_38)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_83,plain,(
    ! [D_38] : k5_relset_1('#skF_3','#skF_1','#skF_4',D_38) = k7_relat_1('#skF_4',D_38) ),
    inference(resolution,[status(thm)],[c_20,c_80])).

tff(c_16,plain,(
    k5_relset_1('#skF_3','#skF_1','#skF_4','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_105,plain,(
    k7_relat_1('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_16])).

tff(c_108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_105])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:20:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.16  
% 1.86/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.16  %$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.86/1.16  
% 1.86/1.16  %Foreground sorts:
% 1.86/1.16  
% 1.86/1.16  
% 1.86/1.16  %Background operators:
% 1.86/1.16  
% 1.86/1.16  
% 1.86/1.16  %Foreground operators:
% 1.86/1.16  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 1.86/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.16  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.86/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.86/1.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.86/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.86/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.86/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.86/1.16  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.86/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.86/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.86/1.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.86/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.86/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.16  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.86/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.86/1.16  
% 1.86/1.17  tff(f_62, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_xboole_0(B, C) => (k5_relset_1(C, A, D, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relset_1)).
% 1.86/1.17  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.86/1.17  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.86/1.17  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.86/1.17  tff(f_41, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 1.86/1.17  tff(f_35, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 1.86/1.17  tff(f_55, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 1.86/1.17  tff(c_18, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.86/1.17  tff(c_21, plain, (![B_18, A_19]: (r1_xboole_0(B_18, A_19) | ~r1_xboole_0(A_19, B_18))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.86/1.17  tff(c_24, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_18, c_21])).
% 1.86/1.17  tff(c_20, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.86/1.17  tff(c_29, plain, (![C_20, A_21, B_22]: (v1_relat_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.86/1.17  tff(c_33, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_29])).
% 1.86/1.17  tff(c_34, plain, (![C_23, A_24, B_25]: (v4_relat_1(C_23, A_24) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.86/1.17  tff(c_38, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_34])).
% 1.86/1.17  tff(c_39, plain, (![B_26, A_27]: (k7_relat_1(B_26, A_27)=B_26 | ~v4_relat_1(B_26, A_27) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.86/1.17  tff(c_42, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_39])).
% 1.86/1.17  tff(c_45, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_33, c_42])).
% 1.86/1.17  tff(c_55, plain, (![C_31, A_32, B_33]: (k7_relat_1(k7_relat_1(C_31, A_32), B_33)=k1_xboole_0 | ~r1_xboole_0(A_32, B_33) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.86/1.17  tff(c_70, plain, (![B_33]: (k7_relat_1('#skF_4', B_33)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_33) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_45, c_55])).
% 1.86/1.17  tff(c_75, plain, (![B_34]: (k7_relat_1('#skF_4', B_34)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_34))), inference(demodulation, [status(thm), theory('equality')], [c_33, c_70])).
% 1.86/1.17  tff(c_79, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_75])).
% 1.86/1.17  tff(c_80, plain, (![A_35, B_36, C_37, D_38]: (k5_relset_1(A_35, B_36, C_37, D_38)=k7_relat_1(C_37, D_38) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.86/1.17  tff(c_83, plain, (![D_38]: (k5_relset_1('#skF_3', '#skF_1', '#skF_4', D_38)=k7_relat_1('#skF_4', D_38))), inference(resolution, [status(thm)], [c_20, c_80])).
% 1.86/1.17  tff(c_16, plain, (k5_relset_1('#skF_3', '#skF_1', '#skF_4', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.86/1.17  tff(c_105, plain, (k7_relat_1('#skF_4', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_83, c_16])).
% 1.86/1.17  tff(c_108, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_105])).
% 1.86/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.17  
% 1.86/1.17  Inference rules
% 1.86/1.17  ----------------------
% 1.86/1.17  #Ref     : 0
% 1.86/1.17  #Sup     : 22
% 1.86/1.17  #Fact    : 0
% 1.86/1.17  #Define  : 0
% 1.86/1.17  #Split   : 0
% 1.86/1.17  #Chain   : 0
% 1.86/1.17  #Close   : 0
% 1.86/1.17  
% 1.86/1.17  Ordering : KBO
% 1.86/1.17  
% 1.86/1.17  Simplification rules
% 1.86/1.17  ----------------------
% 1.86/1.17  #Subsume      : 0
% 1.86/1.17  #Demod        : 6
% 1.86/1.17  #Tautology    : 9
% 1.86/1.17  #SimpNegUnit  : 0
% 1.86/1.17  #BackRed      : 1
% 1.86/1.17  
% 1.86/1.17  #Partial instantiations: 0
% 1.86/1.17  #Strategies tried      : 1
% 1.86/1.17  
% 1.86/1.17  Timing (in seconds)
% 1.86/1.17  ----------------------
% 1.86/1.18  Preprocessing        : 0.29
% 1.86/1.18  Parsing              : 0.15
% 1.86/1.18  CNF conversion       : 0.02
% 1.86/1.18  Main loop            : 0.12
% 1.86/1.18  Inferencing          : 0.05
% 1.86/1.18  Reduction            : 0.04
% 1.86/1.18  Demodulation         : 0.03
% 1.86/1.18  BG Simplification    : 0.01
% 1.86/1.18  Subsumption          : 0.02
% 1.86/1.18  Abstraction          : 0.01
% 1.86/1.18  MUC search           : 0.00
% 1.86/1.18  Cooper               : 0.00
% 1.86/1.18  Total                : 0.43
% 1.86/1.18  Index Insertion      : 0.00
% 1.86/1.18  Index Deletion       : 0.00
% 1.86/1.18  Index Matching       : 0.00
% 1.86/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
