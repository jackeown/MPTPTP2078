%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:01 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 155 expanded)
%              Number of leaves         :   22 (  63 expanded)
%              Depth                    :   10
%              Number of atoms          :   46 ( 265 expanded)
%              Number of equality atoms :   20 ( 105 expanded)
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

tff(f_36,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_25,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_20])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_8,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_72,plain,(
    ! [C_19,B_20,A_21] :
      ( v1_xboole_0(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(B_20,A_21)))
      | ~ v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_78,plain,(
    ! [C_19] :
      ( v1_xboole_0(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_72])).

tff(c_81,plain,(
    ! [C_22] :
      ( v1_xboole_0(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_78])).

tff(c_85,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_25,c_81])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_89,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_85,c_4])).

tff(c_12,plain,(
    ! [A_4] : k9_relat_1(k1_xboole_0,A_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_94,plain,(
    ! [A_4] : k9_relat_1('#skF_3',A_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_89,c_12])).

tff(c_97,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_25])).

tff(c_93,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_3',B_3) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_89,c_10])).

tff(c_115,plain,(
    ! [A_24,B_25,C_26,D_27] :
      ( k7_relset_1(A_24,B_25,C_26,D_27) = k9_relat_1(C_26,D_27)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_183,plain,(
    ! [B_39,C_40,D_41] :
      ( k7_relset_1('#skF_3',B_39,C_40,D_41) = k9_relat_1(C_40,D_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_115])).

tff(c_185,plain,(
    ! [B_39,D_41] : k7_relset_1('#skF_3',B_39,'#skF_3',D_41) = k9_relat_1('#skF_3',D_41) ),
    inference(resolution,[status(thm)],[c_97,c_183])).

tff(c_187,plain,(
    ! [B_39,D_41] : k7_relset_1('#skF_3',B_39,'#skF_3',D_41) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_185])).

tff(c_18,plain,(
    k7_relset_1(k1_xboole_0,'#skF_1','#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_92,plain,(
    k7_relset_1('#skF_3','#skF_1','#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_89,c_18])).

tff(c_190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_92])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:01:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.26  
% 1.94/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.26  %$ v1_funct_2 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.94/1.26  
% 1.94/1.26  %Foreground sorts:
% 1.94/1.26  
% 1.94/1.26  
% 1.94/1.26  %Background operators:
% 1.94/1.26  
% 1.94/1.26  
% 1.94/1.26  %Foreground operators:
% 1.94/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.94/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.26  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 1.94/1.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.94/1.26  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.26  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.94/1.26  tff('#skF_3', type, '#skF_3': $i).
% 1.94/1.26  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.94/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.94/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.94/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.94/1.26  
% 1.94/1.27  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.94/1.27  tff(f_58, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k7_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_2)).
% 1.94/1.27  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.94/1.27  tff(f_45, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 1.94/1.27  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.94/1.27  tff(f_38, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 1.94/1.27  tff(f_49, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 1.94/1.27  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.94/1.27  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.94/1.27  tff(c_25, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_20])).
% 1.94/1.27  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.94/1.27  tff(c_8, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.94/1.27  tff(c_72, plain, (![C_19, B_20, A_21]: (v1_xboole_0(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(B_20, A_21))) | ~v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.94/1.27  tff(c_78, plain, (![C_19]: (v1_xboole_0(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_72])).
% 1.94/1.27  tff(c_81, plain, (![C_22]: (v1_xboole_0(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_78])).
% 1.94/1.27  tff(c_85, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_25, c_81])).
% 1.94/1.27  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.94/1.27  tff(c_89, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_85, c_4])).
% 1.94/1.27  tff(c_12, plain, (![A_4]: (k9_relat_1(k1_xboole_0, A_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.94/1.27  tff(c_94, plain, (![A_4]: (k9_relat_1('#skF_3', A_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_89, c_12])).
% 1.94/1.27  tff(c_97, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_25])).
% 1.94/1.27  tff(c_93, plain, (![B_3]: (k2_zfmisc_1('#skF_3', B_3)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_89, c_10])).
% 1.94/1.27  tff(c_115, plain, (![A_24, B_25, C_26, D_27]: (k7_relset_1(A_24, B_25, C_26, D_27)=k9_relat_1(C_26, D_27) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.94/1.27  tff(c_183, plain, (![B_39, C_40, D_41]: (k7_relset_1('#skF_3', B_39, C_40, D_41)=k9_relat_1(C_40, D_41) | ~m1_subset_1(C_40, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_93, c_115])).
% 1.94/1.27  tff(c_185, plain, (![B_39, D_41]: (k7_relset_1('#skF_3', B_39, '#skF_3', D_41)=k9_relat_1('#skF_3', D_41))), inference(resolution, [status(thm)], [c_97, c_183])).
% 1.94/1.27  tff(c_187, plain, (![B_39, D_41]: (k7_relset_1('#skF_3', B_39, '#skF_3', D_41)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_185])).
% 1.94/1.27  tff(c_18, plain, (k7_relset_1(k1_xboole_0, '#skF_1', '#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.94/1.27  tff(c_92, plain, (k7_relset_1('#skF_3', '#skF_1', '#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_89, c_89, c_18])).
% 1.94/1.27  tff(c_190, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_187, c_92])).
% 1.94/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.27  
% 1.94/1.27  Inference rules
% 1.94/1.27  ----------------------
% 1.94/1.27  #Ref     : 0
% 1.94/1.27  #Sup     : 37
% 1.94/1.27  #Fact    : 0
% 1.94/1.27  #Define  : 0
% 1.94/1.27  #Split   : 0
% 1.94/1.27  #Chain   : 0
% 1.94/1.27  #Close   : 0
% 1.94/1.27  
% 1.94/1.27  Ordering : KBO
% 1.94/1.27  
% 1.94/1.27  Simplification rules
% 1.94/1.27  ----------------------
% 1.94/1.27  #Subsume      : 3
% 1.94/1.27  #Demod        : 25
% 1.94/1.27  #Tautology    : 28
% 1.94/1.27  #SimpNegUnit  : 0
% 1.94/1.27  #BackRed      : 11
% 1.94/1.27  
% 1.94/1.27  #Partial instantiations: 0
% 1.94/1.27  #Strategies tried      : 1
% 1.94/1.27  
% 1.94/1.27  Timing (in seconds)
% 1.94/1.27  ----------------------
% 1.94/1.28  Preprocessing        : 0.31
% 1.94/1.28  Parsing              : 0.17
% 1.94/1.28  CNF conversion       : 0.02
% 1.94/1.28  Main loop            : 0.14
% 1.94/1.28  Inferencing          : 0.05
% 1.94/1.28  Reduction            : 0.05
% 1.94/1.28  Demodulation         : 0.04
% 1.94/1.28  BG Simplification    : 0.01
% 1.94/1.28  Subsumption          : 0.02
% 1.94/1.28  Abstraction          : 0.01
% 1.94/1.28  MUC search           : 0.00
% 1.94/1.28  Cooper               : 0.00
% 1.94/1.28  Total                : 0.48
% 1.94/1.28  Index Insertion      : 0.00
% 1.94/1.28  Index Deletion       : 0.00
% 1.94/1.28  Index Matching       : 0.00
% 1.94/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
