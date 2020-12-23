%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:04 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 177 expanded)
%              Number of leaves         :   23 (  71 expanded)
%              Depth                    :   10
%              Number of atoms          :   46 ( 272 expanded)
%              Number of equality atoms :   21 (  98 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

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
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_45,axiom,(
    ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_2,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_33,plain,(
    ! [A_13] :
      ( k1_xboole_0 = A_13
      | ~ v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_37,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_33])).

tff(c_38,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_2])).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_25,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_20])).

tff(c_81,plain,(
    ! [B_18,A_19] :
      ( v1_xboole_0(B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_19))
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_84,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_25,c_81])).

tff(c_87,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_84])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_91,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_87,c_4])).

tff(c_14,plain,(
    ! [A_7] : k10_relat_1(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_95,plain,(
    ! [A_7] : k10_relat_1('#skF_3',A_7) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_91,c_14])).

tff(c_100,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_25])).

tff(c_119,plain,(
    ! [B_25] : k2_zfmisc_1('#skF_3',B_25) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_91,c_10])).

tff(c_16,plain,(
    ! [A_8,B_9,C_10,D_11] :
      ( k8_relset_1(A_8,B_9,C_10,D_11) = k10_relat_1(C_10,D_11)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_180,plain,(
    ! [B_35,C_36,D_37] :
      ( k8_relset_1('#skF_3',B_35,C_36,D_37) = k10_relat_1(C_36,D_37)
      | ~ m1_subset_1(C_36,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_16])).

tff(c_182,plain,(
    ! [B_35,D_37] : k8_relset_1('#skF_3',B_35,'#skF_3',D_37) = k10_relat_1('#skF_3',D_37) ),
    inference(resolution,[status(thm)],[c_100,c_180])).

tff(c_184,plain,(
    ! [B_35,D_37] : k8_relset_1('#skF_3',B_35,'#skF_3',D_37) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_182])).

tff(c_18,plain,(
    k8_relset_1(k1_xboole_0,'#skF_1','#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_94,plain,(
    k8_relset_1('#skF_3','#skF_1','#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_91,c_18])).

tff(c_187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_94])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:16:47 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.15  
% 1.70/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.15  %$ v1_funct_2 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.70/1.15  
% 1.70/1.15  %Foreground sorts:
% 1.70/1.15  
% 1.70/1.15  
% 1.70/1.15  %Background operators:
% 1.70/1.15  
% 1.70/1.15  
% 1.70/1.15  %Foreground operators:
% 1.70/1.15  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 1.70/1.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.70/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.15  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.70/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.70/1.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.70/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.70/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.70/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.70/1.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.70/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.15  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.70/1.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.70/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.70/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.70/1.15  
% 1.70/1.16  tff(f_26, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 1.70/1.16  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.70/1.16  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.70/1.16  tff(f_58, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_funct_2)).
% 1.70/1.16  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 1.70/1.16  tff(f_45, axiom, (![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 1.70/1.16  tff(f_49, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 1.70/1.16  tff(c_2, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.70/1.16  tff(c_33, plain, (![A_13]: (k1_xboole_0=A_13 | ~v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.70/1.16  tff(c_37, plain, (o_0_0_xboole_0=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_33])).
% 1.70/1.16  tff(c_38, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_37, c_2])).
% 1.70/1.16  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.70/1.16  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.70/1.16  tff(c_25, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_20])).
% 1.70/1.16  tff(c_81, plain, (![B_18, A_19]: (v1_xboole_0(B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(A_19)) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.70/1.16  tff(c_84, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_25, c_81])).
% 1.70/1.16  tff(c_87, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_84])).
% 1.70/1.16  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.70/1.16  tff(c_91, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_87, c_4])).
% 1.70/1.16  tff(c_14, plain, (![A_7]: (k10_relat_1(k1_xboole_0, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.70/1.16  tff(c_95, plain, (![A_7]: (k10_relat_1('#skF_3', A_7)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_91, c_14])).
% 1.70/1.16  tff(c_100, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_25])).
% 1.70/1.16  tff(c_119, plain, (![B_25]: (k2_zfmisc_1('#skF_3', B_25)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_91, c_10])).
% 1.70/1.16  tff(c_16, plain, (![A_8, B_9, C_10, D_11]: (k8_relset_1(A_8, B_9, C_10, D_11)=k10_relat_1(C_10, D_11) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.70/1.16  tff(c_180, plain, (![B_35, C_36, D_37]: (k8_relset_1('#skF_3', B_35, C_36, D_37)=k10_relat_1(C_36, D_37) | ~m1_subset_1(C_36, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_119, c_16])).
% 1.70/1.16  tff(c_182, plain, (![B_35, D_37]: (k8_relset_1('#skF_3', B_35, '#skF_3', D_37)=k10_relat_1('#skF_3', D_37))), inference(resolution, [status(thm)], [c_100, c_180])).
% 1.70/1.16  tff(c_184, plain, (![B_35, D_37]: (k8_relset_1('#skF_3', B_35, '#skF_3', D_37)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_182])).
% 1.70/1.16  tff(c_18, plain, (k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.70/1.16  tff(c_94, plain, (k8_relset_1('#skF_3', '#skF_1', '#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_91, c_91, c_18])).
% 1.70/1.16  tff(c_187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_184, c_94])).
% 1.70/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.16  
% 1.70/1.16  Inference rules
% 1.70/1.16  ----------------------
% 1.70/1.16  #Ref     : 0
% 1.70/1.16  #Sup     : 38
% 1.70/1.16  #Fact    : 0
% 1.70/1.16  #Define  : 0
% 1.70/1.16  #Split   : 0
% 1.70/1.16  #Chain   : 0
% 1.70/1.16  #Close   : 0
% 1.70/1.16  
% 1.70/1.16  Ordering : KBO
% 1.70/1.16  
% 1.70/1.16  Simplification rules
% 1.70/1.16  ----------------------
% 1.70/1.16  #Subsume      : 0
% 1.70/1.16  #Demod        : 25
% 1.70/1.16  #Tautology    : 32
% 1.70/1.16  #SimpNegUnit  : 0
% 1.70/1.16  #BackRed      : 12
% 1.70/1.16  
% 1.70/1.16  #Partial instantiations: 0
% 1.70/1.16  #Strategies tried      : 1
% 1.70/1.16  
% 1.70/1.16  Timing (in seconds)
% 1.70/1.16  ----------------------
% 1.70/1.16  Preprocessing        : 0.28
% 1.70/1.16  Parsing              : 0.15
% 1.70/1.16  CNF conversion       : 0.02
% 1.70/1.16  Main loop            : 0.12
% 1.70/1.16  Inferencing          : 0.04
% 1.70/1.16  Reduction            : 0.04
% 1.70/1.16  Demodulation         : 0.03
% 1.70/1.16  BG Simplification    : 0.01
% 1.70/1.16  Subsumption          : 0.02
% 1.70/1.16  Abstraction          : 0.01
% 1.70/1.16  MUC search           : 0.00
% 1.70/1.16  Cooper               : 0.00
% 1.70/1.16  Total                : 0.43
% 1.70/1.16  Index Insertion      : 0.00
% 1.70/1.16  Index Deletion       : 0.00
% 1.70/1.16  Index Matching       : 0.00
% 1.70/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
