%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:08 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 140 expanded)
%              Number of leaves         :   21 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :   44 ( 208 expanded)
%              Number of equality atoms :   18 (  98 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k8_relset_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(c_10,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_25,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_20])).

tff(c_57,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ m1_subset_1(A_19,k1_zfmisc_1(B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_65,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_25,c_57])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_69,plain,(
    k3_xboole_0('#skF_3',k1_xboole_0) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_65,c_2])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_4])).

tff(c_84,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_25])).

tff(c_82,plain,(
    ! [A_3] : k3_xboole_0(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_72,c_4])).

tff(c_81,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_72,c_10])).

tff(c_147,plain,(
    ! [A_26,B_27,C_28,D_29] :
      ( m1_subset_1(k8_relset_1(A_26,B_27,C_28,D_29),k1_zfmisc_1(A_26))
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_152,plain,(
    ! [A_30,B_31,C_32,D_33] :
      ( r1_tarski(k8_relset_1(A_30,B_31,C_32,D_33),A_30)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(resolution,[status(thm)],[c_147,c_12])).

tff(c_170,plain,(
    ! [B_37,C_38,D_39] :
      ( r1_tarski(k8_relset_1('#skF_3',B_37,C_38,D_39),'#skF_3')
      | ~ m1_subset_1(C_38,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_152])).

tff(c_173,plain,(
    ! [B_37,C_38,D_39] :
      ( k3_xboole_0(k8_relset_1('#skF_3',B_37,C_38,D_39),'#skF_3') = k8_relset_1('#skF_3',B_37,C_38,D_39)
      | ~ m1_subset_1(C_38,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_170,c_2])).

tff(c_176,plain,(
    ! [B_40,C_41,D_42] :
      ( k8_relset_1('#skF_3',B_40,C_41,D_42) = '#skF_3'
      | ~ m1_subset_1(C_41,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_173])).

tff(c_187,plain,(
    ! [B_40,D_42] : k8_relset_1('#skF_3',B_40,'#skF_3',D_42) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_84,c_176])).

tff(c_18,plain,(
    k8_relset_1(k1_xboole_0,'#skF_1','#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_80,plain,(
    k8_relset_1('#skF_3','#skF_1','#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_72,c_18])).

tff(c_191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_80])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:14:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.30  
% 1.86/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.30  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k8_relset_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.86/1.30  
% 1.86/1.30  %Foreground sorts:
% 1.86/1.30  
% 1.86/1.30  
% 1.86/1.30  %Background operators:
% 1.86/1.30  
% 1.86/1.30  
% 1.86/1.30  %Foreground operators:
% 1.86/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.86/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.30  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.86/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.86/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.86/1.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.86/1.30  tff('#skF_2', type, '#skF_2': $i).
% 1.86/1.30  tff('#skF_3', type, '#skF_3': $i).
% 1.86/1.30  tff('#skF_1', type, '#skF_1': $i).
% 1.86/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.86/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.86/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.86/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.86/1.30  
% 2.09/1.31  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.09/1.31  tff(f_54, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_2)).
% 2.09/1.31  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.09/1.31  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.09/1.31  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.09/1.31  tff(f_45, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k8_relset_1(A, B, C, D), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 2.09/1.31  tff(c_10, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.09/1.31  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.09/1.31  tff(c_25, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_20])).
% 2.09/1.31  tff(c_57, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | ~m1_subset_1(A_19, k1_zfmisc_1(B_20)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.09/1.31  tff(c_65, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_25, c_57])).
% 2.09/1.31  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.09/1.31  tff(c_69, plain, (k3_xboole_0('#skF_3', k1_xboole_0)='#skF_3'), inference(resolution, [status(thm)], [c_65, c_2])).
% 2.09/1.31  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.09/1.31  tff(c_72, plain, (k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_69, c_4])).
% 2.09/1.31  tff(c_84, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_25])).
% 2.09/1.31  tff(c_82, plain, (![A_3]: (k3_xboole_0(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_72, c_4])).
% 2.09/1.31  tff(c_81, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_72, c_10])).
% 2.09/1.31  tff(c_147, plain, (![A_26, B_27, C_28, D_29]: (m1_subset_1(k8_relset_1(A_26, B_27, C_28, D_29), k1_zfmisc_1(A_26)) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.09/1.31  tff(c_12, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.09/1.31  tff(c_152, plain, (![A_30, B_31, C_32, D_33]: (r1_tarski(k8_relset_1(A_30, B_31, C_32, D_33), A_30) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(resolution, [status(thm)], [c_147, c_12])).
% 2.09/1.31  tff(c_170, plain, (![B_37, C_38, D_39]: (r1_tarski(k8_relset_1('#skF_3', B_37, C_38, D_39), '#skF_3') | ~m1_subset_1(C_38, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_81, c_152])).
% 2.09/1.31  tff(c_173, plain, (![B_37, C_38, D_39]: (k3_xboole_0(k8_relset_1('#skF_3', B_37, C_38, D_39), '#skF_3')=k8_relset_1('#skF_3', B_37, C_38, D_39) | ~m1_subset_1(C_38, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_170, c_2])).
% 2.09/1.31  tff(c_176, plain, (![B_40, C_41, D_42]: (k8_relset_1('#skF_3', B_40, C_41, D_42)='#skF_3' | ~m1_subset_1(C_41, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_173])).
% 2.09/1.31  tff(c_187, plain, (![B_40, D_42]: (k8_relset_1('#skF_3', B_40, '#skF_3', D_42)='#skF_3')), inference(resolution, [status(thm)], [c_84, c_176])).
% 2.09/1.31  tff(c_18, plain, (k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.09/1.31  tff(c_80, plain, (k8_relset_1('#skF_3', '#skF_1', '#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_72, c_18])).
% 2.09/1.31  tff(c_191, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_187, c_80])).
% 2.09/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.31  
% 2.09/1.31  Inference rules
% 2.09/1.31  ----------------------
% 2.09/1.31  #Ref     : 0
% 2.09/1.32  #Sup     : 41
% 2.09/1.32  #Fact    : 0
% 2.09/1.32  #Define  : 0
% 2.09/1.32  #Split   : 0
% 2.09/1.32  #Chain   : 0
% 2.09/1.32  #Close   : 0
% 2.09/1.32  
% 2.09/1.32  Ordering : KBO
% 2.09/1.32  
% 2.09/1.32  Simplification rules
% 2.09/1.32  ----------------------
% 2.09/1.32  #Subsume      : 0
% 2.09/1.32  #Demod        : 23
% 2.09/1.32  #Tautology    : 29
% 2.09/1.32  #SimpNegUnit  : 0
% 2.09/1.32  #BackRed      : 9
% 2.09/1.32  
% 2.09/1.32  #Partial instantiations: 0
% 2.09/1.32  #Strategies tried      : 1
% 2.09/1.32  
% 2.09/1.32  Timing (in seconds)
% 2.09/1.32  ----------------------
% 2.09/1.32  Preprocessing        : 0.33
% 2.09/1.32  Parsing              : 0.18
% 2.09/1.32  CNF conversion       : 0.02
% 2.09/1.32  Main loop            : 0.16
% 2.09/1.32  Inferencing          : 0.06
% 2.09/1.32  Reduction            : 0.05
% 2.09/1.32  Demodulation         : 0.04
% 2.09/1.32  BG Simplification    : 0.01
% 2.09/1.32  Subsumption          : 0.03
% 2.09/1.32  Abstraction          : 0.01
% 2.09/1.32  MUC search           : 0.00
% 2.09/1.32  Cooper               : 0.00
% 2.09/1.32  Total                : 0.52
% 2.09/1.32  Index Insertion      : 0.00
% 2.09/1.32  Index Deletion       : 0.00
% 2.09/1.32  Index Matching       : 0.00
% 2.09/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
