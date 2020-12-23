%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:06 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   33 (  37 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   38 (  50 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r1_tarski(k8_relset_1(A,B,D,C),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_24,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_25,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_20])).

tff(c_85,plain,(
    ! [A_19,B_20,D_21,C_22] :
      ( r1_tarski(k8_relset_1(A_19,B_20,D_21,C_22),A_19)
      | ~ m1_subset_1(D_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20)))
      | ~ v1_funct_1(D_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_117,plain,(
    ! [B_29,D_30,C_31] :
      ( r1_tarski(k8_relset_1(k1_xboole_0,B_29,D_30,C_31),k1_xboole_0)
      | ~ m1_subset_1(D_30,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_1(D_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_85])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_62,plain,(
    ! [B_16,A_17] :
      ( B_16 = A_17
      | ~ r1_tarski(B_16,A_17)
      | ~ r1_tarski(A_17,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_71,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_62])).

tff(c_132,plain,(
    ! [B_32,D_33,C_34] :
      ( k8_relset_1(k1_xboole_0,B_32,D_33,C_34) = k1_xboole_0
      | ~ m1_subset_1(D_33,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_1(D_33) ) ),
    inference(resolution,[status(thm)],[c_117,c_71])).

tff(c_134,plain,(
    ! [B_32,C_34] :
      ( k8_relset_1(k1_xboole_0,B_32,'#skF_3',C_34) = k1_xboole_0
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_25,c_132])).

tff(c_137,plain,(
    ! [B_32,C_34] : k8_relset_1(k1_xboole_0,B_32,'#skF_3',C_34) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_134])).

tff(c_18,plain,(
    k8_relset_1(k1_xboole_0,'#skF_1','#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:23:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.49  
% 2.18/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.50  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.18/1.50  
% 2.18/1.50  %Foreground sorts:
% 2.18/1.50  
% 2.18/1.50  
% 2.18/1.50  %Background operators:
% 2.18/1.50  
% 2.18/1.50  
% 2.18/1.50  %Foreground operators:
% 2.18/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.18/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.50  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.18/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.18/1.50  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.50  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.18/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.50  
% 2.18/1.51  tff(f_54, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_funct_2)).
% 2.18/1.51  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.18/1.51  tff(f_45, axiom, (![A, B, C, D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r1_tarski(k8_relset_1(A, B, D, C), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_funct_2)).
% 2.18/1.51  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.18/1.51  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.18/1.51  tff(c_24, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.18/1.51  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.18/1.51  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.18/1.51  tff(c_25, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_20])).
% 2.18/1.51  tff(c_85, plain, (![A_19, B_20, D_21, C_22]: (r1_tarski(k8_relset_1(A_19, B_20, D_21, C_22), A_19) | ~m1_subset_1(D_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))) | ~v1_funct_1(D_21))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.18/1.51  tff(c_117, plain, (![B_29, D_30, C_31]: (r1_tarski(k8_relset_1(k1_xboole_0, B_29, D_30, C_31), k1_xboole_0) | ~m1_subset_1(D_30, k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(D_30))), inference(superposition, [status(thm), theory('equality')], [c_14, c_85])).
% 2.18/1.51  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.18/1.51  tff(c_62, plain, (![B_16, A_17]: (B_16=A_17 | ~r1_tarski(B_16, A_17) | ~r1_tarski(A_17, B_16))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.18/1.51  tff(c_71, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_62])).
% 2.18/1.51  tff(c_132, plain, (![B_32, D_33, C_34]: (k8_relset_1(k1_xboole_0, B_32, D_33, C_34)=k1_xboole_0 | ~m1_subset_1(D_33, k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(D_33))), inference(resolution, [status(thm)], [c_117, c_71])).
% 2.18/1.51  tff(c_134, plain, (![B_32, C_34]: (k8_relset_1(k1_xboole_0, B_32, '#skF_3', C_34)=k1_xboole_0 | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_25, c_132])).
% 2.18/1.51  tff(c_137, plain, (![B_32, C_34]: (k8_relset_1(k1_xboole_0, B_32, '#skF_3', C_34)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_134])).
% 2.18/1.51  tff(c_18, plain, (k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.18/1.51  tff(c_141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_137, c_18])).
% 2.18/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.51  
% 2.18/1.51  Inference rules
% 2.18/1.51  ----------------------
% 2.18/1.51  #Ref     : 0
% 2.18/1.51  #Sup     : 24
% 2.18/1.51  #Fact    : 0
% 2.18/1.51  #Define  : 0
% 2.18/1.51  #Split   : 0
% 2.18/1.51  #Chain   : 0
% 2.18/1.51  #Close   : 0
% 2.18/1.51  
% 2.18/1.51  Ordering : KBO
% 2.18/1.51  
% 2.18/1.51  Simplification rules
% 2.18/1.51  ----------------------
% 2.18/1.51  #Subsume      : 1
% 2.18/1.51  #Demod        : 14
% 2.18/1.51  #Tautology    : 17
% 2.18/1.51  #SimpNegUnit  : 0
% 2.18/1.51  #BackRed      : 1
% 2.18/1.51  
% 2.18/1.51  #Partial instantiations: 0
% 2.18/1.51  #Strategies tried      : 1
% 2.18/1.51  
% 2.18/1.51  Timing (in seconds)
% 2.18/1.51  ----------------------
% 2.18/1.52  Preprocessing        : 0.42
% 2.18/1.52  Parsing              : 0.23
% 2.18/1.52  CNF conversion       : 0.03
% 2.18/1.52  Main loop            : 0.22
% 2.18/1.52  Inferencing          : 0.09
% 2.18/1.52  Reduction            : 0.06
% 2.18/1.52  Demodulation         : 0.05
% 2.18/1.52  BG Simplification    : 0.01
% 2.18/1.52  Subsumption          : 0.04
% 2.18/1.52  Abstraction          : 0.01
% 2.18/1.52  MUC search           : 0.00
% 2.18/1.52  Cooper               : 0.00
% 2.18/1.52  Total                : 0.68
% 2.18/1.52  Index Insertion      : 0.00
% 2.18/1.52  Index Deletion       : 0.00
% 2.18/1.52  Index Matching       : 0.00
% 2.18/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
