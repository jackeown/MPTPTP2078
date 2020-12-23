%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:09 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 115 expanded)
%              Number of leaves         :   19 (  49 expanded)
%              Depth                    :    9
%              Number of atoms          :   40 ( 184 expanded)
%              Number of equality atoms :   14 (  74 expanded)
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

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_52,negated_conjecture,(
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

tff(f_43,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_23,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_18])).

tff(c_48,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_56,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_23,c_48])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_60,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_56,c_2])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_23])).

tff(c_64,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_3',B_3) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_60,c_8])).

tff(c_117,plain,(
    ! [A_22,B_23,C_24,D_25] :
      ( m1_subset_1(k8_relset_1(A_22,B_23,C_24,D_25),k1_zfmisc_1(A_22))
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_122,plain,(
    ! [A_26,B_27,C_28,D_29] :
      ( r1_tarski(k8_relset_1(A_26,B_27,C_28,D_29),A_26)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(resolution,[status(thm)],[c_117,c_10])).

tff(c_135,plain,(
    ! [B_30,C_31,D_32] :
      ( r1_tarski(k8_relset_1('#skF_3',B_30,C_31,D_32),'#skF_3')
      | ~ m1_subset_1(C_31,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_122])).

tff(c_63,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ r1_tarski(A_1,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_60,c_2])).

tff(c_140,plain,(
    ! [B_33,C_34,D_35] :
      ( k8_relset_1('#skF_3',B_33,C_34,D_35) = '#skF_3'
      | ~ m1_subset_1(C_34,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_135,c_63])).

tff(c_151,plain,(
    ! [B_33,D_35] : k8_relset_1('#skF_3',B_33,'#skF_3',D_35) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_66,c_140])).

tff(c_16,plain,(
    k8_relset_1(k1_xboole_0,'#skF_1','#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_62,plain,(
    k8_relset_1('#skF_3','#skF_1','#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_60,c_16])).

tff(c_155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:54:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.15  
% 1.64/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.15  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.64/1.15  
% 1.64/1.15  %Foreground sorts:
% 1.64/1.15  
% 1.64/1.15  
% 1.64/1.15  %Background operators:
% 1.64/1.15  
% 1.64/1.15  
% 1.64/1.15  %Foreground operators:
% 1.64/1.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.64/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.15  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.64/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.64/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.64/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.64/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.64/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.64/1.15  
% 1.64/1.16  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.64/1.16  tff(f_52, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_funct_2)).
% 1.64/1.16  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.64/1.16  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.64/1.16  tff(f_43, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k8_relset_1(A, B, C, D), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 1.64/1.16  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.64/1.16  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.64/1.16  tff(c_23, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_18])).
% 1.64/1.16  tff(c_48, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.64/1.16  tff(c_56, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_23, c_48])).
% 1.64/1.16  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.64/1.16  tff(c_60, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_56, c_2])).
% 1.64/1.16  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_23])).
% 1.64/1.16  tff(c_64, plain, (![B_3]: (k2_zfmisc_1('#skF_3', B_3)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_60, c_8])).
% 1.64/1.16  tff(c_117, plain, (![A_22, B_23, C_24, D_25]: (m1_subset_1(k8_relset_1(A_22, B_23, C_24, D_25), k1_zfmisc_1(A_22)) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.64/1.16  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.64/1.16  tff(c_122, plain, (![A_26, B_27, C_28, D_29]: (r1_tarski(k8_relset_1(A_26, B_27, C_28, D_29), A_26) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(resolution, [status(thm)], [c_117, c_10])).
% 1.64/1.16  tff(c_135, plain, (![B_30, C_31, D_32]: (r1_tarski(k8_relset_1('#skF_3', B_30, C_31, D_32), '#skF_3') | ~m1_subset_1(C_31, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_64, c_122])).
% 1.64/1.16  tff(c_63, plain, (![A_1]: (A_1='#skF_3' | ~r1_tarski(A_1, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_60, c_2])).
% 1.64/1.16  tff(c_140, plain, (![B_33, C_34, D_35]: (k8_relset_1('#skF_3', B_33, C_34, D_35)='#skF_3' | ~m1_subset_1(C_34, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_135, c_63])).
% 1.64/1.16  tff(c_151, plain, (![B_33, D_35]: (k8_relset_1('#skF_3', B_33, '#skF_3', D_35)='#skF_3')), inference(resolution, [status(thm)], [c_66, c_140])).
% 1.64/1.16  tff(c_16, plain, (k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.64/1.16  tff(c_62, plain, (k8_relset_1('#skF_3', '#skF_1', '#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_60, c_16])).
% 1.64/1.16  tff(c_155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_151, c_62])).
% 1.64/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.16  
% 1.64/1.16  Inference rules
% 1.64/1.16  ----------------------
% 1.64/1.16  #Ref     : 0
% 1.64/1.16  #Sup     : 30
% 1.64/1.16  #Fact    : 0
% 1.64/1.16  #Define  : 0
% 1.64/1.16  #Split   : 0
% 1.64/1.16  #Chain   : 0
% 1.64/1.16  #Close   : 0
% 1.64/1.16  
% 1.64/1.16  Ordering : KBO
% 1.64/1.16  
% 1.64/1.16  Simplification rules
% 1.64/1.16  ----------------------
% 1.64/1.16  #Subsume      : 0
% 1.64/1.16  #Demod        : 18
% 1.64/1.16  #Tautology    : 19
% 1.64/1.16  #SimpNegUnit  : 0
% 1.64/1.16  #BackRed      : 8
% 1.64/1.16  
% 1.64/1.16  #Partial instantiations: 0
% 1.64/1.16  #Strategies tried      : 1
% 1.64/1.16  
% 1.64/1.16  Timing (in seconds)
% 1.64/1.16  ----------------------
% 1.64/1.17  Preprocessing        : 0.27
% 1.64/1.17  Parsing              : 0.15
% 1.64/1.17  CNF conversion       : 0.02
% 1.64/1.17  Main loop            : 0.14
% 1.64/1.17  Inferencing          : 0.05
% 1.64/1.17  Reduction            : 0.04
% 1.64/1.17  Demodulation         : 0.03
% 1.64/1.17  BG Simplification    : 0.01
% 1.64/1.17  Subsumption          : 0.02
% 1.64/1.17  Abstraction          : 0.01
% 1.64/1.17  MUC search           : 0.00
% 1.64/1.17  Cooper               : 0.00
% 1.64/1.17  Total                : 0.43
% 1.64/1.17  Index Insertion      : 0.00
% 1.64/1.17  Index Deletion       : 0.00
% 1.64/1.17  Index Matching       : 0.00
% 1.64/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
