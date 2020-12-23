%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:31 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   34 (  36 expanded)
%              Number of leaves         :   20 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :   35 (  37 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > #nlpp > k9_setfam_1 > k3_yellow_1 > k3_yellow_0 > k2_yellow_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_28,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_30,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_44,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_53,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_51,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k1_xboole_0,A)
       => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A] : k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow_1)).

tff(c_2,plain,(
    ! [A_1] : ~ v1_xboole_0(k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_10,plain,(
    ! [A_8] : k9_setfam_1(A_8) = k1_zfmisc_1(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_14,plain,(
    ! [A_10] : k2_yellow_1(k9_setfam_1(A_10)) = k3_yellow_1(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_17,plain,(
    ! [A_10] : k2_yellow_1(k1_zfmisc_1(A_10)) = k3_yellow_1(A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14])).

tff(c_39,plain,(
    ! [A_17] :
      ( k3_yellow_0(k2_yellow_1(A_17)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_48,plain,(
    ! [A_10] :
      ( k3_yellow_0(k3_yellow_1(A_10)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(A_10))
      | v1_xboole_0(k1_zfmisc_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17,c_39])).

tff(c_52,plain,(
    ! [A_18] :
      ( k3_yellow_0(k3_yellow_1(A_18)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(A_18)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2,c_48])).

tff(c_55,plain,(
    ! [A_18] :
      ( k3_yellow_0(k3_yellow_1(A_18)) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_18))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_18)) ) ),
    inference(resolution,[status(thm)],[c_6,c_52])).

tff(c_58,plain,(
    ! [A_18] :
      ( k3_yellow_0(k3_yellow_1(A_18)) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_18)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_55])).

tff(c_59,plain,(
    ! [A_18] : k3_yellow_0(k3_yellow_1(A_18)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_2,c_58])).

tff(c_16,plain,(
    k3_yellow_0(k3_yellow_1('#skF_1')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_63,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:40:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.18  
% 1.73/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.18  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > #nlpp > k9_setfam_1 > k3_yellow_1 > k3_yellow_0 > k2_yellow_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1
% 1.73/1.18  
% 1.73/1.18  %Foreground sorts:
% 1.73/1.18  
% 1.73/1.18  
% 1.73/1.18  %Background operators:
% 1.73/1.18  
% 1.73/1.18  
% 1.73/1.18  %Foreground operators:
% 1.73/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.73/1.18  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 1.73/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.73/1.18  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 1.73/1.18  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 1.73/1.18  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 1.73/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.73/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.73/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.73/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.73/1.18  
% 1.73/1.19  tff(f_28, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.73/1.19  tff(f_30, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 1.73/1.19  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 1.73/1.19  tff(f_44, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 1.73/1.19  tff(f_53, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 1.73/1.19  tff(f_51, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow_1)).
% 1.73/1.19  tff(f_56, negated_conjecture, ~(![A]: (k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_yellow_1)).
% 1.73/1.19  tff(c_2, plain, (![A_1]: (~v1_xboole_0(k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.73/1.19  tff(c_4, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.73/1.19  tff(c_6, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.73/1.19  tff(c_10, plain, (![A_8]: (k9_setfam_1(A_8)=k1_zfmisc_1(A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.73/1.19  tff(c_14, plain, (![A_10]: (k2_yellow_1(k9_setfam_1(A_10))=k3_yellow_1(A_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.73/1.19  tff(c_17, plain, (![A_10]: (k2_yellow_1(k1_zfmisc_1(A_10))=k3_yellow_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14])).
% 1.73/1.19  tff(c_39, plain, (![A_17]: (k3_yellow_0(k2_yellow_1(A_17))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.73/1.19  tff(c_48, plain, (![A_10]: (k3_yellow_0(k3_yellow_1(A_10))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, k1_zfmisc_1(A_10)) | v1_xboole_0(k1_zfmisc_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_17, c_39])).
% 1.73/1.19  tff(c_52, plain, (![A_18]: (k3_yellow_0(k3_yellow_1(A_18))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, k1_zfmisc_1(A_18)))), inference(negUnitSimplification, [status(thm)], [c_2, c_48])).
% 1.73/1.19  tff(c_55, plain, (![A_18]: (k3_yellow_0(k3_yellow_1(A_18))=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_18)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_18)))), inference(resolution, [status(thm)], [c_6, c_52])).
% 1.73/1.19  tff(c_58, plain, (![A_18]: (k3_yellow_0(k3_yellow_1(A_18))=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_55])).
% 1.73/1.19  tff(c_59, plain, (![A_18]: (k3_yellow_0(k3_yellow_1(A_18))=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_2, c_58])).
% 1.73/1.19  tff(c_16, plain, (k3_yellow_0(k3_yellow_1('#skF_1'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.73/1.19  tff(c_63, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_16])).
% 1.73/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.19  
% 1.73/1.19  Inference rules
% 1.73/1.19  ----------------------
% 1.73/1.19  #Ref     : 0
% 1.73/1.19  #Sup     : 8
% 1.73/1.19  #Fact    : 0
% 1.73/1.19  #Define  : 0
% 1.73/1.19  #Split   : 0
% 1.73/1.19  #Chain   : 0
% 1.73/1.19  #Close   : 0
% 1.73/1.19  
% 1.73/1.19  Ordering : KBO
% 1.73/1.19  
% 1.73/1.19  Simplification rules
% 1.73/1.19  ----------------------
% 1.73/1.19  #Subsume      : 0
% 1.73/1.19  #Demod        : 4
% 1.73/1.19  #Tautology    : 7
% 1.73/1.19  #SimpNegUnit  : 2
% 1.73/1.19  #BackRed      : 1
% 1.73/1.19  
% 1.73/1.19  #Partial instantiations: 0
% 1.73/1.19  #Strategies tried      : 1
% 1.73/1.19  
% 1.73/1.19  Timing (in seconds)
% 1.73/1.19  ----------------------
% 1.73/1.20  Preprocessing        : 0.29
% 1.73/1.20  Parsing              : 0.16
% 1.73/1.20  CNF conversion       : 0.01
% 1.73/1.20  Main loop            : 0.08
% 1.73/1.20  Inferencing          : 0.04
% 1.73/1.20  Reduction            : 0.03
% 1.73/1.20  Demodulation         : 0.02
% 1.73/1.20  BG Simplification    : 0.01
% 1.73/1.20  Subsumption          : 0.01
% 1.73/1.20  Abstraction          : 0.01
% 1.73/1.20  MUC search           : 0.00
% 1.73/1.20  Cooper               : 0.00
% 1.73/1.20  Total                : 0.40
% 1.73/1.20  Index Insertion      : 0.00
% 1.73/1.20  Index Deletion       : 0.00
% 1.73/1.20  Index Matching       : 0.00
% 1.73/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
