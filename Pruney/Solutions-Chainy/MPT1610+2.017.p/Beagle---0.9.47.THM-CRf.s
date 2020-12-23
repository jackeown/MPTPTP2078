%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
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
%              Number of atoms          :   38 (  40 expanded)
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

tff(f_41,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_51,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_60,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k1_xboole_0,A)
       => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_63,negated_conjecture,(
    ~ ! [A] : k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow_1)).

tff(c_10,plain,(
    ! [A_3] : ~ v1_xboole_0(k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r2_hidden(B_2,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_16,plain,(
    ! [A_8] : k9_setfam_1(A_8) = k1_zfmisc_1(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    ! [A_10] : k2_yellow_1(k9_setfam_1(A_10)) = k3_yellow_1(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_23,plain,(
    ! [A_10] : k2_yellow_1(k1_zfmisc_1(A_10)) = k3_yellow_1(A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_20])).

tff(c_60,plain,(
    ! [A_23] :
      ( k3_yellow_0(k2_yellow_1(A_23)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,A_23)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_69,plain,(
    ! [A_10] :
      ( k3_yellow_0(k3_yellow_1(A_10)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(A_10))
      | v1_xboole_0(k1_zfmisc_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23,c_60])).

tff(c_73,plain,(
    ! [A_24] :
      ( k3_yellow_0(k3_yellow_1(A_24)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(A_24)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_69])).

tff(c_76,plain,(
    ! [A_24] :
      ( k3_yellow_0(k3_yellow_1(A_24)) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_24))
      | v1_xboole_0(k1_zfmisc_1(A_24)) ) ),
    inference(resolution,[status(thm)],[c_4,c_73])).

tff(c_79,plain,(
    ! [A_24] :
      ( k3_yellow_0(k3_yellow_1(A_24)) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_24)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_76])).

tff(c_80,plain,(
    ! [A_24] : k3_yellow_0(k3_yellow_1(A_24)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_79])).

tff(c_22,plain,(
    k3_yellow_0(k3_yellow_1('#skF_1')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_84,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:10:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.16  
% 1.73/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.17  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > #nlpp > k9_setfam_1 > k3_yellow_1 > k3_yellow_0 > k2_yellow_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1
% 1.73/1.17  
% 1.73/1.17  %Foreground sorts:
% 1.73/1.17  
% 1.73/1.17  
% 1.73/1.17  %Background operators:
% 1.73/1.17  
% 1.73/1.17  
% 1.73/1.17  %Foreground operators:
% 1.73/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.73/1.17  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 1.73/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.73/1.17  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 1.73/1.17  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 1.73/1.17  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 1.73/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.73/1.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.73/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.73/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.73/1.17  
% 1.73/1.18  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.73/1.18  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 1.73/1.18  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 1.73/1.18  tff(f_51, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 1.73/1.18  tff(f_60, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 1.73/1.18  tff(f_58, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow_1)).
% 1.73/1.18  tff(f_63, negated_conjecture, ~(![A]: (k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_yellow_1)).
% 1.73/1.18  tff(c_10, plain, (![A_3]: (~v1_xboole_0(k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.73/1.18  tff(c_12, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.73/1.18  tff(c_4, plain, (![B_2, A_1]: (r2_hidden(B_2, A_1) | ~m1_subset_1(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.73/1.18  tff(c_16, plain, (![A_8]: (k9_setfam_1(A_8)=k1_zfmisc_1(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.73/1.18  tff(c_20, plain, (![A_10]: (k2_yellow_1(k9_setfam_1(A_10))=k3_yellow_1(A_10))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.73/1.18  tff(c_23, plain, (![A_10]: (k2_yellow_1(k1_zfmisc_1(A_10))=k3_yellow_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_20])).
% 1.73/1.18  tff(c_60, plain, (![A_23]: (k3_yellow_0(k2_yellow_1(A_23))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, A_23) | v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.73/1.18  tff(c_69, plain, (![A_10]: (k3_yellow_0(k3_yellow_1(A_10))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, k1_zfmisc_1(A_10)) | v1_xboole_0(k1_zfmisc_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_23, c_60])).
% 1.73/1.18  tff(c_73, plain, (![A_24]: (k3_yellow_0(k3_yellow_1(A_24))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, k1_zfmisc_1(A_24)))), inference(negUnitSimplification, [status(thm)], [c_10, c_69])).
% 1.73/1.18  tff(c_76, plain, (![A_24]: (k3_yellow_0(k3_yellow_1(A_24))=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_24)) | v1_xboole_0(k1_zfmisc_1(A_24)))), inference(resolution, [status(thm)], [c_4, c_73])).
% 1.73/1.18  tff(c_79, plain, (![A_24]: (k3_yellow_0(k3_yellow_1(A_24))=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_76])).
% 1.73/1.18  tff(c_80, plain, (![A_24]: (k3_yellow_0(k3_yellow_1(A_24))=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_10, c_79])).
% 1.73/1.18  tff(c_22, plain, (k3_yellow_0(k3_yellow_1('#skF_1'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.73/1.18  tff(c_84, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_22])).
% 1.73/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.18  
% 1.73/1.18  Inference rules
% 1.73/1.18  ----------------------
% 1.73/1.18  #Ref     : 0
% 1.73/1.18  #Sup     : 11
% 1.73/1.18  #Fact    : 0
% 1.73/1.18  #Define  : 0
% 1.73/1.18  #Split   : 0
% 1.73/1.18  #Chain   : 0
% 1.73/1.18  #Close   : 0
% 1.73/1.18  
% 1.73/1.18  Ordering : KBO
% 1.73/1.18  
% 1.73/1.18  Simplification rules
% 1.73/1.18  ----------------------
% 1.73/1.18  #Subsume      : 1
% 1.73/1.18  #Demod        : 4
% 1.73/1.18  #Tautology    : 9
% 1.73/1.18  #SimpNegUnit  : 2
% 1.73/1.18  #BackRed      : 1
% 1.73/1.18  
% 1.73/1.18  #Partial instantiations: 0
% 1.73/1.18  #Strategies tried      : 1
% 1.73/1.18  
% 1.73/1.18  Timing (in seconds)
% 1.73/1.18  ----------------------
% 1.73/1.18  Preprocessing        : 0.26
% 1.73/1.18  Parsing              : 0.14
% 1.73/1.18  CNF conversion       : 0.02
% 1.73/1.18  Main loop            : 0.09
% 1.73/1.18  Inferencing          : 0.04
% 1.73/1.18  Reduction            : 0.03
% 1.73/1.18  Demodulation         : 0.02
% 1.73/1.18  BG Simplification    : 0.01
% 1.73/1.18  Subsumption          : 0.01
% 1.73/1.18  Abstraction          : 0.01
% 1.73/1.18  MUC search           : 0.00
% 1.73/1.18  Cooper               : 0.00
% 1.73/1.18  Total                : 0.38
% 1.73/1.18  Index Insertion      : 0.00
% 1.73/1.18  Index Deletion       : 0.00
% 1.73/1.18  Index Matching       : 0.00
% 1.73/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
