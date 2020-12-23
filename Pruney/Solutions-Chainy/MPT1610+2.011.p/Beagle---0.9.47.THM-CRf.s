%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:30 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   46 (  48 expanded)
%              Number of leaves         :   26 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :   53 (  55 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k9_setfam_1 > k3_yellow_1 > k3_yellow_0 > k2_yellow_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_54,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_63,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k1_xboole_0,A)
       => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A] : k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow_1)).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_72,plain,(
    ! [A_32,B_33] :
      ( r2_hidden('#skF_2'(A_32,B_33),A_32)
      | r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_81,plain,(
    ! [A_32,B_33] :
      ( ~ v1_xboole_0(A_32)
      | r1_tarski(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_72,c_2])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    ! [A_10] : ~ v1_xboole_0(k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | v1_xboole_0(B_12)
      | ~ m1_subset_1(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22,plain,(
    ! [A_15] : k9_setfam_1(A_15) = k1_zfmisc_1(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_26,plain,(
    ! [A_17] : k2_yellow_1(k9_setfam_1(A_17)) = k3_yellow_1(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_29,plain,(
    ! [A_17] : k2_yellow_1(k1_zfmisc_1(A_17)) = k3_yellow_1(A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26])).

tff(c_94,plain,(
    ! [A_40] :
      ( k3_yellow_0(k2_yellow_1(A_40)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_103,plain,(
    ! [A_17] :
      ( k3_yellow_0(k3_yellow_1(A_17)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(A_17))
      | v1_xboole_0(k1_zfmisc_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29,c_94])).

tff(c_107,plain,(
    ! [A_41] :
      ( k3_yellow_0(k3_yellow_1(A_41)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(A_41)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_103])).

tff(c_110,plain,(
    ! [A_41] :
      ( k3_yellow_0(k3_yellow_1(A_41)) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_41))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_41)) ) ),
    inference(resolution,[status(thm)],[c_16,c_107])).

tff(c_114,plain,(
    ! [A_42] :
      ( k3_yellow_0(k3_yellow_1(A_42)) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_42)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_110])).

tff(c_120,plain,(
    ! [B_43] :
      ( k3_yellow_0(k3_yellow_1(B_43)) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,B_43) ) ),
    inference(resolution,[status(thm)],[c_20,c_114])).

tff(c_28,plain,(
    k3_yellow_0(k3_yellow_1('#skF_3')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_131,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_28])).

tff(c_135,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_81,c_131])).

tff(c_139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_135])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:29:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.21  
% 1.91/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.22  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k9_setfam_1 > k3_yellow_1 > k3_yellow_0 > k2_yellow_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.91/1.22  
% 1.91/1.22  %Foreground sorts:
% 1.91/1.22  
% 1.91/1.22  
% 1.91/1.22  %Background operators:
% 1.91/1.22  
% 1.91/1.22  
% 1.91/1.22  %Foreground operators:
% 1.91/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.22  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 1.91/1.22  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.91/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.91/1.22  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 1.91/1.22  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 1.91/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.22  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 1.91/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.91/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.91/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.91/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.91/1.22  
% 1.91/1.23  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.91/1.23  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.91/1.23  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.91/1.23  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.91/1.23  tff(f_42, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.91/1.23  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 1.91/1.23  tff(f_54, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 1.91/1.23  tff(f_63, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 1.91/1.23  tff(f_61, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow_1)).
% 1.91/1.23  tff(f_66, negated_conjecture, ~(![A]: (k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_yellow_1)).
% 1.91/1.23  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.91/1.23  tff(c_72, plain, (![A_32, B_33]: (r2_hidden('#skF_2'(A_32, B_33), A_32) | r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.91/1.23  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.91/1.23  tff(c_81, plain, (![A_32, B_33]: (~v1_xboole_0(A_32) | r1_tarski(A_32, B_33))), inference(resolution, [status(thm)], [c_72, c_2])).
% 1.91/1.23  tff(c_20, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.91/1.23  tff(c_14, plain, (![A_10]: (~v1_xboole_0(k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.91/1.23  tff(c_16, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | v1_xboole_0(B_12) | ~m1_subset_1(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.91/1.23  tff(c_22, plain, (![A_15]: (k9_setfam_1(A_15)=k1_zfmisc_1(A_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.91/1.23  tff(c_26, plain, (![A_17]: (k2_yellow_1(k9_setfam_1(A_17))=k3_yellow_1(A_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.91/1.23  tff(c_29, plain, (![A_17]: (k2_yellow_1(k1_zfmisc_1(A_17))=k3_yellow_1(A_17))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_26])).
% 1.91/1.23  tff(c_94, plain, (![A_40]: (k3_yellow_0(k2_yellow_1(A_40))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, A_40) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.91/1.23  tff(c_103, plain, (![A_17]: (k3_yellow_0(k3_yellow_1(A_17))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, k1_zfmisc_1(A_17)) | v1_xboole_0(k1_zfmisc_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_29, c_94])).
% 1.91/1.23  tff(c_107, plain, (![A_41]: (k3_yellow_0(k3_yellow_1(A_41))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, k1_zfmisc_1(A_41)))), inference(negUnitSimplification, [status(thm)], [c_14, c_103])).
% 1.91/1.23  tff(c_110, plain, (![A_41]: (k3_yellow_0(k3_yellow_1(A_41))=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_41)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_41)))), inference(resolution, [status(thm)], [c_16, c_107])).
% 1.91/1.23  tff(c_114, plain, (![A_42]: (k3_yellow_0(k3_yellow_1(A_42))=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_42)))), inference(negUnitSimplification, [status(thm)], [c_14, c_110])).
% 1.91/1.23  tff(c_120, plain, (![B_43]: (k3_yellow_0(k3_yellow_1(B_43))=k1_xboole_0 | ~r1_tarski(k1_xboole_0, B_43))), inference(resolution, [status(thm)], [c_20, c_114])).
% 1.91/1.23  tff(c_28, plain, (k3_yellow_0(k3_yellow_1('#skF_3'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.91/1.23  tff(c_131, plain, (~r1_tarski(k1_xboole_0, '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_120, c_28])).
% 1.91/1.23  tff(c_135, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_81, c_131])).
% 1.91/1.23  tff(c_139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_135])).
% 1.91/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.23  
% 1.91/1.23  Inference rules
% 1.91/1.23  ----------------------
% 1.91/1.23  #Ref     : 0
% 1.91/1.23  #Sup     : 22
% 1.91/1.23  #Fact    : 0
% 1.91/1.23  #Define  : 0
% 1.91/1.23  #Split   : 0
% 1.91/1.23  #Chain   : 0
% 1.91/1.23  #Close   : 0
% 1.91/1.23  
% 1.91/1.23  Ordering : KBO
% 1.91/1.23  
% 1.91/1.23  Simplification rules
% 1.91/1.23  ----------------------
% 1.91/1.23  #Subsume      : 0
% 1.91/1.23  #Demod        : 2
% 1.91/1.23  #Tautology    : 11
% 1.91/1.23  #SimpNegUnit  : 2
% 1.91/1.23  #BackRed      : 0
% 1.91/1.23  
% 1.91/1.23  #Partial instantiations: 0
% 1.91/1.23  #Strategies tried      : 1
% 1.91/1.23  
% 1.91/1.23  Timing (in seconds)
% 1.91/1.23  ----------------------
% 1.91/1.23  Preprocessing        : 0.27
% 1.91/1.23  Parsing              : 0.14
% 1.91/1.23  CNF conversion       : 0.02
% 1.91/1.23  Main loop            : 0.12
% 1.91/1.23  Inferencing          : 0.05
% 1.91/1.23  Reduction            : 0.03
% 1.91/1.23  Demodulation         : 0.03
% 1.91/1.23  BG Simplification    : 0.01
% 1.91/1.23  Subsumption          : 0.02
% 1.91/1.23  Abstraction          : 0.01
% 1.91/1.23  MUC search           : 0.00
% 1.91/1.23  Cooper               : 0.00
% 1.91/1.23  Total                : 0.42
% 1.91/1.23  Index Insertion      : 0.00
% 1.91/1.23  Index Deletion       : 0.00
% 1.91/1.23  Index Matching       : 0.00
% 1.91/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
