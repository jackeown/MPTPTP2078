%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:29 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   46 (  49 expanded)
%              Number of leaves         :   26 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   49 (  53 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > g1_orders_2 > #nlpp > k9_setfam_1 > k3_yellow_1 > k3_yellow_0 > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_43,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_48,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_56,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_67,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k1_xboole_0,A)
       => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A] : k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow_1)).

tff(c_10,plain,(
    ! [A_7] : ~ v1_xboole_0(k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_8] : v1_xboole_0('#skF_2'(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,(
    ! [B_23,A_24] :
      ( ~ v1_xboole_0(B_23)
      | B_23 = A_24
      | ~ v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_62,plain,(
    ! [A_26] :
      ( k1_xboole_0 = A_26
      | ~ v1_xboole_0(A_26) ) ),
    inference(resolution,[status(thm)],[c_6,c_50])).

tff(c_69,plain,(
    ! [A_8] : '#skF_2'(A_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_62])).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1('#skF_2'(A_8),k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_72,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_14])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( r2_hidden(A_10,B_11)
      | v1_xboole_0(B_11)
      | ~ m1_subset_1(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,(
    ! [A_12] : k9_setfam_1(A_12) = k1_zfmisc_1(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_24,plain,(
    ! [A_15] : k2_yellow_1(k9_setfam_1(A_15)) = k3_yellow_1(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_27,plain,(
    ! [A_15] : k2_yellow_1(k1_zfmisc_1(A_15)) = k3_yellow_1(A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_24])).

tff(c_98,plain,(
    ! [A_32] :
      ( k3_yellow_0(k2_yellow_1(A_32)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,A_32)
      | v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_107,plain,(
    ! [A_15] :
      ( k3_yellow_0(k3_yellow_1(A_15)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(A_15))
      | v1_xboole_0(k1_zfmisc_1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27,c_98])).

tff(c_111,plain,(
    ! [A_33] :
      ( k3_yellow_0(k3_yellow_1(A_33)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(A_33)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_107])).

tff(c_114,plain,(
    ! [A_33] :
      ( k3_yellow_0(k3_yellow_1(A_33)) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_33))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_33)) ) ),
    inference(resolution,[status(thm)],[c_16,c_111])).

tff(c_117,plain,(
    ! [A_33] :
      ( k3_yellow_0(k3_yellow_1(A_33)) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_33)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_114])).

tff(c_118,plain,(
    ! [A_33] : k3_yellow_0(k3_yellow_1(A_33)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_117])).

tff(c_26,plain,(
    k3_yellow_0(k3_yellow_1('#skF_3')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_122,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:43:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.18  
% 1.83/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.18  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > g1_orders_2 > #nlpp > k9_setfam_1 > k3_yellow_1 > k3_yellow_0 > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3
% 1.83/1.18  
% 1.83/1.18  %Foreground sorts:
% 1.83/1.18  
% 1.83/1.18  
% 1.83/1.18  %Background operators:
% 1.83/1.18  
% 1.83/1.18  
% 1.83/1.18  %Foreground operators:
% 1.83/1.18  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.83/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.83/1.18  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 1.83/1.18  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.83/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.83/1.18  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 1.83/1.18  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 1.83/1.18  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 1.83/1.18  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 1.83/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.83/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.83/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.18  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 1.83/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.83/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.83/1.18  
% 1.83/1.19  tff(f_43, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.83/1.19  tff(f_48, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_subset_1)).
% 1.83/1.19  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.83/1.19  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 1.83/1.19  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 1.83/1.19  tff(f_56, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 1.83/1.19  tff(f_67, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 1.83/1.19  tff(f_65, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow_1)).
% 1.83/1.19  tff(f_70, negated_conjecture, ~(![A]: (k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_yellow_1)).
% 1.83/1.19  tff(c_10, plain, (![A_7]: (~v1_xboole_0(k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.83/1.19  tff(c_12, plain, (![A_8]: (v1_xboole_0('#skF_2'(A_8)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.83/1.19  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.83/1.19  tff(c_50, plain, (![B_23, A_24]: (~v1_xboole_0(B_23) | B_23=A_24 | ~v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.83/1.19  tff(c_62, plain, (![A_26]: (k1_xboole_0=A_26 | ~v1_xboole_0(A_26))), inference(resolution, [status(thm)], [c_6, c_50])).
% 1.83/1.19  tff(c_69, plain, (![A_8]: ('#skF_2'(A_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_62])).
% 1.83/1.19  tff(c_14, plain, (![A_8]: (m1_subset_1('#skF_2'(A_8), k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.83/1.19  tff(c_72, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_14])).
% 1.83/1.19  tff(c_16, plain, (![A_10, B_11]: (r2_hidden(A_10, B_11) | v1_xboole_0(B_11) | ~m1_subset_1(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.83/1.19  tff(c_18, plain, (![A_12]: (k9_setfam_1(A_12)=k1_zfmisc_1(A_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.83/1.19  tff(c_24, plain, (![A_15]: (k2_yellow_1(k9_setfam_1(A_15))=k3_yellow_1(A_15))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.83/1.19  tff(c_27, plain, (![A_15]: (k2_yellow_1(k1_zfmisc_1(A_15))=k3_yellow_1(A_15))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_24])).
% 1.83/1.19  tff(c_98, plain, (![A_32]: (k3_yellow_0(k2_yellow_1(A_32))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, A_32) | v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.83/1.19  tff(c_107, plain, (![A_15]: (k3_yellow_0(k3_yellow_1(A_15))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, k1_zfmisc_1(A_15)) | v1_xboole_0(k1_zfmisc_1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_27, c_98])).
% 1.83/1.19  tff(c_111, plain, (![A_33]: (k3_yellow_0(k3_yellow_1(A_33))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, k1_zfmisc_1(A_33)))), inference(negUnitSimplification, [status(thm)], [c_10, c_107])).
% 1.83/1.19  tff(c_114, plain, (![A_33]: (k3_yellow_0(k3_yellow_1(A_33))=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_33)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_33)))), inference(resolution, [status(thm)], [c_16, c_111])).
% 1.83/1.19  tff(c_117, plain, (![A_33]: (k3_yellow_0(k3_yellow_1(A_33))=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_33)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_114])).
% 1.83/1.19  tff(c_118, plain, (![A_33]: (k3_yellow_0(k3_yellow_1(A_33))=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_10, c_117])).
% 1.83/1.19  tff(c_26, plain, (k3_yellow_0(k3_yellow_1('#skF_3'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.83/1.19  tff(c_122, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_26])).
% 1.83/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.19  
% 1.83/1.19  Inference rules
% 1.83/1.19  ----------------------
% 1.83/1.19  #Ref     : 0
% 1.83/1.19  #Sup     : 18
% 1.83/1.19  #Fact    : 0
% 1.83/1.19  #Define  : 0
% 1.83/1.19  #Split   : 0
% 1.83/1.19  #Chain   : 0
% 1.83/1.19  #Close   : 0
% 1.83/1.19  
% 1.83/1.19  Ordering : KBO
% 1.83/1.19  
% 1.83/1.19  Simplification rules
% 1.83/1.19  ----------------------
% 1.83/1.19  #Subsume      : 1
% 1.83/1.19  #Demod        : 8
% 1.83/1.19  #Tautology    : 15
% 1.83/1.19  #SimpNegUnit  : 2
% 1.83/1.19  #BackRed      : 3
% 1.83/1.19  
% 1.83/1.19  #Partial instantiations: 0
% 1.83/1.19  #Strategies tried      : 1
% 1.83/1.19  
% 1.83/1.19  Timing (in seconds)
% 1.83/1.19  ----------------------
% 1.83/1.19  Preprocessing        : 0.29
% 1.83/1.19  Parsing              : 0.16
% 1.83/1.19  CNF conversion       : 0.02
% 1.83/1.19  Main loop            : 0.11
% 1.83/1.19  Inferencing          : 0.04
% 1.83/1.19  Reduction            : 0.04
% 1.83/1.19  Demodulation         : 0.03
% 1.83/1.19  BG Simplification    : 0.01
% 1.83/1.19  Subsumption          : 0.02
% 1.83/1.19  Abstraction          : 0.01
% 1.83/1.19  MUC search           : 0.00
% 1.83/1.19  Cooper               : 0.00
% 1.83/1.19  Total                : 0.43
% 1.83/1.19  Index Insertion      : 0.00
% 1.83/1.19  Index Deletion       : 0.00
% 1.83/1.19  Index Matching       : 0.00
% 1.83/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
