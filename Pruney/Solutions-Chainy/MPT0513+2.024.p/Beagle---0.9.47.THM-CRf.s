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
% DateTime   : Thu Dec  3 10:00:01 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   35 (  42 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   42 (  54 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_62,axiom,(
    ? [A] :
      ( ~ v1_xboole_0(A)
      & v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A) )
     => ( v1_xboole_0(k7_relat_1(A,B))
        & v1_relat_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc17_relat_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_65,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_6,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_41,plain,(
    ! [B_20,A_21] :
      ( v1_relat_1(B_20)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_21))
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_45,plain,(
    ! [A_3] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_41])).

tff(c_46,plain,(
    ! [A_3] : ~ v1_relat_1(A_3) ),
    inference(splitLeft,[status(thm)],[c_45])).

tff(c_16,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_50,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_16])).

tff(c_51,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_45])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_32,plain,(
    ! [A_16,B_17] :
      ( v1_xboole_0(k7_relat_1(A_16,B_17))
      | ~ v1_relat_1(A_16)
      | ~ v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22,plain,(
    ! [B_13,A_14] :
      ( ~ v1_xboole_0(B_13)
      | B_13 = A_14
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_25,plain,(
    ! [A_14] :
      ( k1_xboole_0 = A_14
      | ~ v1_xboole_0(A_14) ) ),
    inference(resolution,[status(thm)],[c_2,c_22])).

tff(c_52,plain,(
    ! [A_22,B_23] :
      ( k7_relat_1(A_22,B_23) = k1_xboole_0
      | ~ v1_relat_1(A_22)
      | ~ v1_xboole_0(A_22) ) ),
    inference(resolution,[status(thm)],[c_32,c_25])).

tff(c_56,plain,(
    ! [B_23] :
      ( k7_relat_1(k1_xboole_0,B_23) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2,c_52])).

tff(c_60,plain,(
    ! [B_23] : k7_relat_1(k1_xboole_0,B_23) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_56])).

tff(c_20,plain,(
    k7_relat_1(k1_xboole_0,'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_63,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:09:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.24  
% 1.76/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.25  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.76/1.25  
% 1.76/1.25  %Foreground sorts:
% 1.76/1.25  
% 1.76/1.25  
% 1.76/1.25  %Background operators:
% 1.76/1.25  
% 1.76/1.25  
% 1.76/1.25  %Foreground operators:
% 1.76/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.76/1.25  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.76/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.76/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.76/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.76/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.76/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.76/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.76/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.76/1.25  
% 1.90/1.26  tff(f_36, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 1.90/1.26  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.90/1.26  tff(f_62, axiom, (?[A]: (~v1_xboole_0(A) & v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_relat_1)).
% 1.90/1.26  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.90/1.26  tff(f_57, axiom, (![A, B]: ((v1_xboole_0(A) & v1_relat_1(A)) => (v1_xboole_0(k7_relat_1(A, B)) & v1_relat_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc17_relat_1)).
% 1.90/1.26  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 1.90/1.26  tff(f_65, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 1.90/1.26  tff(c_6, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.90/1.26  tff(c_41, plain, (![B_20, A_21]: (v1_relat_1(B_20) | ~m1_subset_1(B_20, k1_zfmisc_1(A_21)) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.90/1.26  tff(c_45, plain, (![A_3]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_3))), inference(resolution, [status(thm)], [c_6, c_41])).
% 1.90/1.26  tff(c_46, plain, (![A_3]: (~v1_relat_1(A_3))), inference(splitLeft, [status(thm)], [c_45])).
% 1.90/1.26  tff(c_16, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.90/1.26  tff(c_50, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_16])).
% 1.90/1.26  tff(c_51, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_45])).
% 1.90/1.26  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.90/1.26  tff(c_32, plain, (![A_16, B_17]: (v1_xboole_0(k7_relat_1(A_16, B_17)) | ~v1_relat_1(A_16) | ~v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.90/1.26  tff(c_22, plain, (![B_13, A_14]: (~v1_xboole_0(B_13) | B_13=A_14 | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.90/1.26  tff(c_25, plain, (![A_14]: (k1_xboole_0=A_14 | ~v1_xboole_0(A_14))), inference(resolution, [status(thm)], [c_2, c_22])).
% 1.90/1.26  tff(c_52, plain, (![A_22, B_23]: (k7_relat_1(A_22, B_23)=k1_xboole_0 | ~v1_relat_1(A_22) | ~v1_xboole_0(A_22))), inference(resolution, [status(thm)], [c_32, c_25])).
% 1.90/1.26  tff(c_56, plain, (![B_23]: (k7_relat_1(k1_xboole_0, B_23)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_52])).
% 1.90/1.26  tff(c_60, plain, (![B_23]: (k7_relat_1(k1_xboole_0, B_23)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_51, c_56])).
% 1.90/1.26  tff(c_20, plain, (k7_relat_1(k1_xboole_0, '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.90/1.26  tff(c_63, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_20])).
% 1.90/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.26  
% 1.90/1.26  Inference rules
% 1.90/1.26  ----------------------
% 1.90/1.26  #Ref     : 0
% 1.90/1.26  #Sup     : 7
% 1.90/1.26  #Fact    : 0
% 1.90/1.26  #Define  : 0
% 1.90/1.26  #Split   : 1
% 1.90/1.26  #Chain   : 0
% 1.90/1.26  #Close   : 0
% 1.90/1.26  
% 1.90/1.26  Ordering : KBO
% 1.90/1.26  
% 1.90/1.26  Simplification rules
% 1.90/1.26  ----------------------
% 1.90/1.26  #Subsume      : 3
% 1.90/1.26  #Demod        : 2
% 1.90/1.26  #Tautology    : 1
% 1.90/1.26  #SimpNegUnit  : 3
% 1.90/1.26  #BackRed      : 2
% 1.90/1.26  
% 1.90/1.26  #Partial instantiations: 0
% 1.90/1.26  #Strategies tried      : 1
% 1.90/1.26  
% 1.90/1.26  Timing (in seconds)
% 1.90/1.26  ----------------------
% 1.90/1.26  Preprocessing        : 0.25
% 1.90/1.26  Parsing              : 0.14
% 1.90/1.26  CNF conversion       : 0.02
% 1.90/1.26  Main loop            : 0.19
% 1.90/1.26  Inferencing          : 0.08
% 1.90/1.26  Reduction            : 0.04
% 1.90/1.26  Demodulation         : 0.02
% 1.90/1.26  BG Simplification    : 0.01
% 1.90/1.26  Subsumption          : 0.03
% 1.90/1.26  Abstraction          : 0.00
% 1.90/1.26  MUC search           : 0.00
% 1.90/1.26  Cooper               : 0.00
% 1.90/1.26  Total                : 0.47
% 1.90/1.26  Index Insertion      : 0.00
% 1.90/1.26  Index Deletion       : 0.00
% 1.90/1.26  Index Matching       : 0.00
% 1.90/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
