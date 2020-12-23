%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:27 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   42 (  55 expanded)
%              Number of leaves         :   24 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  70 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v5_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k2_tarski > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v5_ordinal1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_ordinal1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v4_relat_1(k1_xboole_0,A)
      & v5_relat_1(k1_xboole_0,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t206_relat_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(k1_xboole_0)
        & v5_relat_1(k1_xboole_0,A)
        & v1_funct_1(k1_xboole_0)
        & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).

tff(f_28,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : v1_relat_1(k2_tarski(k4_tarski(A,B),k4_tarski(C,D))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_relat_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_18,plain,(
    ! [A_15] :
      ( v5_ordinal1(A_15)
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [A_19] :
      ( v1_funct_1(A_19)
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_30,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_26])).

tff(c_14,plain,(
    ! [B_13] : v5_relat_1(k1_xboole_0,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,'#skF_1')
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_20])).

tff(c_33,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_22])).

tff(c_34,plain,(
    ~ v5_ordinal1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_33])).

tff(c_37,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_34])).

tff(c_41,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_37])).

tff(c_42,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_33])).

tff(c_4,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_44,plain,(
    ! [B_21,A_22] :
      ( v1_relat_1(B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_22))
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_47,plain,(
    ! [A_1] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_44])).

tff(c_50,plain,(
    ! [A_1] : ~ v1_relat_1(A_1) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_47])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10,D_11] : v1_relat_1(k2_tarski(k4_tarski(A_8,B_9),k4_tarski(C_10,D_11))) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_53,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:11:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.12  
% 1.69/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.12  %$ v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v5_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k2_tarski > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1
% 1.69/1.12  
% 1.69/1.12  %Foreground sorts:
% 1.69/1.12  
% 1.69/1.12  
% 1.69/1.12  %Background operators:
% 1.69/1.12  
% 1.69/1.12  
% 1.69/1.12  %Foreground operators:
% 1.69/1.12  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.69/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.69/1.12  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.69/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.69/1.12  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 1.69/1.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.69/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.69/1.12  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.69/1.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.69/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.69/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.12  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.69/1.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.69/1.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.69/1.12  
% 1.69/1.13  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.69/1.13  tff(f_55, axiom, (![A]: (v1_xboole_0(A) => v5_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_ordinal1)).
% 1.69/1.13  tff(f_51, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 1.69/1.13  tff(f_47, axiom, (![A, B]: (v4_relat_1(k1_xboole_0, A) & v5_relat_1(k1_xboole_0, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t206_relat_1)).
% 1.69/1.13  tff(f_64, negated_conjecture, ~(![A]: (((v1_relat_1(k1_xboole_0) & v5_relat_1(k1_xboole_0, A)) & v1_funct_1(k1_xboole_0)) & v5_ordinal1(k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_ordinal1)).
% 1.69/1.13  tff(f_28, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 1.69/1.13  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.69/1.13  tff(f_43, axiom, (![A, B, C, D]: v1_relat_1(k2_tarski(k4_tarski(A, B), k4_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_relat_1)).
% 1.69/1.13  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.69/1.13  tff(c_18, plain, (![A_15]: (v5_ordinal1(A_15) | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.69/1.13  tff(c_26, plain, (![A_19]: (v1_funct_1(A_19) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.69/1.13  tff(c_30, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_26])).
% 1.69/1.13  tff(c_14, plain, (![B_13]: (v5_relat_1(k1_xboole_0, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.69/1.13  tff(c_20, plain, (~v1_relat_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0, '#skF_1') | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.69/1.13  tff(c_22, plain, (~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_20])).
% 1.69/1.13  tff(c_33, plain, (~v1_relat_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_22])).
% 1.69/1.13  tff(c_34, plain, (~v5_ordinal1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_33])).
% 1.69/1.13  tff(c_37, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_34])).
% 1.69/1.13  tff(c_41, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_37])).
% 1.69/1.13  tff(c_42, plain, (~v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_33])).
% 1.69/1.13  tff(c_4, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.69/1.13  tff(c_44, plain, (![B_21, A_22]: (v1_relat_1(B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(A_22)) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.69/1.13  tff(c_47, plain, (![A_1]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_1))), inference(resolution, [status(thm)], [c_4, c_44])).
% 1.69/1.13  tff(c_50, plain, (![A_1]: (~v1_relat_1(A_1))), inference(negUnitSimplification, [status(thm)], [c_42, c_47])).
% 1.69/1.13  tff(c_10, plain, (![A_8, B_9, C_10, D_11]: (v1_relat_1(k2_tarski(k4_tarski(A_8, B_9), k4_tarski(C_10, D_11))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.69/1.13  tff(c_53, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_10])).
% 1.69/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.13  
% 1.69/1.13  Inference rules
% 1.69/1.13  ----------------------
% 1.69/1.13  #Ref     : 0
% 1.69/1.13  #Sup     : 3
% 1.69/1.13  #Fact    : 0
% 1.69/1.13  #Define  : 0
% 1.69/1.13  #Split   : 1
% 1.69/1.13  #Chain   : 0
% 1.69/1.13  #Close   : 0
% 1.69/1.13  
% 1.69/1.13  Ordering : KBO
% 1.69/1.13  
% 1.69/1.13  Simplification rules
% 1.69/1.13  ----------------------
% 1.69/1.13  #Subsume      : 2
% 1.69/1.13  #Demod        : 3
% 1.69/1.13  #Tautology    : 0
% 1.69/1.13  #SimpNegUnit  : 3
% 1.69/1.13  #BackRed      : 0
% 1.69/1.13  
% 1.69/1.13  #Partial instantiations: 0
% 1.69/1.13  #Strategies tried      : 1
% 1.69/1.13  
% 1.69/1.13  Timing (in seconds)
% 1.69/1.13  ----------------------
% 1.69/1.14  Preprocessing        : 0.27
% 1.69/1.14  Parsing              : 0.15
% 1.69/1.14  CNF conversion       : 0.02
% 1.69/1.14  Main loop            : 0.10
% 1.69/1.14  Inferencing          : 0.04
% 1.69/1.14  Reduction            : 0.03
% 1.69/1.14  Demodulation         : 0.02
% 1.69/1.14  BG Simplification    : 0.01
% 1.69/1.14  Subsumption          : 0.01
% 1.69/1.14  Abstraction          : 0.00
% 1.69/1.14  MUC search           : 0.00
% 1.69/1.14  Cooper               : 0.00
% 1.69/1.14  Total                : 0.40
% 1.69/1.14  Index Insertion      : 0.00
% 1.69/1.14  Index Deletion       : 0.00
% 1.69/1.14  Index Matching       : 0.00
% 1.69/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
