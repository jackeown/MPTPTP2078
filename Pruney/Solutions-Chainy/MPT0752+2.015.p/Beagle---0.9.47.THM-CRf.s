%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:28 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   71 (  98 expanded)
%              Number of leaves         :   32 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :   94 ( 156 expanded)
%              Number of equality atoms :   25 (  26 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > v5_ordinal1 > v1_relat_1 > v1_funct_1 > k8_relat_1 > k7_relat_1 > k4_xboole_0 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_59,axiom,(
    ! [A,B] :
      ( v4_relat_1(k1_xboole_0,A)
      & v5_relat_1(k1_xboole_0,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t206_relat_1)).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(k1_xboole_0)
        & v5_relat_1(k1_xboole_0,A)
        & v1_funct_1(k1_xboole_0)
        & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).

tff(f_95,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v5_relat_1(B,A)
      & v1_funct_1(B)
      & v5_ordinal1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_ordinal1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k8_relat_1(k1_xboole_0,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

tff(c_20,plain,(
    ! [B_13] : v5_relat_1(k1_xboole_0,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_50,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,'#skF_3')
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_61,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_50])).

tff(c_80,plain,(
    ~ v5_ordinal1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_48,plain,(
    ! [A_22] : v1_relat_1('#skF_2'(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_46,plain,(
    ! [A_22] : v5_relat_1('#skF_2'(A_22),A_22) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_363,plain,(
    ! [A_62,B_63] :
      ( k8_relat_1(A_62,B_63) = B_63
      | ~ r1_tarski(k2_relat_1(B_63),A_62)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_368,plain,(
    ! [A_64,B_65] :
      ( k8_relat_1(A_64,B_65) = B_65
      | ~ v5_relat_1(B_65,A_64)
      | ~ v1_relat_1(B_65) ) ),
    inference(resolution,[status(thm)],[c_4,c_363])).

tff(c_374,plain,(
    ! [A_22] :
      ( k8_relat_1(A_22,'#skF_2'(A_22)) = '#skF_2'(A_22)
      | ~ v1_relat_1('#skF_2'(A_22)) ) ),
    inference(resolution,[status(thm)],[c_46,c_368])).

tff(c_410,plain,(
    ! [A_67] : k8_relat_1(A_67,'#skF_2'(A_67)) = '#skF_2'(A_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_374])).

tff(c_99,plain,(
    ! [A_37] :
      ( k8_relat_1(k1_xboole_0,A_37) = k1_xboole_0
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_107,plain,(
    ! [A_22] : k8_relat_1(k1_xboole_0,'#skF_2'(A_22)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_99])).

tff(c_426,plain,(
    '#skF_2'(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_107])).

tff(c_42,plain,(
    ! [A_22] : v5_ordinal1('#skF_2'(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_454,plain,(
    v5_ordinal1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_426,c_42])).

tff(c_466,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_454])).

tff(c_467,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_469,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_467])).

tff(c_30,plain,(
    ! [A_16] : v1_relat_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_505,plain,(
    ! [A_77] :
      ( k8_relat_1(k1_xboole_0,A_77) = k1_xboole_0
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_536,plain,(
    ! [A_79] : k8_relat_1(k1_xboole_0,k6_relat_1(A_79)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_505])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(k8_relat_1(A_4,B_5))
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_541,plain,(
    ! [A_79] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k6_relat_1(A_79)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_536,c_8])).

tff(c_546,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_541])).

tff(c_548,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_469,c_546])).

tff(c_549,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_467])).

tff(c_32,plain,(
    ! [A_16] : v1_funct_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_40,plain,(
    ! [A_17] :
      ( k1_relat_1(k6_relat_1(A_17)) = A_17
      | ~ v1_funct_1(k6_relat_1(A_17))
      | ~ v1_relat_1(k6_relat_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_52,plain,(
    ! [A_17] :
      ( k1_relat_1(k6_relat_1(A_17)) = A_17
      | ~ v1_relat_1(k6_relat_1(A_17)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_40])).

tff(c_56,plain,(
    ! [A_17] : k1_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_52])).

tff(c_648,plain,(
    ! [A_92] :
      ( k7_relat_1(A_92,k1_relat_1(A_92)) = A_92
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_657,plain,(
    ! [A_17] :
      ( k7_relat_1(k6_relat_1(A_17),A_17) = k6_relat_1(A_17)
      | ~ v1_relat_1(k6_relat_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_648])).

tff(c_662,plain,(
    ! [A_93] : k7_relat_1(k6_relat_1(A_93),A_93) = k6_relat_1(A_93) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_657])).

tff(c_553,plain,(
    ! [A_82] :
      ( k7_relat_1(A_82,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_564,plain,(
    ! [A_16] : k7_relat_1(k6_relat_1(A_16),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_553])).

tff(c_669,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_662,c_564])).

tff(c_699,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_669,c_32])).

tff(c_709,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_549,c_699])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:32:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.37  
% 2.70/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.38  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > v5_ordinal1 > v1_relat_1 > v1_funct_1 > k8_relat_1 > k7_relat_1 > k4_xboole_0 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.70/1.38  
% 2.70/1.38  %Foreground sorts:
% 2.70/1.38  
% 2.70/1.38  
% 2.70/1.38  %Background operators:
% 2.70/1.38  
% 2.70/1.38  
% 2.70/1.38  %Foreground operators:
% 2.70/1.38  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.70/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.70/1.38  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.70/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.70/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.70/1.38  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.70/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.70/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.70/1.38  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 2.70/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.70/1.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.70/1.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.70/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.70/1.38  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.70/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.70/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.70/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.70/1.38  
% 2.70/1.39  tff(f_59, axiom, (![A, B]: (v4_relat_1(k1_xboole_0, A) & v5_relat_1(k1_xboole_0, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t206_relat_1)).
% 2.70/1.39  tff(f_104, negated_conjecture, ~(![A]: (((v1_relat_1(k1_xboole_0) & v5_relat_1(k1_xboole_0, A)) & v1_funct_1(k1_xboole_0)) & v5_ordinal1(k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_ordinal1)).
% 2.70/1.39  tff(f_95, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) & v5_ordinal1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_ordinal1)).
% 2.70/1.39  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.70/1.39  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 2.70/1.39  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k1_xboole_0, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_relat_1)).
% 2.70/1.39  tff(f_73, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.70/1.39  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 2.70/1.39  tff(f_86, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 2.70/1.39  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 2.70/1.39  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_relat_1)).
% 2.70/1.39  tff(c_20, plain, (![B_13]: (v5_relat_1(k1_xboole_0, B_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.70/1.39  tff(c_50, plain, (~v1_relat_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0, '#skF_3') | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.70/1.39  tff(c_61, plain, (~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_50])).
% 2.70/1.39  tff(c_80, plain, (~v5_ordinal1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_61])).
% 2.70/1.39  tff(c_48, plain, (![A_22]: (v1_relat_1('#skF_2'(A_22)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.70/1.39  tff(c_46, plain, (![A_22]: (v5_relat_1('#skF_2'(A_22), A_22))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.70/1.39  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.70/1.39  tff(c_363, plain, (![A_62, B_63]: (k8_relat_1(A_62, B_63)=B_63 | ~r1_tarski(k2_relat_1(B_63), A_62) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.70/1.39  tff(c_368, plain, (![A_64, B_65]: (k8_relat_1(A_64, B_65)=B_65 | ~v5_relat_1(B_65, A_64) | ~v1_relat_1(B_65))), inference(resolution, [status(thm)], [c_4, c_363])).
% 2.70/1.39  tff(c_374, plain, (![A_22]: (k8_relat_1(A_22, '#skF_2'(A_22))='#skF_2'(A_22) | ~v1_relat_1('#skF_2'(A_22)))), inference(resolution, [status(thm)], [c_46, c_368])).
% 2.70/1.39  tff(c_410, plain, (![A_67]: (k8_relat_1(A_67, '#skF_2'(A_67))='#skF_2'(A_67))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_374])).
% 2.70/1.39  tff(c_99, plain, (![A_37]: (k8_relat_1(k1_xboole_0, A_37)=k1_xboole_0 | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.70/1.39  tff(c_107, plain, (![A_22]: (k8_relat_1(k1_xboole_0, '#skF_2'(A_22))=k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_99])).
% 2.70/1.39  tff(c_426, plain, ('#skF_2'(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_410, c_107])).
% 2.70/1.39  tff(c_42, plain, (![A_22]: (v5_ordinal1('#skF_2'(A_22)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.70/1.39  tff(c_454, plain, (v5_ordinal1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_426, c_42])).
% 2.70/1.39  tff(c_466, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_454])).
% 2.70/1.39  tff(c_467, plain, (~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_61])).
% 2.70/1.39  tff(c_469, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_467])).
% 2.70/1.39  tff(c_30, plain, (![A_16]: (v1_relat_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.70/1.39  tff(c_505, plain, (![A_77]: (k8_relat_1(k1_xboole_0, A_77)=k1_xboole_0 | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.70/1.39  tff(c_536, plain, (![A_79]: (k8_relat_1(k1_xboole_0, k6_relat_1(A_79))=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_505])).
% 2.70/1.39  tff(c_8, plain, (![A_4, B_5]: (v1_relat_1(k8_relat_1(A_4, B_5)) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.70/1.39  tff(c_541, plain, (![A_79]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(k6_relat_1(A_79)))), inference(superposition, [status(thm), theory('equality')], [c_536, c_8])).
% 2.70/1.39  tff(c_546, plain, (v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_541])).
% 2.70/1.39  tff(c_548, plain, $false, inference(negUnitSimplification, [status(thm)], [c_469, c_546])).
% 2.70/1.39  tff(c_549, plain, (~v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_467])).
% 2.70/1.39  tff(c_32, plain, (![A_16]: (v1_funct_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.70/1.39  tff(c_40, plain, (![A_17]: (k1_relat_1(k6_relat_1(A_17))=A_17 | ~v1_funct_1(k6_relat_1(A_17)) | ~v1_relat_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.70/1.39  tff(c_52, plain, (![A_17]: (k1_relat_1(k6_relat_1(A_17))=A_17 | ~v1_relat_1(k6_relat_1(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_40])).
% 2.70/1.39  tff(c_56, plain, (![A_17]: (k1_relat_1(k6_relat_1(A_17))=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_52])).
% 2.70/1.39  tff(c_648, plain, (![A_92]: (k7_relat_1(A_92, k1_relat_1(A_92))=A_92 | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.70/1.39  tff(c_657, plain, (![A_17]: (k7_relat_1(k6_relat_1(A_17), A_17)=k6_relat_1(A_17) | ~v1_relat_1(k6_relat_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_648])).
% 2.70/1.39  tff(c_662, plain, (![A_93]: (k7_relat_1(k6_relat_1(A_93), A_93)=k6_relat_1(A_93))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_657])).
% 2.70/1.39  tff(c_553, plain, (![A_82]: (k7_relat_1(A_82, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.70/1.39  tff(c_564, plain, (![A_16]: (k7_relat_1(k6_relat_1(A_16), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_553])).
% 2.70/1.39  tff(c_669, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_662, c_564])).
% 2.70/1.39  tff(c_699, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_669, c_32])).
% 2.70/1.39  tff(c_709, plain, $false, inference(negUnitSimplification, [status(thm)], [c_549, c_699])).
% 2.70/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.39  
% 2.70/1.39  Inference rules
% 2.70/1.39  ----------------------
% 2.70/1.39  #Ref     : 0
% 2.70/1.39  #Sup     : 157
% 2.70/1.39  #Fact    : 0
% 2.70/1.39  #Define  : 0
% 2.70/1.39  #Split   : 2
% 2.70/1.39  #Chain   : 0
% 2.70/1.39  #Close   : 0
% 2.70/1.39  
% 2.70/1.39  Ordering : KBO
% 2.70/1.39  
% 2.70/1.39  Simplification rules
% 2.70/1.39  ----------------------
% 2.70/1.39  #Subsume      : 0
% 2.70/1.39  #Demod        : 79
% 2.70/1.39  #Tautology    : 107
% 2.70/1.39  #SimpNegUnit  : 3
% 2.70/1.39  #BackRed      : 0
% 2.70/1.39  
% 2.70/1.39  #Partial instantiations: 0
% 2.70/1.39  #Strategies tried      : 1
% 2.70/1.39  
% 2.70/1.39  Timing (in seconds)
% 2.70/1.39  ----------------------
% 2.70/1.39  Preprocessing        : 0.31
% 2.70/1.39  Parsing              : 0.18
% 2.70/1.39  CNF conversion       : 0.02
% 2.70/1.39  Main loop            : 0.28
% 2.70/1.39  Inferencing          : 0.11
% 2.70/1.39  Reduction            : 0.09
% 2.70/1.39  Demodulation         : 0.07
% 2.70/1.39  BG Simplification    : 0.02
% 2.70/1.39  Subsumption          : 0.04
% 2.70/1.39  Abstraction          : 0.01
% 2.70/1.39  MUC search           : 0.00
% 2.70/1.39  Cooper               : 0.00
% 2.70/1.39  Total                : 0.63
% 2.70/1.39  Index Insertion      : 0.00
% 2.70/1.39  Index Deletion       : 0.00
% 2.70/1.39  Index Matching       : 0.00
% 2.70/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
