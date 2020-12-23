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
% DateTime   : Thu Dec  3 10:03:52 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 129 expanded)
%              Number of leaves         :   24 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :  108 ( 302 expanded)
%              Number of equality atoms :   41 ( 109 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
            & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_22,plain,(
    ! [A_14] :
      ( k7_relat_1(A_14,k1_relat_1(A_14)) = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_513,plain,(
    ! [B_41,A_42] :
      ( k2_relat_1(k7_relat_1(B_41,A_42)) = k9_relat_1(B_41,A_42)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_693,plain,(
    ! [A_49] :
      ( k9_relat_1(A_49,k1_relat_1(A_49)) = k2_relat_1(A_49)
      | ~ v1_relat_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_513])).

tff(c_30,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_28,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_525,plain,(
    ! [A_43] :
      ( k4_relat_1(A_43) = k2_funct_1(A_43)
      | ~ v2_funct_1(A_43)
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_528,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_525])).

tff(c_531,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_528])).

tff(c_8,plain,(
    ! [A_3] :
      ( v1_relat_1(k4_relat_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_559,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_531,c_8])).

tff(c_569,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_559])).

tff(c_16,plain,(
    ! [A_10] :
      ( k2_relat_1(k4_relat_1(A_10)) = k1_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_553,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_531,c_16])).

tff(c_565,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_553])).

tff(c_14,plain,(
    ! [B_9,A_7] :
      ( k9_relat_1(B_9,k2_relat_1(A_7)) = k2_relat_1(k5_relat_1(A_7,B_9))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_599,plain,(
    ! [B_9] :
      ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),B_9)) = k9_relat_1(B_9,k1_relat_1('#skF_1'))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_565,c_14])).

tff(c_672,plain,(
    ! [B_48] :
      ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),B_48)) = k9_relat_1(B_48,k1_relat_1('#skF_1'))
      | ~ v1_relat_1(B_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_569,c_599])).

tff(c_26,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_92,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_112,plain,(
    ! [A_26] :
      ( k4_relat_1(A_26) = k2_funct_1(A_26)
      | ~ v2_funct_1(A_26)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_115,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_112])).

tff(c_118,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_115])).

tff(c_131,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_8])).

tff(c_141,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_131])).

tff(c_18,plain,(
    ! [A_10] :
      ( k1_relat_1(k4_relat_1(A_10)) = k2_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_122,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_18])).

tff(c_135,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_122])).

tff(c_125,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_16])).

tff(c_137,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_125])).

tff(c_232,plain,(
    ! [A_29,B_30] :
      ( k1_relat_1(k5_relat_1(A_29,B_30)) = k1_relat_1(A_29)
      | ~ r1_tarski(k2_relat_1(A_29),k1_relat_1(B_30))
      | ~ v1_relat_1(B_30)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_241,plain,(
    ! [B_30] :
      ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),B_30)) = k1_relat_1(k2_funct_1('#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1(B_30))
      | ~ v1_relat_1(B_30)
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_232])).

tff(c_474,plain,(
    ! [B_38] :
      ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),B_38)) = k2_relat_1('#skF_1')
      | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1(B_38))
      | ~ v1_relat_1(B_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_135,c_241])).

tff(c_487,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_474])).

tff(c_494,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_487])).

tff(c_496,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_494])).

tff(c_497,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_684,plain,
    ( k9_relat_1('#skF_1',k1_relat_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_672,c_497])).

tff(c_690,plain,(
    k9_relat_1('#skF_1',k1_relat_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_684])).

tff(c_699,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_693,c_690])).

tff(c_716,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_699])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:26:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.42  
% 2.49/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.43  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.49/1.43  
% 2.49/1.43  %Foreground sorts:
% 2.49/1.43  
% 2.49/1.43  
% 2.49/1.43  %Background operators:
% 2.49/1.43  
% 2.49/1.43  
% 2.49/1.43  %Foreground operators:
% 2.49/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.49/1.43  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.49/1.43  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.49/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.43  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.49/1.43  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.49/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.49/1.43  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.49/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.49/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.49/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.49/1.43  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.49/1.43  
% 2.49/1.44  tff(f_88, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_1)).
% 2.49/1.44  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 2.49/1.44  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.49/1.44  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 2.49/1.44  tff(f_35, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 2.49/1.44  tff(f_56, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 2.49/1.44  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 2.49/1.44  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.49/1.44  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 2.49/1.44  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.49/1.44  tff(c_22, plain, (![A_14]: (k7_relat_1(A_14, k1_relat_1(A_14))=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.49/1.44  tff(c_513, plain, (![B_41, A_42]: (k2_relat_1(k7_relat_1(B_41, A_42))=k9_relat_1(B_41, A_42) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.49/1.44  tff(c_693, plain, (![A_49]: (k9_relat_1(A_49, k1_relat_1(A_49))=k2_relat_1(A_49) | ~v1_relat_1(A_49) | ~v1_relat_1(A_49))), inference(superposition, [status(thm), theory('equality')], [c_22, c_513])).
% 2.49/1.44  tff(c_30, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.49/1.44  tff(c_28, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.49/1.44  tff(c_525, plain, (![A_43]: (k4_relat_1(A_43)=k2_funct_1(A_43) | ~v2_funct_1(A_43) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.49/1.44  tff(c_528, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_28, c_525])).
% 2.49/1.44  tff(c_531, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_528])).
% 2.49/1.44  tff(c_8, plain, (![A_3]: (v1_relat_1(k4_relat_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.49/1.44  tff(c_559, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_531, c_8])).
% 2.49/1.44  tff(c_569, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_559])).
% 2.49/1.44  tff(c_16, plain, (![A_10]: (k2_relat_1(k4_relat_1(A_10))=k1_relat_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.49/1.44  tff(c_553, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_531, c_16])).
% 2.49/1.44  tff(c_565, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_553])).
% 2.49/1.44  tff(c_14, plain, (![B_9, A_7]: (k9_relat_1(B_9, k2_relat_1(A_7))=k2_relat_1(k5_relat_1(A_7, B_9)) | ~v1_relat_1(B_9) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.49/1.44  tff(c_599, plain, (![B_9]: (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), B_9))=k9_relat_1(B_9, k1_relat_1('#skF_1')) | ~v1_relat_1(B_9) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_565, c_14])).
% 2.49/1.44  tff(c_672, plain, (![B_48]: (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), B_48))=k9_relat_1(B_48, k1_relat_1('#skF_1')) | ~v1_relat_1(B_48))), inference(demodulation, [status(thm), theory('equality')], [c_569, c_599])).
% 2.49/1.44  tff(c_26, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.49/1.44  tff(c_92, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_26])).
% 2.49/1.44  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.49/1.44  tff(c_112, plain, (![A_26]: (k4_relat_1(A_26)=k2_funct_1(A_26) | ~v2_funct_1(A_26) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.49/1.44  tff(c_115, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_28, c_112])).
% 2.49/1.44  tff(c_118, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_115])).
% 2.49/1.44  tff(c_131, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_118, c_8])).
% 2.49/1.44  tff(c_141, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_131])).
% 2.49/1.44  tff(c_18, plain, (![A_10]: (k1_relat_1(k4_relat_1(A_10))=k2_relat_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.49/1.44  tff(c_122, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_118, c_18])).
% 2.49/1.44  tff(c_135, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_122])).
% 2.49/1.44  tff(c_125, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_118, c_16])).
% 2.49/1.44  tff(c_137, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_125])).
% 2.49/1.44  tff(c_232, plain, (![A_29, B_30]: (k1_relat_1(k5_relat_1(A_29, B_30))=k1_relat_1(A_29) | ~r1_tarski(k2_relat_1(A_29), k1_relat_1(B_30)) | ~v1_relat_1(B_30) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.49/1.44  tff(c_241, plain, (![B_30]: (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), B_30))=k1_relat_1(k2_funct_1('#skF_1')) | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1(B_30)) | ~v1_relat_1(B_30) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_137, c_232])).
% 2.49/1.44  tff(c_474, plain, (![B_38]: (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), B_38))=k2_relat_1('#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1(B_38)) | ~v1_relat_1(B_38))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_135, c_241])).
% 2.49/1.44  tff(c_487, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_474])).
% 2.49/1.44  tff(c_494, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_487])).
% 2.49/1.44  tff(c_496, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_494])).
% 2.49/1.44  tff(c_497, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_26])).
% 2.49/1.44  tff(c_684, plain, (k9_relat_1('#skF_1', k1_relat_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_672, c_497])).
% 2.49/1.44  tff(c_690, plain, (k9_relat_1('#skF_1', k1_relat_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_684])).
% 2.49/1.44  tff(c_699, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_693, c_690])).
% 2.49/1.44  tff(c_716, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_699])).
% 2.49/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.44  
% 2.49/1.44  Inference rules
% 2.49/1.44  ----------------------
% 2.49/1.44  #Ref     : 0
% 2.49/1.44  #Sup     : 173
% 2.49/1.44  #Fact    : 0
% 2.49/1.44  #Define  : 0
% 2.49/1.44  #Split   : 3
% 2.49/1.44  #Chain   : 0
% 2.49/1.44  #Close   : 0
% 2.49/1.44  
% 2.49/1.44  Ordering : KBO
% 2.49/1.44  
% 2.49/1.44  Simplification rules
% 2.49/1.44  ----------------------
% 2.49/1.44  #Subsume      : 4
% 2.49/1.44  #Demod        : 104
% 2.49/1.44  #Tautology    : 92
% 2.49/1.44  #SimpNegUnit  : 1
% 2.49/1.44  #BackRed      : 0
% 2.49/1.44  
% 2.49/1.44  #Partial instantiations: 0
% 2.49/1.44  #Strategies tried      : 1
% 2.49/1.44  
% 2.49/1.44  Timing (in seconds)
% 2.49/1.44  ----------------------
% 2.49/1.44  Preprocessing        : 0.33
% 2.49/1.44  Parsing              : 0.18
% 2.49/1.44  CNF conversion       : 0.02
% 2.49/1.44  Main loop            : 0.30
% 2.49/1.44  Inferencing          : 0.11
% 2.49/1.44  Reduction            : 0.09
% 2.49/1.44  Demodulation         : 0.07
% 2.49/1.44  BG Simplification    : 0.02
% 2.49/1.44  Subsumption          : 0.05
% 2.49/1.44  Abstraction          : 0.02
% 2.49/1.44  MUC search           : 0.00
% 2.49/1.44  Cooper               : 0.00
% 2.49/1.45  Total                : 0.67
% 2.49/1.45  Index Insertion      : 0.00
% 2.49/1.45  Index Deletion       : 0.00
% 2.49/1.45  Index Matching       : 0.00
% 2.49/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
