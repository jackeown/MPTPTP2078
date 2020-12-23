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
% DateTime   : Thu Dec  3 10:06:28 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   52 (  70 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   68 ( 107 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > v5_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_57,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v4_relat_1(k1_xboole_0,A)
      & v5_relat_1(k1_xboole_0,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(k1_xboole_0)
        & v5_relat_1(k1_xboole_0,A)
        & v1_funct_1(k1_xboole_0)
        & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).

tff(f_70,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v5_relat_1(B,A)
      & v1_funct_1(B)
      & v5_ordinal1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_ordinal1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_26,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_52,plain,(
    ! [A_17] : v1_relat_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_54,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_52])).

tff(c_20,plain,(
    ! [B_8] : v5_relat_1(k1_xboole_0,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_40,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,'#skF_2')
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_42,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_40])).

tff(c_57,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_42])).

tff(c_58,plain,(
    ~ v5_ordinal1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_57])).

tff(c_38,plain,(
    ! [A_11] : v1_relat_1('#skF_1'(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_36,plain,(
    ! [A_11] : v5_relat_1('#skF_1'(A_11),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_141,plain,(
    ! [B_36,A_37] :
      ( r1_tarski(k2_relat_1(B_36),A_37)
      | ~ v5_relat_1(B_36,A_37)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_99,plain,(
    ! [B_26,A_27] :
      ( B_26 = A_27
      | ~ r1_tarski(B_26,A_27)
      | ~ r1_tarski(A_27,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_108,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_99])).

tff(c_154,plain,(
    ! [B_38] :
      ( k2_relat_1(B_38) = k1_xboole_0
      | ~ v5_relat_1(B_38,k1_xboole_0)
      | ~ v1_relat_1(B_38) ) ),
    inference(resolution,[status(thm)],[c_141,c_108])).

tff(c_158,plain,
    ( k2_relat_1('#skF_1'(k1_xboole_0)) = k1_xboole_0
    | ~ v1_relat_1('#skF_1'(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_36,c_154])).

tff(c_165,plain,(
    k2_relat_1('#skF_1'(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_158])).

tff(c_85,plain,(
    ! [A_25] :
      ( k2_relat_1(A_25) != k1_xboole_0
      | k1_xboole_0 = A_25
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_98,plain,(
    ! [A_11] :
      ( k2_relat_1('#skF_1'(A_11)) != k1_xboole_0
      | '#skF_1'(A_11) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38,c_85])).

tff(c_236,plain,(
    '#skF_1'(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_98])).

tff(c_32,plain,(
    ! [A_11] : v5_ordinal1('#skF_1'(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_251,plain,(
    v5_ordinal1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_32])).

tff(c_263,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_251])).

tff(c_264,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_57])).

tff(c_268,plain,(
    ! [A_43] : v1_funct_1(k6_relat_1(A_43)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_270,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_268])).

tff(c_272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_264,c_270])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:33:59 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.25  
% 2.10/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.25  %$ v5_relat_1 > v4_relat_1 > r1_tarski > v5_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2
% 2.10/1.25  
% 2.10/1.25  %Foreground sorts:
% 2.10/1.25  
% 2.10/1.25  
% 2.10/1.25  %Background operators:
% 2.10/1.25  
% 2.10/1.25  
% 2.10/1.25  %Foreground operators:
% 2.10/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.25  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.10/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.10/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.10/1.25  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 2.10/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.25  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.10/1.25  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.25  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.10/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.10/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.10/1.25  
% 2.10/1.26  tff(f_57, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.10/1.26  tff(f_61, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.10/1.26  tff(f_48, axiom, (![A, B]: (v4_relat_1(k1_xboole_0, A) & v5_relat_1(k1_xboole_0, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l222_relat_1)).
% 2.10/1.26  tff(f_79, negated_conjecture, ~(![A]: (((v1_relat_1(k1_xboole_0) & v5_relat_1(k1_xboole_0, A)) & v1_funct_1(k1_xboole_0)) & v5_ordinal1(k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_ordinal1)).
% 2.10/1.26  tff(f_70, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) & v5_ordinal1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_ordinal1)).
% 2.10/1.26  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.10/1.26  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.10/1.26  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.10/1.26  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.10/1.26  tff(c_26, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.10/1.26  tff(c_52, plain, (![A_17]: (v1_relat_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.10/1.26  tff(c_54, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_52])).
% 2.10/1.26  tff(c_20, plain, (![B_8]: (v5_relat_1(k1_xboole_0, B_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.10/1.26  tff(c_40, plain, (~v1_relat_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0, '#skF_2') | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.10/1.26  tff(c_42, plain, (~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_40])).
% 2.10/1.26  tff(c_57, plain, (~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_42])).
% 2.10/1.26  tff(c_58, plain, (~v5_ordinal1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_57])).
% 2.10/1.26  tff(c_38, plain, (![A_11]: (v1_relat_1('#skF_1'(A_11)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.10/1.26  tff(c_36, plain, (![A_11]: (v5_relat_1('#skF_1'(A_11), A_11))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.10/1.26  tff(c_141, plain, (![B_36, A_37]: (r1_tarski(k2_relat_1(B_36), A_37) | ~v5_relat_1(B_36, A_37) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.10/1.26  tff(c_10, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.10/1.26  tff(c_99, plain, (![B_26, A_27]: (B_26=A_27 | ~r1_tarski(B_26, A_27) | ~r1_tarski(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.10/1.26  tff(c_108, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_99])).
% 2.10/1.26  tff(c_154, plain, (![B_38]: (k2_relat_1(B_38)=k1_xboole_0 | ~v5_relat_1(B_38, k1_xboole_0) | ~v1_relat_1(B_38))), inference(resolution, [status(thm)], [c_141, c_108])).
% 2.10/1.26  tff(c_158, plain, (k2_relat_1('#skF_1'(k1_xboole_0))=k1_xboole_0 | ~v1_relat_1('#skF_1'(k1_xboole_0))), inference(resolution, [status(thm)], [c_36, c_154])).
% 2.10/1.26  tff(c_165, plain, (k2_relat_1('#skF_1'(k1_xboole_0))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_158])).
% 2.10/1.26  tff(c_85, plain, (![A_25]: (k2_relat_1(A_25)!=k1_xboole_0 | k1_xboole_0=A_25 | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.10/1.26  tff(c_98, plain, (![A_11]: (k2_relat_1('#skF_1'(A_11))!=k1_xboole_0 | '#skF_1'(A_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_85])).
% 2.10/1.26  tff(c_236, plain, ('#skF_1'(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_165, c_98])).
% 2.10/1.26  tff(c_32, plain, (![A_11]: (v5_ordinal1('#skF_1'(A_11)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.10/1.26  tff(c_251, plain, (v5_ordinal1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_236, c_32])).
% 2.10/1.26  tff(c_263, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_251])).
% 2.10/1.26  tff(c_264, plain, (~v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_57])).
% 2.10/1.26  tff(c_268, plain, (![A_43]: (v1_funct_1(k6_relat_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.10/1.26  tff(c_270, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_268])).
% 2.10/1.26  tff(c_272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_264, c_270])).
% 2.10/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.26  
% 2.10/1.26  Inference rules
% 2.10/1.26  ----------------------
% 2.10/1.26  #Ref     : 0
% 2.10/1.26  #Sup     : 48
% 2.10/1.26  #Fact    : 0
% 2.10/1.26  #Define  : 0
% 2.10/1.26  #Split   : 1
% 2.10/1.26  #Chain   : 0
% 2.10/1.26  #Close   : 0
% 2.10/1.26  
% 2.10/1.26  Ordering : KBO
% 2.10/1.26  
% 2.10/1.26  Simplification rules
% 2.10/1.26  ----------------------
% 2.10/1.26  #Subsume      : 3
% 2.10/1.26  #Demod        : 34
% 2.10/1.26  #Tautology    : 27
% 2.10/1.26  #SimpNegUnit  : 2
% 2.10/1.26  #BackRed      : 1
% 2.10/1.26  
% 2.10/1.26  #Partial instantiations: 0
% 2.10/1.26  #Strategies tried      : 1
% 2.10/1.26  
% 2.10/1.26  Timing (in seconds)
% 2.10/1.26  ----------------------
% 2.19/1.27  Preprocessing        : 0.28
% 2.19/1.27  Parsing              : 0.16
% 2.19/1.27  CNF conversion       : 0.02
% 2.19/1.27  Main loop            : 0.20
% 2.19/1.27  Inferencing          : 0.08
% 2.19/1.27  Reduction            : 0.06
% 2.19/1.27  Demodulation         : 0.04
% 2.19/1.27  BG Simplification    : 0.01
% 2.19/1.27  Subsumption          : 0.03
% 2.19/1.27  Abstraction          : 0.01
% 2.19/1.27  MUC search           : 0.00
% 2.19/1.27  Cooper               : 0.00
% 2.19/1.27  Total                : 0.52
% 2.19/1.27  Index Insertion      : 0.00
% 2.19/1.27  Index Deletion       : 0.00
% 2.19/1.27  Index Matching       : 0.00
% 2.19/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
