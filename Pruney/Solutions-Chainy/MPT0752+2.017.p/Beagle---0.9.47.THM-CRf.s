%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:28 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   52 (  75 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   75 ( 120 expanded)
%              Number of equality atoms :   24 (  30 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > v5_ordinal1 > v1_relat_1 > v1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_54,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v4_relat_1(k1_xboole_0,A)
      & v5_relat_1(k1_xboole_0,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(k1_xboole_0)
        & v5_relat_1(k1_xboole_0,A)
        & v1_funct_1(k1_xboole_0)
        & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).

tff(f_67,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v5_relat_1(B,A)
      & v1_funct_1(B)
      & v5_ordinal1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_ordinal1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_53,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( ( k2_relat_1(A) = k1_xboole_0
              & k2_relat_1(B) = k1_xboole_0 )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t197_relat_1)).

tff(c_18,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_50,plain,(
    ! [A_15] : v1_relat_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_52,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_50])).

tff(c_10,plain,(
    ! [B_5] : v5_relat_1(k1_xboole_0,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_32,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,'#skF_2')
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_34,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_32])).

tff(c_55,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_34])).

tff(c_56,plain,(
    ~ v5_ordinal1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_55])).

tff(c_30,plain,(
    ! [A_10] : v1_relat_1('#skF_1'(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_28,plain,(
    ! [A_10] : v5_relat_1('#skF_1'(A_10),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_63,plain,(
    ! [B_21,A_22] :
      ( r1_tarski(k2_relat_1(B_21),A_22)
      | ~ v5_relat_1(B_21,A_22)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_81,plain,(
    ! [B_24] :
      ( k2_relat_1(B_24) = k1_xboole_0
      | ~ v5_relat_1(B_24,k1_xboole_0)
      | ~ v1_relat_1(B_24) ) ),
    inference(resolution,[status(thm)],[c_63,c_2])).

tff(c_85,plain,
    ( k2_relat_1('#skF_1'(k1_xboole_0)) = k1_xboole_0
    | ~ v1_relat_1('#skF_1'(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_28,c_81])).

tff(c_92,plain,(
    k2_relat_1('#skF_1'(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_85])).

tff(c_14,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_128,plain,(
    ! [B_28,A_29] :
      ( B_28 = A_29
      | k2_relat_1(B_28) != k1_xboole_0
      | k2_relat_1(A_29) != k1_xboole_0
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_130,plain,(
    ! [A_29] :
      ( k1_xboole_0 = A_29
      | k2_relat_1(k1_xboole_0) != k1_xboole_0
      | k2_relat_1(A_29) != k1_xboole_0
      | ~ v1_relat_1(A_29) ) ),
    inference(resolution,[status(thm)],[c_52,c_128])).

tff(c_140,plain,(
    ! [A_30] :
      ( k1_xboole_0 = A_30
      | k2_relat_1(A_30) != k1_xboole_0
      | ~ v1_relat_1(A_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_130])).

tff(c_166,plain,(
    ! [A_34] :
      ( '#skF_1'(A_34) = k1_xboole_0
      | k2_relat_1('#skF_1'(A_34)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_140])).

tff(c_170,plain,(
    '#skF_1'(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_166])).

tff(c_24,plain,(
    ! [A_10] : v5_ordinal1('#skF_1'(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_185,plain,(
    v5_ordinal1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_24])).

tff(c_198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_185])).

tff(c_199,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_201,plain,(
    ! [A_35] : v1_funct_1(k6_relat_1(A_35)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_203,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_201])).

tff(c_205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_199,c_203])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:15:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.17  
% 1.66/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.18  %$ v5_relat_1 > v4_relat_1 > r1_tarski > v5_ordinal1 > v1_relat_1 > v1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2
% 1.66/1.18  
% 1.66/1.18  %Foreground sorts:
% 1.66/1.18  
% 1.66/1.18  
% 1.66/1.18  %Background operators:
% 1.66/1.18  
% 1.66/1.18  
% 1.66/1.18  %Foreground operators:
% 1.66/1.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.66/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.18  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.66/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.66/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.66/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.66/1.18  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 1.66/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.18  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.66/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.66/1.18  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.66/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.18  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.66/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.66/1.18  
% 1.95/1.19  tff(f_54, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 1.95/1.19  tff(f_58, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.95/1.19  tff(f_39, axiom, (![A, B]: (v4_relat_1(k1_xboole_0, A) & v5_relat_1(k1_xboole_0, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l222_relat_1)).
% 1.95/1.19  tff(f_76, negated_conjecture, ~(![A]: (((v1_relat_1(k1_xboole_0) & v5_relat_1(k1_xboole_0, A)) & v1_funct_1(k1_xboole_0)) & v5_ordinal1(k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_ordinal1)).
% 1.95/1.19  tff(f_67, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) & v5_ordinal1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_ordinal1)).
% 1.95/1.19  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 1.95/1.19  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.95/1.19  tff(f_53, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.95/1.19  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (((k2_relat_1(A) = k1_xboole_0) & (k2_relat_1(B) = k1_xboole_0)) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t197_relat_1)).
% 1.95/1.19  tff(c_18, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.95/1.19  tff(c_50, plain, (![A_15]: (v1_relat_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.95/1.19  tff(c_52, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_50])).
% 1.95/1.19  tff(c_10, plain, (![B_5]: (v5_relat_1(k1_xboole_0, B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.95/1.19  tff(c_32, plain, (~v1_relat_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0, '#skF_2') | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.95/1.19  tff(c_34, plain, (~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_32])).
% 1.95/1.19  tff(c_55, plain, (~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_34])).
% 1.95/1.19  tff(c_56, plain, (~v5_ordinal1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_55])).
% 1.95/1.19  tff(c_30, plain, (![A_10]: (v1_relat_1('#skF_1'(A_10)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.95/1.19  tff(c_28, plain, (![A_10]: (v5_relat_1('#skF_1'(A_10), A_10))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.95/1.19  tff(c_63, plain, (![B_21, A_22]: (r1_tarski(k2_relat_1(B_21), A_22) | ~v5_relat_1(B_21, A_22) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.95/1.19  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.95/1.19  tff(c_81, plain, (![B_24]: (k2_relat_1(B_24)=k1_xboole_0 | ~v5_relat_1(B_24, k1_xboole_0) | ~v1_relat_1(B_24))), inference(resolution, [status(thm)], [c_63, c_2])).
% 1.95/1.19  tff(c_85, plain, (k2_relat_1('#skF_1'(k1_xboole_0))=k1_xboole_0 | ~v1_relat_1('#skF_1'(k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_81])).
% 1.95/1.19  tff(c_92, plain, (k2_relat_1('#skF_1'(k1_xboole_0))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_85])).
% 1.95/1.19  tff(c_14, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.95/1.19  tff(c_128, plain, (![B_28, A_29]: (B_28=A_29 | k2_relat_1(B_28)!=k1_xboole_0 | k2_relat_1(A_29)!=k1_xboole_0 | ~v1_relat_1(B_28) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.95/1.19  tff(c_130, plain, (![A_29]: (k1_xboole_0=A_29 | k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k2_relat_1(A_29)!=k1_xboole_0 | ~v1_relat_1(A_29))), inference(resolution, [status(thm)], [c_52, c_128])).
% 1.95/1.19  tff(c_140, plain, (![A_30]: (k1_xboole_0=A_30 | k2_relat_1(A_30)!=k1_xboole_0 | ~v1_relat_1(A_30))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_130])).
% 1.95/1.19  tff(c_166, plain, (![A_34]: ('#skF_1'(A_34)=k1_xboole_0 | k2_relat_1('#skF_1'(A_34))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_140])).
% 1.95/1.19  tff(c_170, plain, ('#skF_1'(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_92, c_166])).
% 1.95/1.19  tff(c_24, plain, (![A_10]: (v5_ordinal1('#skF_1'(A_10)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.95/1.19  tff(c_185, plain, (v5_ordinal1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_170, c_24])).
% 1.95/1.19  tff(c_198, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_185])).
% 1.95/1.19  tff(c_199, plain, (~v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_55])).
% 1.95/1.19  tff(c_201, plain, (![A_35]: (v1_funct_1(k6_relat_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.95/1.19  tff(c_203, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_201])).
% 1.95/1.19  tff(c_205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_199, c_203])).
% 1.95/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.19  
% 1.95/1.19  Inference rules
% 1.95/1.19  ----------------------
% 1.95/1.19  #Ref     : 0
% 1.95/1.19  #Sup     : 38
% 1.95/1.19  #Fact    : 0
% 1.95/1.19  #Define  : 0
% 1.95/1.19  #Split   : 1
% 1.95/1.19  #Chain   : 0
% 1.95/1.19  #Close   : 0
% 1.95/1.19  
% 1.95/1.19  Ordering : KBO
% 1.95/1.19  
% 1.95/1.19  Simplification rules
% 1.95/1.19  ----------------------
% 1.95/1.19  #Subsume      : 1
% 1.95/1.19  #Demod        : 29
% 1.95/1.19  #Tautology    : 21
% 1.95/1.19  #SimpNegUnit  : 2
% 1.95/1.19  #BackRed      : 2
% 1.95/1.19  
% 1.95/1.19  #Partial instantiations: 0
% 1.95/1.19  #Strategies tried      : 1
% 1.95/1.19  
% 1.95/1.19  Timing (in seconds)
% 1.95/1.19  ----------------------
% 1.95/1.19  Preprocessing        : 0.27
% 1.95/1.19  Parsing              : 0.15
% 1.95/1.19  CNF conversion       : 0.02
% 1.95/1.19  Main loop            : 0.17
% 1.95/1.19  Inferencing          : 0.07
% 1.95/1.19  Reduction            : 0.05
% 1.95/1.19  Demodulation         : 0.04
% 1.95/1.19  BG Simplification    : 0.01
% 1.95/1.19  Subsumption          : 0.03
% 1.95/1.19  Abstraction          : 0.01
% 1.95/1.19  MUC search           : 0.00
% 1.95/1.20  Cooper               : 0.00
% 1.95/1.20  Total                : 0.47
% 1.95/1.20  Index Insertion      : 0.00
% 1.95/1.20  Index Deletion       : 0.00
% 1.95/1.20  Index Matching       : 0.00
% 1.95/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
