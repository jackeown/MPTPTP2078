%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:23 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   59 (  89 expanded)
%              Number of leaves         :   36 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :   50 (  90 expanded)
%              Number of equality atoms :   23 (  54 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_47,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_82,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_51,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_42,plain,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_12,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_98,plain,(
    ! [A_70,B_71] : k5_xboole_0(A_70,k3_xboole_0(A_70,B_71)) = k4_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_107,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = k4_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_98])).

tff(c_111,plain,(
    ! [A_72] : k4_xboole_0(A_72,k1_xboole_0) = A_72 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_107])).

tff(c_16,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_123,plain,(
    ! [A_73] : k5_xboole_0(k1_xboole_0,A_73) = k2_xboole_0(k1_xboole_0,A_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_16])).

tff(c_138,plain,(
    k2_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_12])).

tff(c_40,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_38,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_178,plain,(
    ! [A_77] :
      ( k2_xboole_0(k1_relat_1(A_77),k2_relat_1(A_77)) = k3_relat_1(A_77)
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_187,plain,
    ( k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0) = k3_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_178])).

tff(c_193,plain,
    ( k3_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_40,c_187])).

tff(c_194,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_193])).

tff(c_34,plain,(
    ! [A_36] :
      ( r2_hidden('#skF_2'(A_36),A_36)
      | v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_14,plain,(
    ! [A_10] : r1_xboole_0(A_10,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_198,plain,(
    ! [A_78,B_79,C_80] :
      ( ~ r1_xboole_0(A_78,B_79)
      | ~ r2_hidden(C_80,B_79)
      | ~ r2_hidden(C_80,A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_202,plain,(
    ! [C_81,A_82] :
      ( ~ r2_hidden(C_81,k1_xboole_0)
      | ~ r2_hidden(C_81,A_82) ) ),
    inference(resolution,[status(thm)],[c_14,c_198])).

tff(c_211,plain,(
    ! [A_82] :
      ( ~ r2_hidden('#skF_2'(k1_xboole_0),A_82)
      | v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_34,c_202])).

tff(c_227,plain,(
    ! [A_86] : ~ r2_hidden('#skF_2'(k1_xboole_0),A_86) ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_211])).

tff(c_231,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_34,c_227])).

tff(c_235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_231])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n005.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 10:20:32 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.27  
% 2.02/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.28  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.02/1.28  
% 2.02/1.28  %Foreground sorts:
% 2.02/1.28  
% 2.02/1.28  
% 2.02/1.28  %Background operators:
% 2.02/1.28  
% 2.02/1.28  
% 2.02/1.28  %Foreground operators:
% 2.02/1.28  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.02/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.02/1.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.02/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.02/1.28  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.02/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.02/1.28  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.02/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.02/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.02/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.02/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.02/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.02/1.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.02/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.02/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.02/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.02/1.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.02/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.02/1.28  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.02/1.28  
% 2.02/1.29  tff(f_84, negated_conjecture, ~(k3_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_relat_1)).
% 2.02/1.29  tff(f_49, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.02/1.29  tff(f_47, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.02/1.29  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.02/1.29  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.02/1.29  tff(f_82, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.02/1.29  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 2.02/1.29  tff(f_75, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.02/1.29  tff(f_51, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.02/1.29  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.02/1.29  tff(c_42, plain, (k3_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.02/1.29  tff(c_12, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.02/1.29  tff(c_10, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.02/1.29  tff(c_98, plain, (![A_70, B_71]: (k5_xboole_0(A_70, k3_xboole_0(A_70, B_71))=k4_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.02/1.29  tff(c_107, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=k4_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_98])).
% 2.02/1.29  tff(c_111, plain, (![A_72]: (k4_xboole_0(A_72, k1_xboole_0)=A_72)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_107])).
% 2.02/1.29  tff(c_16, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.02/1.29  tff(c_123, plain, (![A_73]: (k5_xboole_0(k1_xboole_0, A_73)=k2_xboole_0(k1_xboole_0, A_73))), inference(superposition, [status(thm), theory('equality')], [c_111, c_16])).
% 2.02/1.29  tff(c_138, plain, (k2_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_123, c_12])).
% 2.02/1.29  tff(c_40, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.02/1.29  tff(c_38, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.02/1.29  tff(c_178, plain, (![A_77]: (k2_xboole_0(k1_relat_1(A_77), k2_relat_1(A_77))=k3_relat_1(A_77) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.02/1.29  tff(c_187, plain, (k2_xboole_0(k1_relat_1(k1_xboole_0), k1_xboole_0)=k3_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_38, c_178])).
% 2.02/1.29  tff(c_193, plain, (k3_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_138, c_40, c_187])).
% 2.02/1.29  tff(c_194, plain, (~v1_relat_1(k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_42, c_193])).
% 2.02/1.29  tff(c_34, plain, (![A_36]: (r2_hidden('#skF_2'(A_36), A_36) | v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.02/1.29  tff(c_14, plain, (![A_10]: (r1_xboole_0(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.02/1.29  tff(c_198, plain, (![A_78, B_79, C_80]: (~r1_xboole_0(A_78, B_79) | ~r2_hidden(C_80, B_79) | ~r2_hidden(C_80, A_78))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.02/1.29  tff(c_202, plain, (![C_81, A_82]: (~r2_hidden(C_81, k1_xboole_0) | ~r2_hidden(C_81, A_82))), inference(resolution, [status(thm)], [c_14, c_198])).
% 2.02/1.29  tff(c_211, plain, (![A_82]: (~r2_hidden('#skF_2'(k1_xboole_0), A_82) | v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_34, c_202])).
% 2.02/1.29  tff(c_227, plain, (![A_86]: (~r2_hidden('#skF_2'(k1_xboole_0), A_86))), inference(negUnitSimplification, [status(thm)], [c_194, c_211])).
% 2.02/1.29  tff(c_231, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_227])).
% 2.02/1.29  tff(c_235, plain, $false, inference(negUnitSimplification, [status(thm)], [c_194, c_231])).
% 2.02/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.29  
% 2.02/1.29  Inference rules
% 2.02/1.29  ----------------------
% 2.02/1.29  #Ref     : 0
% 2.02/1.29  #Sup     : 44
% 2.02/1.29  #Fact    : 0
% 2.02/1.29  #Define  : 0
% 2.02/1.29  #Split   : 0
% 2.02/1.29  #Chain   : 0
% 2.02/1.29  #Close   : 0
% 2.02/1.29  
% 2.02/1.29  Ordering : KBO
% 2.02/1.29  
% 2.02/1.29  Simplification rules
% 2.02/1.29  ----------------------
% 2.02/1.29  #Subsume      : 1
% 2.02/1.29  #Demod        : 12
% 2.02/1.29  #Tautology    : 34
% 2.02/1.29  #SimpNegUnit  : 4
% 2.02/1.29  #BackRed      : 0
% 2.02/1.29  
% 2.02/1.29  #Partial instantiations: 0
% 2.02/1.29  #Strategies tried      : 1
% 2.02/1.29  
% 2.02/1.29  Timing (in seconds)
% 2.02/1.29  ----------------------
% 2.02/1.29  Preprocessing        : 0.31
% 2.02/1.29  Parsing              : 0.17
% 2.02/1.29  CNF conversion       : 0.02
% 2.02/1.29  Main loop            : 0.22
% 2.02/1.29  Inferencing          : 0.09
% 2.02/1.29  Reduction            : 0.07
% 2.02/1.29  Demodulation         : 0.04
% 2.02/1.29  BG Simplification    : 0.01
% 2.02/1.29  Subsumption          : 0.02
% 2.02/1.29  Abstraction          : 0.01
% 2.02/1.29  MUC search           : 0.00
% 2.02/1.29  Cooper               : 0.00
% 2.02/1.29  Total                : 0.56
% 2.02/1.29  Index Insertion      : 0.00
% 2.02/1.29  Index Deletion       : 0.00
% 2.02/1.29  Index Matching       : 0.00
% 2.02/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
