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
% DateTime   : Thu Dec  3 10:02:24 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   49 (  53 expanded)
%              Number of leaves         :   31 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   55 (  65 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_xboole_0(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_36,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_xboole_0(B) )
     => ( v1_xboole_0(k7_relat_1(A,B))
        & v1_relat_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc16_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_66,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_46,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_10,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_38,plain,(
    ! [A_42,B_43] :
      ( v1_xboole_0(k7_relat_1(A_42,B_43))
      | ~ v1_xboole_0(B_43)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_112,plain,(
    ! [A_64,B_65] :
      ( r2_hidden('#skF_2'(A_64,B_65),A_64)
      | r1_xboole_0(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_117,plain,(
    ! [A_66,B_67] :
      ( ~ v1_xboole_0(A_66)
      | r1_xboole_0(A_66,B_67) ) ),
    inference(resolution,[status(thm)],[c_112,c_2])).

tff(c_20,plain,(
    ! [A_12] :
      ( ~ r1_xboole_0(A_12,A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_132,plain,(
    ! [B_70] :
      ( k1_xboole_0 = B_70
      | ~ v1_xboole_0(B_70) ) ),
    inference(resolution,[status(thm)],[c_117,c_20])).

tff(c_210,plain,(
    ! [A_82,B_83] :
      ( k7_relat_1(A_82,B_83) = k1_xboole_0
      | ~ v1_xboole_0(B_83)
      | ~ v1_relat_1(A_82) ) ),
    inference(resolution,[status(thm)],[c_38,c_132])).

tff(c_217,plain,(
    ! [A_84] :
      ( k7_relat_1(A_84,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_84) ) ),
    inference(resolution,[status(thm)],[c_10,c_210])).

tff(c_225,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_217])).

tff(c_44,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_75,plain,(
    ! [A_56,B_57] :
      ( k3_xboole_0(A_56,B_57) = k1_xboole_0
      | ~ r1_xboole_0(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_87,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_75])).

tff(c_382,plain,(
    ! [C_101,A_102,B_103] :
      ( k7_relat_1(k7_relat_1(C_101,A_102),B_103) = k7_relat_1(C_101,k3_xboole_0(A_102,B_103))
      | ~ v1_relat_1(C_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_42,plain,(
    k7_relat_1(k7_relat_1('#skF_5','#skF_3'),'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_397,plain,
    ( k7_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_42])).

tff(c_413,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_225,c_87,c_397])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:34:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.32  
% 2.41/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.32  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.41/1.32  
% 2.41/1.32  %Foreground sorts:
% 2.41/1.32  
% 2.41/1.32  
% 2.41/1.32  %Background operators:
% 2.41/1.32  
% 2.41/1.32  
% 2.41/1.32  %Foreground operators:
% 2.41/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.41/1.32  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.41/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.41/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.41/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.41/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.41/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.41/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.41/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.41/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.41/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.41/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.41/1.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.41/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.41/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.41/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.41/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.41/1.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.41/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.41/1.32  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.41/1.32  
% 2.41/1.33  tff(f_99, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 2.41/1.33  tff(f_36, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.41/1.33  tff(f_88, axiom, (![A, B]: ((v1_relat_1(A) & v1_xboole_0(B)) => (v1_xboole_0(k7_relat_1(A, B)) & v1_relat_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc16_relat_1)).
% 2.41/1.33  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.41/1.33  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.41/1.33  tff(f_66, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.41/1.33  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.41/1.33  tff(f_92, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 2.41/1.33  tff(c_46, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.41/1.33  tff(c_10, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.41/1.33  tff(c_38, plain, (![A_42, B_43]: (v1_xboole_0(k7_relat_1(A_42, B_43)) | ~v1_xboole_0(B_43) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.41/1.33  tff(c_112, plain, (![A_64, B_65]: (r2_hidden('#skF_2'(A_64, B_65), A_64) | r1_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.41/1.33  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.41/1.33  tff(c_117, plain, (![A_66, B_67]: (~v1_xboole_0(A_66) | r1_xboole_0(A_66, B_67))), inference(resolution, [status(thm)], [c_112, c_2])).
% 2.41/1.33  tff(c_20, plain, (![A_12]: (~r1_xboole_0(A_12, A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.41/1.33  tff(c_132, plain, (![B_70]: (k1_xboole_0=B_70 | ~v1_xboole_0(B_70))), inference(resolution, [status(thm)], [c_117, c_20])).
% 2.41/1.33  tff(c_210, plain, (![A_82, B_83]: (k7_relat_1(A_82, B_83)=k1_xboole_0 | ~v1_xboole_0(B_83) | ~v1_relat_1(A_82))), inference(resolution, [status(thm)], [c_38, c_132])).
% 2.41/1.33  tff(c_217, plain, (![A_84]: (k7_relat_1(A_84, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_84))), inference(resolution, [status(thm)], [c_10, c_210])).
% 2.41/1.33  tff(c_225, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_217])).
% 2.41/1.33  tff(c_44, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.41/1.33  tff(c_75, plain, (![A_56, B_57]: (k3_xboole_0(A_56, B_57)=k1_xboole_0 | ~r1_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.41/1.33  tff(c_87, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_75])).
% 2.41/1.33  tff(c_382, plain, (![C_101, A_102, B_103]: (k7_relat_1(k7_relat_1(C_101, A_102), B_103)=k7_relat_1(C_101, k3_xboole_0(A_102, B_103)) | ~v1_relat_1(C_101))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.41/1.33  tff(c_42, plain, (k7_relat_1(k7_relat_1('#skF_5', '#skF_3'), '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.41/1.33  tff(c_397, plain, (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_382, c_42])).
% 2.41/1.33  tff(c_413, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_225, c_87, c_397])).
% 2.41/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.33  
% 2.41/1.33  Inference rules
% 2.41/1.33  ----------------------
% 2.41/1.33  #Ref     : 0
% 2.41/1.33  #Sup     : 87
% 2.41/1.33  #Fact    : 0
% 2.41/1.33  #Define  : 0
% 2.41/1.33  #Split   : 1
% 2.41/1.33  #Chain   : 0
% 2.41/1.33  #Close   : 0
% 2.41/1.33  
% 2.41/1.33  Ordering : KBO
% 2.41/1.33  
% 2.41/1.33  Simplification rules
% 2.41/1.33  ----------------------
% 2.41/1.33  #Subsume      : 6
% 2.41/1.33  #Demod        : 20
% 2.41/1.33  #Tautology    : 43
% 2.41/1.33  #SimpNegUnit  : 0
% 2.41/1.33  #BackRed      : 0
% 2.41/1.33  
% 2.41/1.33  #Partial instantiations: 0
% 2.41/1.33  #Strategies tried      : 1
% 2.41/1.33  
% 2.41/1.33  Timing (in seconds)
% 2.41/1.33  ----------------------
% 2.41/1.33  Preprocessing        : 0.33
% 2.41/1.33  Parsing              : 0.17
% 2.41/1.33  CNF conversion       : 0.02
% 2.41/1.34  Main loop            : 0.24
% 2.41/1.34  Inferencing          : 0.09
% 2.41/1.34  Reduction            : 0.06
% 2.41/1.34  Demodulation         : 0.04
% 2.41/1.34  BG Simplification    : 0.02
% 2.41/1.34  Subsumption          : 0.05
% 2.41/1.34  Abstraction          : 0.02
% 2.41/1.34  MUC search           : 0.00
% 2.41/1.34  Cooper               : 0.00
% 2.41/1.34  Total                : 0.60
% 2.41/1.34  Index Insertion      : 0.00
% 2.41/1.34  Index Deletion       : 0.00
% 2.41/1.34  Index Matching       : 0.00
% 2.41/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
