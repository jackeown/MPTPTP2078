%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:03 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 257 expanded)
%              Number of leaves         :   34 ( 106 expanded)
%              Depth                    :   10
%              Number of atoms          :   48 ( 403 expanded)
%              Number of equality atoms :   23 ( 182 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_47,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => r2_xboole_0(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_42,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_66,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_95,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_18,plain,(
    ! [A_8] :
      ( r2_xboole_0(k1_xboole_0,A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_79,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(A_70,B_71)
      | ~ r2_xboole_0(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_83,plain,(
    ! [A_8] :
      ( r1_tarski(k1_xboole_0,A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(resolution,[status(thm)],[c_18,c_79])).

tff(c_44,plain,(
    ! [A_41] :
      ( r2_hidden('#skF_1'(A_41),A_41)
      | v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_16,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_193,plain,(
    ! [B_92,A_93] :
      ( ~ r2_hidden(B_92,A_93)
      | k4_xboole_0(A_93,k1_tarski(B_92)) != A_93 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_203,plain,(
    ! [B_94] : ~ r2_hidden(B_94,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_193])).

tff(c_208,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_44,c_203])).

tff(c_50,plain,(
    ! [A_64] :
      ( k7_relat_1(A_64,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_212,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_208,c_50])).

tff(c_270,plain,(
    ! [C_105,A_106,B_107] :
      ( k7_relat_1(k7_relat_1(C_105,A_106),B_107) = k7_relat_1(C_105,A_106)
      | ~ r1_tarski(A_106,B_107)
      | ~ v1_relat_1(C_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_298,plain,(
    ! [B_107] :
      ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1(k1_xboole_0,B_107)
      | ~ r1_tarski(k1_xboole_0,B_107)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_270])).

tff(c_310,plain,(
    ! [B_108] :
      ( k7_relat_1(k1_xboole_0,B_108) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,B_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_212,c_298])).

tff(c_332,plain,(
    ! [A_111] :
      ( k7_relat_1(k1_xboole_0,A_111) = k1_xboole_0
      | k1_xboole_0 = A_111 ) ),
    inference(resolution,[status(thm)],[c_83,c_310])).

tff(c_52,plain,(
    k7_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_361,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_52])).

tff(c_374,plain,(
    k7_relat_1('#skF_4','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_361,c_52])).

tff(c_366,plain,(
    k7_relat_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_361,c_361,c_212])).

tff(c_419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_374,c_366])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:55:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.39  
% 2.46/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.39  %$ r2_xboole_0 > r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.46/1.39  
% 2.46/1.39  %Foreground sorts:
% 2.46/1.39  
% 2.46/1.39  
% 2.46/1.39  %Background operators:
% 2.46/1.39  
% 2.46/1.39  
% 2.46/1.39  %Foreground operators:
% 2.46/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.46/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.46/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.46/1.39  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.46/1.39  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.46/1.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.46/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.46/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.46/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.46/1.39  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.46/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.46/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.46/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.46/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.46/1.39  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.46/1.39  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.46/1.39  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.46/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.46/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.46/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.46/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.46/1.39  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.46/1.39  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.46/1.39  
% 2.46/1.41  tff(f_47, axiom, (![A]: (~(A = k1_xboole_0) => r2_xboole_0(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_xboole_1)).
% 2.46/1.41  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.46/1.41  tff(f_78, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.46/1.41  tff(f_42, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.46/1.41  tff(f_66, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.46/1.41  tff(f_92, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_relat_1)).
% 2.46/1.41  tff(f_88, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_relat_1)).
% 2.46/1.41  tff(f_95, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 2.46/1.41  tff(c_18, plain, (![A_8]: (r2_xboole_0(k1_xboole_0, A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.46/1.41  tff(c_79, plain, (![A_70, B_71]: (r1_tarski(A_70, B_71) | ~r2_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.46/1.41  tff(c_83, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8) | k1_xboole_0=A_8)), inference(resolution, [status(thm)], [c_18, c_79])).
% 2.46/1.41  tff(c_44, plain, (![A_41]: (r2_hidden('#skF_1'(A_41), A_41) | v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.46/1.41  tff(c_16, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.46/1.41  tff(c_193, plain, (![B_92, A_93]: (~r2_hidden(B_92, A_93) | k4_xboole_0(A_93, k1_tarski(B_92))!=A_93)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.46/1.41  tff(c_203, plain, (![B_94]: (~r2_hidden(B_94, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_193])).
% 2.46/1.41  tff(c_208, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_203])).
% 2.46/1.41  tff(c_50, plain, (![A_64]: (k7_relat_1(A_64, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.46/1.41  tff(c_212, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_208, c_50])).
% 2.46/1.41  tff(c_270, plain, (![C_105, A_106, B_107]: (k7_relat_1(k7_relat_1(C_105, A_106), B_107)=k7_relat_1(C_105, A_106) | ~r1_tarski(A_106, B_107) | ~v1_relat_1(C_105))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.46/1.41  tff(c_298, plain, (![B_107]: (k7_relat_1(k1_xboole_0, k1_xboole_0)=k7_relat_1(k1_xboole_0, B_107) | ~r1_tarski(k1_xboole_0, B_107) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_212, c_270])).
% 2.46/1.41  tff(c_310, plain, (![B_108]: (k7_relat_1(k1_xboole_0, B_108)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, B_108))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_212, c_298])).
% 2.46/1.41  tff(c_332, plain, (![A_111]: (k7_relat_1(k1_xboole_0, A_111)=k1_xboole_0 | k1_xboole_0=A_111)), inference(resolution, [status(thm)], [c_83, c_310])).
% 2.46/1.41  tff(c_52, plain, (k7_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.46/1.41  tff(c_361, plain, (k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_332, c_52])).
% 2.46/1.41  tff(c_374, plain, (k7_relat_1('#skF_4', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_361, c_361, c_52])).
% 2.46/1.41  tff(c_366, plain, (k7_relat_1('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_361, c_361, c_361, c_212])).
% 2.46/1.41  tff(c_419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_374, c_366])).
% 2.46/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.41  
% 2.46/1.41  Inference rules
% 2.46/1.41  ----------------------
% 2.46/1.41  #Ref     : 0
% 2.46/1.41  #Sup     : 77
% 2.46/1.41  #Fact    : 0
% 2.46/1.41  #Define  : 0
% 2.46/1.41  #Split   : 0
% 2.46/1.41  #Chain   : 0
% 2.46/1.41  #Close   : 0
% 2.46/1.41  
% 2.46/1.41  Ordering : KBO
% 2.46/1.41  
% 2.46/1.41  Simplification rules
% 2.46/1.41  ----------------------
% 2.46/1.41  #Subsume      : 1
% 2.46/1.41  #Demod        : 38
% 2.46/1.41  #Tautology    : 62
% 2.46/1.41  #SimpNegUnit  : 3
% 2.46/1.41  #BackRed      : 11
% 2.46/1.41  
% 2.46/1.41  #Partial instantiations: 0
% 2.46/1.41  #Strategies tried      : 1
% 2.46/1.41  
% 2.46/1.41  Timing (in seconds)
% 2.46/1.41  ----------------------
% 2.46/1.41  Preprocessing        : 0.35
% 2.46/1.41  Parsing              : 0.18
% 2.46/1.41  CNF conversion       : 0.02
% 2.46/1.41  Main loop            : 0.25
% 2.46/1.41  Inferencing          : 0.10
% 2.46/1.41  Reduction            : 0.08
% 2.46/1.41  Demodulation         : 0.06
% 2.46/1.41  BG Simplification    : 0.02
% 2.46/1.41  Subsumption          : 0.03
% 2.46/1.41  Abstraction          : 0.02
% 2.46/1.41  MUC search           : 0.00
% 2.46/1.41  Cooper               : 0.00
% 2.46/1.41  Total                : 0.63
% 2.46/1.41  Index Insertion      : 0.00
% 2.46/1.41  Index Deletion       : 0.00
% 2.46/1.41  Index Matching       : 0.00
% 2.46/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
