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
% DateTime   : Thu Dec  3 09:56:04 EST 2020

% Result     : Theorem 3.41s
% Output     : CNFRefutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :   64 (  90 expanded)
%              Number of leaves         :   37 (  48 expanded)
%              Depth                    :    7
%              Number of atoms          :   63 ( 109 expanded)
%              Number of equality atoms :   19 (  45 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_42,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_105,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_116,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_79,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_109,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_60,plain,(
    ! [A_64] : k1_subset_1(A_64) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_72,plain,
    ( r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_3'))
    | k1_subset_1('#skF_2') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_74,plain,
    ( r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_3'))
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_72])).

tff(c_129,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_28,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_132,plain,(
    r1_xboole_0('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_129,c_28])).

tff(c_326,plain,(
    ! [B_92,A_93] :
      ( ~ r1_xboole_0(B_92,A_93)
      | ~ r1_tarski(B_92,A_93)
      | v1_xboole_0(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_329,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_132,c_326])).

tff(c_332,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_329])).

tff(c_333,plain,(
    ! [A_94,B_95] :
      ( r2_hidden('#skF_1'(A_94,B_95),A_94)
      | r1_tarski(A_94,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_34,plain,(
    ! [B_26,A_25] :
      ( ~ v1_xboole_0(B_26)
      | ~ r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_338,plain,(
    ! [A_96,B_97] :
      ( ~ v1_xboole_0(A_96)
      | r1_tarski(A_96,B_97) ) ),
    inference(resolution,[status(thm)],[c_333,c_34])).

tff(c_66,plain,
    ( k1_subset_1('#skF_2') != '#skF_3'
    | ~ r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_73,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_66])).

tff(c_282,plain,(
    ~ r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_73])).

tff(c_347,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_338,c_282])).

tff(c_353,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_347])).

tff(c_355,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_354,plain,(
    r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_64,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_996,plain,(
    ! [A_148,B_149] :
      ( k4_xboole_0(A_148,B_149) = k3_subset_1(A_148,B_149)
      | ~ m1_subset_1(B_149,k1_zfmisc_1(A_148)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1000,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k3_subset_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_996])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( k1_xboole_0 = A_14
      | ~ r1_tarski(A_14,k4_xboole_0(B_15,A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1004,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1000,c_20])).

tff(c_1008,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_1004])).

tff(c_1010,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_355,c_1008])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:54:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.41/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.64  
% 3.41/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.64  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.41/1.64  
% 3.41/1.64  %Foreground sorts:
% 3.41/1.64  
% 3.41/1.64  
% 3.41/1.64  %Background operators:
% 3.41/1.64  
% 3.41/1.64  
% 3.41/1.64  %Foreground operators:
% 3.41/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.41/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.41/1.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.41/1.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.41/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.41/1.64  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.41/1.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.41/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.41/1.64  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.41/1.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.41/1.64  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.41/1.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.41/1.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.41/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.41/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.41/1.64  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.41/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.41/1.64  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.41/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.41/1.64  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.41/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.41/1.64  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.41/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.41/1.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.41/1.64  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.41/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.41/1.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.41/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.41/1.64  
% 3.41/1.66  tff(f_42, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.41/1.66  tff(f_105, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 3.41/1.66  tff(f_116, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 3.41/1.66  tff(f_66, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.41/1.66  tff(f_74, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.41/1.66  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.41/1.66  tff(f_79, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_boole)).
% 3.41/1.66  tff(f_109, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.41/1.66  tff(f_48, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 3.41/1.66  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.41/1.66  tff(c_60, plain, (![A_64]: (k1_subset_1(A_64)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.41/1.66  tff(c_72, plain, (r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_3')) | k1_subset_1('#skF_2')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.41/1.66  tff(c_74, plain, (r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_3')) | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_72])).
% 3.41/1.66  tff(c_129, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_74])).
% 3.41/1.66  tff(c_28, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.41/1.66  tff(c_132, plain, (r1_xboole_0('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_129, c_28])).
% 3.41/1.66  tff(c_326, plain, (![B_92, A_93]: (~r1_xboole_0(B_92, A_93) | ~r1_tarski(B_92, A_93) | v1_xboole_0(B_92))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.41/1.66  tff(c_329, plain, (~r1_tarski('#skF_3', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_132, c_326])).
% 3.41/1.66  tff(c_332, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_329])).
% 3.41/1.66  tff(c_333, plain, (![A_94, B_95]: (r2_hidden('#skF_1'(A_94, B_95), A_94) | r1_tarski(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.41/1.66  tff(c_34, plain, (![B_26, A_25]: (~v1_xboole_0(B_26) | ~r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.41/1.66  tff(c_338, plain, (![A_96, B_97]: (~v1_xboole_0(A_96) | r1_tarski(A_96, B_97))), inference(resolution, [status(thm)], [c_333, c_34])).
% 3.41/1.66  tff(c_66, plain, (k1_subset_1('#skF_2')!='#skF_3' | ~r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.41/1.66  tff(c_73, plain, (k1_xboole_0!='#skF_3' | ~r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_66])).
% 3.41/1.66  tff(c_282, plain, (~r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_73])).
% 3.41/1.66  tff(c_347, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_338, c_282])).
% 3.41/1.66  tff(c_353, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_332, c_347])).
% 3.41/1.66  tff(c_355, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_74])).
% 3.41/1.66  tff(c_354, plain, (r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_74])).
% 3.41/1.66  tff(c_64, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.41/1.66  tff(c_996, plain, (![A_148, B_149]: (k4_xboole_0(A_148, B_149)=k3_subset_1(A_148, B_149) | ~m1_subset_1(B_149, k1_zfmisc_1(A_148)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.41/1.66  tff(c_1000, plain, (k4_xboole_0('#skF_2', '#skF_3')=k3_subset_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_996])).
% 3.41/1.66  tff(c_20, plain, (![A_14, B_15]: (k1_xboole_0=A_14 | ~r1_tarski(A_14, k4_xboole_0(B_15, A_14)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.41/1.66  tff(c_1004, plain, (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1000, c_20])).
% 3.41/1.66  tff(c_1008, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_354, c_1004])).
% 3.41/1.66  tff(c_1010, plain, $false, inference(negUnitSimplification, [status(thm)], [c_355, c_1008])).
% 3.41/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.66  
% 3.41/1.66  Inference rules
% 3.41/1.66  ----------------------
% 3.41/1.66  #Ref     : 0
% 3.41/1.66  #Sup     : 213
% 3.41/1.66  #Fact    : 0
% 3.41/1.66  #Define  : 0
% 3.41/1.66  #Split   : 2
% 3.41/1.66  #Chain   : 0
% 3.41/1.66  #Close   : 0
% 3.41/1.66  
% 3.41/1.66  Ordering : KBO
% 3.41/1.66  
% 3.41/1.66  Simplification rules
% 3.41/1.66  ----------------------
% 3.41/1.66  #Subsume      : 8
% 3.41/1.66  #Demod        : 85
% 3.41/1.66  #Tautology    : 155
% 3.41/1.66  #SimpNegUnit  : 1
% 3.41/1.66  #BackRed      : 4
% 3.41/1.66  
% 3.41/1.66  #Partial instantiations: 0
% 3.41/1.66  #Strategies tried      : 1
% 3.41/1.66  
% 3.41/1.66  Timing (in seconds)
% 3.41/1.66  ----------------------
% 3.41/1.66  Preprocessing        : 0.44
% 3.41/1.66  Parsing              : 0.24
% 3.41/1.66  CNF conversion       : 0.03
% 3.41/1.66  Main loop            : 0.38
% 3.41/1.66  Inferencing          : 0.14
% 3.41/1.66  Reduction            : 0.14
% 3.41/1.66  Demodulation         : 0.10
% 3.41/1.66  BG Simplification    : 0.02
% 3.41/1.66  Subsumption          : 0.06
% 3.41/1.66  Abstraction          : 0.02
% 3.41/1.66  MUC search           : 0.00
% 3.41/1.66  Cooper               : 0.00
% 3.41/1.66  Total                : 0.86
% 3.41/1.66  Index Insertion      : 0.00
% 3.41/1.66  Index Deletion       : 0.00
% 3.41/1.66  Index Matching       : 0.00
% 3.41/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
