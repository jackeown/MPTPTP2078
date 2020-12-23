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
% DateTime   : Thu Dec  3 10:28:24 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   56 (  64 expanded)
%              Number of leaves         :   31 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :   63 (  88 expanded)
%              Number of equality atoms :   15 (  17 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_58,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    ! [A_12] : k3_xboole_0(A_12,A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_143,plain,(
    ! [A_76,B_77] : k5_xboole_0(A_76,k3_xboole_0(A_76,B_77)) = k4_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_152,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k4_xboole_0(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_143])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_62,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_36,plain,(
    ! [A_18,B_19] : r1_tarski(k3_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_355,plain,(
    ! [B_107,A_108] :
      ( B_107 = A_108
      | ~ r1_tarski(A_108,B_107)
      | ~ v1_zfmisc_1(B_107)
      | v1_xboole_0(B_107)
      | v1_xboole_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_483,plain,(
    ! [A_131,B_132] :
      ( k3_xboole_0(A_131,B_132) = A_131
      | ~ v1_zfmisc_1(A_131)
      | v1_xboole_0(A_131)
      | v1_xboole_0(k3_xboole_0(A_131,B_132)) ) ),
    inference(resolution,[status(thm)],[c_36,c_355])).

tff(c_60,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_486,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_483,c_60])).

tff(c_495,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = '#skF_4'
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_486])).

tff(c_496,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_495])).

tff(c_34,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_509,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_34])).

tff(c_520,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k4_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_509])).

tff(c_8,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,k4_xboole_0(A_6,B_7))
      | r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_575,plain,(
    ! [D_137] :
      ( r2_hidden(D_137,k4_xboole_0('#skF_4','#skF_4'))
      | r2_hidden(D_137,'#skF_5')
      | ~ r2_hidden(D_137,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_520,c_8])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_601,plain,(
    ! [D_138] :
      ( r2_hidden(D_138,'#skF_5')
      | ~ r2_hidden(D_138,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_575,c_10])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_615,plain,(
    ! [A_139] :
      ( r1_tarski(A_139,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_139,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_601,c_4])).

tff(c_627,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_615])).

tff(c_633,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_58,c_627])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:15:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.34  
% 2.60/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.34  %$ r2_hidden > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.60/1.34  
% 2.60/1.34  %Foreground sorts:
% 2.60/1.34  
% 2.60/1.34  
% 2.60/1.34  %Background operators:
% 2.60/1.34  
% 2.60/1.34  
% 2.60/1.34  %Foreground operators:
% 2.60/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.60/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.60/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.60/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.60/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.60/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.60/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.60/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.60/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.60/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.60/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.60/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.60/1.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.60/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.60/1.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.60/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.34  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.60/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.60/1.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.60/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.60/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.60/1.34  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.60/1.34  
% 2.60/1.35  tff(f_97, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tex_2)).
% 2.60/1.35  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.60/1.35  tff(f_44, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.60/1.35  tff(f_52, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.60/1.35  tff(f_54, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.60/1.35  tff(f_85, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.60/1.35  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.60/1.35  tff(c_58, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.60/1.35  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.60/1.35  tff(c_26, plain, (![A_12]: (k3_xboole_0(A_12, A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.60/1.35  tff(c_143, plain, (![A_76, B_77]: (k5_xboole_0(A_76, k3_xboole_0(A_76, B_77))=k4_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.60/1.35  tff(c_152, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k4_xboole_0(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_26, c_143])).
% 2.60/1.35  tff(c_64, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.60/1.35  tff(c_62, plain, (v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.60/1.35  tff(c_36, plain, (![A_18, B_19]: (r1_tarski(k3_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.60/1.35  tff(c_355, plain, (![B_107, A_108]: (B_107=A_108 | ~r1_tarski(A_108, B_107) | ~v1_zfmisc_1(B_107) | v1_xboole_0(B_107) | v1_xboole_0(A_108))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.60/1.35  tff(c_483, plain, (![A_131, B_132]: (k3_xboole_0(A_131, B_132)=A_131 | ~v1_zfmisc_1(A_131) | v1_xboole_0(A_131) | v1_xboole_0(k3_xboole_0(A_131, B_132)))), inference(resolution, [status(thm)], [c_36, c_355])).
% 2.60/1.35  tff(c_60, plain, (~v1_xboole_0(k3_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.60/1.35  tff(c_486, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4' | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_483, c_60])).
% 2.60/1.35  tff(c_495, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4' | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_486])).
% 2.60/1.35  tff(c_496, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_64, c_495])).
% 2.60/1.35  tff(c_34, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.60/1.35  tff(c_509, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_496, c_34])).
% 2.60/1.35  tff(c_520, plain, (k4_xboole_0('#skF_4', '#skF_5')=k4_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_509])).
% 2.60/1.35  tff(c_8, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, k4_xboole_0(A_6, B_7)) | r2_hidden(D_11, B_7) | ~r2_hidden(D_11, A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.60/1.35  tff(c_575, plain, (![D_137]: (r2_hidden(D_137, k4_xboole_0('#skF_4', '#skF_4')) | r2_hidden(D_137, '#skF_5') | ~r2_hidden(D_137, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_520, c_8])).
% 2.60/1.35  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.60/1.35  tff(c_601, plain, (![D_138]: (r2_hidden(D_138, '#skF_5') | ~r2_hidden(D_138, '#skF_4'))), inference(resolution, [status(thm)], [c_575, c_10])).
% 2.60/1.35  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.60/1.35  tff(c_615, plain, (![A_139]: (r1_tarski(A_139, '#skF_5') | ~r2_hidden('#skF_1'(A_139, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_601, c_4])).
% 2.60/1.35  tff(c_627, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_615])).
% 2.60/1.35  tff(c_633, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_58, c_627])).
% 2.60/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.35  
% 2.60/1.35  Inference rules
% 2.60/1.35  ----------------------
% 2.60/1.35  #Ref     : 0
% 2.60/1.35  #Sup     : 125
% 2.60/1.35  #Fact    : 0
% 2.60/1.35  #Define  : 0
% 2.60/1.35  #Split   : 1
% 2.60/1.35  #Chain   : 0
% 2.60/1.35  #Close   : 0
% 2.60/1.35  
% 2.60/1.35  Ordering : KBO
% 2.60/1.35  
% 2.60/1.35  Simplification rules
% 2.60/1.35  ----------------------
% 2.60/1.35  #Subsume      : 10
% 2.60/1.35  #Demod        : 49
% 2.60/1.35  #Tautology    : 76
% 2.60/1.35  #SimpNegUnit  : 3
% 2.60/1.35  #BackRed      : 1
% 2.60/1.35  
% 2.60/1.35  #Partial instantiations: 0
% 2.60/1.35  #Strategies tried      : 1
% 2.60/1.35  
% 2.60/1.35  Timing (in seconds)
% 2.60/1.35  ----------------------
% 2.60/1.36  Preprocessing        : 0.33
% 2.60/1.36  Parsing              : 0.17
% 2.60/1.36  CNF conversion       : 0.03
% 2.60/1.36  Main loop            : 0.27
% 2.60/1.36  Inferencing          : 0.10
% 2.60/1.36  Reduction            : 0.08
% 2.60/1.36  Demodulation         : 0.06
% 2.60/1.36  BG Simplification    : 0.02
% 2.60/1.36  Subsumption          : 0.05
% 2.60/1.36  Abstraction          : 0.02
% 2.60/1.36  MUC search           : 0.00
% 2.60/1.36  Cooper               : 0.00
% 2.60/1.36  Total                : 0.63
% 2.60/1.36  Index Insertion      : 0.00
% 2.60/1.36  Index Deletion       : 0.00
% 2.60/1.36  Index Matching       : 0.00
% 2.60/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
