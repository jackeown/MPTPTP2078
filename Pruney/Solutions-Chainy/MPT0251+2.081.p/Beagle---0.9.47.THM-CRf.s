%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:57 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   62 (  69 expanded)
%              Number of leaves         :   31 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :   59 (  69 expanded)
%              Number of equality atoms :   32 (  39 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_51,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_44,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_14,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [A_16] : r1_xboole_0(A_16,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_67,plain,(
    ! [B_37,A_38] :
      ( r1_xboole_0(B_37,A_38)
      | ~ r1_xboole_0(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    ! [A_16] : r1_xboole_0(k1_xboole_0,A_16) ),
    inference(resolution,[status(thm)],[c_22,c_67])).

tff(c_191,plain,(
    ! [A_50,B_51] :
      ( k4_xboole_0(A_50,B_51) = A_50
      | ~ r1_xboole_0(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_198,plain,(
    ! [A_16] : k4_xboole_0(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_70,c_191])).

tff(c_76,plain,(
    ! [B_40,A_41] : k2_xboole_0(B_40,A_41) = k2_xboole_0(A_41,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_92,plain,(
    ! [A_41] : k2_xboole_0(k1_xboole_0,A_41) = A_41 ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_14])).

tff(c_307,plain,(
    ! [A_66,B_67] : k4_xboole_0(k2_xboole_0(A_66,B_67),B_67) = k4_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_333,plain,(
    ! [A_41] : k4_xboole_0(k1_xboole_0,A_41) = k4_xboole_0(A_41,A_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_307])).

tff(c_348,plain,(
    ! [A_41] : k4_xboole_0(A_41,A_41) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_333])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_173,plain,(
    ! [A_47,B_48] :
      ( k3_xboole_0(A_47,B_48) = A_47
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_181,plain,(
    ! [B_6] : k3_xboole_0(B_6,B_6) = B_6 ),
    inference(resolution,[status(thm)],[c_10,c_173])).

tff(c_432,plain,(
    ! [A_73,B_74] : k5_xboole_0(A_73,k3_xboole_0(A_73,B_74)) = k4_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_441,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k4_xboole_0(B_6,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_432])).

tff(c_444,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_441])).

tff(c_38,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(k1_tarski(A_29),B_30)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_828,plain,(
    ! [A_95,B_96] :
      ( k3_xboole_0(k1_tarski(A_95),B_96) = k1_tarski(A_95)
      | ~ r2_hidden(A_95,B_96) ) ),
    inference(resolution,[status(thm)],[c_38,c_173])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_834,plain,(
    ! [A_95,B_96] :
      ( k5_xboole_0(k1_tarski(A_95),k1_tarski(A_95)) = k4_xboole_0(k1_tarski(A_95),B_96)
      | ~ r2_hidden(A_95,B_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_828,c_12])).

tff(c_1050,plain,(
    ! [A_103,B_104] :
      ( k4_xboole_0(k1_tarski(A_103),B_104) = k1_xboole_0
      | ~ r2_hidden(A_103,B_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_834])).

tff(c_18,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1083,plain,(
    ! [B_104,A_103] :
      ( k2_xboole_0(B_104,k1_tarski(A_103)) = k2_xboole_0(B_104,k1_xboole_0)
      | ~ r2_hidden(A_103,B_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1050,c_18])).

tff(c_1187,plain,(
    ! [B_110,A_111] :
      ( k2_xboole_0(B_110,k1_tarski(A_111)) = B_110
      | ~ r2_hidden(A_111,B_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1083])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_42,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_46,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_42])).

tff(c_1228,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1187,c_46])).

tff(c_1261,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1228])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:52:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.53  
% 2.92/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.53  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.92/1.53  
% 2.92/1.53  %Foreground sorts:
% 2.92/1.53  
% 2.92/1.53  
% 2.92/1.53  %Background operators:
% 2.92/1.53  
% 2.92/1.53  
% 2.92/1.53  %Foreground operators:
% 2.92/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.92/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.92/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.92/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.92/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.92/1.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.92/1.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.92/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.92/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.92/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.92/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.92/1.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.92/1.53  tff('#skF_2', type, '#skF_2': $i).
% 2.92/1.53  tff('#skF_1', type, '#skF_1': $i).
% 2.92/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.92/1.53  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.92/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.92/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.92/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.92/1.53  
% 2.92/1.54  tff(f_74, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 2.92/1.54  tff(f_41, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.92/1.54  tff(f_51, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.92/1.54  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.92/1.54  tff(f_55, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.92/1.54  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.92/1.54  tff(f_49, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.92/1.54  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.92/1.54  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.92/1.54  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.92/1.54  tff(f_67, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.92/1.54  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.92/1.54  tff(c_44, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.92/1.54  tff(c_14, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.92/1.54  tff(c_22, plain, (![A_16]: (r1_xboole_0(A_16, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.92/1.54  tff(c_67, plain, (![B_37, A_38]: (r1_xboole_0(B_37, A_38) | ~r1_xboole_0(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.92/1.54  tff(c_70, plain, (![A_16]: (r1_xboole_0(k1_xboole_0, A_16))), inference(resolution, [status(thm)], [c_22, c_67])).
% 2.92/1.54  tff(c_191, plain, (![A_50, B_51]: (k4_xboole_0(A_50, B_51)=A_50 | ~r1_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.92/1.54  tff(c_198, plain, (![A_16]: (k4_xboole_0(k1_xboole_0, A_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_70, c_191])).
% 2.92/1.54  tff(c_76, plain, (![B_40, A_41]: (k2_xboole_0(B_40, A_41)=k2_xboole_0(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.92/1.54  tff(c_92, plain, (![A_41]: (k2_xboole_0(k1_xboole_0, A_41)=A_41)), inference(superposition, [status(thm), theory('equality')], [c_76, c_14])).
% 2.92/1.54  tff(c_307, plain, (![A_66, B_67]: (k4_xboole_0(k2_xboole_0(A_66, B_67), B_67)=k4_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.92/1.54  tff(c_333, plain, (![A_41]: (k4_xboole_0(k1_xboole_0, A_41)=k4_xboole_0(A_41, A_41))), inference(superposition, [status(thm), theory('equality')], [c_92, c_307])).
% 2.92/1.54  tff(c_348, plain, (![A_41]: (k4_xboole_0(A_41, A_41)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_198, c_333])).
% 2.92/1.54  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.92/1.54  tff(c_173, plain, (![A_47, B_48]: (k3_xboole_0(A_47, B_48)=A_47 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.92/1.54  tff(c_181, plain, (![B_6]: (k3_xboole_0(B_6, B_6)=B_6)), inference(resolution, [status(thm)], [c_10, c_173])).
% 2.92/1.54  tff(c_432, plain, (![A_73, B_74]: (k5_xboole_0(A_73, k3_xboole_0(A_73, B_74))=k4_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.92/1.54  tff(c_441, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k4_xboole_0(B_6, B_6))), inference(superposition, [status(thm), theory('equality')], [c_181, c_432])).
% 2.92/1.54  tff(c_444, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_348, c_441])).
% 2.92/1.54  tff(c_38, plain, (![A_29, B_30]: (r1_tarski(k1_tarski(A_29), B_30) | ~r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.92/1.54  tff(c_828, plain, (![A_95, B_96]: (k3_xboole_0(k1_tarski(A_95), B_96)=k1_tarski(A_95) | ~r2_hidden(A_95, B_96))), inference(resolution, [status(thm)], [c_38, c_173])).
% 2.92/1.54  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.92/1.54  tff(c_834, plain, (![A_95, B_96]: (k5_xboole_0(k1_tarski(A_95), k1_tarski(A_95))=k4_xboole_0(k1_tarski(A_95), B_96) | ~r2_hidden(A_95, B_96))), inference(superposition, [status(thm), theory('equality')], [c_828, c_12])).
% 2.92/1.54  tff(c_1050, plain, (![A_103, B_104]: (k4_xboole_0(k1_tarski(A_103), B_104)=k1_xboole_0 | ~r2_hidden(A_103, B_104))), inference(demodulation, [status(thm), theory('equality')], [c_444, c_834])).
% 2.92/1.54  tff(c_18, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.92/1.54  tff(c_1083, plain, (![B_104, A_103]: (k2_xboole_0(B_104, k1_tarski(A_103))=k2_xboole_0(B_104, k1_xboole_0) | ~r2_hidden(A_103, B_104))), inference(superposition, [status(thm), theory('equality')], [c_1050, c_18])).
% 2.92/1.54  tff(c_1187, plain, (![B_110, A_111]: (k2_xboole_0(B_110, k1_tarski(A_111))=B_110 | ~r2_hidden(A_111, B_110))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1083])).
% 2.92/1.54  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.92/1.54  tff(c_42, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.92/1.54  tff(c_46, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_42])).
% 2.92/1.54  tff(c_1228, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1187, c_46])).
% 2.92/1.54  tff(c_1261, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_1228])).
% 2.92/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.54  
% 2.92/1.54  Inference rules
% 2.92/1.54  ----------------------
% 2.92/1.54  #Ref     : 0
% 2.92/1.54  #Sup     : 287
% 2.92/1.54  #Fact    : 0
% 2.92/1.54  #Define  : 0
% 2.92/1.54  #Split   : 0
% 2.92/1.54  #Chain   : 0
% 2.92/1.54  #Close   : 0
% 2.92/1.54  
% 2.92/1.54  Ordering : KBO
% 2.92/1.54  
% 2.92/1.54  Simplification rules
% 2.92/1.54  ----------------------
% 2.92/1.54  #Subsume      : 13
% 2.92/1.54  #Demod        : 229
% 2.92/1.54  #Tautology    : 218
% 2.92/1.54  #SimpNegUnit  : 0
% 2.92/1.54  #BackRed      : 1
% 2.92/1.54  
% 2.92/1.54  #Partial instantiations: 0
% 2.92/1.54  #Strategies tried      : 1
% 2.92/1.54  
% 2.92/1.54  Timing (in seconds)
% 2.92/1.54  ----------------------
% 2.92/1.54  Preprocessing        : 0.32
% 2.92/1.55  Parsing              : 0.15
% 2.92/1.55  CNF conversion       : 0.02
% 2.92/1.55  Main loop            : 0.40
% 2.92/1.55  Inferencing          : 0.15
% 2.92/1.55  Reduction            : 0.15
% 2.92/1.55  Demodulation         : 0.12
% 2.92/1.55  BG Simplification    : 0.02
% 2.92/1.55  Subsumption          : 0.06
% 2.92/1.55  Abstraction          : 0.03
% 2.92/1.55  MUC search           : 0.00
% 2.92/1.55  Cooper               : 0.00
% 2.92/1.55  Total                : 0.76
% 2.92/1.55  Index Insertion      : 0.00
% 2.92/1.55  Index Deletion       : 0.00
% 2.92/1.55  Index Matching       : 0.00
% 2.92/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
