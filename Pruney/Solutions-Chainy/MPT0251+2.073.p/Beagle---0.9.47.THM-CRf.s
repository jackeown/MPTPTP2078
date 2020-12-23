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
% DateTime   : Thu Dec  3 09:50:56 EST 2020

% Result     : Theorem 10.59s
% Output     : CNFRefutation 10.59s
% Verified   : 
% Statistics : Number of formulae       :   62 (  64 expanded)
%              Number of leaves         :   35 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :   75 (  81 expanded)
%              Number of equality atoms :   24 (  26 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_68,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_78,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_76,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_66,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_40,plain,(
    ! [A_23] : k2_xboole_0(A_23,k1_xboole_0) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_48,plain,(
    ! [A_29] : k2_tarski(A_29,A_29) = k1_tarski(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_795,plain,(
    ! [A_138,B_139,C_140] :
      ( r1_tarski(k2_tarski(A_138,B_139),C_140)
      | ~ r2_hidden(B_139,C_140)
      | ~ r2_hidden(A_138,C_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_815,plain,(
    ! [A_29,C_140] :
      ( r1_tarski(k1_tarski(A_29),C_140)
      | ~ r2_hidden(A_29,C_140)
      | ~ r2_hidden(A_29,C_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_795])).

tff(c_1086,plain,(
    ! [A_162,B_163,C_164] :
      ( r2_hidden('#skF_2'(A_162,B_163,C_164),A_162)
      | r2_hidden('#skF_3'(A_162,B_163,C_164),C_164)
      | k4_xboole_0(A_162,B_163) = C_164 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_5796,plain,(
    ! [A_429,B_430,C_431,B_432] :
      ( r2_hidden('#skF_2'(A_429,B_430,C_431),B_432)
      | ~ r1_tarski(A_429,B_432)
      | r2_hidden('#skF_3'(A_429,B_430,C_431),C_431)
      | k4_xboole_0(A_429,B_430) = C_431 ) ),
    inference(resolution,[status(thm)],[c_1086,c_4])).

tff(c_24,plain,(
    ! [A_8,B_9,C_10] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9,C_10),B_9)
      | r2_hidden('#skF_3'(A_8,B_9,C_10),C_10)
      | k4_xboole_0(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_22895,plain,(
    ! [A_860,B_861,C_862] :
      ( ~ r1_tarski(A_860,B_861)
      | r2_hidden('#skF_3'(A_860,B_861,C_862),C_862)
      | k4_xboole_0(A_860,B_861) = C_862 ) ),
    inference(resolution,[status(thm)],[c_5796,c_24])).

tff(c_46,plain,(
    ! [A_28] : r1_xboole_0(A_28,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_36,plain,(
    ! [B_20] : r1_tarski(B_20,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_174,plain,(
    ! [A_51,B_52] :
      ( k3_xboole_0(A_51,B_52) = A_51
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_178,plain,(
    ! [B_20] : k3_xboole_0(B_20,B_20) = B_20 ),
    inference(resolution,[status(thm)],[c_36,c_174])).

tff(c_353,plain,(
    ! [A_92,B_93,C_94] :
      ( ~ r1_xboole_0(A_92,B_93)
      | ~ r2_hidden(C_94,k3_xboole_0(A_92,B_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_362,plain,(
    ! [B_95,C_96] :
      ( ~ r1_xboole_0(B_95,B_95)
      | ~ r2_hidden(C_96,B_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_353])).

tff(c_366,plain,(
    ! [C_96] : ~ r2_hidden(C_96,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_46,c_362])).

tff(c_22974,plain,(
    ! [A_863,B_864] :
      ( ~ r1_tarski(A_863,B_864)
      | k4_xboole_0(A_863,B_864) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22895,c_366])).

tff(c_23030,plain,(
    ! [A_865,C_866] :
      ( k4_xboole_0(k1_tarski(A_865),C_866) = k1_xboole_0
      | ~ r2_hidden(A_865,C_866) ) ),
    inference(resolution,[status(thm)],[c_815,c_22974])).

tff(c_44,plain,(
    ! [A_26,B_27] : k2_xboole_0(A_26,k4_xboole_0(B_27,A_26)) = k2_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_23494,plain,(
    ! [C_866,A_865] :
      ( k2_xboole_0(C_866,k1_tarski(A_865)) = k2_xboole_0(C_866,k1_xboole_0)
      | ~ r2_hidden(A_865,C_866) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23030,c_44])).

tff(c_23685,plain,(
    ! [C_867,A_868] :
      ( k2_xboole_0(C_867,k1_tarski(A_868)) = C_867
      | ~ r2_hidden(A_868,C_867) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_23494])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_64,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_68,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_64])).

tff(c_23725,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_23685,c_68])).

tff(c_23772,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_23725])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:56:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.59/4.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.59/4.26  
% 10.59/4.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.59/4.26  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.59/4.26  
% 10.59/4.26  %Foreground sorts:
% 10.59/4.26  
% 10.59/4.26  
% 10.59/4.26  %Background operators:
% 10.59/4.26  
% 10.59/4.26  
% 10.59/4.26  %Foreground operators:
% 10.59/4.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.59/4.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.59/4.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.59/4.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.59/4.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.59/4.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.59/4.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.59/4.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.59/4.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.59/4.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.59/4.26  tff('#skF_5', type, '#skF_5': $i).
% 10.59/4.26  tff('#skF_6', type, '#skF_6': $i).
% 10.59/4.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.59/4.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.59/4.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.59/4.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.59/4.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 10.59/4.26  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.59/4.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.59/4.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.59/4.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.59/4.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.59/4.26  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 10.59/4.26  
% 10.59/4.27  tff(f_97, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 10.59/4.27  tff(f_68, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 10.59/4.27  tff(f_78, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 10.59/4.27  tff(f_92, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 10.59/4.27  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 10.59/4.27  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 10.59/4.27  tff(f_76, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 10.59/4.27  tff(f_64, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.59/4.27  tff(f_72, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 10.59/4.27  tff(f_58, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 10.59/4.27  tff(f_74, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 10.59/4.27  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 10.59/4.27  tff(c_66, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.59/4.27  tff(c_40, plain, (![A_23]: (k2_xboole_0(A_23, k1_xboole_0)=A_23)), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.59/4.27  tff(c_48, plain, (![A_29]: (k2_tarski(A_29, A_29)=k1_tarski(A_29))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.59/4.27  tff(c_795, plain, (![A_138, B_139, C_140]: (r1_tarski(k2_tarski(A_138, B_139), C_140) | ~r2_hidden(B_139, C_140) | ~r2_hidden(A_138, C_140))), inference(cnfTransformation, [status(thm)], [f_92])).
% 10.59/4.27  tff(c_815, plain, (![A_29, C_140]: (r1_tarski(k1_tarski(A_29), C_140) | ~r2_hidden(A_29, C_140) | ~r2_hidden(A_29, C_140))), inference(superposition, [status(thm), theory('equality')], [c_48, c_795])).
% 10.59/4.27  tff(c_1086, plain, (![A_162, B_163, C_164]: (r2_hidden('#skF_2'(A_162, B_163, C_164), A_162) | r2_hidden('#skF_3'(A_162, B_163, C_164), C_164) | k4_xboole_0(A_162, B_163)=C_164)), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.59/4.27  tff(c_4, plain, (![C_7, B_4, A_3]: (r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.59/4.27  tff(c_5796, plain, (![A_429, B_430, C_431, B_432]: (r2_hidden('#skF_2'(A_429, B_430, C_431), B_432) | ~r1_tarski(A_429, B_432) | r2_hidden('#skF_3'(A_429, B_430, C_431), C_431) | k4_xboole_0(A_429, B_430)=C_431)), inference(resolution, [status(thm)], [c_1086, c_4])).
% 10.59/4.27  tff(c_24, plain, (![A_8, B_9, C_10]: (~r2_hidden('#skF_2'(A_8, B_9, C_10), B_9) | r2_hidden('#skF_3'(A_8, B_9, C_10), C_10) | k4_xboole_0(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.59/4.27  tff(c_22895, plain, (![A_860, B_861, C_862]: (~r1_tarski(A_860, B_861) | r2_hidden('#skF_3'(A_860, B_861, C_862), C_862) | k4_xboole_0(A_860, B_861)=C_862)), inference(resolution, [status(thm)], [c_5796, c_24])).
% 10.59/4.27  tff(c_46, plain, (![A_28]: (r1_xboole_0(A_28, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.59/4.27  tff(c_36, plain, (![B_20]: (r1_tarski(B_20, B_20))), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.59/4.27  tff(c_174, plain, (![A_51, B_52]: (k3_xboole_0(A_51, B_52)=A_51 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.59/4.27  tff(c_178, plain, (![B_20]: (k3_xboole_0(B_20, B_20)=B_20)), inference(resolution, [status(thm)], [c_36, c_174])).
% 10.59/4.27  tff(c_353, plain, (![A_92, B_93, C_94]: (~r1_xboole_0(A_92, B_93) | ~r2_hidden(C_94, k3_xboole_0(A_92, B_93)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.59/4.27  tff(c_362, plain, (![B_95, C_96]: (~r1_xboole_0(B_95, B_95) | ~r2_hidden(C_96, B_95))), inference(superposition, [status(thm), theory('equality')], [c_178, c_353])).
% 10.59/4.27  tff(c_366, plain, (![C_96]: (~r2_hidden(C_96, k1_xboole_0))), inference(resolution, [status(thm)], [c_46, c_362])).
% 10.59/4.27  tff(c_22974, plain, (![A_863, B_864]: (~r1_tarski(A_863, B_864) | k4_xboole_0(A_863, B_864)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22895, c_366])).
% 10.59/4.27  tff(c_23030, plain, (![A_865, C_866]: (k4_xboole_0(k1_tarski(A_865), C_866)=k1_xboole_0 | ~r2_hidden(A_865, C_866))), inference(resolution, [status(thm)], [c_815, c_22974])).
% 10.59/4.27  tff(c_44, plain, (![A_26, B_27]: (k2_xboole_0(A_26, k4_xboole_0(B_27, A_26))=k2_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.59/4.27  tff(c_23494, plain, (![C_866, A_865]: (k2_xboole_0(C_866, k1_tarski(A_865))=k2_xboole_0(C_866, k1_xboole_0) | ~r2_hidden(A_865, C_866))), inference(superposition, [status(thm), theory('equality')], [c_23030, c_44])).
% 10.59/4.27  tff(c_23685, plain, (![C_867, A_868]: (k2_xboole_0(C_867, k1_tarski(A_868))=C_867 | ~r2_hidden(A_868, C_867))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_23494])).
% 10.59/4.27  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.59/4.27  tff(c_64, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.59/4.27  tff(c_68, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_64])).
% 10.59/4.27  tff(c_23725, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_23685, c_68])).
% 10.59/4.27  tff(c_23772, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_23725])).
% 10.59/4.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.59/4.27  
% 10.59/4.27  Inference rules
% 10.59/4.27  ----------------------
% 10.59/4.27  #Ref     : 0
% 10.59/4.27  #Sup     : 6196
% 10.59/4.27  #Fact    : 0
% 10.59/4.27  #Define  : 0
% 10.59/4.27  #Split   : 6
% 10.59/4.27  #Chain   : 0
% 10.59/4.27  #Close   : 0
% 10.59/4.27  
% 10.59/4.27  Ordering : KBO
% 10.59/4.27  
% 10.59/4.27  Simplification rules
% 10.59/4.27  ----------------------
% 10.59/4.27  #Subsume      : 3349
% 10.59/4.27  #Demod        : 2845
% 10.59/4.27  #Tautology    : 1289
% 10.59/4.27  #SimpNegUnit  : 125
% 10.59/4.27  #BackRed      : 5
% 10.59/4.27  
% 10.59/4.27  #Partial instantiations: 0
% 10.59/4.27  #Strategies tried      : 1
% 10.59/4.27  
% 10.59/4.27  Timing (in seconds)
% 10.59/4.27  ----------------------
% 10.59/4.27  Preprocessing        : 0.41
% 10.59/4.27  Parsing              : 0.19
% 10.59/4.27  CNF conversion       : 0.03
% 10.59/4.27  Main loop            : 3.05
% 10.59/4.27  Inferencing          : 0.76
% 10.59/4.27  Reduction            : 0.96
% 10.59/4.27  Demodulation         : 0.73
% 10.59/4.27  BG Simplification    : 0.07
% 10.59/4.27  Subsumption          : 1.09
% 10.59/4.27  Abstraction          : 0.12
% 10.59/4.27  MUC search           : 0.00
% 10.59/4.27  Cooper               : 0.00
% 10.59/4.27  Total                : 3.50
% 10.59/4.27  Index Insertion      : 0.00
% 10.59/4.27  Index Deletion       : 0.00
% 10.59/4.27  Index Matching       : 0.00
% 10.59/4.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
