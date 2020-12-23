%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:57 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   66 (  92 expanded)
%              Number of leaves         :   29 (  43 expanded)
%              Depth                    :   14
%              Number of atoms          :   61 (  91 expanded)
%              Number of equality atoms :   40 (  66 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_40,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_12,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_63,plain,(
    ! [B_35,A_36] : k2_xboole_0(B_35,A_36) = k2_xboole_0(A_36,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_79,plain,(
    ! [A_36] : k2_xboole_0(k1_xboole_0,A_36) = A_36 ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_12])).

tff(c_278,plain,(
    ! [A_58,B_59] : k2_xboole_0(A_58,k4_xboole_0(B_59,A_58)) = k2_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_285,plain,(
    ! [B_59] : k4_xboole_0(B_59,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_79])).

tff(c_333,plain,(
    ! [B_62] : k4_xboole_0(B_62,k1_xboole_0) = B_62 ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_285])).

tff(c_22,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_346,plain,(
    ! [B_62] : k5_xboole_0(k1_xboole_0,B_62) = k2_xboole_0(k1_xboole_0,B_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_22])).

tff(c_357,plain,(
    ! [B_62] : k5_xboole_0(k1_xboole_0,B_62) = B_62 ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_346])).

tff(c_16,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_166,plain,(
    ! [A_43,B_44] :
      ( k3_xboole_0(A_43,B_44) = A_43
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_173,plain,(
    ! [A_10] : k3_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_166])).

tff(c_380,plain,(
    ! [A_64,B_65] : k5_xboole_0(A_64,k3_xboole_0(A_64,B_65)) = k4_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_400,plain,(
    ! [A_10] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_380])).

tff(c_405,plain,(
    ! [A_10] : k4_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_400])).

tff(c_297,plain,(
    ! [A_60,B_61] : k4_xboole_0(k2_xboole_0(A_60,B_61),B_61) = k4_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_318,plain,(
    ! [A_36] : k4_xboole_0(k1_xboole_0,A_36) = k4_xboole_0(A_36,A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_297])).

tff(c_452,plain,(
    ! [A_36] : k4_xboole_0(A_36,A_36) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_405,c_318])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_174,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_166])).

tff(c_397,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_380])).

tff(c_548,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_397])).

tff(c_175,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(k1_tarski(A_45),B_46)
      | ~ r2_hidden(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_695,plain,(
    ! [A_83,B_84] :
      ( k3_xboole_0(k1_tarski(A_83),B_84) = k1_tarski(A_83)
      | ~ r2_hidden(A_83,B_84) ) ),
    inference(resolution,[status(thm)],[c_175,c_14])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_701,plain,(
    ! [A_83,B_84] :
      ( k5_xboole_0(k1_tarski(A_83),k1_tarski(A_83)) = k4_xboole_0(k1_tarski(A_83),B_84)
      | ~ r2_hidden(A_83,B_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_695,c_10])).

tff(c_1000,plain,(
    ! [A_95,B_96] :
      ( k4_xboole_0(k1_tarski(A_95),B_96) = k1_xboole_0
      | ~ r2_hidden(A_95,B_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_548,c_701])).

tff(c_18,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1025,plain,(
    ! [B_96,A_95] :
      ( k2_xboole_0(B_96,k1_tarski(A_95)) = k2_xboole_0(B_96,k1_xboole_0)
      | ~ r2_hidden(A_95,B_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1000,c_18])).

tff(c_1260,plain,(
    ! [B_101,A_102] :
      ( k2_xboole_0(B_101,k1_tarski(A_102)) = B_101
      | ~ r2_hidden(A_102,B_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1025])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_38,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_42,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_38])).

tff(c_1308,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1260,c_42])).

tff(c_1347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1308])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:54:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.40  
% 2.83/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.40  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.83/1.40  
% 2.83/1.40  %Foreground sorts:
% 2.83/1.40  
% 2.83/1.40  
% 2.83/1.40  %Background operators:
% 2.83/1.40  
% 2.83/1.40  
% 2.83/1.40  %Foreground operators:
% 2.83/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.83/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.83/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.83/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.83/1.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.83/1.40  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.83/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.83/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.83/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.83/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.83/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.83/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.83/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.40  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.83/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.83/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.83/1.40  
% 2.83/1.41  tff(f_68, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 2.83/1.41  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.83/1.41  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.83/1.41  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.83/1.41  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.83/1.41  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.83/1.41  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.83/1.41  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.83/1.41  tff(f_47, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.83/1.41  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.83/1.41  tff(f_61, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.83/1.41  tff(c_40, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.83/1.41  tff(c_12, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.83/1.41  tff(c_63, plain, (![B_35, A_36]: (k2_xboole_0(B_35, A_36)=k2_xboole_0(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.83/1.41  tff(c_79, plain, (![A_36]: (k2_xboole_0(k1_xboole_0, A_36)=A_36)), inference(superposition, [status(thm), theory('equality')], [c_63, c_12])).
% 2.83/1.41  tff(c_278, plain, (![A_58, B_59]: (k2_xboole_0(A_58, k4_xboole_0(B_59, A_58))=k2_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.83/1.41  tff(c_285, plain, (![B_59]: (k4_xboole_0(B_59, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_59))), inference(superposition, [status(thm), theory('equality')], [c_278, c_79])).
% 2.83/1.41  tff(c_333, plain, (![B_62]: (k4_xboole_0(B_62, k1_xboole_0)=B_62)), inference(demodulation, [status(thm), theory('equality')], [c_79, c_285])).
% 2.83/1.41  tff(c_22, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.83/1.41  tff(c_346, plain, (![B_62]: (k5_xboole_0(k1_xboole_0, B_62)=k2_xboole_0(k1_xboole_0, B_62))), inference(superposition, [status(thm), theory('equality')], [c_333, c_22])).
% 2.83/1.41  tff(c_357, plain, (![B_62]: (k5_xboole_0(k1_xboole_0, B_62)=B_62)), inference(demodulation, [status(thm), theory('equality')], [c_79, c_346])).
% 2.83/1.41  tff(c_16, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.83/1.41  tff(c_166, plain, (![A_43, B_44]: (k3_xboole_0(A_43, B_44)=A_43 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.83/1.41  tff(c_173, plain, (![A_10]: (k3_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_166])).
% 2.83/1.41  tff(c_380, plain, (![A_64, B_65]: (k5_xboole_0(A_64, k3_xboole_0(A_64, B_65))=k4_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.83/1.41  tff(c_400, plain, (![A_10]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_10))), inference(superposition, [status(thm), theory('equality')], [c_173, c_380])).
% 2.83/1.41  tff(c_405, plain, (![A_10]: (k4_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_357, c_400])).
% 2.83/1.41  tff(c_297, plain, (![A_60, B_61]: (k4_xboole_0(k2_xboole_0(A_60, B_61), B_61)=k4_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.83/1.41  tff(c_318, plain, (![A_36]: (k4_xboole_0(k1_xboole_0, A_36)=k4_xboole_0(A_36, A_36))), inference(superposition, [status(thm), theory('equality')], [c_79, c_297])).
% 2.83/1.41  tff(c_452, plain, (![A_36]: (k4_xboole_0(A_36, A_36)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_405, c_318])).
% 2.83/1.41  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.83/1.41  tff(c_174, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_166])).
% 2.83/1.41  tff(c_397, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_174, c_380])).
% 2.83/1.41  tff(c_548, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_452, c_397])).
% 2.83/1.41  tff(c_175, plain, (![A_45, B_46]: (r1_tarski(k1_tarski(A_45), B_46) | ~r2_hidden(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.83/1.41  tff(c_14, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.83/1.41  tff(c_695, plain, (![A_83, B_84]: (k3_xboole_0(k1_tarski(A_83), B_84)=k1_tarski(A_83) | ~r2_hidden(A_83, B_84))), inference(resolution, [status(thm)], [c_175, c_14])).
% 2.83/1.41  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.83/1.41  tff(c_701, plain, (![A_83, B_84]: (k5_xboole_0(k1_tarski(A_83), k1_tarski(A_83))=k4_xboole_0(k1_tarski(A_83), B_84) | ~r2_hidden(A_83, B_84))), inference(superposition, [status(thm), theory('equality')], [c_695, c_10])).
% 2.83/1.41  tff(c_1000, plain, (![A_95, B_96]: (k4_xboole_0(k1_tarski(A_95), B_96)=k1_xboole_0 | ~r2_hidden(A_95, B_96))), inference(demodulation, [status(thm), theory('equality')], [c_548, c_701])).
% 2.83/1.41  tff(c_18, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.83/1.41  tff(c_1025, plain, (![B_96, A_95]: (k2_xboole_0(B_96, k1_tarski(A_95))=k2_xboole_0(B_96, k1_xboole_0) | ~r2_hidden(A_95, B_96))), inference(superposition, [status(thm), theory('equality')], [c_1000, c_18])).
% 2.83/1.41  tff(c_1260, plain, (![B_101, A_102]: (k2_xboole_0(B_101, k1_tarski(A_102))=B_101 | ~r2_hidden(A_102, B_101))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1025])).
% 2.83/1.41  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.83/1.41  tff(c_38, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.83/1.41  tff(c_42, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_38])).
% 2.83/1.41  tff(c_1308, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1260, c_42])).
% 2.83/1.41  tff(c_1347, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_1308])).
% 2.83/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.41  
% 2.83/1.41  Inference rules
% 2.83/1.41  ----------------------
% 2.83/1.41  #Ref     : 0
% 2.83/1.41  #Sup     : 301
% 2.83/1.41  #Fact    : 0
% 2.83/1.41  #Define  : 0
% 2.83/1.41  #Split   : 0
% 2.83/1.41  #Chain   : 0
% 2.83/1.41  #Close   : 0
% 2.83/1.41  
% 2.83/1.41  Ordering : KBO
% 2.83/1.41  
% 2.83/1.41  Simplification rules
% 2.83/1.41  ----------------------
% 2.83/1.41  #Subsume      : 12
% 2.83/1.41  #Demod        : 250
% 2.83/1.41  #Tautology    : 239
% 2.83/1.41  #SimpNegUnit  : 0
% 2.83/1.41  #BackRed      : 1
% 2.83/1.41  
% 2.83/1.41  #Partial instantiations: 0
% 2.83/1.41  #Strategies tried      : 1
% 2.83/1.41  
% 2.83/1.41  Timing (in seconds)
% 2.83/1.41  ----------------------
% 2.83/1.42  Preprocessing        : 0.30
% 2.83/1.42  Parsing              : 0.17
% 2.83/1.42  CNF conversion       : 0.02
% 2.83/1.42  Main loop            : 0.34
% 2.83/1.42  Inferencing          : 0.12
% 2.83/1.42  Reduction            : 0.14
% 2.83/1.42  Demodulation         : 0.12
% 2.83/1.42  BG Simplification    : 0.02
% 2.83/1.42  Subsumption          : 0.05
% 2.83/1.42  Abstraction          : 0.02
% 2.83/1.42  MUC search           : 0.00
% 2.83/1.42  Cooper               : 0.00
% 2.83/1.42  Total                : 0.67
% 2.83/1.42  Index Insertion      : 0.00
% 2.83/1.42  Index Deletion       : 0.00
% 2.83/1.42  Index Matching       : 0.00
% 2.83/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
