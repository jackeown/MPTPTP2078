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
% DateTime   : Thu Dec  3 09:54:33 EST 2020

% Result     : Theorem 5.93s
% Output     : CNFRefutation 5.93s
% Verified   : 
% Statistics : Number of formulae       :   55 (  68 expanded)
%              Number of leaves         :   29 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :   52 (  66 expanded)
%              Number of equality atoms :   27 (  40 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_64,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_22,plain,(
    ! [A_9] : k2_xboole_0(A_9,A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_119,plain,(
    ! [A_50,B_51] : k4_xboole_0(A_50,k2_xboole_0(A_50,B_51)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_132,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_119])).

tff(c_507,plain,(
    ! [A_90,B_91] : k5_xboole_0(A_90,k4_xboole_0(B_91,A_90)) = k2_xboole_0(A_90,B_91) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_525,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = k2_xboole_0(A_9,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_507])).

tff(c_533,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_525])).

tff(c_50,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(k1_tarski(A_32),B_33)
      | ~ r2_hidden(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_32,plain,(
    ! [A_14,C_16,B_15] :
      ( r1_tarski(k4_xboole_0(A_14,C_16),B_15)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_40,plain,(
    ! [A_24,C_26,B_25] :
      ( r1_xboole_0(A_24,k4_xboole_0(C_26,B_25))
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_534,plain,(
    ! [A_92,B_93] :
      ( k4_xboole_0(k2_xboole_0(A_92,B_93),B_93) = A_92
      | ~ r1_xboole_0(A_92,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_588,plain,(
    ! [A_9] :
      ( k4_xboole_0(A_9,A_9) = A_9
      | ~ r1_xboole_0(A_9,A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_534])).

tff(c_635,plain,(
    ! [A_96] :
      ( k1_xboole_0 = A_96
      | ~ r1_xboole_0(A_96,A_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_588])).

tff(c_5910,plain,(
    ! [C_292,B_293] :
      ( k4_xboole_0(C_292,B_293) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(C_292,B_293),B_293) ) ),
    inference(resolution,[status(thm)],[c_40,c_635])).

tff(c_5981,plain,(
    ! [A_294,B_295] :
      ( k4_xboole_0(A_294,B_295) = k1_xboole_0
      | ~ r1_tarski(A_294,B_295) ) ),
    inference(resolution,[status(thm)],[c_32,c_5910])).

tff(c_6061,plain,(
    ! [A_296,B_297] :
      ( k4_xboole_0(k1_tarski(A_296),B_297) = k1_xboole_0
      | ~ r2_hidden(A_296,B_297) ) ),
    inference(resolution,[status(thm)],[c_50,c_5981])).

tff(c_44,plain,(
    ! [A_29,B_30] : k5_xboole_0(A_29,k4_xboole_0(B_30,A_29)) = k2_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6138,plain,(
    ! [B_297,A_296] :
      ( k2_xboole_0(B_297,k1_tarski(A_296)) = k5_xboole_0(B_297,k1_xboole_0)
      | ~ r2_hidden(A_296,B_297) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6061,c_44])).

tff(c_6243,plain,(
    ! [B_298,A_299] :
      ( k2_xboole_0(B_298,k1_tarski(A_299)) = B_298
      | ~ r2_hidden(A_299,B_298) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_6138])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    ! [A_17,B_18] : k2_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_62,plain,(
    k2_xboole_0(k4_xboole_0('#skF_7',k1_tarski('#skF_6')),k1_tarski('#skF_6')) != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_65,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k4_xboole_0('#skF_7',k1_tarski('#skF_6'))) != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_62])).

tff(c_66,plain,(
    k2_xboole_0('#skF_7',k1_tarski('#skF_6')) != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_34,c_65])).

tff(c_6442,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_6243,c_66])).

tff(c_6499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_6442])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:37:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.93/2.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.93/2.18  
% 5.93/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.93/2.18  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4
% 5.93/2.18  
% 5.93/2.18  %Foreground sorts:
% 5.93/2.18  
% 5.93/2.18  
% 5.93/2.18  %Background operators:
% 5.93/2.18  
% 5.93/2.18  
% 5.93/2.18  %Foreground operators:
% 5.93/2.18  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.93/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.93/2.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.93/2.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.93/2.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.93/2.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.93/2.18  tff('#skF_7', type, '#skF_7': $i).
% 5.93/2.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.93/2.18  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.93/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.93/2.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.93/2.18  tff('#skF_6', type, '#skF_6': $i).
% 5.93/2.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.93/2.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.93/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.93/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.93/2.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.93/2.18  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.93/2.18  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.93/2.18  
% 5.93/2.19  tff(f_97, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 5.93/2.19  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 5.93/2.19  tff(f_56, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 5.93/2.19  tff(f_66, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.93/2.19  tff(f_72, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 5.93/2.19  tff(f_50, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_xboole_1)).
% 5.93/2.19  tff(f_60, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 5.93/2.19  tff(f_64, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 5.93/2.19  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.93/2.19  tff(f_52, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.93/2.19  tff(c_64, plain, (r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.93/2.19  tff(c_22, plain, (![A_9]: (k2_xboole_0(A_9, A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.93/2.19  tff(c_119, plain, (![A_50, B_51]: (k4_xboole_0(A_50, k2_xboole_0(A_50, B_51))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.93/2.19  tff(c_132, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_119])).
% 5.93/2.19  tff(c_507, plain, (![A_90, B_91]: (k5_xboole_0(A_90, k4_xboole_0(B_91, A_90))=k2_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.93/2.19  tff(c_525, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=k2_xboole_0(A_9, A_9))), inference(superposition, [status(thm), theory('equality')], [c_132, c_507])).
% 5.93/2.19  tff(c_533, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_525])).
% 5.93/2.19  tff(c_50, plain, (![A_32, B_33]: (r1_tarski(k1_tarski(A_32), B_33) | ~r2_hidden(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.93/2.19  tff(c_32, plain, (![A_14, C_16, B_15]: (r1_tarski(k4_xboole_0(A_14, C_16), B_15) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.93/2.19  tff(c_40, plain, (![A_24, C_26, B_25]: (r1_xboole_0(A_24, k4_xboole_0(C_26, B_25)) | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.93/2.19  tff(c_534, plain, (![A_92, B_93]: (k4_xboole_0(k2_xboole_0(A_92, B_93), B_93)=A_92 | ~r1_xboole_0(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.93/2.19  tff(c_588, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=A_9 | ~r1_xboole_0(A_9, A_9))), inference(superposition, [status(thm), theory('equality')], [c_22, c_534])).
% 5.93/2.19  tff(c_635, plain, (![A_96]: (k1_xboole_0=A_96 | ~r1_xboole_0(A_96, A_96))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_588])).
% 5.93/2.19  tff(c_5910, plain, (![C_292, B_293]: (k4_xboole_0(C_292, B_293)=k1_xboole_0 | ~r1_tarski(k4_xboole_0(C_292, B_293), B_293))), inference(resolution, [status(thm)], [c_40, c_635])).
% 5.93/2.19  tff(c_5981, plain, (![A_294, B_295]: (k4_xboole_0(A_294, B_295)=k1_xboole_0 | ~r1_tarski(A_294, B_295))), inference(resolution, [status(thm)], [c_32, c_5910])).
% 5.93/2.19  tff(c_6061, plain, (![A_296, B_297]: (k4_xboole_0(k1_tarski(A_296), B_297)=k1_xboole_0 | ~r2_hidden(A_296, B_297))), inference(resolution, [status(thm)], [c_50, c_5981])).
% 5.93/2.19  tff(c_44, plain, (![A_29, B_30]: (k5_xboole_0(A_29, k4_xboole_0(B_30, A_29))=k2_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.93/2.19  tff(c_6138, plain, (![B_297, A_296]: (k2_xboole_0(B_297, k1_tarski(A_296))=k5_xboole_0(B_297, k1_xboole_0) | ~r2_hidden(A_296, B_297))), inference(superposition, [status(thm), theory('equality')], [c_6061, c_44])).
% 5.93/2.19  tff(c_6243, plain, (![B_298, A_299]: (k2_xboole_0(B_298, k1_tarski(A_299))=B_298 | ~r2_hidden(A_299, B_298))), inference(demodulation, [status(thm), theory('equality')], [c_533, c_6138])).
% 5.93/2.19  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.93/2.19  tff(c_34, plain, (![A_17, B_18]: (k2_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.93/2.19  tff(c_62, plain, (k2_xboole_0(k4_xboole_0('#skF_7', k1_tarski('#skF_6')), k1_tarski('#skF_6'))!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.93/2.19  tff(c_65, plain, (k2_xboole_0(k1_tarski('#skF_6'), k4_xboole_0('#skF_7', k1_tarski('#skF_6')))!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_62])).
% 5.93/2.19  tff(c_66, plain, (k2_xboole_0('#skF_7', k1_tarski('#skF_6'))!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_34, c_65])).
% 5.93/2.19  tff(c_6442, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_6243, c_66])).
% 5.93/2.19  tff(c_6499, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_6442])).
% 5.93/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.93/2.19  
% 5.93/2.19  Inference rules
% 5.93/2.19  ----------------------
% 5.93/2.19  #Ref     : 0
% 5.93/2.19  #Sup     : 1614
% 5.93/2.19  #Fact    : 0
% 5.93/2.19  #Define  : 0
% 5.93/2.19  #Split   : 0
% 5.93/2.19  #Chain   : 0
% 5.93/2.19  #Close   : 0
% 5.93/2.19  
% 5.93/2.19  Ordering : KBO
% 5.93/2.19  
% 5.93/2.19  Simplification rules
% 5.93/2.19  ----------------------
% 5.93/2.19  #Subsume      : 436
% 5.93/2.19  #Demod        : 728
% 5.93/2.19  #Tautology    : 661
% 5.93/2.19  #SimpNegUnit  : 21
% 5.93/2.19  #BackRed      : 0
% 5.93/2.19  
% 5.93/2.19  #Partial instantiations: 0
% 5.93/2.19  #Strategies tried      : 1
% 5.93/2.19  
% 5.93/2.19  Timing (in seconds)
% 5.93/2.19  ----------------------
% 5.93/2.20  Preprocessing        : 0.34
% 5.93/2.20  Parsing              : 0.17
% 5.93/2.20  CNF conversion       : 0.03
% 5.93/2.20  Main loop            : 1.13
% 5.93/2.20  Inferencing          : 0.35
% 5.93/2.20  Reduction            : 0.43
% 5.93/2.20  Demodulation         : 0.34
% 5.93/2.20  BG Simplification    : 0.04
% 5.93/2.20  Subsumption          : 0.22
% 5.93/2.20  Abstraction          : 0.05
% 5.93/2.20  MUC search           : 0.00
% 5.93/2.20  Cooper               : 0.00
% 5.93/2.20  Total                : 1.49
% 5.93/2.20  Index Insertion      : 0.00
% 5.93/2.20  Index Deletion       : 0.00
% 5.93/2.20  Index Matching       : 0.00
% 5.93/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
