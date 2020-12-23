%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:24 EST 2020

% Result     : Theorem 5.64s
% Output     : CNFRefutation 5.99s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 233 expanded)
%              Number of leaves         :   21 (  85 expanded)
%              Depth                    :   10
%              Number of atoms          :   90 ( 405 expanded)
%              Number of equality atoms :   50 ( 205 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_41,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] : k4_xboole_0(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(A,C),B),k2_zfmisc_1(A,k4_xboole_0(B,D))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
          | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
        & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_3675,plain,(
    ! [A_152,B_153] :
      ( r1_tarski(A_152,B_153)
      | k4_xboole_0(A_152,B_153) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_64,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_76,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_64])).

tff(c_152,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,B_38)
      | k4_xboole_0(A_37,B_38) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_32,plain,
    ( ~ r1_tarski('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_63,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_164,plain,(
    k4_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_152,c_63])).

tff(c_36,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = k1_xboole_0
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_80,plain,(
    k4_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_14])).

tff(c_1415,plain,(
    ! [A_93,C_94,B_95,D_96] : k2_xboole_0(k2_zfmisc_1(k4_xboole_0(A_93,C_94),B_95),k2_zfmisc_1(A_93,k4_xboole_0(B_95,D_96))) = k4_xboole_0(k2_zfmisc_1(A_93,B_95),k2_zfmisc_1(C_94,D_96)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3241,plain,(
    ! [A_139,C_140,B_141,D_142] : r1_tarski(k2_zfmisc_1(k4_xboole_0(A_139,C_140),B_141),k4_xboole_0(k2_zfmisc_1(A_139,B_141),k2_zfmisc_1(C_140,D_142))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1415,c_16])).

tff(c_3276,plain,(
    r1_tarski(k2_zfmisc_1(k4_xboole_0('#skF_1','#skF_3'),'#skF_2'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_3241])).

tff(c_22,plain,(
    ! [A_13] : k2_zfmisc_1(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_645,plain,(
    ! [A_67,B_68,C_69] :
      ( ~ r1_tarski(k2_zfmisc_1(A_67,B_68),k2_zfmisc_1(A_67,C_69))
      | r1_tarski(B_68,C_69)
      | k1_xboole_0 = A_67 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_660,plain,(
    ! [A_13,B_68] :
      ( ~ r1_tarski(k2_zfmisc_1(A_13,B_68),k1_xboole_0)
      | r1_tarski(B_68,k1_xboole_0)
      | k1_xboole_0 = A_13 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_645])).

tff(c_3328,plain,
    ( r1_tarski('#skF_2',k1_xboole_0)
    | k4_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3276,c_660])).

tff(c_3354,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_3328])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | k4_xboole_0(A_6,B_7) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_192,plain,(
    ! [B_40,A_41] :
      ( B_40 = A_41
      | ~ r1_tarski(B_40,A_41)
      | ~ r1_tarski(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_203,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | k4_xboole_0(A_6,B_7) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_192])).

tff(c_3374,plain,
    ( k1_xboole_0 = '#skF_2'
    | k4_xboole_0(k1_xboole_0,'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3354,c_203])).

tff(c_3392,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_3374])).

tff(c_3444,plain,(
    ! [A_13] : k2_zfmisc_1(A_13,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3392,c_3392,c_22])).

tff(c_34,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3443,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3392,c_34])).

tff(c_3607,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3444,c_3443])).

tff(c_3608,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_3683,plain,(
    k4_xboole_0('#skF_2','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3675,c_3608])).

tff(c_3610,plain,(
    ! [A_148,B_149] :
      ( k2_xboole_0(A_148,B_149) = B_149
      | ~ r1_tarski(A_148,B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3630,plain,(
    ! [A_5] : k2_xboole_0(k1_xboole_0,A_5) = A_5 ),
    inference(resolution,[status(thm)],[c_10,c_3610])).

tff(c_24,plain,(
    ! [B_14] : k2_zfmisc_1(k1_xboole_0,B_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3609,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_3684,plain,(
    ! [A_154,B_155] :
      ( k4_xboole_0(A_154,B_155) = k1_xboole_0
      | ~ r1_tarski(A_154,B_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3704,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3609,c_3684])).

tff(c_4985,plain,(
    ! [A_209,C_210,B_211,D_212] : k2_xboole_0(k2_zfmisc_1(k4_xboole_0(A_209,C_210),B_211),k2_zfmisc_1(A_209,k4_xboole_0(B_211,D_212))) = k4_xboole_0(k2_zfmisc_1(A_209,B_211),k2_zfmisc_1(C_210,D_212)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_5072,plain,(
    ! [B_211,D_212] : k2_xboole_0(k2_zfmisc_1(k1_xboole_0,B_211),k2_zfmisc_1('#skF_1',k4_xboole_0(B_211,D_212))) = k4_xboole_0(k2_zfmisc_1('#skF_1',B_211),k2_zfmisc_1('#skF_3',D_212)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3704,c_4985])).

tff(c_7910,plain,(
    ! [B_275,D_276] : k4_xboole_0(k2_zfmisc_1('#skF_1',B_275),k2_zfmisc_1('#skF_3',D_276)) = k2_zfmisc_1('#skF_1',k4_xboole_0(B_275,D_276)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3630,c_24,c_5072])).

tff(c_3705,plain,(
    k4_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_3684])).

tff(c_7944,plain,(
    k2_zfmisc_1('#skF_1',k4_xboole_0('#skF_2','#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7910,c_3705])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( k1_xboole_0 = B_14
      | k1_xboole_0 = A_13
      | k2_zfmisc_1(A_13,B_14) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8025,plain,
    ( k4_xboole_0('#skF_2','#skF_4') = k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_7944,c_20])).

tff(c_8056,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_3683,c_8025])).

tff(c_8111,plain,(
    ! [B_14] : k2_zfmisc_1('#skF_1',B_14) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8056,c_8056,c_24])).

tff(c_8112,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8056,c_34])).

tff(c_8392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8111,c_8112])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:13:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.64/2.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.64/2.21  
% 5.64/2.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.99/2.21  %$ r1_tarski > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.99/2.21  
% 5.99/2.21  %Foreground sorts:
% 5.99/2.21  
% 5.99/2.21  
% 5.99/2.21  %Background operators:
% 5.99/2.21  
% 5.99/2.21  
% 5.99/2.21  %Foreground operators:
% 5.99/2.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.99/2.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.99/2.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.99/2.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.99/2.21  tff('#skF_2', type, '#skF_2': $i).
% 5.99/2.21  tff('#skF_3', type, '#skF_3': $i).
% 5.99/2.21  tff('#skF_1', type, '#skF_1': $i).
% 5.99/2.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.99/2.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.99/2.21  tff('#skF_4', type, '#skF_4': $i).
% 5.99/2.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.99/2.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.99/2.21  
% 5.99/2.22  tff(f_41, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 5.99/2.22  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.99/2.22  tff(f_75, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 5.99/2.22  tff(f_66, axiom, (![A, B, C, D]: (k4_xboole_0(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(A, C), B), k2_zfmisc_1(A, k4_xboole_0(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_zfmisc_1)).
% 5.99/2.22  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.99/2.22  tff(f_53, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.99/2.22  tff(f_64, axiom, (![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 5.99/2.22  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.99/2.22  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.99/2.22  tff(c_3675, plain, (![A_152, B_153]: (r1_tarski(A_152, B_153) | k4_xboole_0(A_152, B_153)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.99/2.22  tff(c_10, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.99/2.22  tff(c_64, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.99/2.22  tff(c_76, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_64])).
% 5.99/2.22  tff(c_152, plain, (![A_37, B_38]: (r1_tarski(A_37, B_38) | k4_xboole_0(A_37, B_38)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.99/2.22  tff(c_32, plain, (~r1_tarski('#skF_2', '#skF_4') | ~r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.99/2.22  tff(c_63, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_32])).
% 5.99/2.22  tff(c_164, plain, (k4_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_152, c_63])).
% 5.99/2.22  tff(c_36, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.99/2.22  tff(c_14, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=k1_xboole_0 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.99/2.22  tff(c_80, plain, (k4_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_14])).
% 5.99/2.22  tff(c_1415, plain, (![A_93, C_94, B_95, D_96]: (k2_xboole_0(k2_zfmisc_1(k4_xboole_0(A_93, C_94), B_95), k2_zfmisc_1(A_93, k4_xboole_0(B_95, D_96)))=k4_xboole_0(k2_zfmisc_1(A_93, B_95), k2_zfmisc_1(C_94, D_96)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.99/2.22  tff(c_16, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.99/2.22  tff(c_3241, plain, (![A_139, C_140, B_141, D_142]: (r1_tarski(k2_zfmisc_1(k4_xboole_0(A_139, C_140), B_141), k4_xboole_0(k2_zfmisc_1(A_139, B_141), k2_zfmisc_1(C_140, D_142))))), inference(superposition, [status(thm), theory('equality')], [c_1415, c_16])).
% 5.99/2.22  tff(c_3276, plain, (r1_tarski(k2_zfmisc_1(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_80, c_3241])).
% 5.99/2.22  tff(c_22, plain, (![A_13]: (k2_zfmisc_1(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.99/2.22  tff(c_645, plain, (![A_67, B_68, C_69]: (~r1_tarski(k2_zfmisc_1(A_67, B_68), k2_zfmisc_1(A_67, C_69)) | r1_tarski(B_68, C_69) | k1_xboole_0=A_67)), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.99/2.22  tff(c_660, plain, (![A_13, B_68]: (~r1_tarski(k2_zfmisc_1(A_13, B_68), k1_xboole_0) | r1_tarski(B_68, k1_xboole_0) | k1_xboole_0=A_13)), inference(superposition, [status(thm), theory('equality')], [c_22, c_645])).
% 5.99/2.22  tff(c_3328, plain, (r1_tarski('#skF_2', k1_xboole_0) | k4_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_3276, c_660])).
% 5.99/2.22  tff(c_3354, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_164, c_3328])).
% 5.99/2.22  tff(c_12, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | k4_xboole_0(A_6, B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.99/2.22  tff(c_192, plain, (![B_40, A_41]: (B_40=A_41 | ~r1_tarski(B_40, A_41) | ~r1_tarski(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.99/2.22  tff(c_203, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | k4_xboole_0(A_6, B_7)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_192])).
% 5.99/2.22  tff(c_3374, plain, (k1_xboole_0='#skF_2' | k4_xboole_0(k1_xboole_0, '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_3354, c_203])).
% 5.99/2.22  tff(c_3392, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_3374])).
% 5.99/2.22  tff(c_3444, plain, (![A_13]: (k2_zfmisc_1(A_13, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3392, c_3392, c_22])).
% 5.99/2.22  tff(c_34, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.99/2.22  tff(c_3443, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3392, c_34])).
% 5.99/2.22  tff(c_3607, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3444, c_3443])).
% 5.99/2.22  tff(c_3608, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_32])).
% 5.99/2.22  tff(c_3683, plain, (k4_xboole_0('#skF_2', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_3675, c_3608])).
% 5.99/2.22  tff(c_3610, plain, (![A_148, B_149]: (k2_xboole_0(A_148, B_149)=B_149 | ~r1_tarski(A_148, B_149))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.99/2.22  tff(c_3630, plain, (![A_5]: (k2_xboole_0(k1_xboole_0, A_5)=A_5)), inference(resolution, [status(thm)], [c_10, c_3610])).
% 5.99/2.22  tff(c_24, plain, (![B_14]: (k2_zfmisc_1(k1_xboole_0, B_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.99/2.22  tff(c_3609, plain, (r1_tarski('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_32])).
% 5.99/2.22  tff(c_3684, plain, (![A_154, B_155]: (k4_xboole_0(A_154, B_155)=k1_xboole_0 | ~r1_tarski(A_154, B_155))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.99/2.22  tff(c_3704, plain, (k4_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_3609, c_3684])).
% 5.99/2.22  tff(c_4985, plain, (![A_209, C_210, B_211, D_212]: (k2_xboole_0(k2_zfmisc_1(k4_xboole_0(A_209, C_210), B_211), k2_zfmisc_1(A_209, k4_xboole_0(B_211, D_212)))=k4_xboole_0(k2_zfmisc_1(A_209, B_211), k2_zfmisc_1(C_210, D_212)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.99/2.22  tff(c_5072, plain, (![B_211, D_212]: (k2_xboole_0(k2_zfmisc_1(k1_xboole_0, B_211), k2_zfmisc_1('#skF_1', k4_xboole_0(B_211, D_212)))=k4_xboole_0(k2_zfmisc_1('#skF_1', B_211), k2_zfmisc_1('#skF_3', D_212)))), inference(superposition, [status(thm), theory('equality')], [c_3704, c_4985])).
% 5.99/2.22  tff(c_7910, plain, (![B_275, D_276]: (k4_xboole_0(k2_zfmisc_1('#skF_1', B_275), k2_zfmisc_1('#skF_3', D_276))=k2_zfmisc_1('#skF_1', k4_xboole_0(B_275, D_276)))), inference(demodulation, [status(thm), theory('equality')], [c_3630, c_24, c_5072])).
% 5.99/2.22  tff(c_3705, plain, (k4_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_3684])).
% 5.99/2.22  tff(c_7944, plain, (k2_zfmisc_1('#skF_1', k4_xboole_0('#skF_2', '#skF_4'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7910, c_3705])).
% 5.99/2.22  tff(c_20, plain, (![B_14, A_13]: (k1_xboole_0=B_14 | k1_xboole_0=A_13 | k2_zfmisc_1(A_13, B_14)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.99/2.22  tff(c_8025, plain, (k4_xboole_0('#skF_2', '#skF_4')=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_7944, c_20])).
% 5.99/2.22  tff(c_8056, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_3683, c_8025])).
% 5.99/2.22  tff(c_8111, plain, (![B_14]: (k2_zfmisc_1('#skF_1', B_14)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8056, c_8056, c_24])).
% 5.99/2.22  tff(c_8112, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8056, c_34])).
% 5.99/2.22  tff(c_8392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8111, c_8112])).
% 5.99/2.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.99/2.22  
% 5.99/2.22  Inference rules
% 5.99/2.22  ----------------------
% 5.99/2.22  #Ref     : 0
% 5.99/2.22  #Sup     : 1926
% 5.99/2.22  #Fact    : 0
% 5.99/2.22  #Define  : 0
% 5.99/2.22  #Split   : 6
% 5.99/2.22  #Chain   : 0
% 5.99/2.22  #Close   : 0
% 5.99/2.22  
% 5.99/2.22  Ordering : KBO
% 5.99/2.22  
% 5.99/2.22  Simplification rules
% 5.99/2.22  ----------------------
% 5.99/2.22  #Subsume      : 413
% 5.99/2.22  #Demod        : 1577
% 5.99/2.22  #Tautology    : 1041
% 5.99/2.22  #SimpNegUnit  : 8
% 5.99/2.22  #BackRed      : 117
% 5.99/2.22  
% 5.99/2.22  #Partial instantiations: 0
% 5.99/2.22  #Strategies tried      : 1
% 5.99/2.22  
% 5.99/2.22  Timing (in seconds)
% 5.99/2.22  ----------------------
% 5.99/2.23  Preprocessing        : 0.30
% 5.99/2.23  Parsing              : 0.17
% 5.99/2.23  CNF conversion       : 0.02
% 5.99/2.23  Main loop            : 1.13
% 5.99/2.23  Inferencing          : 0.37
% 5.99/2.23  Reduction            : 0.42
% 5.99/2.23  Demodulation         : 0.31
% 5.99/2.23  BG Simplification    : 0.04
% 5.99/2.23  Subsumption          : 0.22
% 5.99/2.23  Abstraction          : 0.07
% 5.99/2.23  MUC search           : 0.00
% 5.99/2.23  Cooper               : 0.00
% 5.99/2.23  Total                : 1.46
% 5.99/2.23  Index Insertion      : 0.00
% 5.99/2.23  Index Deletion       : 0.00
% 5.99/2.23  Index Matching       : 0.00
% 5.99/2.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
