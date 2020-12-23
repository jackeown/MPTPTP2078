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
% DateTime   : Thu Dec  3 09:50:19 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 153 expanded)
%              Number of leaves         :   20 (  57 expanded)
%              Depth                    :   11
%              Number of atoms          :  128 ( 408 expanded)
%              Number of equality atoms :   94 ( 352 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(c_32,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_49,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_30,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_75,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_36,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_67,plain,(
    ! [A_23,B_24] : r1_tarski(A_23,k2_xboole_0(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_70,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_67])).

tff(c_14,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_189,plain,(
    ! [B_44,C_45,A_46] :
      ( k2_tarski(B_44,C_45) = A_46
      | k1_tarski(C_45) = A_46
      | k1_tarski(B_44) = A_46
      | k1_xboole_0 = A_46
      | ~ r1_tarski(A_46,k2_tarski(B_44,C_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_202,plain,(
    ! [A_9,A_46] :
      ( k2_tarski(A_9,A_9) = A_46
      | k1_tarski(A_9) = A_46
      | k1_tarski(A_9) = A_46
      | k1_xboole_0 = A_46
      | ~ r1_tarski(A_46,k1_tarski(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_189])).

tff(c_523,plain,(
    ! [A_74,A_75] :
      ( k1_tarski(A_74) = A_75
      | k1_tarski(A_74) = A_75
      | k1_tarski(A_74) = A_75
      | k1_xboole_0 = A_75
      | ~ r1_tarski(A_75,k1_tarski(A_74)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_202])).

tff(c_533,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_70,c_523])).

tff(c_544,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_75,c_75,c_75,c_533])).

tff(c_545,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_546,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_34,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_555,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_546,c_34])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_547,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_36])).

tff(c_698,plain,(
    ! [A_91,C_92,B_93] :
      ( r1_tarski(A_91,k2_xboole_0(C_92,B_93))
      | ~ r1_tarski(A_91,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_709,plain,(
    ! [A_91] :
      ( r1_tarski(A_91,'#skF_2')
      | ~ r1_tarski(A_91,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_547,c_698])).

tff(c_801,plain,(
    ! [B_103,C_104,A_105] :
      ( k2_tarski(B_103,C_104) = A_105
      | k1_tarski(C_104) = A_105
      | k1_tarski(B_103) = A_105
      | k1_xboole_0 = A_105
      | ~ r1_tarski(A_105,k2_tarski(B_103,C_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_820,plain,(
    ! [A_9,A_105] :
      ( k2_tarski(A_9,A_9) = A_105
      | k1_tarski(A_9) = A_105
      | k1_tarski(A_9) = A_105
      | k1_xboole_0 = A_105
      | ~ r1_tarski(A_105,k1_tarski(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_801])).

tff(c_1214,plain,(
    ! [A_132,A_133] :
      ( k1_tarski(A_132) = A_133
      | k1_tarski(A_132) = A_133
      | k1_tarski(A_132) = A_133
      | k1_xboole_0 = A_133
      | ~ r1_tarski(A_133,k1_tarski(A_132)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_820])).

tff(c_1221,plain,(
    ! [A_133] :
      ( k1_tarski('#skF_1') = A_133
      | k1_tarski('#skF_1') = A_133
      | k1_tarski('#skF_1') = A_133
      | k1_xboole_0 = A_133
      | ~ r1_tarski(A_133,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_546,c_1214])).

tff(c_1255,plain,(
    ! [A_139] :
      ( A_139 = '#skF_2'
      | A_139 = '#skF_2'
      | A_139 = '#skF_2'
      | k1_xboole_0 = A_139
      | ~ r1_tarski(A_139,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_546,c_546,c_1221])).

tff(c_1276,plain,(
    ! [A_140] :
      ( A_140 = '#skF_2'
      | k1_xboole_0 = A_140
      | ~ r1_tarski(A_140,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_709,c_1255])).

tff(c_1284,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6,c_1276])).

tff(c_1292,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_545,c_555,c_1284])).

tff(c_1293,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1394,plain,(
    ! [A_158,C_159,B_160] :
      ( r1_tarski(A_158,k2_xboole_0(C_159,B_160))
      | ~ r1_tarski(A_158,B_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1400,plain,(
    ! [A_158] :
      ( r1_tarski(A_158,k1_tarski('#skF_1'))
      | ~ r1_tarski(A_158,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1394])).

tff(c_1294,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_18,plain,(
    ! [B_13,C_14,A_12] :
      ( k2_tarski(B_13,C_14) = A_12
      | k1_tarski(C_14) = A_12
      | k1_tarski(B_13) = A_12
      | k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k2_tarski(B_13,C_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1467,plain,(
    ! [B_170,C_171,A_172] :
      ( k2_tarski(B_170,C_171) = A_172
      | k1_tarski(C_171) = A_172
      | k1_tarski(B_170) = A_172
      | A_172 = '#skF_2'
      | ~ r1_tarski(A_172,k2_tarski(B_170,C_171)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1294,c_18])).

tff(c_1480,plain,(
    ! [A_9,A_172] :
      ( k2_tarski(A_9,A_9) = A_172
      | k1_tarski(A_9) = A_172
      | k1_tarski(A_9) = A_172
      | A_172 = '#skF_2'
      | ~ r1_tarski(A_172,k1_tarski(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1467])).

tff(c_1792,plain,(
    ! [A_200,A_201] :
      ( k1_tarski(A_200) = A_201
      | k1_tarski(A_200) = A_201
      | k1_tarski(A_200) = A_201
      | A_201 = '#skF_2'
      | ~ r1_tarski(A_201,k1_tarski(A_200)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1480])).

tff(c_1809,plain,(
    ! [A_202] :
      ( k1_tarski('#skF_1') = A_202
      | A_202 = '#skF_2'
      | ~ r1_tarski(A_202,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1400,c_1792])).

tff(c_1817,plain,
    ( k1_tarski('#skF_1') = '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6,c_1809])).

tff(c_1824,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1293,c_1817])).

tff(c_10,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1295,plain,(
    ! [A_6] : k2_xboole_0(A_6,'#skF_2') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1294,c_10])).

tff(c_1841,plain,(
    ! [A_6] : k2_xboole_0(A_6,'#skF_3') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1824,c_1295])).

tff(c_1840,plain,(
    k2_xboole_0('#skF_3','#skF_3') = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1824,c_36])).

tff(c_1879,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1841,c_1840])).

tff(c_1881,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1293,c_1879])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:37:14 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.48/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.64  
% 3.48/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.64  %$ r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.48/1.64  
% 3.48/1.64  %Foreground sorts:
% 3.48/1.64  
% 3.48/1.64  
% 3.48/1.64  %Background operators:
% 3.48/1.64  
% 3.48/1.64  
% 3.48/1.64  %Foreground operators:
% 3.48/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.48/1.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.48/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.48/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.48/1.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.48/1.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.48/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.48/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.48/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.48/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.48/1.64  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.48/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.48/1.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.48/1.64  
% 3.82/1.65  tff(f_79, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.82/1.65  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.82/1.65  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.82/1.65  tff(f_58, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.82/1.65  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.82/1.65  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.82/1.65  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.82/1.65  tff(c_32, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.82/1.65  tff(c_49, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_32])).
% 3.82/1.65  tff(c_30, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.82/1.65  tff(c_75, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_30])).
% 3.82/1.65  tff(c_36, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.82/1.65  tff(c_67, plain, (![A_23, B_24]: (r1_tarski(A_23, k2_xboole_0(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.82/1.65  tff(c_70, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_67])).
% 3.82/1.65  tff(c_14, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.82/1.65  tff(c_189, plain, (![B_44, C_45, A_46]: (k2_tarski(B_44, C_45)=A_46 | k1_tarski(C_45)=A_46 | k1_tarski(B_44)=A_46 | k1_xboole_0=A_46 | ~r1_tarski(A_46, k2_tarski(B_44, C_45)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.82/1.65  tff(c_202, plain, (![A_9, A_46]: (k2_tarski(A_9, A_9)=A_46 | k1_tarski(A_9)=A_46 | k1_tarski(A_9)=A_46 | k1_xboole_0=A_46 | ~r1_tarski(A_46, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_189])).
% 3.82/1.65  tff(c_523, plain, (![A_74, A_75]: (k1_tarski(A_74)=A_75 | k1_tarski(A_74)=A_75 | k1_tarski(A_74)=A_75 | k1_xboole_0=A_75 | ~r1_tarski(A_75, k1_tarski(A_74)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_202])).
% 3.82/1.65  tff(c_533, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_70, c_523])).
% 3.82/1.65  tff(c_544, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_75, c_75, c_75, c_533])).
% 3.82/1.65  tff(c_545, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_30])).
% 3.82/1.65  tff(c_546, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_30])).
% 3.82/1.65  tff(c_34, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.82/1.65  tff(c_555, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_546, c_546, c_34])).
% 3.82/1.65  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.82/1.65  tff(c_547, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_546, c_36])).
% 3.82/1.65  tff(c_698, plain, (![A_91, C_92, B_93]: (r1_tarski(A_91, k2_xboole_0(C_92, B_93)) | ~r1_tarski(A_91, B_93))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.82/1.65  tff(c_709, plain, (![A_91]: (r1_tarski(A_91, '#skF_2') | ~r1_tarski(A_91, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_547, c_698])).
% 3.82/1.65  tff(c_801, plain, (![B_103, C_104, A_105]: (k2_tarski(B_103, C_104)=A_105 | k1_tarski(C_104)=A_105 | k1_tarski(B_103)=A_105 | k1_xboole_0=A_105 | ~r1_tarski(A_105, k2_tarski(B_103, C_104)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.82/1.65  tff(c_820, plain, (![A_9, A_105]: (k2_tarski(A_9, A_9)=A_105 | k1_tarski(A_9)=A_105 | k1_tarski(A_9)=A_105 | k1_xboole_0=A_105 | ~r1_tarski(A_105, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_801])).
% 3.82/1.65  tff(c_1214, plain, (![A_132, A_133]: (k1_tarski(A_132)=A_133 | k1_tarski(A_132)=A_133 | k1_tarski(A_132)=A_133 | k1_xboole_0=A_133 | ~r1_tarski(A_133, k1_tarski(A_132)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_820])).
% 3.82/1.65  tff(c_1221, plain, (![A_133]: (k1_tarski('#skF_1')=A_133 | k1_tarski('#skF_1')=A_133 | k1_tarski('#skF_1')=A_133 | k1_xboole_0=A_133 | ~r1_tarski(A_133, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_546, c_1214])).
% 3.82/1.65  tff(c_1255, plain, (![A_139]: (A_139='#skF_2' | A_139='#skF_2' | A_139='#skF_2' | k1_xboole_0=A_139 | ~r1_tarski(A_139, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_546, c_546, c_546, c_1221])).
% 3.82/1.65  tff(c_1276, plain, (![A_140]: (A_140='#skF_2' | k1_xboole_0=A_140 | ~r1_tarski(A_140, '#skF_3'))), inference(resolution, [status(thm)], [c_709, c_1255])).
% 3.82/1.65  tff(c_1284, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_6, c_1276])).
% 3.82/1.65  tff(c_1292, plain, $false, inference(negUnitSimplification, [status(thm)], [c_545, c_555, c_1284])).
% 3.82/1.65  tff(c_1293, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_32])).
% 3.82/1.65  tff(c_1394, plain, (![A_158, C_159, B_160]: (r1_tarski(A_158, k2_xboole_0(C_159, B_160)) | ~r1_tarski(A_158, B_160))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.82/1.65  tff(c_1400, plain, (![A_158]: (r1_tarski(A_158, k1_tarski('#skF_1')) | ~r1_tarski(A_158, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1394])).
% 3.82/1.65  tff(c_1294, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_32])).
% 3.82/1.65  tff(c_18, plain, (![B_13, C_14, A_12]: (k2_tarski(B_13, C_14)=A_12 | k1_tarski(C_14)=A_12 | k1_tarski(B_13)=A_12 | k1_xboole_0=A_12 | ~r1_tarski(A_12, k2_tarski(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.82/1.65  tff(c_1467, plain, (![B_170, C_171, A_172]: (k2_tarski(B_170, C_171)=A_172 | k1_tarski(C_171)=A_172 | k1_tarski(B_170)=A_172 | A_172='#skF_2' | ~r1_tarski(A_172, k2_tarski(B_170, C_171)))), inference(demodulation, [status(thm), theory('equality')], [c_1294, c_18])).
% 3.82/1.65  tff(c_1480, plain, (![A_9, A_172]: (k2_tarski(A_9, A_9)=A_172 | k1_tarski(A_9)=A_172 | k1_tarski(A_9)=A_172 | A_172='#skF_2' | ~r1_tarski(A_172, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1467])).
% 3.82/1.65  tff(c_1792, plain, (![A_200, A_201]: (k1_tarski(A_200)=A_201 | k1_tarski(A_200)=A_201 | k1_tarski(A_200)=A_201 | A_201='#skF_2' | ~r1_tarski(A_201, k1_tarski(A_200)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1480])).
% 3.82/1.65  tff(c_1809, plain, (![A_202]: (k1_tarski('#skF_1')=A_202 | A_202='#skF_2' | ~r1_tarski(A_202, '#skF_3'))), inference(resolution, [status(thm)], [c_1400, c_1792])).
% 3.82/1.65  tff(c_1817, plain, (k1_tarski('#skF_1')='#skF_3' | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_6, c_1809])).
% 3.82/1.65  tff(c_1824, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1293, c_1817])).
% 3.82/1.65  tff(c_10, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.82/1.65  tff(c_1295, plain, (![A_6]: (k2_xboole_0(A_6, '#skF_2')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_1294, c_10])).
% 3.82/1.65  tff(c_1841, plain, (![A_6]: (k2_xboole_0(A_6, '#skF_3')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_1824, c_1295])).
% 3.82/1.65  tff(c_1840, plain, (k2_xboole_0('#skF_3', '#skF_3')=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1824, c_36])).
% 3.82/1.65  tff(c_1879, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1841, c_1840])).
% 3.82/1.65  tff(c_1881, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1293, c_1879])).
% 3.82/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.65  
% 3.82/1.65  Inference rules
% 3.82/1.65  ----------------------
% 3.82/1.65  #Ref     : 0
% 3.82/1.65  #Sup     : 398
% 3.82/1.65  #Fact    : 0
% 3.82/1.65  #Define  : 0
% 3.82/1.65  #Split   : 6
% 3.82/1.65  #Chain   : 0
% 3.82/1.65  #Close   : 0
% 3.82/1.65  
% 3.82/1.65  Ordering : KBO
% 3.82/1.65  
% 3.82/1.65  Simplification rules
% 3.82/1.65  ----------------------
% 3.82/1.65  #Subsume      : 63
% 3.82/1.65  #Demod        : 195
% 3.82/1.65  #Tautology    : 158
% 3.82/1.65  #SimpNegUnit  : 20
% 3.82/1.65  #BackRed      : 21
% 3.82/1.65  
% 3.82/1.65  #Partial instantiations: 0
% 3.82/1.65  #Strategies tried      : 1
% 3.82/1.65  
% 3.82/1.65  Timing (in seconds)
% 3.82/1.65  ----------------------
% 3.82/1.66  Preprocessing        : 0.31
% 3.82/1.66  Parsing              : 0.16
% 3.82/1.66  CNF conversion       : 0.02
% 3.82/1.66  Main loop            : 0.57
% 3.82/1.66  Inferencing          : 0.20
% 3.82/1.66  Reduction            : 0.18
% 3.82/1.66  Demodulation         : 0.13
% 3.82/1.66  BG Simplification    : 0.02
% 3.82/1.66  Subsumption          : 0.11
% 3.82/1.66  Abstraction          : 0.03
% 3.82/1.66  MUC search           : 0.00
% 3.82/1.66  Cooper               : 0.00
% 3.82/1.66  Total                : 0.91
% 3.82/1.66  Index Insertion      : 0.00
% 3.82/1.66  Index Deletion       : 0.00
% 3.82/1.66  Index Matching       : 0.00
% 3.82/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
