%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:09 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   53 (  85 expanded)
%              Number of leaves         :   18 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   68 ( 190 expanded)
%              Number of equality atoms :   58 ( 177 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_24,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_22,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_43,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_28,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_46,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k2_xboole_0(A_17,B_18)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_53,plain,(
    k4_xboole_0('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_46])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | k4_xboole_0(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_442,plain,(
    ! [B_36,A_37] :
      ( k1_tarski(B_36) = A_37
      | k1_xboole_0 = A_37
      | ~ r1_tarski(A_37,k1_tarski(B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1182,plain,(
    ! [B_50,A_51] :
      ( k1_tarski(B_50) = A_51
      | k1_xboole_0 = A_51
      | k4_xboole_0(A_51,k1_tarski(B_50)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_442])).

tff(c_1200,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_1182])).

tff(c_1211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_43,c_1200])).

tff(c_1212,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_1213,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1214,plain,(
    ! [A_3] : k2_xboole_0(A_3,'#skF_2') = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1213,c_4])).

tff(c_1256,plain,(
    ! [B_58,A_59] : k2_xboole_0(B_58,A_59) = k2_xboole_0(A_59,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1285,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1256,c_28])).

tff(c_1317,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1214,c_1285])).

tff(c_1319,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1212,c_1317])).

tff(c_1320,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_1321,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_26,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1345,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1321,c_1321,c_26])).

tff(c_1347,plain,(
    ! [B_61,A_62] : k2_xboole_0(B_61,A_62) = k2_xboole_0(A_62,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1322,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1321,c_28])).

tff(c_1362,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1347,c_1322])).

tff(c_1448,plain,(
    ! [A_64,B_65] : k4_xboole_0(A_64,k2_xboole_0(A_64,B_65)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1458,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1362,c_1448])).

tff(c_1768,plain,(
    ! [B_82,A_83] :
      ( k1_tarski(B_82) = A_83
      | k1_xboole_0 = A_83
      | ~ r1_tarski(A_83,k1_tarski(B_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1778,plain,(
    ! [A_83] :
      ( k1_tarski('#skF_1') = A_83
      | k1_xboole_0 = A_83
      | ~ r1_tarski(A_83,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1321,c_1768])).

tff(c_1788,plain,(
    ! [A_84] :
      ( A_84 = '#skF_2'
      | k1_xboole_0 = A_84
      | ~ r1_tarski(A_84,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1321,c_1778])).

tff(c_1864,plain,(
    ! [A_87] :
      ( A_87 = '#skF_2'
      | k1_xboole_0 = A_87
      | k4_xboole_0(A_87,'#skF_2') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_1788])).

tff(c_1879,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1458,c_1864])).

tff(c_1891,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1320,c_1345,c_1879])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:10:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.18/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.57  
% 3.18/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.58  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.18/1.58  
% 3.18/1.58  %Foreground sorts:
% 3.18/1.58  
% 3.18/1.58  
% 3.18/1.58  %Background operators:
% 3.18/1.58  
% 3.18/1.58  
% 3.18/1.58  %Foreground operators:
% 3.18/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.18/1.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.18/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.18/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.18/1.58  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.18/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.18/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.18/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.18/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.18/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.18/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.18/1.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.18/1.58  
% 3.18/1.59  tff(f_64, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.18/1.59  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.18/1.59  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 3.18/1.59  tff(f_45, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.18/1.59  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.18/1.59  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.18/1.59  tff(c_24, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.18/1.59  tff(c_44, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_24])).
% 3.18/1.59  tff(c_22, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.18/1.59  tff(c_43, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_22])).
% 3.18/1.59  tff(c_28, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.18/1.59  tff(c_46, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k2_xboole_0(A_17, B_18))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.18/1.59  tff(c_53, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_28, c_46])).
% 3.18/1.59  tff(c_6, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | k4_xboole_0(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.18/1.59  tff(c_442, plain, (![B_36, A_37]: (k1_tarski(B_36)=A_37 | k1_xboole_0=A_37 | ~r1_tarski(A_37, k1_tarski(B_36)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.18/1.59  tff(c_1182, plain, (![B_50, A_51]: (k1_tarski(B_50)=A_51 | k1_xboole_0=A_51 | k4_xboole_0(A_51, k1_tarski(B_50))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_442])).
% 3.18/1.59  tff(c_1200, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_53, c_1182])).
% 3.18/1.59  tff(c_1211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_43, c_1200])).
% 3.18/1.59  tff(c_1212, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_24])).
% 3.18/1.59  tff(c_1213, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_24])).
% 3.18/1.59  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.18/1.59  tff(c_1214, plain, (![A_3]: (k2_xboole_0(A_3, '#skF_2')=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_1213, c_4])).
% 3.18/1.59  tff(c_1256, plain, (![B_58, A_59]: (k2_xboole_0(B_58, A_59)=k2_xboole_0(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.18/1.59  tff(c_1285, plain, (k2_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1256, c_28])).
% 3.18/1.59  tff(c_1317, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1214, c_1285])).
% 3.18/1.59  tff(c_1319, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1212, c_1317])).
% 3.18/1.59  tff(c_1320, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_22])).
% 3.18/1.59  tff(c_1321, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_22])).
% 3.18/1.59  tff(c_26, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.18/1.59  tff(c_1345, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1321, c_1321, c_26])).
% 3.18/1.59  tff(c_1347, plain, (![B_61, A_62]: (k2_xboole_0(B_61, A_62)=k2_xboole_0(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.18/1.59  tff(c_1322, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1321, c_28])).
% 3.18/1.59  tff(c_1362, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1347, c_1322])).
% 3.18/1.59  tff(c_1448, plain, (![A_64, B_65]: (k4_xboole_0(A_64, k2_xboole_0(A_64, B_65))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.18/1.59  tff(c_1458, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1362, c_1448])).
% 3.18/1.59  tff(c_1768, plain, (![B_82, A_83]: (k1_tarski(B_82)=A_83 | k1_xboole_0=A_83 | ~r1_tarski(A_83, k1_tarski(B_82)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.18/1.59  tff(c_1778, plain, (![A_83]: (k1_tarski('#skF_1')=A_83 | k1_xboole_0=A_83 | ~r1_tarski(A_83, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1321, c_1768])).
% 3.18/1.59  tff(c_1788, plain, (![A_84]: (A_84='#skF_2' | k1_xboole_0=A_84 | ~r1_tarski(A_84, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1321, c_1778])).
% 3.18/1.59  tff(c_1864, plain, (![A_87]: (A_87='#skF_2' | k1_xboole_0=A_87 | k4_xboole_0(A_87, '#skF_2')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_1788])).
% 3.18/1.59  tff(c_1879, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1458, c_1864])).
% 3.18/1.59  tff(c_1891, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1320, c_1345, c_1879])).
% 3.18/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.59  
% 3.18/1.59  Inference rules
% 3.18/1.59  ----------------------
% 3.18/1.59  #Ref     : 0
% 3.18/1.59  #Sup     : 463
% 3.18/1.59  #Fact    : 0
% 3.18/1.59  #Define  : 0
% 3.18/1.59  #Split   : 3
% 3.18/1.59  #Chain   : 0
% 3.18/1.59  #Close   : 0
% 3.18/1.59  
% 3.18/1.59  Ordering : KBO
% 3.18/1.59  
% 3.18/1.59  Simplification rules
% 3.18/1.59  ----------------------
% 3.18/1.59  #Subsume      : 2
% 3.18/1.59  #Demod        : 402
% 3.18/1.59  #Tautology    : 385
% 3.18/1.59  #SimpNegUnit  : 6
% 3.18/1.59  #BackRed      : 3
% 3.18/1.59  
% 3.18/1.59  #Partial instantiations: 0
% 3.18/1.59  #Strategies tried      : 1
% 3.18/1.59  
% 3.18/1.59  Timing (in seconds)
% 3.18/1.59  ----------------------
% 3.18/1.59  Preprocessing        : 0.33
% 3.18/1.59  Parsing              : 0.18
% 3.18/1.59  CNF conversion       : 0.02
% 3.18/1.59  Main loop            : 0.45
% 3.18/1.59  Inferencing          : 0.15
% 3.18/1.59  Reduction            : 0.20
% 3.18/1.59  Demodulation         : 0.16
% 3.18/1.59  BG Simplification    : 0.02
% 3.18/1.59  Subsumption          : 0.06
% 3.18/1.59  Abstraction          : 0.02
% 3.18/1.59  MUC search           : 0.00
% 3.18/1.59  Cooper               : 0.00
% 3.18/1.59  Total                : 0.81
% 3.18/1.59  Index Insertion      : 0.00
% 3.18/1.59  Index Deletion       : 0.00
% 3.18/1.59  Index Matching       : 0.00
% 3.18/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
