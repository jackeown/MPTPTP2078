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
% DateTime   : Thu Dec  3 09:49:37 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 209 expanded)
%              Number of leaves         :   21 (  77 expanded)
%              Depth                    :   14
%              Number of atoms          :   86 ( 437 expanded)
%              Number of equality atoms :   61 ( 325 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
        & A != B
        & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(c_26,plain,(
    '#skF_1' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_28,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    ! [A_23] : k2_tarski(A_23,A_23) = k1_tarski(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    ! [B_16,C_17] : r1_tarski(k1_xboole_0,k2_tarski(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_37,plain,(
    ! [A_23] : r1_tarski(k1_xboole_0,k1_tarski(A_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_22])).

tff(c_87,plain,(
    ! [A_32,B_33] :
      ( k3_xboole_0(A_32,B_33) = A_32
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_110,plain,(
    ! [A_23] : k3_xboole_0(k1_xboole_0,k1_tarski(A_23)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_37,c_87])).

tff(c_30,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_255,plain,(
    ! [B_60,C_61,A_62] :
      ( k2_tarski(B_60,C_61) = A_62
      | k1_tarski(C_61) = A_62
      | k1_tarski(B_60) = A_62
      | k1_xboole_0 = A_62
      | ~ r1_tarski(A_62,k2_tarski(B_60,C_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_276,plain,
    ( k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_1','#skF_2')
    | k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_4')
    | k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3')
    | k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_255])).

tff(c_295,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_276])).

tff(c_18,plain,(
    ! [C_17,B_16] : r1_tarski(k1_tarski(C_17),k2_tarski(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_107,plain,(
    ! [C_17,B_16] : k3_xboole_0(k1_tarski(C_17),k2_tarski(B_16,C_17)) = k1_tarski(C_17) ),
    inference(resolution,[status(thm)],[c_18,c_87])).

tff(c_318,plain,(
    k3_xboole_0(k1_tarski('#skF_2'),k1_xboole_0) = k1_tarski('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_107])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_365,plain,(
    k3_xboole_0(k1_xboole_0,k1_tarski('#skF_2')) = k1_tarski('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_2])).

tff(c_377,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_365])).

tff(c_209,plain,(
    ! [C_49,A_50,B_51] :
      ( C_49 = A_50
      | B_51 = A_50
      | ~ r1_tarski(k1_tarski(A_50),k2_tarski(B_51,C_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_218,plain,(
    ! [A_50,A_5] :
      ( A_50 = A_5
      | A_50 = A_5
      | ~ r1_tarski(k1_tarski(A_50),k1_tarski(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_209])).

tff(c_392,plain,(
    ! [A_5] :
      ( A_5 = '#skF_2'
      | A_5 = '#skF_2'
      | ~ r1_tarski(k1_xboole_0,k1_tarski(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_218])).

tff(c_446,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_392])).

tff(c_431,plain,(
    ! [A_5] : A_5 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_392])).

tff(c_584,plain,(
    ! [A_621] : A_621 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_446,c_431])).

tff(c_702,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_584,c_26])).

tff(c_703,plain,
    ( k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3')
    | k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_4')
    | k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_705,plain,(
    k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_703])).

tff(c_739,plain,(
    r1_tarski(k1_tarski('#skF_4'),k2_tarski('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_705,c_18])).

tff(c_24,plain,(
    ! [C_20,A_18,B_19] :
      ( C_20 = A_18
      | B_19 = A_18
      | ~ r1_tarski(k1_tarski(A_18),k2_tarski(B_19,C_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_760,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_739,c_24])).

tff(c_767,plain,(
    '#skF_2' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_760])).

tff(c_20,plain,(
    ! [B_16,C_17] : r1_tarski(k1_tarski(B_16),k2_tarski(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_742,plain,(
    r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_705,c_20])).

tff(c_777,plain,(
    r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_1','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_767,c_742])).

tff(c_783,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_777,c_24])).

tff(c_790,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_783])).

tff(c_770,plain,(
    k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_767,c_705])).

tff(c_799,plain,(
    k2_tarski('#skF_1','#skF_4') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_790,c_770])).

tff(c_833,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_799,c_20])).

tff(c_854,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_833,c_218])).

tff(c_862,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_26,c_854])).

tff(c_863,plain,
    ( k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_4')
    | k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_703])).

tff(c_865,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_863])).

tff(c_904,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_865,c_20])).

tff(c_941,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_904,c_218])).

tff(c_949,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_28,c_941])).

tff(c_950,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_863])).

tff(c_990,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_950,c_20])).

tff(c_1009,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_990,c_218])).

tff(c_1017,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_26,c_1009])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:57:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.47  
% 2.98/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.47  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.98/1.47  
% 2.98/1.47  %Foreground sorts:
% 2.98/1.47  
% 2.98/1.47  
% 2.98/1.47  %Background operators:
% 2.98/1.47  
% 2.98/1.47  
% 2.98/1.47  %Foreground operators:
% 2.98/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.98/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.98/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.98/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.98/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.98/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.98/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.98/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.98/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.98/1.47  tff('#skF_1', type, '#skF_1': $i).
% 2.98/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.47  tff('#skF_4', type, '#skF_4': $i).
% 2.98/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.98/1.47  
% 3.12/1.48  tff(f_73, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 3.12/1.48  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.12/1.48  tff(f_54, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.12/1.48  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.12/1.48  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.12/1.48  tff(f_63, axiom, (![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 3.12/1.48  tff(c_26, plain, ('#skF_1'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.12/1.48  tff(c_28, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.12/1.48  tff(c_6, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.12/1.48  tff(c_32, plain, (![A_23]: (k2_tarski(A_23, A_23)=k1_tarski(A_23))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.12/1.48  tff(c_22, plain, (![B_16, C_17]: (r1_tarski(k1_xboole_0, k2_tarski(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.12/1.48  tff(c_37, plain, (![A_23]: (r1_tarski(k1_xboole_0, k1_tarski(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_22])).
% 3.12/1.48  tff(c_87, plain, (![A_32, B_33]: (k3_xboole_0(A_32, B_33)=A_32 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.12/1.48  tff(c_110, plain, (![A_23]: (k3_xboole_0(k1_xboole_0, k1_tarski(A_23))=k1_xboole_0)), inference(resolution, [status(thm)], [c_37, c_87])).
% 3.12/1.48  tff(c_30, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.12/1.48  tff(c_255, plain, (![B_60, C_61, A_62]: (k2_tarski(B_60, C_61)=A_62 | k1_tarski(C_61)=A_62 | k1_tarski(B_60)=A_62 | k1_xboole_0=A_62 | ~r1_tarski(A_62, k2_tarski(B_60, C_61)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.12/1.48  tff(c_276, plain, (k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_1', '#skF_2') | k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_4') | k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_3') | k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_255])).
% 3.12/1.48  tff(c_295, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_276])).
% 3.12/1.48  tff(c_18, plain, (![C_17, B_16]: (r1_tarski(k1_tarski(C_17), k2_tarski(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.12/1.48  tff(c_107, plain, (![C_17, B_16]: (k3_xboole_0(k1_tarski(C_17), k2_tarski(B_16, C_17))=k1_tarski(C_17))), inference(resolution, [status(thm)], [c_18, c_87])).
% 3.12/1.48  tff(c_318, plain, (k3_xboole_0(k1_tarski('#skF_2'), k1_xboole_0)=k1_tarski('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_295, c_107])).
% 3.12/1.48  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.12/1.48  tff(c_365, plain, (k3_xboole_0(k1_xboole_0, k1_tarski('#skF_2'))=k1_tarski('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_318, c_2])).
% 3.12/1.48  tff(c_377, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_110, c_365])).
% 3.12/1.48  tff(c_209, plain, (![C_49, A_50, B_51]: (C_49=A_50 | B_51=A_50 | ~r1_tarski(k1_tarski(A_50), k2_tarski(B_51, C_49)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.12/1.48  tff(c_218, plain, (![A_50, A_5]: (A_50=A_5 | A_50=A_5 | ~r1_tarski(k1_tarski(A_50), k1_tarski(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_209])).
% 3.12/1.48  tff(c_392, plain, (![A_5]: (A_5='#skF_2' | A_5='#skF_2' | ~r1_tarski(k1_xboole_0, k1_tarski(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_377, c_218])).
% 3.12/1.48  tff(c_446, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_37, c_392])).
% 3.12/1.48  tff(c_431, plain, (![A_5]: (A_5='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_37, c_392])).
% 3.12/1.48  tff(c_584, plain, (![A_621]: (A_621='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_446, c_431])).
% 3.12/1.48  tff(c_702, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_584, c_26])).
% 3.12/1.48  tff(c_703, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_3') | k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_4') | k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_276])).
% 3.12/1.48  tff(c_705, plain, (k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_703])).
% 3.12/1.48  tff(c_739, plain, (r1_tarski(k1_tarski('#skF_4'), k2_tarski('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_705, c_18])).
% 3.12/1.48  tff(c_24, plain, (![C_20, A_18, B_19]: (C_20=A_18 | B_19=A_18 | ~r1_tarski(k1_tarski(A_18), k2_tarski(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.12/1.48  tff(c_760, plain, ('#skF_2'='#skF_4' | '#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_739, c_24])).
% 3.12/1.48  tff(c_767, plain, ('#skF_2'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_26, c_760])).
% 3.12/1.48  tff(c_20, plain, (![B_16, C_17]: (r1_tarski(k1_tarski(B_16), k2_tarski(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.12/1.48  tff(c_742, plain, (r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_705, c_20])).
% 3.12/1.48  tff(c_777, plain, (r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_1', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_767, c_742])).
% 3.12/1.48  tff(c_783, plain, ('#skF_3'='#skF_4' | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_777, c_24])).
% 3.12/1.48  tff(c_790, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_28, c_783])).
% 3.12/1.48  tff(c_770, plain, (k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_767, c_705])).
% 3.12/1.48  tff(c_799, plain, (k2_tarski('#skF_1', '#skF_4')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_790, c_770])).
% 3.12/1.48  tff(c_833, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_799, c_20])).
% 3.12/1.48  tff(c_854, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_833, c_218])).
% 3.12/1.48  tff(c_862, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_26, c_854])).
% 3.12/1.48  tff(c_863, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_4') | k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_703])).
% 3.12/1.48  tff(c_865, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_3')), inference(splitLeft, [status(thm)], [c_863])).
% 3.12/1.48  tff(c_904, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_865, c_20])).
% 3.12/1.48  tff(c_941, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_904, c_218])).
% 3.12/1.48  tff(c_949, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_28, c_941])).
% 3.12/1.48  tff(c_950, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_863])).
% 3.12/1.48  tff(c_990, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_950, c_20])).
% 3.12/1.48  tff(c_1009, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_990, c_218])).
% 3.12/1.48  tff(c_1017, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_26, c_1009])).
% 3.12/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.48  
% 3.12/1.48  Inference rules
% 3.12/1.48  ----------------------
% 3.12/1.48  #Ref     : 0
% 3.12/1.48  #Sup     : 303
% 3.12/1.48  #Fact    : 0
% 3.12/1.48  #Define  : 0
% 3.12/1.48  #Split   : 3
% 3.12/1.48  #Chain   : 0
% 3.12/1.48  #Close   : 0
% 3.12/1.48  
% 3.12/1.48  Ordering : KBO
% 3.12/1.48  
% 3.12/1.48  Simplification rules
% 3.12/1.48  ----------------------
% 3.12/1.48  #Subsume      : 32
% 3.12/1.48  #Demod        : 147
% 3.12/1.48  #Tautology    : 126
% 3.12/1.48  #SimpNegUnit  : 5
% 3.12/1.48  #BackRed      : 22
% 3.12/1.48  
% 3.12/1.48  #Partial instantiations: 96
% 3.12/1.48  #Strategies tried      : 1
% 3.12/1.48  
% 3.12/1.48  Timing (in seconds)
% 3.12/1.48  ----------------------
% 3.12/1.49  Preprocessing        : 0.31
% 3.12/1.49  Parsing              : 0.16
% 3.12/1.49  CNF conversion       : 0.02
% 3.12/1.49  Main loop            : 0.41
% 3.12/1.49  Inferencing          : 0.16
% 3.12/1.49  Reduction            : 0.14
% 3.12/1.49  Demodulation         : 0.11
% 3.12/1.49  BG Simplification    : 0.02
% 3.12/1.49  Subsumption          : 0.07
% 3.12/1.49  Abstraction          : 0.02
% 3.12/1.49  MUC search           : 0.00
% 3.12/1.49  Cooper               : 0.00
% 3.12/1.49  Total                : 0.75
% 3.12/1.49  Index Insertion      : 0.00
% 3.12/1.49  Index Deletion       : 0.00
% 3.12/1.49  Index Matching       : 0.00
% 3.12/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
