%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:36 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 113 expanded)
%              Number of leaves         :   28 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :   60 ( 166 expanded)
%              Number of equality atoms :   24 (  59 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_64,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_60,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_38,plain,(
    ! [C_24] : r2_hidden(C_24,k1_tarski(C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_67,plain,(
    ! [B_37,A_38] :
      ( ~ r2_hidden(B_37,A_38)
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_71,plain,(
    ! [C_24] : ~ v1_xboole_0(k1_tarski(C_24)) ),
    inference(resolution,[status(thm)],[c_38,c_67])).

tff(c_110,plain,(
    ! [A_47] :
      ( v1_xboole_0(A_47)
      | r2_hidden('#skF_1'(A_47),A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    ! [C_24,A_20] :
      ( C_24 = A_20
      | ~ r2_hidden(C_24,k1_tarski(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_114,plain,(
    ! [A_20] :
      ( '#skF_1'(k1_tarski(A_20)) = A_20
      | v1_xboole_0(k1_tarski(A_20)) ) ),
    inference(resolution,[status(thm)],[c_110,c_36])).

tff(c_120,plain,(
    ! [A_20] : '#skF_1'(k1_tarski(A_20)) = A_20 ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_114])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ! [A_16,B_17] : r1_tarski(k3_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_74,plain,(
    ! [A_42] :
      ( k1_xboole_0 = A_42
      | ~ r1_tarski(A_42,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_79,plain,(
    ! [B_17] : k3_xboole_0(k1_xboole_0,B_17) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_74])).

tff(c_186,plain,(
    ! [D_62,B_63,A_64] :
      ( r2_hidden(D_62,B_63)
      | ~ r2_hidden(D_62,k3_xboole_0(A_64,B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_205,plain,(
    ! [D_65,B_66] :
      ( r2_hidden(D_65,B_66)
      | ~ r2_hidden(D_65,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_186])).

tff(c_218,plain,(
    ! [B_66] :
      ( r2_hidden('#skF_1'(k1_xboole_0),B_66)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_205])).

tff(c_219,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_62,plain,(
    r1_tarski(k1_tarski('#skF_7'),k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_300,plain,(
    ! [B_81,A_82] :
      ( k1_tarski(B_81) = A_82
      | k1_xboole_0 = A_82
      | ~ r1_tarski(A_82,k1_tarski(B_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_317,plain,
    ( k1_tarski('#skF_7') = k1_tarski('#skF_8')
    | k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_62,c_300])).

tff(c_320,plain,(
    k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_317])).

tff(c_334,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_71])).

tff(c_351,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_334])).

tff(c_352,plain,(
    k1_tarski('#skF_7') = k1_tarski('#skF_8') ),
    inference(splitRight,[status(thm)],[c_317])).

tff(c_363,plain,(
    '#skF_1'(k1_tarski('#skF_8')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_120])).

tff(c_383,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_363])).

tff(c_385,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_383])).

tff(c_388,plain,(
    ! [B_83] : r2_hidden('#skF_1'(k1_xboole_0),B_83) ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_523,plain,(
    '#skF_1'(k1_xboole_0) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_388,c_36])).

tff(c_417,plain,(
    ! [A_85] : A_85 = '#skF_1'(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_388,c_36])).

tff(c_694,plain,(
    ! [A_1329] : A_1329 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_417])).

tff(c_755,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_694,c_60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:42:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.43  
% 2.92/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.43  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 2.92/1.43  
% 2.92/1.43  %Foreground sorts:
% 2.92/1.43  
% 2.92/1.43  
% 2.92/1.43  %Background operators:
% 2.92/1.43  
% 2.92/1.43  
% 2.92/1.43  %Foreground operators:
% 2.92/1.43  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.92/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.92/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.92/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.92/1.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.92/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.92/1.43  tff('#skF_7', type, '#skF_7': $i).
% 2.92/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.92/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.92/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.92/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.92/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.92/1.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.92/1.43  tff('#skF_8', type, '#skF_8': $i).
% 2.92/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.92/1.43  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.92/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.92/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.92/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.92/1.43  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.92/1.43  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.92/1.43  
% 2.92/1.45  tff(f_90, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.92/1.45  tff(f_73, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.92/1.45  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.92/1.45  tff(f_60, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.92/1.45  tff(f_64, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.92/1.45  tff(f_40, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.92/1.45  tff(f_85, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.92/1.45  tff(c_60, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.92/1.45  tff(c_38, plain, (![C_24]: (r2_hidden(C_24, k1_tarski(C_24)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.92/1.45  tff(c_67, plain, (![B_37, A_38]: (~r2_hidden(B_37, A_38) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.92/1.45  tff(c_71, plain, (![C_24]: (~v1_xboole_0(k1_tarski(C_24)))), inference(resolution, [status(thm)], [c_38, c_67])).
% 2.92/1.45  tff(c_110, plain, (![A_47]: (v1_xboole_0(A_47) | r2_hidden('#skF_1'(A_47), A_47))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.92/1.45  tff(c_36, plain, (![C_24, A_20]: (C_24=A_20 | ~r2_hidden(C_24, k1_tarski(A_20)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.92/1.45  tff(c_114, plain, (![A_20]: ('#skF_1'(k1_tarski(A_20))=A_20 | v1_xboole_0(k1_tarski(A_20)))), inference(resolution, [status(thm)], [c_110, c_36])).
% 2.92/1.45  tff(c_120, plain, (![A_20]: ('#skF_1'(k1_tarski(A_20))=A_20)), inference(negUnitSimplification, [status(thm)], [c_71, c_114])).
% 2.92/1.45  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.92/1.45  tff(c_30, plain, (![A_16, B_17]: (r1_tarski(k3_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.92/1.45  tff(c_74, plain, (![A_42]: (k1_xboole_0=A_42 | ~r1_tarski(A_42, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.92/1.45  tff(c_79, plain, (![B_17]: (k3_xboole_0(k1_xboole_0, B_17)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_74])).
% 2.92/1.45  tff(c_186, plain, (![D_62, B_63, A_64]: (r2_hidden(D_62, B_63) | ~r2_hidden(D_62, k3_xboole_0(A_64, B_63)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.92/1.45  tff(c_205, plain, (![D_65, B_66]: (r2_hidden(D_65, B_66) | ~r2_hidden(D_65, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_79, c_186])).
% 2.92/1.45  tff(c_218, plain, (![B_66]: (r2_hidden('#skF_1'(k1_xboole_0), B_66) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_205])).
% 2.92/1.45  tff(c_219, plain, (v1_xboole_0(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_218])).
% 2.92/1.45  tff(c_62, plain, (r1_tarski(k1_tarski('#skF_7'), k1_tarski('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.92/1.45  tff(c_300, plain, (![B_81, A_82]: (k1_tarski(B_81)=A_82 | k1_xboole_0=A_82 | ~r1_tarski(A_82, k1_tarski(B_81)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.92/1.45  tff(c_317, plain, (k1_tarski('#skF_7')=k1_tarski('#skF_8') | k1_tarski('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_62, c_300])).
% 2.92/1.45  tff(c_320, plain, (k1_tarski('#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_317])).
% 2.92/1.45  tff(c_334, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_320, c_71])).
% 2.92/1.45  tff(c_351, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_219, c_334])).
% 2.92/1.45  tff(c_352, plain, (k1_tarski('#skF_7')=k1_tarski('#skF_8')), inference(splitRight, [status(thm)], [c_317])).
% 2.92/1.45  tff(c_363, plain, ('#skF_1'(k1_tarski('#skF_8'))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_352, c_120])).
% 2.92/1.45  tff(c_383, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_120, c_363])).
% 2.92/1.45  tff(c_385, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_383])).
% 2.92/1.45  tff(c_388, plain, (![B_83]: (r2_hidden('#skF_1'(k1_xboole_0), B_83))), inference(splitRight, [status(thm)], [c_218])).
% 2.92/1.45  tff(c_523, plain, ('#skF_1'(k1_xboole_0)='#skF_8'), inference(resolution, [status(thm)], [c_388, c_36])).
% 2.92/1.45  tff(c_417, plain, (![A_85]: (A_85='#skF_1'(k1_xboole_0))), inference(resolution, [status(thm)], [c_388, c_36])).
% 2.92/1.45  tff(c_694, plain, (![A_1329]: (A_1329='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_523, c_417])).
% 2.92/1.45  tff(c_755, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_694, c_60])).
% 2.92/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.45  
% 2.92/1.45  Inference rules
% 2.92/1.45  ----------------------
% 2.92/1.45  #Ref     : 0
% 2.92/1.45  #Sup     : 197
% 2.92/1.45  #Fact    : 0
% 2.92/1.45  #Define  : 0
% 2.92/1.45  #Split   : 3
% 2.92/1.45  #Chain   : 0
% 2.92/1.45  #Close   : 0
% 2.92/1.45  
% 2.92/1.45  Ordering : KBO
% 2.92/1.45  
% 2.92/1.45  Simplification rules
% 2.92/1.45  ----------------------
% 2.92/1.45  #Subsume      : 37
% 2.92/1.45  #Demod        : 29
% 2.92/1.45  #Tautology    : 40
% 2.92/1.45  #SimpNegUnit  : 6
% 2.92/1.45  #BackRed      : 6
% 2.92/1.45  
% 2.92/1.45  #Partial instantiations: 256
% 2.92/1.45  #Strategies tried      : 1
% 2.92/1.45  
% 2.92/1.45  Timing (in seconds)
% 2.92/1.45  ----------------------
% 2.92/1.45  Preprocessing        : 0.33
% 2.92/1.45  Parsing              : 0.17
% 2.92/1.45  CNF conversion       : 0.03
% 2.92/1.45  Main loop            : 0.31
% 2.92/1.45  Inferencing          : 0.13
% 2.92/1.45  Reduction            : 0.08
% 2.92/1.45  Demodulation         : 0.05
% 2.92/1.45  BG Simplification    : 0.02
% 2.92/1.45  Subsumption          : 0.05
% 2.92/1.45  Abstraction          : 0.01
% 2.92/1.45  MUC search           : 0.00
% 2.92/1.45  Cooper               : 0.00
% 2.92/1.45  Total                : 0.67
% 2.92/1.45  Index Insertion      : 0.00
% 2.92/1.45  Index Deletion       : 0.00
% 2.92/1.45  Index Matching       : 0.00
% 2.92/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
