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
% DateTime   : Thu Dec  3 09:48:33 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   66 (  95 expanded)
%              Number of leaves         :   28 (  44 expanded)
%              Depth                    :    5
%              Number of atoms          :   68 ( 118 expanded)
%              Number of equality atoms :   37 (  77 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,k3_xboole_0(A,B)),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_12,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k3_xboole_0(A_6,B_7)) = k4_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [A_12,B_13] : r1_xboole_0(k4_xboole_0(A_12,k3_xboole_0(A_12,B_13)),B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_915,plain,(
    ! [A_88,B_89] : r1_xboole_0(k4_xboole_0(A_88,B_89),B_89) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_22])).

tff(c_918,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_915])).

tff(c_936,plain,(
    ! [A_95,B_96] :
      ( ~ r2_hidden(A_95,B_96)
      | ~ r1_xboole_0(k1_tarski(A_95),B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_941,plain,(
    ! [A_95] : ~ r2_hidden(A_95,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_918,c_936])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_964,plain,(
    ! [A_104,B_105] :
      ( k4_xboole_0(A_104,B_105) = k1_xboole_0
      | ~ r1_tarski(A_104,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_972,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_964])).

tff(c_65,plain,(
    ! [A_28,B_29] : r1_xboole_0(k4_xboole_0(A_28,B_29),B_29) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_22])).

tff(c_68,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_65])).

tff(c_126,plain,(
    ! [A_44,B_45] :
      ( ~ r2_hidden(A_44,B_45)
      | ~ r1_xboole_0(k1_tarski(A_44),B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_140,plain,(
    ! [A_44] : ~ r2_hidden(A_44,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_68,c_126])).

tff(c_46,plain,
    ( '#skF_3' != '#skF_4'
    | '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_54,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_91,plain,(
    ! [A_37,B_38] :
      ( r1_xboole_0(k1_tarski(A_37),k1_tarski(B_38))
      | B_38 = A_37 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = A_10
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_739,plain,(
    ! [A_78,B_79] :
      ( k4_xboole_0(k1_tarski(A_78),k1_tarski(B_79)) = k1_tarski(A_78)
      | B_79 = A_78 ) ),
    inference(resolution,[status(thm)],[c_91,c_18])).

tff(c_44,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3')
    | '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_176,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_769,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_739,c_176])).

tff(c_792,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_769])).

tff(c_793,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_97,plain,(
    ! [A_41,B_42] :
      ( k4_xboole_0(A_41,B_42) = k1_xboole_0
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_105,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_97])).

tff(c_794,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_48,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3')
    | k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_870,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_793,c_105,c_793,c_794,c_48])).

tff(c_26,plain,(
    ! [C_18] : r2_hidden(C_18,k1_tarski(C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_886,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_870,c_26])).

tff(c_894,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_886])).

tff(c_895,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_896,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_50,plain,
    ( '#skF_3' != '#skF_4'
    | k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1033,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_972,c_895,c_895,c_896,c_50])).

tff(c_1049,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1033,c_26])).

tff(c_1057,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_941,c_1049])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:47:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.37  
% 2.70/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.37  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.70/1.37  
% 2.70/1.37  %Foreground sorts:
% 2.70/1.37  
% 2.70/1.37  
% 2.70/1.37  %Background operators:
% 2.70/1.37  
% 2.70/1.37  
% 2.70/1.37  %Foreground operators:
% 2.70/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.70/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.70/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.70/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.70/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.70/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.70/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.70/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.70/1.37  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.70/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.70/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.70/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.70/1.37  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.70/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.70/1.37  
% 2.70/1.38  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.70/1.38  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.70/1.38  tff(f_47, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, k3_xboole_0(A, B)), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_xboole_1)).
% 2.70/1.38  tff(f_63, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.70/1.38  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.70/1.38  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.70/1.38  tff(f_74, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.70/1.38  tff(f_68, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 2.70/1.38  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.70/1.38  tff(f_54, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.70/1.38  tff(c_12, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.70/1.38  tff(c_14, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k3_xboole_0(A_6, B_7))=k4_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.70/1.38  tff(c_22, plain, (![A_12, B_13]: (r1_xboole_0(k4_xboole_0(A_12, k3_xboole_0(A_12, B_13)), B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.70/1.38  tff(c_915, plain, (![A_88, B_89]: (r1_xboole_0(k4_xboole_0(A_88, B_89), B_89))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_22])).
% 2.70/1.38  tff(c_918, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_915])).
% 2.70/1.38  tff(c_936, plain, (![A_95, B_96]: (~r2_hidden(A_95, B_96) | ~r1_xboole_0(k1_tarski(A_95), B_96))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.70/1.38  tff(c_941, plain, (![A_95]: (~r2_hidden(A_95, k1_xboole_0))), inference(resolution, [status(thm)], [c_918, c_936])).
% 2.70/1.38  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.70/1.38  tff(c_964, plain, (![A_104, B_105]: (k4_xboole_0(A_104, B_105)=k1_xboole_0 | ~r1_tarski(A_104, B_105))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.70/1.38  tff(c_972, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_964])).
% 2.70/1.38  tff(c_65, plain, (![A_28, B_29]: (r1_xboole_0(k4_xboole_0(A_28, B_29), B_29))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_22])).
% 2.70/1.38  tff(c_68, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_65])).
% 2.70/1.38  tff(c_126, plain, (![A_44, B_45]: (~r2_hidden(A_44, B_45) | ~r1_xboole_0(k1_tarski(A_44), B_45))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.70/1.38  tff(c_140, plain, (![A_44]: (~r2_hidden(A_44, k1_xboole_0))), inference(resolution, [status(thm)], [c_68, c_126])).
% 2.70/1.38  tff(c_46, plain, ('#skF_3'!='#skF_4' | '#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.70/1.38  tff(c_54, plain, ('#skF_3'!='#skF_4'), inference(splitLeft, [status(thm)], [c_46])).
% 2.70/1.38  tff(c_91, plain, (![A_37, B_38]: (r1_xboole_0(k1_tarski(A_37), k1_tarski(B_38)) | B_38=A_37)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.70/1.38  tff(c_18, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=A_10 | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.70/1.38  tff(c_739, plain, (![A_78, B_79]: (k4_xboole_0(k1_tarski(A_78), k1_tarski(B_79))=k1_tarski(A_78) | B_79=A_78)), inference(resolution, [status(thm)], [c_91, c_18])).
% 2.70/1.38  tff(c_44, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3') | '#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.70/1.38  tff(c_176, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 2.70/1.38  tff(c_769, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_739, c_176])).
% 2.70/1.38  tff(c_792, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_769])).
% 2.70/1.38  tff(c_793, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_44])).
% 2.70/1.38  tff(c_97, plain, (![A_41, B_42]: (k4_xboole_0(A_41, B_42)=k1_xboole_0 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.70/1.38  tff(c_105, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_97])).
% 2.70/1.38  tff(c_794, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 2.70/1.38  tff(c_48, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3') | k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.70/1.38  tff(c_870, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_793, c_105, c_793, c_794, c_48])).
% 2.70/1.38  tff(c_26, plain, (![C_18]: (r2_hidden(C_18, k1_tarski(C_18)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.70/1.38  tff(c_886, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_870, c_26])).
% 2.70/1.38  tff(c_894, plain, $false, inference(negUnitSimplification, [status(thm)], [c_140, c_886])).
% 2.70/1.38  tff(c_895, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_46])).
% 2.70/1.38  tff(c_896, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_46])).
% 2.70/1.38  tff(c_50, plain, ('#skF_3'!='#skF_4' | k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.70/1.38  tff(c_1033, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_972, c_895, c_895, c_896, c_50])).
% 2.70/1.38  tff(c_1049, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1033, c_26])).
% 2.70/1.38  tff(c_1057, plain, $false, inference(negUnitSimplification, [status(thm)], [c_941, c_1049])).
% 2.70/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.38  
% 2.70/1.38  Inference rules
% 2.70/1.38  ----------------------
% 2.70/1.38  #Ref     : 0
% 2.70/1.38  #Sup     : 244
% 2.70/1.38  #Fact    : 0
% 2.70/1.38  #Define  : 0
% 2.70/1.38  #Split   : 2
% 2.70/1.38  #Chain   : 0
% 2.70/1.38  #Close   : 0
% 2.70/1.38  
% 2.70/1.38  Ordering : KBO
% 2.70/1.38  
% 2.70/1.38  Simplification rules
% 2.70/1.38  ----------------------
% 2.70/1.38  #Subsume      : 8
% 2.70/1.38  #Demod        : 161
% 2.70/1.38  #Tautology    : 165
% 2.70/1.38  #SimpNegUnit  : 3
% 2.70/1.38  #BackRed      : 0
% 2.70/1.38  
% 2.70/1.38  #Partial instantiations: 0
% 2.70/1.38  #Strategies tried      : 1
% 2.70/1.38  
% 2.70/1.38  Timing (in seconds)
% 2.70/1.38  ----------------------
% 2.70/1.39  Preprocessing        : 0.31
% 2.70/1.39  Parsing              : 0.16
% 2.70/1.39  CNF conversion       : 0.02
% 2.70/1.39  Main loop            : 0.31
% 2.70/1.39  Inferencing          : 0.12
% 2.70/1.39  Reduction            : 0.11
% 2.70/1.39  Demodulation         : 0.08
% 2.70/1.39  BG Simplification    : 0.02
% 2.70/1.39  Subsumption          : 0.05
% 2.70/1.39  Abstraction          : 0.02
% 2.70/1.39  MUC search           : 0.00
% 2.70/1.39  Cooper               : 0.00
% 2.70/1.39  Total                : 0.65
% 2.70/1.39  Index Insertion      : 0.00
% 2.70/1.39  Index Deletion       : 0.00
% 2.70/1.39  Index Matching       : 0.00
% 2.70/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
