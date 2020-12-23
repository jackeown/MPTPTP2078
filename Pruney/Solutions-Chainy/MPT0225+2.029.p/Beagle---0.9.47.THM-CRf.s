%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:34 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   59 (  85 expanded)
%              Number of leaves         :   25 (  40 expanded)
%              Depth                    :    5
%              Number of atoms          :   61 ( 110 expanded)
%              Number of equality atoms :   38 (  79 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_32,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_270,plain,(
    ! [A_83,B_84] : k1_enumset1(A_83,A_83,B_84) = k2_tarski(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    ! [E_11,A_5,B_6] : r2_hidden(E_11,k1_enumset1(A_5,B_6,E_11)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_288,plain,(
    ! [B_85,A_86] : r2_hidden(B_85,k2_tarski(A_86,B_85)) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_10])).

tff(c_291,plain,(
    ! [A_12] : r2_hidden(A_12,k1_tarski(A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_288])).

tff(c_84,plain,(
    ! [A_42,B_43] : k1_enumset1(A_42,A_42,B_43) = k2_tarski(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_102,plain,(
    ! [B_44,A_45] : r2_hidden(B_44,k2_tarski(A_45,B_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_10])).

tff(c_105,plain,(
    ! [A_12] : r2_hidden(A_12,k1_tarski(A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_102])).

tff(c_44,plain,
    ( '#skF_3' != '#skF_4'
    | '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_49,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_74,plain,(
    ! [A_38,B_39] :
      ( r1_xboole_0(k1_tarski(A_38),k1_tarski(B_39))
      | B_39 = A_38 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = A_3
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_139,plain,(
    ! [A_54,B_55] :
      ( k4_xboole_0(k1_tarski(A_54),k1_tarski(B_55)) = k1_tarski(A_54)
      | B_55 = A_54 ) ),
    inference(resolution,[status(thm)],[c_74,c_4])).

tff(c_42,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3')
    | '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_127,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_145,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_127])).

tff(c_153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_145])).

tff(c_154,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_155,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_46,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3')
    | k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_203,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_154,c_155,c_46])).

tff(c_64,plain,(
    ! [A_36,B_37] :
      ( r1_xboole_0(A_36,B_37)
      | k4_xboole_0(A_36,B_37) != A_36 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ! [A_18,B_19] :
      ( ~ r2_hidden(A_18,B_19)
      | ~ r1_xboole_0(k1_tarski(A_18),B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_73,plain,(
    ! [A_18,B_37] :
      ( ~ r2_hidden(A_18,B_37)
      | k4_xboole_0(k1_tarski(A_18),B_37) != k1_tarski(A_18) ) ),
    inference(resolution,[status(thm)],[c_64,c_38])).

tff(c_207,plain,(
    ~ r2_hidden('#skF_6',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_73])).

tff(c_219,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_207])).

tff(c_220,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_221,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_48,plain,
    ( '#skF_3' != '#skF_4'
    | k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_255,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_220,c_221,c_48])).

tff(c_244,plain,(
    ! [A_77,B_78] :
      ( r1_xboole_0(A_77,B_78)
      | k4_xboole_0(A_77,B_78) != A_77 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_324,plain,(
    ! [A_95,B_96] :
      ( ~ r2_hidden(A_95,B_96)
      | k4_xboole_0(k1_tarski(A_95),B_96) != k1_tarski(A_95) ) ),
    inference(resolution,[status(thm)],[c_244,c_38])).

tff(c_327,plain,(
    ~ r2_hidden('#skF_6',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_324])).

tff(c_331,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_327])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:52:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.28  
% 2.13/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.29  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.13/1.29  
% 2.13/1.29  %Foreground sorts:
% 2.13/1.29  
% 2.13/1.29  
% 2.13/1.29  %Background operators:
% 2.13/1.29  
% 2.13/1.29  
% 2.13/1.29  %Foreground operators:
% 2.13/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.13/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.13/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.13/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.13/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.13/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.13/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.13/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.13/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.13/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.13/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.13/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.13/1.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.13/1.29  
% 2.13/1.30  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.13/1.30  tff(f_50, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.13/1.30  tff(f_46, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.13/1.30  tff(f_68, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.13/1.30  tff(f_62, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 2.13/1.30  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.13/1.30  tff(f_57, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.13/1.30  tff(c_32, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.13/1.30  tff(c_270, plain, (![A_83, B_84]: (k1_enumset1(A_83, A_83, B_84)=k2_tarski(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.13/1.30  tff(c_10, plain, (![E_11, A_5, B_6]: (r2_hidden(E_11, k1_enumset1(A_5, B_6, E_11)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.13/1.30  tff(c_288, plain, (![B_85, A_86]: (r2_hidden(B_85, k2_tarski(A_86, B_85)))), inference(superposition, [status(thm), theory('equality')], [c_270, c_10])).
% 2.13/1.30  tff(c_291, plain, (![A_12]: (r2_hidden(A_12, k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_288])).
% 2.13/1.30  tff(c_84, plain, (![A_42, B_43]: (k1_enumset1(A_42, A_42, B_43)=k2_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.13/1.30  tff(c_102, plain, (![B_44, A_45]: (r2_hidden(B_44, k2_tarski(A_45, B_44)))), inference(superposition, [status(thm), theory('equality')], [c_84, c_10])).
% 2.13/1.30  tff(c_105, plain, (![A_12]: (r2_hidden(A_12, k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_102])).
% 2.13/1.30  tff(c_44, plain, ('#skF_3'!='#skF_4' | '#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.13/1.30  tff(c_49, plain, ('#skF_3'!='#skF_4'), inference(splitLeft, [status(thm)], [c_44])).
% 2.13/1.30  tff(c_74, plain, (![A_38, B_39]: (r1_xboole_0(k1_tarski(A_38), k1_tarski(B_39)) | B_39=A_38)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.13/1.30  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=A_3 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.30  tff(c_139, plain, (![A_54, B_55]: (k4_xboole_0(k1_tarski(A_54), k1_tarski(B_55))=k1_tarski(A_54) | B_55=A_54)), inference(resolution, [status(thm)], [c_74, c_4])).
% 2.13/1.30  tff(c_42, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3') | '#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.13/1.30  tff(c_127, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3')), inference(splitLeft, [status(thm)], [c_42])).
% 2.13/1.30  tff(c_145, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_139, c_127])).
% 2.13/1.30  tff(c_153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_145])).
% 2.13/1.30  tff(c_154, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_42])).
% 2.13/1.30  tff(c_155, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 2.13/1.30  tff(c_46, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3') | k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.13/1.30  tff(c_203, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_154, c_155, c_46])).
% 2.13/1.30  tff(c_64, plain, (![A_36, B_37]: (r1_xboole_0(A_36, B_37) | k4_xboole_0(A_36, B_37)!=A_36)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.30  tff(c_38, plain, (![A_18, B_19]: (~r2_hidden(A_18, B_19) | ~r1_xboole_0(k1_tarski(A_18), B_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.13/1.30  tff(c_73, plain, (![A_18, B_37]: (~r2_hidden(A_18, B_37) | k4_xboole_0(k1_tarski(A_18), B_37)!=k1_tarski(A_18))), inference(resolution, [status(thm)], [c_64, c_38])).
% 2.13/1.30  tff(c_207, plain, (~r2_hidden('#skF_6', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_203, c_73])).
% 2.13/1.30  tff(c_219, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_105, c_207])).
% 2.13/1.30  tff(c_220, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_44])).
% 2.13/1.30  tff(c_221, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_44])).
% 2.13/1.30  tff(c_48, plain, ('#skF_3'!='#skF_4' | k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.13/1.30  tff(c_255, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_220, c_220, c_221, c_48])).
% 2.13/1.30  tff(c_244, plain, (![A_77, B_78]: (r1_xboole_0(A_77, B_78) | k4_xboole_0(A_77, B_78)!=A_77)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.30  tff(c_324, plain, (![A_95, B_96]: (~r2_hidden(A_95, B_96) | k4_xboole_0(k1_tarski(A_95), B_96)!=k1_tarski(A_95))), inference(resolution, [status(thm)], [c_244, c_38])).
% 2.13/1.30  tff(c_327, plain, (~r2_hidden('#skF_6', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_255, c_324])).
% 2.13/1.30  tff(c_331, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_291, c_327])).
% 2.13/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.30  
% 2.13/1.30  Inference rules
% 2.13/1.30  ----------------------
% 2.13/1.30  #Ref     : 0
% 2.13/1.30  #Sup     : 63
% 2.13/1.30  #Fact    : 0
% 2.13/1.30  #Define  : 0
% 2.13/1.30  #Split   : 3
% 2.13/1.30  #Chain   : 0
% 2.13/1.30  #Close   : 0
% 2.13/1.30  
% 2.13/1.30  Ordering : KBO
% 2.13/1.30  
% 2.13/1.30  Simplification rules
% 2.13/1.30  ----------------------
% 2.13/1.30  #Subsume      : 3
% 2.13/1.30  #Demod        : 20
% 2.13/1.30  #Tautology    : 44
% 2.13/1.30  #SimpNegUnit  : 3
% 2.13/1.30  #BackRed      : 0
% 2.13/1.30  
% 2.13/1.30  #Partial instantiations: 0
% 2.13/1.30  #Strategies tried      : 1
% 2.13/1.30  
% 2.13/1.30  Timing (in seconds)
% 2.13/1.30  ----------------------
% 2.13/1.30  Preprocessing        : 0.32
% 2.13/1.30  Parsing              : 0.16
% 2.13/1.30  CNF conversion       : 0.02
% 2.13/1.30  Main loop            : 0.23
% 2.13/1.30  Inferencing          : 0.10
% 2.13/1.30  Reduction            : 0.06
% 2.13/1.30  Demodulation         : 0.04
% 2.13/1.30  BG Simplification    : 0.01
% 2.13/1.30  Subsumption          : 0.03
% 2.13/1.30  Abstraction          : 0.01
% 2.13/1.30  MUC search           : 0.00
% 2.13/1.30  Cooper               : 0.00
% 2.13/1.30  Total                : 0.57
% 2.13/1.30  Index Insertion      : 0.00
% 2.13/1.30  Index Deletion       : 0.00
% 2.13/1.30  Index Matching       : 0.00
% 2.13/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
