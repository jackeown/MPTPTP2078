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
% DateTime   : Thu Dec  3 10:09:14 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 103 expanded)
%              Number of leaves         :   28 (  49 expanded)
%              Depth                    :    8
%              Number of atoms          :   77 ( 158 expanded)
%              Number of equality atoms :   45 ( 102 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_75,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_55,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_20,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_336,plain,(
    ! [A_94,B_95] :
      ( r1_tarski(A_94,B_95)
      | ~ m1_subset_1(A_94,k1_zfmisc_1(B_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_340,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(resolution,[status(thm)],[c_20,c_336])).

tff(c_147,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(A_52,B_53)
      | ~ m1_subset_1(A_52,k1_zfmisc_1(B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_155,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(resolution,[status(thm)],[c_20,c_147])).

tff(c_42,plain,(
    k4_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_65,plain,(
    ! [A_38,B_39] : k1_mcart_1(k4_tarski(A_38,B_39)) = A_38 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_74,plain,(
    k1_mcart_1('#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_65])).

tff(c_49,plain,(
    ! [A_36,B_37] : k2_mcart_1(k4_tarski(A_36,B_37)) = B_37 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_58,plain,(
    k2_mcart_1('#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_49])).

tff(c_40,plain,
    ( k2_mcart_1('#skF_4') = '#skF_4'
    | k1_mcart_1('#skF_4') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_91,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_58,c_40])).

tff(c_92,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_94,plain,(
    k4_tarski('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_42])).

tff(c_34,plain,(
    ! [A_22] :
      ( r2_hidden('#skF_3'(A_22),A_22)
      | k1_xboole_0 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_115,plain,(
    ! [C_42,A_43] :
      ( C_42 = A_43
      | ~ r2_hidden(C_42,k1_tarski(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_123,plain,(
    ! [A_43] :
      ( '#skF_3'(k1_tarski(A_43)) = A_43
      | k1_tarski(A_43) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_115])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_224,plain,(
    ! [C_74,A_75,D_76] :
      ( ~ r2_hidden(C_74,A_75)
      | k4_tarski(C_74,D_76) != '#skF_3'(A_75)
      | k1_xboole_0 = A_75 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_236,plain,(
    ! [C_81,D_82] :
      ( k4_tarski(C_81,D_82) != '#skF_3'(k1_tarski(C_81))
      | k1_tarski(C_81) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_224])).

tff(c_253,plain,(
    ! [A_85,D_86] :
      ( k4_tarski(A_85,D_86) != A_85
      | k1_tarski(A_85) = k1_xboole_0
      | k1_tarski(A_85) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_236])).

tff(c_257,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_253])).

tff(c_126,plain,(
    ! [B_44,A_45] :
      ( ~ r1_tarski(B_44,A_45)
      | ~ r2_hidden(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_134,plain,(
    ! [C_5] : ~ r1_tarski(k1_tarski(C_5),C_5) ),
    inference(resolution,[status(thm)],[c_4,c_126])).

tff(c_274,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_134])).

tff(c_290,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_274])).

tff(c_291,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_294,plain,(
    k4_tarski('#skF_5','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_42])).

tff(c_315,plain,(
    ! [C_89,A_90] :
      ( C_89 = A_90
      | ~ r2_hidden(C_89,k1_tarski(A_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_323,plain,(
    ! [A_90] :
      ( '#skF_3'(k1_tarski(A_90)) = A_90
      | k1_tarski(A_90) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_315])).

tff(c_389,plain,(
    ! [D_106,A_107,C_108] :
      ( ~ r2_hidden(D_106,A_107)
      | k4_tarski(C_108,D_106) != '#skF_3'(A_107)
      | k1_xboole_0 = A_107 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_400,plain,(
    ! [C_111,C_112] :
      ( k4_tarski(C_111,C_112) != '#skF_3'(k1_tarski(C_112))
      | k1_tarski(C_112) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_389])).

tff(c_457,plain,(
    ! [C_134,A_135] :
      ( k4_tarski(C_134,A_135) != A_135
      | k1_tarski(A_135) = k1_xboole_0
      | k1_tarski(A_135) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_400])).

tff(c_461,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_457])).

tff(c_326,plain,(
    ! [B_91,A_92] :
      ( ~ r1_tarski(B_91,A_92)
      | ~ r2_hidden(A_92,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_334,plain,(
    ! [C_5] : ~ r1_tarski(k1_tarski(C_5),C_5) ),
    inference(resolution,[status(thm)],[c_4,c_326])).

tff(c_478,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_461,c_334])).

tff(c_494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_478])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:52:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.34  
% 2.30/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.35  %$ r2_hidden > r1_tarski > m1_subset_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.30/1.35  
% 2.30/1.35  %Foreground sorts:
% 2.30/1.35  
% 2.30/1.35  
% 2.30/1.35  %Background operators:
% 2.30/1.35  
% 2.30/1.35  
% 2.30/1.35  %Foreground operators:
% 2.30/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.30/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.30/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.30/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.30/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.30/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.30/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.30/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.30/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.30/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.30/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.30/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.35  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.30/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.30/1.35  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.30/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.30/1.35  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.30/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.30/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.30/1.35  
% 2.51/1.36  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.51/1.36  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.51/1.36  tff(f_85, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.51/1.36  tff(f_59, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.51/1.36  tff(f_75, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.51/1.36  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.51/1.36  tff(f_55, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.51/1.36  tff(c_20, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.51/1.36  tff(c_336, plain, (![A_94, B_95]: (r1_tarski(A_94, B_95) | ~m1_subset_1(A_94, k1_zfmisc_1(B_95)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.51/1.36  tff(c_340, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(resolution, [status(thm)], [c_20, c_336])).
% 2.51/1.36  tff(c_147, plain, (![A_52, B_53]: (r1_tarski(A_52, B_53) | ~m1_subset_1(A_52, k1_zfmisc_1(B_53)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.51/1.36  tff(c_155, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(resolution, [status(thm)], [c_20, c_147])).
% 2.51/1.36  tff(c_42, plain, (k4_tarski('#skF_5', '#skF_6')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.51/1.36  tff(c_65, plain, (![A_38, B_39]: (k1_mcart_1(k4_tarski(A_38, B_39))=A_38)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.51/1.36  tff(c_74, plain, (k1_mcart_1('#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_42, c_65])).
% 2.51/1.36  tff(c_49, plain, (![A_36, B_37]: (k2_mcart_1(k4_tarski(A_36, B_37))=B_37)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.51/1.36  tff(c_58, plain, (k2_mcart_1('#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_42, c_49])).
% 2.51/1.36  tff(c_40, plain, (k2_mcart_1('#skF_4')='#skF_4' | k1_mcart_1('#skF_4')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.51/1.36  tff(c_91, plain, ('#skF_6'='#skF_4' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_58, c_40])).
% 2.51/1.36  tff(c_92, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_91])).
% 2.51/1.36  tff(c_94, plain, (k4_tarski('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_42])).
% 2.51/1.36  tff(c_34, plain, (![A_22]: (r2_hidden('#skF_3'(A_22), A_22) | k1_xboole_0=A_22)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.51/1.36  tff(c_115, plain, (![C_42, A_43]: (C_42=A_43 | ~r2_hidden(C_42, k1_tarski(A_43)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.51/1.36  tff(c_123, plain, (![A_43]: ('#skF_3'(k1_tarski(A_43))=A_43 | k1_tarski(A_43)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_115])).
% 2.51/1.36  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.51/1.36  tff(c_224, plain, (![C_74, A_75, D_76]: (~r2_hidden(C_74, A_75) | k4_tarski(C_74, D_76)!='#skF_3'(A_75) | k1_xboole_0=A_75)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.51/1.36  tff(c_236, plain, (![C_81, D_82]: (k4_tarski(C_81, D_82)!='#skF_3'(k1_tarski(C_81)) | k1_tarski(C_81)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_224])).
% 2.51/1.36  tff(c_253, plain, (![A_85, D_86]: (k4_tarski(A_85, D_86)!=A_85 | k1_tarski(A_85)=k1_xboole_0 | k1_tarski(A_85)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_123, c_236])).
% 2.51/1.36  tff(c_257, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_94, c_253])).
% 2.51/1.36  tff(c_126, plain, (![B_44, A_45]: (~r1_tarski(B_44, A_45) | ~r2_hidden(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.51/1.36  tff(c_134, plain, (![C_5]: (~r1_tarski(k1_tarski(C_5), C_5))), inference(resolution, [status(thm)], [c_4, c_126])).
% 2.51/1.36  tff(c_274, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_257, c_134])).
% 2.51/1.36  tff(c_290, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_155, c_274])).
% 2.51/1.36  tff(c_291, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_91])).
% 2.51/1.36  tff(c_294, plain, (k4_tarski('#skF_5', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_291, c_42])).
% 2.51/1.36  tff(c_315, plain, (![C_89, A_90]: (C_89=A_90 | ~r2_hidden(C_89, k1_tarski(A_90)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.51/1.36  tff(c_323, plain, (![A_90]: ('#skF_3'(k1_tarski(A_90))=A_90 | k1_tarski(A_90)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_315])).
% 2.51/1.36  tff(c_389, plain, (![D_106, A_107, C_108]: (~r2_hidden(D_106, A_107) | k4_tarski(C_108, D_106)!='#skF_3'(A_107) | k1_xboole_0=A_107)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.51/1.36  tff(c_400, plain, (![C_111, C_112]: (k4_tarski(C_111, C_112)!='#skF_3'(k1_tarski(C_112)) | k1_tarski(C_112)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_389])).
% 2.51/1.36  tff(c_457, plain, (![C_134, A_135]: (k4_tarski(C_134, A_135)!=A_135 | k1_tarski(A_135)=k1_xboole_0 | k1_tarski(A_135)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_323, c_400])).
% 2.51/1.36  tff(c_461, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_294, c_457])).
% 2.51/1.36  tff(c_326, plain, (![B_91, A_92]: (~r1_tarski(B_91, A_92) | ~r2_hidden(A_92, B_91))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.51/1.36  tff(c_334, plain, (![C_5]: (~r1_tarski(k1_tarski(C_5), C_5))), inference(resolution, [status(thm)], [c_4, c_326])).
% 2.51/1.36  tff(c_478, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_461, c_334])).
% 2.51/1.36  tff(c_494, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_340, c_478])).
% 2.51/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.36  
% 2.51/1.36  Inference rules
% 2.51/1.36  ----------------------
% 2.51/1.36  #Ref     : 0
% 2.51/1.36  #Sup     : 113
% 2.51/1.36  #Fact    : 0
% 2.51/1.36  #Define  : 0
% 2.51/1.36  #Split   : 1
% 2.51/1.36  #Chain   : 0
% 2.51/1.36  #Close   : 0
% 2.51/1.36  
% 2.51/1.36  Ordering : KBO
% 2.51/1.36  
% 2.51/1.36  Simplification rules
% 2.51/1.36  ----------------------
% 2.51/1.36  #Subsume      : 5
% 2.51/1.36  #Demod        : 22
% 2.51/1.36  #Tautology    : 58
% 2.51/1.36  #SimpNegUnit  : 0
% 2.51/1.36  #BackRed      : 4
% 2.51/1.36  
% 2.51/1.36  #Partial instantiations: 0
% 2.51/1.36  #Strategies tried      : 1
% 2.51/1.36  
% 2.51/1.36  Timing (in seconds)
% 2.51/1.36  ----------------------
% 2.51/1.36  Preprocessing        : 0.30
% 2.51/1.36  Parsing              : 0.15
% 2.51/1.36  CNF conversion       : 0.02
% 2.51/1.36  Main loop            : 0.25
% 2.51/1.36  Inferencing          : 0.10
% 2.51/1.36  Reduction            : 0.07
% 2.51/1.36  Demodulation         : 0.05
% 2.51/1.37  BG Simplification    : 0.02
% 2.51/1.37  Subsumption          : 0.04
% 2.51/1.37  Abstraction          : 0.02
% 2.51/1.37  MUC search           : 0.00
% 2.51/1.37  Cooper               : 0.00
% 2.51/1.37  Total                : 0.58
% 2.51/1.37  Index Insertion      : 0.00
% 2.51/1.37  Index Deletion       : 0.00
% 2.51/1.37  Index Matching       : 0.00
% 2.51/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
