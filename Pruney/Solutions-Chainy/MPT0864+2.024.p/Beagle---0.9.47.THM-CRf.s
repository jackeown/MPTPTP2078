%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:11 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 103 expanded)
%              Number of leaves         :   28 (  49 expanded)
%              Depth                    :    8
%              Number of atoms          :   79 ( 158 expanded)
%              Number of equality atoms :   46 ( 102 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k4_tarski > k2_tarski > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_7 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_80,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_34,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_444,plain,(
    ! [A_114,B_115] :
      ( r1_tarski(A_114,B_115)
      | ~ m1_subset_1(A_114,k1_zfmisc_1(B_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_448,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(resolution,[status(thm)],[c_34,c_444])).

tff(c_172,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,B_55)
      | ~ m1_subset_1(A_54,k1_zfmisc_1(B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_176,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(resolution,[status(thm)],[c_34,c_172])).

tff(c_56,plain,(
    k4_tarski('#skF_7','#skF_8') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_81,plain,(
    ! [A_43,B_44] : k1_mcart_1(k4_tarski(A_43,B_44)) = A_43 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_90,plain,(
    k1_mcart_1('#skF_6') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_81])).

tff(c_65,plain,(
    ! [A_41,B_42] : k2_mcart_1(k4_tarski(A_41,B_42)) = B_42 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_74,plain,(
    k2_mcart_1('#skF_6') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_65])).

tff(c_54,plain,
    ( k2_mcart_1('#skF_6') = '#skF_6'
    | k1_mcart_1('#skF_6') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_97,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_74,c_54])).

tff(c_98,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_100,plain,(
    k4_tarski('#skF_6','#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_56])).

tff(c_48,plain,(
    ! [A_23] :
      ( r2_hidden('#skF_5'(A_23),A_23)
      | k1_xboole_0 = A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_139,plain,(
    ! [C_47,A_48] :
      ( C_47 = A_48
      | ~ r2_hidden(C_47,k1_tarski(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_147,plain,(
    ! [A_48] :
      ( '#skF_5'(k1_tarski(A_48)) = A_48
      | k1_tarski(A_48) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_48,c_139])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_230,plain,(
    ! [C_66,A_67,D_68] :
      ( ~ r2_hidden(C_66,A_67)
      | k4_tarski(C_66,D_68) != '#skF_5'(A_67)
      | k1_xboole_0 = A_67 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_247,plain,(
    ! [C_71,D_72] :
      ( k4_tarski(C_71,D_72) != '#skF_5'(k1_tarski(C_71))
      | k1_tarski(C_71) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_230])).

tff(c_321,plain,(
    ! [A_100,D_101] :
      ( k4_tarski(A_100,D_101) != A_100
      | k1_tarski(A_100) = k1_xboole_0
      | k1_tarski(A_100) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_247])).

tff(c_325,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_321])).

tff(c_150,plain,(
    ! [B_49,A_50] :
      ( ~ r1_tarski(B_49,A_50)
      | ~ r2_hidden(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_166,plain,(
    ! [C_5] : ~ r1_tarski(k1_tarski(C_5),C_5) ),
    inference(resolution,[status(thm)],[c_4,c_150])).

tff(c_341,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_166])).

tff(c_357,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_341])).

tff(c_358,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_362,plain,(
    k4_tarski('#skF_7','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_56])).

tff(c_433,plain,(
    ! [A_112] :
      ( r2_hidden('#skF_5'(A_112),A_112)
      | k1_xboole_0 = A_112 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_441,plain,(
    ! [A_1] :
      ( '#skF_5'(k1_tarski(A_1)) = A_1
      | k1_tarski(A_1) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_433,c_2])).

tff(c_518,plain,(
    ! [D_130,A_131,C_132] :
      ( ~ r2_hidden(D_130,A_131)
      | k4_tarski(C_132,D_130) != '#skF_5'(A_131)
      | k1_xboole_0 = A_131 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_548,plain,(
    ! [C_140,C_141] :
      ( k4_tarski(C_140,C_141) != '#skF_5'(k1_tarski(C_141))
      | k1_tarski(C_141) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_518])).

tff(c_588,plain,(
    ! [C_157,A_158] :
      ( k4_tarski(C_157,A_158) != A_158
      | k1_tarski(A_158) = k1_xboole_0
      | k1_tarski(A_158) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_441,c_548])).

tff(c_592,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_588])).

tff(c_405,plain,(
    ! [B_103,A_104] :
      ( ~ r1_tarski(B_103,A_104)
      | ~ r2_hidden(A_104,B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_417,plain,(
    ! [C_5] : ~ r1_tarski(k1_tarski(C_5),C_5) ),
    inference(resolution,[status(thm)],[c_4,c_405])).

tff(c_609,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_592,c_417])).

tff(c_625,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_609])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:48:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.32  
% 2.11/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.32  %$ r2_hidden > r1_tarski > m1_subset_1 > k4_tarski > k2_tarski > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_7 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1
% 2.53/1.32  
% 2.53/1.32  %Foreground sorts:
% 2.53/1.32  
% 2.53/1.32  
% 2.53/1.32  %Background operators:
% 2.53/1.32  
% 2.53/1.32  
% 2.53/1.32  %Foreground operators:
% 2.53/1.32  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.53/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.53/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.53/1.32  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.53/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.53/1.32  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.53/1.32  tff('#skF_7', type, '#skF_7': $i).
% 2.53/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.53/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.53/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.53/1.32  tff('#skF_8', type, '#skF_8': $i).
% 2.53/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.32  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.53/1.32  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.53/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.53/1.32  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.53/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.53/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.53/1.32  
% 2.53/1.34  tff(f_45, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.53/1.34  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.53/1.34  tff(f_90, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.53/1.34  tff(f_64, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.53/1.34  tff(f_80, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.53/1.34  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.53/1.34  tff(f_60, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.53/1.34  tff(c_34, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.53/1.34  tff(c_444, plain, (![A_114, B_115]: (r1_tarski(A_114, B_115) | ~m1_subset_1(A_114, k1_zfmisc_1(B_115)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.53/1.34  tff(c_448, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(resolution, [status(thm)], [c_34, c_444])).
% 2.53/1.34  tff(c_172, plain, (![A_54, B_55]: (r1_tarski(A_54, B_55) | ~m1_subset_1(A_54, k1_zfmisc_1(B_55)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.53/1.34  tff(c_176, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(resolution, [status(thm)], [c_34, c_172])).
% 2.53/1.34  tff(c_56, plain, (k4_tarski('#skF_7', '#skF_8')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.53/1.34  tff(c_81, plain, (![A_43, B_44]: (k1_mcart_1(k4_tarski(A_43, B_44))=A_43)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.53/1.34  tff(c_90, plain, (k1_mcart_1('#skF_6')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_56, c_81])).
% 2.53/1.34  tff(c_65, plain, (![A_41, B_42]: (k2_mcart_1(k4_tarski(A_41, B_42))=B_42)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.53/1.34  tff(c_74, plain, (k2_mcart_1('#skF_6')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_56, c_65])).
% 2.53/1.34  tff(c_54, plain, (k2_mcart_1('#skF_6')='#skF_6' | k1_mcart_1('#skF_6')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.53/1.34  tff(c_97, plain, ('#skF_6'='#skF_8' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_74, c_54])).
% 2.53/1.34  tff(c_98, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_97])).
% 2.53/1.34  tff(c_100, plain, (k4_tarski('#skF_6', '#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_56])).
% 2.53/1.34  tff(c_48, plain, (![A_23]: (r2_hidden('#skF_5'(A_23), A_23) | k1_xboole_0=A_23)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.53/1.34  tff(c_139, plain, (![C_47, A_48]: (C_47=A_48 | ~r2_hidden(C_47, k1_tarski(A_48)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.53/1.34  tff(c_147, plain, (![A_48]: ('#skF_5'(k1_tarski(A_48))=A_48 | k1_tarski(A_48)=k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_139])).
% 2.53/1.34  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.53/1.34  tff(c_230, plain, (![C_66, A_67, D_68]: (~r2_hidden(C_66, A_67) | k4_tarski(C_66, D_68)!='#skF_5'(A_67) | k1_xboole_0=A_67)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.53/1.34  tff(c_247, plain, (![C_71, D_72]: (k4_tarski(C_71, D_72)!='#skF_5'(k1_tarski(C_71)) | k1_tarski(C_71)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_230])).
% 2.53/1.34  tff(c_321, plain, (![A_100, D_101]: (k4_tarski(A_100, D_101)!=A_100 | k1_tarski(A_100)=k1_xboole_0 | k1_tarski(A_100)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_147, c_247])).
% 2.53/1.34  tff(c_325, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_100, c_321])).
% 2.53/1.34  tff(c_150, plain, (![B_49, A_50]: (~r1_tarski(B_49, A_50) | ~r2_hidden(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.53/1.34  tff(c_166, plain, (![C_5]: (~r1_tarski(k1_tarski(C_5), C_5))), inference(resolution, [status(thm)], [c_4, c_150])).
% 2.53/1.34  tff(c_341, plain, (~r1_tarski(k1_xboole_0, '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_325, c_166])).
% 2.53/1.34  tff(c_357, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_176, c_341])).
% 2.53/1.34  tff(c_358, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_97])).
% 2.53/1.34  tff(c_362, plain, (k4_tarski('#skF_7', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_358, c_56])).
% 2.53/1.34  tff(c_433, plain, (![A_112]: (r2_hidden('#skF_5'(A_112), A_112) | k1_xboole_0=A_112)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.53/1.34  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.53/1.34  tff(c_441, plain, (![A_1]: ('#skF_5'(k1_tarski(A_1))=A_1 | k1_tarski(A_1)=k1_xboole_0)), inference(resolution, [status(thm)], [c_433, c_2])).
% 2.53/1.34  tff(c_518, plain, (![D_130, A_131, C_132]: (~r2_hidden(D_130, A_131) | k4_tarski(C_132, D_130)!='#skF_5'(A_131) | k1_xboole_0=A_131)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.53/1.34  tff(c_548, plain, (![C_140, C_141]: (k4_tarski(C_140, C_141)!='#skF_5'(k1_tarski(C_141)) | k1_tarski(C_141)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_518])).
% 2.53/1.34  tff(c_588, plain, (![C_157, A_158]: (k4_tarski(C_157, A_158)!=A_158 | k1_tarski(A_158)=k1_xboole_0 | k1_tarski(A_158)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_441, c_548])).
% 2.53/1.34  tff(c_592, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_362, c_588])).
% 2.53/1.34  tff(c_405, plain, (![B_103, A_104]: (~r1_tarski(B_103, A_104) | ~r2_hidden(A_104, B_103))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.53/1.34  tff(c_417, plain, (![C_5]: (~r1_tarski(k1_tarski(C_5), C_5))), inference(resolution, [status(thm)], [c_4, c_405])).
% 2.53/1.34  tff(c_609, plain, (~r1_tarski(k1_xboole_0, '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_592, c_417])).
% 2.53/1.34  tff(c_625, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_448, c_609])).
% 2.53/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.34  
% 2.53/1.34  Inference rules
% 2.53/1.34  ----------------------
% 2.53/1.34  #Ref     : 0
% 2.53/1.34  #Sup     : 144
% 2.53/1.34  #Fact    : 0
% 2.53/1.34  #Define  : 0
% 2.53/1.34  #Split   : 1
% 2.53/1.34  #Chain   : 0
% 2.53/1.34  #Close   : 0
% 2.53/1.34  
% 2.53/1.34  Ordering : KBO
% 2.53/1.34  
% 2.53/1.34  Simplification rules
% 2.53/1.34  ----------------------
% 2.53/1.34  #Subsume      : 14
% 2.53/1.34  #Demod        : 28
% 2.53/1.34  #Tautology    : 62
% 2.53/1.34  #SimpNegUnit  : 0
% 2.53/1.34  #BackRed      : 5
% 2.53/1.34  
% 2.53/1.34  #Partial instantiations: 0
% 2.53/1.34  #Strategies tried      : 1
% 2.53/1.34  
% 2.53/1.34  Timing (in seconds)
% 2.53/1.34  ----------------------
% 2.53/1.34  Preprocessing        : 0.30
% 2.53/1.34  Parsing              : 0.15
% 2.53/1.34  CNF conversion       : 0.02
% 2.53/1.34  Main loop            : 0.27
% 2.53/1.34  Inferencing          : 0.10
% 2.53/1.34  Reduction            : 0.07
% 2.53/1.34  Demodulation         : 0.05
% 2.53/1.34  BG Simplification    : 0.02
% 2.53/1.34  Subsumption          : 0.05
% 2.53/1.34  Abstraction          : 0.02
% 2.53/1.34  MUC search           : 0.00
% 2.53/1.34  Cooper               : 0.00
% 2.53/1.34  Total                : 0.60
% 2.53/1.34  Index Insertion      : 0.00
% 2.53/1.34  Index Deletion       : 0.00
% 2.53/1.34  Index Matching       : 0.00
% 2.53/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
