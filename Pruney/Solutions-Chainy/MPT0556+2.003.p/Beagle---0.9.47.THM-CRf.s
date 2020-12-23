%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:06 EST 2020

% Result     : Theorem 18.46s
% Output     : CNFRefutation 18.57s
% Verified   : 
% Statistics : Number of formulae       :   48 (  75 expanded)
%              Number of leaves         :   21 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :   83 ( 182 expanded)
%              Number of equality atoms :   15 (  34 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k2_xboole_0 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k9_relat_1(C,A),k9_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k9_relat_1(B,A),k9_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k9_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_50,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_48,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_46,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_40,plain,(
    ! [B_25,A_24,C_27] :
      ( r1_tarski(k9_relat_1(B_25,A_24),k9_relat_1(C_27,A_24))
      | ~ r1_tarski(B_25,C_27)
      | ~ v1_relat_1(C_27)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_44,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1028,plain,(
    ! [A_140,B_141,C_142] :
      ( r2_hidden('#skF_2'(A_140,B_141,C_142),B_141)
      | r2_hidden('#skF_2'(A_140,B_141,C_142),A_140)
      | r2_hidden('#skF_3'(A_140,B_141,C_142),C_142)
      | k2_xboole_0(A_140,B_141) = C_142 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [A_8,B_9,C_10] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9,C_10),C_10)
      | r2_hidden('#skF_3'(A_8,B_9,C_10),C_10)
      | k2_xboole_0(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5533,plain,(
    ! [A_337,B_338] :
      ( r2_hidden('#skF_2'(A_337,B_338,A_337),B_338)
      | r2_hidden('#skF_3'(A_337,B_338,A_337),A_337)
      | k2_xboole_0(A_337,B_338) = A_337 ) ),
    inference(resolution,[status(thm)],[c_1028,c_24])).

tff(c_685,plain,(
    ! [A_119,B_120,C_121] :
      ( r2_hidden('#skF_2'(A_119,B_120,C_121),B_120)
      | r2_hidden('#skF_2'(A_119,B_120,C_121),A_119)
      | ~ r2_hidden('#skF_3'(A_119,B_120,C_121),A_119)
      | k2_xboole_0(A_119,B_120) = C_121 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_8,B_9,C_10] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9,C_10),C_10)
      | ~ r2_hidden('#skF_3'(A_8,B_9,C_10),A_8)
      | k2_xboole_0(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_735,plain,(
    ! [A_119,B_120] :
      ( r2_hidden('#skF_2'(A_119,B_120,A_119),B_120)
      | ~ r2_hidden('#skF_3'(A_119,B_120,A_119),A_119)
      | k2_xboole_0(A_119,B_120) = A_119 ) ),
    inference(resolution,[status(thm)],[c_685,c_20])).

tff(c_5627,plain,(
    ! [A_339,B_340] :
      ( r2_hidden('#skF_2'(A_339,B_340,A_339),B_340)
      | k2_xboole_0(A_339,B_340) = A_339 ) ),
    inference(resolution,[status(thm)],[c_5533,c_735])).

tff(c_4,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12290,plain,(
    ! [A_479,B_480,B_481] :
      ( r2_hidden('#skF_2'(A_479,B_480,A_479),B_481)
      | ~ r1_tarski(B_480,B_481)
      | k2_xboole_0(A_479,B_480) = A_479 ) ),
    inference(resolution,[status(thm)],[c_5627,c_4])).

tff(c_17152,plain,(
    ! [B_599,B_600] :
      ( r2_hidden('#skF_3'(B_599,B_600,B_599),B_599)
      | ~ r1_tarski(B_600,B_599)
      | k2_xboole_0(B_599,B_600) = B_599 ) ),
    inference(resolution,[status(thm)],[c_12290,c_24])).

tff(c_12350,plain,(
    ! [B_481,B_480] :
      ( ~ r2_hidden('#skF_3'(B_481,B_480,B_481),B_481)
      | ~ r1_tarski(B_480,B_481)
      | k2_xboole_0(B_481,B_480) = B_481 ) ),
    inference(resolution,[status(thm)],[c_12290,c_20])).

tff(c_17271,plain,(
    ! [B_601,B_602] :
      ( ~ r1_tarski(B_601,B_602)
      | k2_xboole_0(B_602,B_601) = B_602 ) ),
    inference(resolution,[status(thm)],[c_17152,c_12350])).

tff(c_17392,plain,(
    k2_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_44,c_17271])).

tff(c_257,plain,(
    ! [C_66,A_67,B_68] :
      ( k2_xboole_0(k9_relat_1(C_66,A_67),k9_relat_1(C_66,B_68)) = k9_relat_1(C_66,k2_xboole_0(A_67,B_68))
      | ~ v1_relat_1(C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_34,plain,(
    ! [A_16,C_18,B_17] :
      ( r1_tarski(A_16,k2_xboole_0(C_18,B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_284,plain,(
    ! [A_16,C_66,A_67,B_68] :
      ( r1_tarski(A_16,k9_relat_1(C_66,k2_xboole_0(A_67,B_68)))
      | ~ r1_tarski(A_16,k9_relat_1(C_66,B_68))
      | ~ v1_relat_1(C_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_34])).

tff(c_41605,plain,(
    ! [A_849,C_850] :
      ( r1_tarski(A_849,k9_relat_1(C_850,'#skF_5'))
      | ~ r1_tarski(A_849,k9_relat_1(C_850,'#skF_4'))
      | ~ v1_relat_1(C_850) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17392,c_284])).

tff(c_42,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_4'),k9_relat_1('#skF_7','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_41766,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_6','#skF_4'),k9_relat_1('#skF_7','#skF_4'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_41605,c_42])).

tff(c_41816,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_4'),k9_relat_1('#skF_7','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_41766])).

tff(c_41819,plain,
    ( ~ r1_tarski('#skF_6','#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_41816])).

tff(c_41823,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_41819])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:22:42 EST 2020
% 0.21/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.46/8.88  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.46/8.89  
% 18.46/8.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.46/8.89  %$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k2_xboole_0 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 18.46/8.89  
% 18.46/8.89  %Foreground sorts:
% 18.46/8.89  
% 18.46/8.89  
% 18.46/8.89  %Background operators:
% 18.46/8.89  
% 18.46/8.89  
% 18.46/8.89  %Foreground operators:
% 18.46/8.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.46/8.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 18.46/8.89  tff('#skF_7', type, '#skF_7': $i).
% 18.46/8.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.46/8.89  tff('#skF_5', type, '#skF_5': $i).
% 18.46/8.89  tff('#skF_6', type, '#skF_6': $i).
% 18.46/8.89  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 18.46/8.89  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 18.46/8.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.46/8.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 18.46/8.89  tff('#skF_4', type, '#skF_4': $i).
% 18.46/8.89  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 18.46/8.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.46/8.89  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 18.46/8.89  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 18.46/8.89  
% 18.57/8.90  tff(f_80, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k9_relat_1(C, A), k9_relat_1(D, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_relat_1)).
% 18.57/8.90  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k9_relat_1(B, A), k9_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_relat_1)).
% 18.57/8.90  tff(f_43, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 18.57/8.90  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 18.57/8.90  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (k9_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t153_relat_1)).
% 18.57/8.90  tff(f_53, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 18.57/8.90  tff(c_50, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_80])).
% 18.57/8.90  tff(c_48, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_80])).
% 18.57/8.90  tff(c_46, plain, (r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_80])).
% 18.57/8.90  tff(c_40, plain, (![B_25, A_24, C_27]: (r1_tarski(k9_relat_1(B_25, A_24), k9_relat_1(C_27, A_24)) | ~r1_tarski(B_25, C_27) | ~v1_relat_1(C_27) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_68])).
% 18.57/8.90  tff(c_44, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 18.57/8.90  tff(c_1028, plain, (![A_140, B_141, C_142]: (r2_hidden('#skF_2'(A_140, B_141, C_142), B_141) | r2_hidden('#skF_2'(A_140, B_141, C_142), A_140) | r2_hidden('#skF_3'(A_140, B_141, C_142), C_142) | k2_xboole_0(A_140, B_141)=C_142)), inference(cnfTransformation, [status(thm)], [f_43])).
% 18.57/8.90  tff(c_24, plain, (![A_8, B_9, C_10]: (~r2_hidden('#skF_2'(A_8, B_9, C_10), C_10) | r2_hidden('#skF_3'(A_8, B_9, C_10), C_10) | k2_xboole_0(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_43])).
% 18.57/8.90  tff(c_5533, plain, (![A_337, B_338]: (r2_hidden('#skF_2'(A_337, B_338, A_337), B_338) | r2_hidden('#skF_3'(A_337, B_338, A_337), A_337) | k2_xboole_0(A_337, B_338)=A_337)), inference(resolution, [status(thm)], [c_1028, c_24])).
% 18.57/8.90  tff(c_685, plain, (![A_119, B_120, C_121]: (r2_hidden('#skF_2'(A_119, B_120, C_121), B_120) | r2_hidden('#skF_2'(A_119, B_120, C_121), A_119) | ~r2_hidden('#skF_3'(A_119, B_120, C_121), A_119) | k2_xboole_0(A_119, B_120)=C_121)), inference(cnfTransformation, [status(thm)], [f_43])).
% 18.57/8.90  tff(c_20, plain, (![A_8, B_9, C_10]: (~r2_hidden('#skF_2'(A_8, B_9, C_10), C_10) | ~r2_hidden('#skF_3'(A_8, B_9, C_10), A_8) | k2_xboole_0(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_43])).
% 18.57/8.90  tff(c_735, plain, (![A_119, B_120]: (r2_hidden('#skF_2'(A_119, B_120, A_119), B_120) | ~r2_hidden('#skF_3'(A_119, B_120, A_119), A_119) | k2_xboole_0(A_119, B_120)=A_119)), inference(resolution, [status(thm)], [c_685, c_20])).
% 18.57/8.90  tff(c_5627, plain, (![A_339, B_340]: (r2_hidden('#skF_2'(A_339, B_340, A_339), B_340) | k2_xboole_0(A_339, B_340)=A_339)), inference(resolution, [status(thm)], [c_5533, c_735])).
% 18.57/8.90  tff(c_4, plain, (![C_7, B_4, A_3]: (r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 18.57/8.90  tff(c_12290, plain, (![A_479, B_480, B_481]: (r2_hidden('#skF_2'(A_479, B_480, A_479), B_481) | ~r1_tarski(B_480, B_481) | k2_xboole_0(A_479, B_480)=A_479)), inference(resolution, [status(thm)], [c_5627, c_4])).
% 18.57/8.90  tff(c_17152, plain, (![B_599, B_600]: (r2_hidden('#skF_3'(B_599, B_600, B_599), B_599) | ~r1_tarski(B_600, B_599) | k2_xboole_0(B_599, B_600)=B_599)), inference(resolution, [status(thm)], [c_12290, c_24])).
% 18.57/8.90  tff(c_12350, plain, (![B_481, B_480]: (~r2_hidden('#skF_3'(B_481, B_480, B_481), B_481) | ~r1_tarski(B_480, B_481) | k2_xboole_0(B_481, B_480)=B_481)), inference(resolution, [status(thm)], [c_12290, c_20])).
% 18.57/8.90  tff(c_17271, plain, (![B_601, B_602]: (~r1_tarski(B_601, B_602) | k2_xboole_0(B_602, B_601)=B_602)), inference(resolution, [status(thm)], [c_17152, c_12350])).
% 18.57/8.90  tff(c_17392, plain, (k2_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_44, c_17271])).
% 18.57/8.90  tff(c_257, plain, (![C_66, A_67, B_68]: (k2_xboole_0(k9_relat_1(C_66, A_67), k9_relat_1(C_66, B_68))=k9_relat_1(C_66, k2_xboole_0(A_67, B_68)) | ~v1_relat_1(C_66))), inference(cnfTransformation, [status(thm)], [f_59])).
% 18.57/8.90  tff(c_34, plain, (![A_16, C_18, B_17]: (r1_tarski(A_16, k2_xboole_0(C_18, B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 18.57/8.90  tff(c_284, plain, (![A_16, C_66, A_67, B_68]: (r1_tarski(A_16, k9_relat_1(C_66, k2_xboole_0(A_67, B_68))) | ~r1_tarski(A_16, k9_relat_1(C_66, B_68)) | ~v1_relat_1(C_66))), inference(superposition, [status(thm), theory('equality')], [c_257, c_34])).
% 18.57/8.90  tff(c_41605, plain, (![A_849, C_850]: (r1_tarski(A_849, k9_relat_1(C_850, '#skF_5')) | ~r1_tarski(A_849, k9_relat_1(C_850, '#skF_4')) | ~v1_relat_1(C_850))), inference(superposition, [status(thm), theory('equality')], [c_17392, c_284])).
% 18.57/8.90  tff(c_42, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_4'), k9_relat_1('#skF_7', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 18.57/8.90  tff(c_41766, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_4'), k9_relat_1('#skF_7', '#skF_4')) | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_41605, c_42])).
% 18.57/8.90  tff(c_41816, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_4'), k9_relat_1('#skF_7', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_41766])).
% 18.57/8.90  tff(c_41819, plain, (~r1_tarski('#skF_6', '#skF_7') | ~v1_relat_1('#skF_7') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_40, c_41816])).
% 18.57/8.90  tff(c_41823, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_41819])).
% 18.57/8.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.57/8.90  
% 18.57/8.90  Inference rules
% 18.57/8.90  ----------------------
% 18.57/8.90  #Ref     : 0
% 18.57/8.90  #Sup     : 10820
% 18.57/8.90  #Fact    : 46
% 18.57/8.90  #Define  : 0
% 18.57/8.90  #Split   : 10
% 18.57/8.90  #Chain   : 0
% 18.57/8.90  #Close   : 0
% 18.57/8.90  
% 18.57/8.90  Ordering : KBO
% 18.57/8.90  
% 18.57/8.90  Simplification rules
% 18.57/8.90  ----------------------
% 18.57/8.90  #Subsume      : 3545
% 18.57/8.90  #Demod        : 5529
% 18.57/8.90  #Tautology    : 1241
% 18.57/8.90  #SimpNegUnit  : 10
% 18.57/8.90  #BackRed      : 3
% 18.57/8.90  
% 18.57/8.90  #Partial instantiations: 0
% 18.57/8.90  #Strategies tried      : 1
% 18.57/8.90  
% 18.57/8.90  Timing (in seconds)
% 18.57/8.90  ----------------------
% 18.57/8.90  Preprocessing        : 0.32
% 18.57/8.90  Parsing              : 0.17
% 18.57/8.90  CNF conversion       : 0.03
% 18.57/8.90  Main loop            : 7.81
% 18.57/8.90  Inferencing          : 1.13
% 18.57/8.90  Reduction            : 2.59
% 18.57/8.90  Demodulation         : 2.14
% 18.57/8.90  BG Simplification    : 0.16
% 18.57/8.91  Subsumption          : 3.48
% 18.57/8.91  Abstraction          : 0.22
% 18.57/8.91  MUC search           : 0.00
% 18.57/8.91  Cooper               : 0.00
% 18.57/8.91  Total                : 8.16
% 18.57/8.91  Index Insertion      : 0.00
% 18.57/8.91  Index Deletion       : 0.00
% 18.57/8.91  Index Matching       : 0.00
% 18.57/8.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
