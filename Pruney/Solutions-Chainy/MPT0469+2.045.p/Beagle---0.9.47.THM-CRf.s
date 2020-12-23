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
% DateTime   : Thu Dec  3 09:58:57 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 4.07s
% Verified   : 
% Statistics : Number of formulae       :   58 (  92 expanded)
%              Number of leaves         :   32 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 ( 110 expanded)
%              Number of equality atoms :   16 (  25 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_8 > #skF_7 > #skF_2 > #skF_5 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_77,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k1_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_relat_1)).

tff(c_40,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_52,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_345,plain,(
    ! [A_125,B_126] :
      ( r2_hidden(k4_tarski('#skF_5'(A_125,B_126),'#skF_4'(A_125,B_126)),A_125)
      | r2_hidden('#skF_6'(A_125,B_126),B_126)
      | k2_relat_1(A_125) = B_126 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_62,plain,(
    ! [A_77,B_78] :
      ( ~ r2_hidden(A_77,B_78)
      | ~ r1_xboole_0(k1_tarski(A_77),B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_67,plain,(
    ! [A_77] : ~ r2_hidden(A_77,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_62])).

tff(c_1377,plain,(
    ! [B_169] :
      ( r2_hidden('#skF_6'(k1_xboole_0,B_169),B_169)
      | k2_relat_1(k1_xboole_0) = B_169 ) ),
    inference(resolution,[status(thm)],[c_345,c_67])).

tff(c_1533,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1377,c_67])).

tff(c_24,plain,(
    ! [A_32] :
      ( r2_hidden('#skF_1'(A_32),A_32)
      | v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_68,plain,(
    ! [A_79] : ~ r2_hidden(A_79,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_62])).

tff(c_73,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_68])).

tff(c_38,plain,(
    ! [A_69,B_70] :
      ( r2_hidden('#skF_8'(A_69,B_70),k2_relat_1(B_70))
      | ~ r2_hidden(A_69,k1_relat_1(B_70))
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_95,plain,(
    ! [A_95,C_96] :
      ( r2_hidden(k4_tarski('#skF_7'(A_95,k2_relat_1(A_95),C_96),C_96),A_95)
      | ~ r2_hidden(C_96,k2_relat_1(A_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_111,plain,(
    ! [C_99] : ~ r2_hidden(C_99,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_95,c_67])).

tff(c_123,plain,(
    ! [A_69] :
      ( ~ r2_hidden(A_69,k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_38,c_111])).

tff(c_132,plain,(
    ! [A_69] : ~ r2_hidden(A_69,k1_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_123])).

tff(c_1530,plain,(
    k2_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1377,c_132])).

tff(c_1658,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1533,c_1530])).

tff(c_1659,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1658])).

tff(c_1660,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1965,plain,(
    ! [A_221,B_222] :
      ( r2_hidden(k4_tarski('#skF_5'(A_221,B_222),'#skF_4'(A_221,B_222)),A_221)
      | r2_hidden('#skF_6'(A_221,B_222),B_222)
      | k2_relat_1(A_221) = B_222 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1676,plain,(
    ! [A_176,B_177] :
      ( ~ r2_hidden(A_176,B_177)
      | ~ r1_xboole_0(k1_tarski(A_176),B_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1681,plain,(
    ! [A_176] : ~ r2_hidden(A_176,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_1676])).

tff(c_2151,plain,(
    ! [B_238] :
      ( r2_hidden('#skF_6'(k1_xboole_0,B_238),B_238)
      | k2_relat_1(k1_xboole_0) = B_238 ) ),
    inference(resolution,[status(thm)],[c_1965,c_1681])).

tff(c_2215,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2151,c_1681])).

tff(c_2235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1660,c_2215])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:14:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.74/1.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/1.68  
% 4.07/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/1.69  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_8 > #skF_7 > #skF_2 > #skF_5 > #skF_4
% 4.07/1.69  
% 4.07/1.69  %Foreground sorts:
% 4.07/1.69  
% 4.07/1.69  
% 4.07/1.69  %Background operators:
% 4.07/1.69  
% 4.07/1.69  
% 4.07/1.69  %Foreground operators:
% 4.07/1.69  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.07/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.07/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.07/1.69  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.07/1.69  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.07/1.69  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.07/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.07/1.69  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.07/1.69  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.07/1.69  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.07/1.69  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.07/1.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.07/1.69  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.07/1.69  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.07/1.69  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 4.07/1.69  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.07/1.69  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 4.07/1.69  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.07/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.07/1.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.07/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.07/1.69  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.07/1.69  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.07/1.69  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.07/1.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.07/1.69  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.07/1.69  
% 4.07/1.70  tff(f_77, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 4.07/1.70  tff(f_64, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 4.07/1.70  tff(f_27, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.07/1.70  tff(f_46, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 4.07/1.70  tff(f_56, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 4.07/1.70  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k1_relat_1(B)) & (![C]: ~r2_hidden(C, k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_relat_1)).
% 4.07/1.70  tff(c_40, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.07/1.70  tff(c_52, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_40])).
% 4.07/1.70  tff(c_345, plain, (![A_125, B_126]: (r2_hidden(k4_tarski('#skF_5'(A_125, B_126), '#skF_4'(A_125, B_126)), A_125) | r2_hidden('#skF_6'(A_125, B_126), B_126) | k2_relat_1(A_125)=B_126)), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.07/1.70  tff(c_2, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.07/1.70  tff(c_62, plain, (![A_77, B_78]: (~r2_hidden(A_77, B_78) | ~r1_xboole_0(k1_tarski(A_77), B_78))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.07/1.70  tff(c_67, plain, (![A_77]: (~r2_hidden(A_77, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_62])).
% 4.07/1.70  tff(c_1377, plain, (![B_169]: (r2_hidden('#skF_6'(k1_xboole_0, B_169), B_169) | k2_relat_1(k1_xboole_0)=B_169)), inference(resolution, [status(thm)], [c_345, c_67])).
% 4.07/1.70  tff(c_1533, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1377, c_67])).
% 4.07/1.70  tff(c_24, plain, (![A_32]: (r2_hidden('#skF_1'(A_32), A_32) | v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.07/1.70  tff(c_68, plain, (![A_79]: (~r2_hidden(A_79, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_62])).
% 4.07/1.70  tff(c_73, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_68])).
% 4.07/1.70  tff(c_38, plain, (![A_69, B_70]: (r2_hidden('#skF_8'(A_69, B_70), k2_relat_1(B_70)) | ~r2_hidden(A_69, k1_relat_1(B_70)) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.07/1.70  tff(c_95, plain, (![A_95, C_96]: (r2_hidden(k4_tarski('#skF_7'(A_95, k2_relat_1(A_95), C_96), C_96), A_95) | ~r2_hidden(C_96, k2_relat_1(A_95)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.07/1.70  tff(c_111, plain, (![C_99]: (~r2_hidden(C_99, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_95, c_67])).
% 4.07/1.70  tff(c_123, plain, (![A_69]: (~r2_hidden(A_69, k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_38, c_111])).
% 4.07/1.70  tff(c_132, plain, (![A_69]: (~r2_hidden(A_69, k1_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_123])).
% 4.07/1.70  tff(c_1530, plain, (k2_relat_1(k1_xboole_0)=k1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_1377, c_132])).
% 4.07/1.70  tff(c_1658, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1533, c_1530])).
% 4.07/1.70  tff(c_1659, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_1658])).
% 4.07/1.70  tff(c_1660, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 4.07/1.70  tff(c_1965, plain, (![A_221, B_222]: (r2_hidden(k4_tarski('#skF_5'(A_221, B_222), '#skF_4'(A_221, B_222)), A_221) | r2_hidden('#skF_6'(A_221, B_222), B_222) | k2_relat_1(A_221)=B_222)), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.07/1.70  tff(c_1676, plain, (![A_176, B_177]: (~r2_hidden(A_176, B_177) | ~r1_xboole_0(k1_tarski(A_176), B_177))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.07/1.70  tff(c_1681, plain, (![A_176]: (~r2_hidden(A_176, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_1676])).
% 4.07/1.70  tff(c_2151, plain, (![B_238]: (r2_hidden('#skF_6'(k1_xboole_0, B_238), B_238) | k2_relat_1(k1_xboole_0)=B_238)), inference(resolution, [status(thm)], [c_1965, c_1681])).
% 4.07/1.70  tff(c_2215, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2151, c_1681])).
% 4.07/1.70  tff(c_2235, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1660, c_2215])).
% 4.07/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/1.70  
% 4.07/1.70  Inference rules
% 4.07/1.70  ----------------------
% 4.07/1.70  #Ref     : 1
% 4.07/1.70  #Sup     : 411
% 4.07/1.70  #Fact    : 0
% 4.07/1.70  #Define  : 0
% 4.07/1.70  #Split   : 1
% 4.07/1.70  #Chain   : 0
% 4.07/1.70  #Close   : 0
% 4.07/1.70  
% 4.07/1.70  Ordering : KBO
% 4.07/1.70  
% 4.07/1.70  Simplification rules
% 4.07/1.70  ----------------------
% 4.07/1.70  #Subsume      : 99
% 4.07/1.70  #Demod        : 102
% 4.07/1.70  #Tautology    : 54
% 4.07/1.70  #SimpNegUnit  : 6
% 4.07/1.70  #BackRed      : 32
% 4.07/1.70  
% 4.07/1.70  #Partial instantiations: 0
% 4.07/1.70  #Strategies tried      : 1
% 4.07/1.70  
% 4.07/1.70  Timing (in seconds)
% 4.07/1.70  ----------------------
% 4.07/1.70  Preprocessing        : 0.33
% 4.07/1.70  Parsing              : 0.17
% 4.07/1.70  CNF conversion       : 0.02
% 4.07/1.70  Main loop            : 0.60
% 4.07/1.70  Inferencing          : 0.22
% 4.07/1.70  Reduction            : 0.18
% 4.07/1.70  Demodulation         : 0.10
% 4.07/1.70  BG Simplification    : 0.03
% 4.07/1.70  Subsumption          : 0.12
% 4.07/1.70  Abstraction          : 0.03
% 4.07/1.70  MUC search           : 0.00
% 4.07/1.70  Cooper               : 0.00
% 4.07/1.70  Total                : 0.96
% 4.07/1.70  Index Insertion      : 0.00
% 4.07/1.70  Index Deletion       : 0.00
% 4.07/1.70  Index Matching       : 0.00
% 4.07/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
