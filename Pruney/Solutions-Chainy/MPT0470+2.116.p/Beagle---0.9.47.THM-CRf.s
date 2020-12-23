%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:17 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :   47 (  97 expanded)
%              Number of leaves         :   24 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :   72 ( 158 expanded)
%              Number of equality atoms :   24 (  64 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_3 > #skF_10 > #skF_5 > #skF_7 > #skF_9 > #skF_2 > #skF_8

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( C = k5_relat_1(A,B)
              <=> ! [D,E] :
                    ( r2_hidden(k4_tarski(D,E),C)
                  <=> ? [F] :
                        ( r2_hidden(k4_tarski(D,F),A)
                        & r2_hidden(k4_tarski(F,E),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

tff(c_34,plain,
    ( k5_relat_1('#skF_10',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_10') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_74,plain,(
    k5_relat_1(k1_xboole_0,'#skF_10') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_36,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_67,plain,(
    ! [A_127] :
      ( r2_hidden('#skF_1'(A_127),A_127)
      | v1_relat_1(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ! [A_124,B_125] : ~ r2_hidden(A_124,k2_zfmisc_1(A_124,B_125)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_62,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_59])).

tff(c_72,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_67,c_62])).

tff(c_549,plain,(
    ! [A_210,B_211,C_212] :
      ( r2_hidden(k4_tarski('#skF_5'(A_210,B_211,C_212),'#skF_7'(A_210,B_211,C_212)),A_210)
      | r2_hidden(k4_tarski('#skF_8'(A_210,B_211,C_212),'#skF_9'(A_210,B_211,C_212)),C_212)
      | k5_relat_1(A_210,B_211) = C_212
      | ~ v1_relat_1(C_212)
      | ~ v1_relat_1(B_211)
      | ~ v1_relat_1(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_588,plain,(
    ! [B_211,C_212] :
      ( r2_hidden(k4_tarski('#skF_8'(k1_xboole_0,B_211,C_212),'#skF_9'(k1_xboole_0,B_211,C_212)),C_212)
      | k5_relat_1(k1_xboole_0,B_211) = C_212
      | ~ v1_relat_1(C_212)
      | ~ v1_relat_1(B_211)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_549,c_62])).

tff(c_649,plain,(
    ! [B_213,C_214] :
      ( r2_hidden(k4_tarski('#skF_8'(k1_xboole_0,B_213,C_214),'#skF_9'(k1_xboole_0,B_213,C_214)),C_214)
      | k5_relat_1(k1_xboole_0,B_213) = C_214
      | ~ v1_relat_1(C_214)
      | ~ v1_relat_1(B_213) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_588])).

tff(c_688,plain,(
    ! [B_213] :
      ( k5_relat_1(k1_xboole_0,B_213) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(B_213) ) ),
    inference(resolution,[status(thm)],[c_649,c_62])).

tff(c_702,plain,(
    ! [B_215] :
      ( k5_relat_1(k1_xboole_0,B_215) = k1_xboole_0
      | ~ v1_relat_1(B_215) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_688])).

tff(c_708,plain,(
    k5_relat_1(k1_xboole_0,'#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_702])).

tff(c_714,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_708])).

tff(c_715,plain,(
    k5_relat_1('#skF_10',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1098,plain,(
    ! [A_275,B_276,C_277] :
      ( r2_hidden(k4_tarski('#skF_7'(A_275,B_276,C_277),'#skF_6'(A_275,B_276,C_277)),B_276)
      | r2_hidden(k4_tarski('#skF_8'(A_275,B_276,C_277),'#skF_9'(A_275,B_276,C_277)),C_277)
      | k5_relat_1(A_275,B_276) = C_277
      | ~ v1_relat_1(C_277)
      | ~ v1_relat_1(B_276)
      | ~ v1_relat_1(A_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1129,plain,(
    ! [A_275,C_277] :
      ( r2_hidden(k4_tarski('#skF_8'(A_275,k1_xboole_0,C_277),'#skF_9'(A_275,k1_xboole_0,C_277)),C_277)
      | k5_relat_1(A_275,k1_xboole_0) = C_277
      | ~ v1_relat_1(C_277)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_275) ) ),
    inference(resolution,[status(thm)],[c_1098,c_62])).

tff(c_1178,plain,(
    ! [A_278,C_279] :
      ( r2_hidden(k4_tarski('#skF_8'(A_278,k1_xboole_0,C_279),'#skF_9'(A_278,k1_xboole_0,C_279)),C_279)
      | k5_relat_1(A_278,k1_xboole_0) = C_279
      | ~ v1_relat_1(C_279)
      | ~ v1_relat_1(A_278) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1129])).

tff(c_1209,plain,(
    ! [A_278] :
      ( k5_relat_1(A_278,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_278) ) ),
    inference(resolution,[status(thm)],[c_1178,c_62])).

tff(c_1221,plain,(
    ! [A_280] :
      ( k5_relat_1(A_280,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_280) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1209])).

tff(c_1227,plain,(
    k5_relat_1('#skF_10',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_1221])).

tff(c_1233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_715,c_1227])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:04:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.77/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.64  
% 3.77/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.64  %$ r2_hidden > v1_relat_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_3 > #skF_10 > #skF_5 > #skF_7 > #skF_9 > #skF_2 > #skF_8
% 3.77/1.64  
% 3.77/1.64  %Foreground sorts:
% 3.77/1.64  
% 3.77/1.64  
% 3.77/1.64  %Background operators:
% 3.77/1.64  
% 3.77/1.64  
% 3.77/1.64  %Foreground operators:
% 3.77/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.77/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.77/1.64  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.77/1.64  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.77/1.64  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.77/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.77/1.64  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 3.77/1.64  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.77/1.64  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.77/1.64  tff('#skF_10', type, '#skF_10': $i).
% 3.77/1.64  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.77/1.64  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.77/1.64  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 3.77/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.77/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.77/1.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.77/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.77/1.64  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.77/1.64  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 3.77/1.64  
% 3.77/1.65  tff(f_69, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 3.77/1.65  tff(f_44, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 3.77/1.65  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.77/1.65  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.77/1.65  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 3.77/1.65  tff(c_34, plain, (k5_relat_1('#skF_10', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_10')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.77/1.65  tff(c_74, plain, (k5_relat_1(k1_xboole_0, '#skF_10')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_34])).
% 3.77/1.65  tff(c_36, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.77/1.65  tff(c_67, plain, (![A_127]: (r2_hidden('#skF_1'(A_127), A_127) | v1_relat_1(A_127))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.77/1.65  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.77/1.65  tff(c_59, plain, (![A_124, B_125]: (~r2_hidden(A_124, k2_zfmisc_1(A_124, B_125)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.77/1.65  tff(c_62, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_59])).
% 3.77/1.65  tff(c_72, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_67, c_62])).
% 3.77/1.65  tff(c_549, plain, (![A_210, B_211, C_212]: (r2_hidden(k4_tarski('#skF_5'(A_210, B_211, C_212), '#skF_7'(A_210, B_211, C_212)), A_210) | r2_hidden(k4_tarski('#skF_8'(A_210, B_211, C_212), '#skF_9'(A_210, B_211, C_212)), C_212) | k5_relat_1(A_210, B_211)=C_212 | ~v1_relat_1(C_212) | ~v1_relat_1(B_211) | ~v1_relat_1(A_210))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.77/1.65  tff(c_588, plain, (![B_211, C_212]: (r2_hidden(k4_tarski('#skF_8'(k1_xboole_0, B_211, C_212), '#skF_9'(k1_xboole_0, B_211, C_212)), C_212) | k5_relat_1(k1_xboole_0, B_211)=C_212 | ~v1_relat_1(C_212) | ~v1_relat_1(B_211) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_549, c_62])).
% 3.77/1.65  tff(c_649, plain, (![B_213, C_214]: (r2_hidden(k4_tarski('#skF_8'(k1_xboole_0, B_213, C_214), '#skF_9'(k1_xboole_0, B_213, C_214)), C_214) | k5_relat_1(k1_xboole_0, B_213)=C_214 | ~v1_relat_1(C_214) | ~v1_relat_1(B_213))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_588])).
% 3.77/1.65  tff(c_688, plain, (![B_213]: (k5_relat_1(k1_xboole_0, B_213)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(B_213))), inference(resolution, [status(thm)], [c_649, c_62])).
% 3.77/1.65  tff(c_702, plain, (![B_215]: (k5_relat_1(k1_xboole_0, B_215)=k1_xboole_0 | ~v1_relat_1(B_215))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_688])).
% 3.77/1.65  tff(c_708, plain, (k5_relat_1(k1_xboole_0, '#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_702])).
% 3.77/1.65  tff(c_714, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_708])).
% 3.77/1.65  tff(c_715, plain, (k5_relat_1('#skF_10', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 3.77/1.65  tff(c_1098, plain, (![A_275, B_276, C_277]: (r2_hidden(k4_tarski('#skF_7'(A_275, B_276, C_277), '#skF_6'(A_275, B_276, C_277)), B_276) | r2_hidden(k4_tarski('#skF_8'(A_275, B_276, C_277), '#skF_9'(A_275, B_276, C_277)), C_277) | k5_relat_1(A_275, B_276)=C_277 | ~v1_relat_1(C_277) | ~v1_relat_1(B_276) | ~v1_relat_1(A_275))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.77/1.65  tff(c_1129, plain, (![A_275, C_277]: (r2_hidden(k4_tarski('#skF_8'(A_275, k1_xboole_0, C_277), '#skF_9'(A_275, k1_xboole_0, C_277)), C_277) | k5_relat_1(A_275, k1_xboole_0)=C_277 | ~v1_relat_1(C_277) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_275))), inference(resolution, [status(thm)], [c_1098, c_62])).
% 3.77/1.65  tff(c_1178, plain, (![A_278, C_279]: (r2_hidden(k4_tarski('#skF_8'(A_278, k1_xboole_0, C_279), '#skF_9'(A_278, k1_xboole_0, C_279)), C_279) | k5_relat_1(A_278, k1_xboole_0)=C_279 | ~v1_relat_1(C_279) | ~v1_relat_1(A_278))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1129])).
% 3.77/1.65  tff(c_1209, plain, (![A_278]: (k5_relat_1(A_278, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_278))), inference(resolution, [status(thm)], [c_1178, c_62])).
% 3.77/1.65  tff(c_1221, plain, (![A_280]: (k5_relat_1(A_280, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_280))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1209])).
% 3.77/1.65  tff(c_1227, plain, (k5_relat_1('#skF_10', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_1221])).
% 3.77/1.65  tff(c_1233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_715, c_1227])).
% 3.77/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.65  
% 3.77/1.65  Inference rules
% 3.77/1.65  ----------------------
% 3.77/1.65  #Ref     : 2
% 3.77/1.65  #Sup     : 257
% 3.77/1.65  #Fact    : 0
% 3.77/1.65  #Define  : 0
% 3.77/1.65  #Split   : 1
% 3.77/1.65  #Chain   : 0
% 3.77/1.65  #Close   : 0
% 3.77/1.65  
% 3.77/1.65  Ordering : KBO
% 3.77/1.66  
% 3.77/1.66  Simplification rules
% 3.77/1.66  ----------------------
% 3.77/1.66  #Subsume      : 54
% 3.77/1.66  #Demod        : 189
% 3.77/1.66  #Tautology    : 27
% 3.77/1.66  #SimpNegUnit  : 8
% 3.77/1.66  #BackRed      : 0
% 3.77/1.66  
% 3.77/1.66  #Partial instantiations: 0
% 3.77/1.66  #Strategies tried      : 1
% 3.77/1.66  
% 3.77/1.66  Timing (in seconds)
% 3.77/1.66  ----------------------
% 3.77/1.66  Preprocessing        : 0.32
% 3.77/1.66  Parsing              : 0.16
% 3.77/1.66  CNF conversion       : 0.03
% 3.77/1.66  Main loop            : 0.56
% 3.77/1.66  Inferencing          : 0.19
% 3.77/1.66  Reduction            : 0.13
% 3.77/1.66  Demodulation         : 0.09
% 3.77/1.66  BG Simplification    : 0.03
% 3.77/1.66  Subsumption          : 0.18
% 3.77/1.66  Abstraction          : 0.03
% 3.77/1.66  MUC search           : 0.00
% 3.77/1.66  Cooper               : 0.00
% 3.77/1.66  Total                : 0.91
% 3.77/1.66  Index Insertion      : 0.00
% 3.77/1.66  Index Deletion       : 0.00
% 3.77/1.66  Index Matching       : 0.00
% 3.77/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
