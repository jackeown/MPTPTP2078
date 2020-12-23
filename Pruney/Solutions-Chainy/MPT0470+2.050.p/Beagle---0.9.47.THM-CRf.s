%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:07 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 135 expanded)
%              Number of leaves         :   22 (  57 expanded)
%              Depth                    :   12
%              Number of atoms          :   98 ( 258 expanded)
%              Number of equality atoms :   22 (  66 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_tarski > #nlpp > k1_xboole_0 > #skF_6 > #skF_2 > #skF_1 > #skF_4 > #skF_5 > #skF_7 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_61,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_54,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_28,plain,
    ( k5_relat_1('#skF_8',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_8') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_42,plain,(
    k5_relat_1(k1_xboole_0,'#skF_8') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_30,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_31,plain,(
    ! [A_105] :
      ( v1_relat_1(A_105)
      | ~ v1_xboole_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_35,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_31])).

tff(c_164,plain,(
    ! [A_153,B_154,C_155] :
      ( r2_hidden(k4_tarski('#skF_3'(A_153,B_154,C_155),'#skF_5'(A_153,B_154,C_155)),A_153)
      | r2_hidden(k4_tarski('#skF_6'(A_153,B_154,C_155),'#skF_7'(A_153,B_154,C_155)),C_155)
      | k5_relat_1(A_153,B_154) = C_155
      | ~ v1_relat_1(C_155)
      | ~ v1_relat_1(B_154)
      | ~ v1_relat_1(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_314,plain,(
    ! [A_159,B_160,C_161] :
      ( ~ v1_xboole_0(A_159)
      | r2_hidden(k4_tarski('#skF_6'(A_159,B_160,C_161),'#skF_7'(A_159,B_160,C_161)),C_161)
      | k5_relat_1(A_159,B_160) = C_161
      | ~ v1_relat_1(C_161)
      | ~ v1_relat_1(B_160)
      | ~ v1_relat_1(A_159) ) ),
    inference(resolution,[status(thm)],[c_164,c_2])).

tff(c_352,plain,(
    ! [C_162,A_163,B_164] :
      ( ~ v1_xboole_0(C_162)
      | ~ v1_xboole_0(A_163)
      | k5_relat_1(A_163,B_164) = C_162
      | ~ v1_relat_1(C_162)
      | ~ v1_relat_1(B_164)
      | ~ v1_relat_1(A_163) ) ),
    inference(resolution,[status(thm)],[c_314,c_2])).

tff(c_354,plain,(
    ! [A_163,B_164] :
      ( ~ v1_xboole_0(A_163)
      | k5_relat_1(A_163,B_164) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(B_164)
      | ~ v1_relat_1(A_163) ) ),
    inference(resolution,[status(thm)],[c_6,c_352])).

tff(c_358,plain,(
    ! [A_165,B_166] :
      ( ~ v1_xboole_0(A_165)
      | k5_relat_1(A_165,B_166) = k1_xboole_0
      | ~ v1_relat_1(B_166)
      | ~ v1_relat_1(A_165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_354])).

tff(c_360,plain,(
    ! [B_166] :
      ( k5_relat_1(k1_xboole_0,B_166) = k1_xboole_0
      | ~ v1_relat_1(B_166)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_358])).

tff(c_364,plain,(
    ! [B_167] :
      ( k5_relat_1(k1_xboole_0,B_167) = k1_xboole_0
      | ~ v1_relat_1(B_167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_360])).

tff(c_370,plain,(
    k5_relat_1(k1_xboole_0,'#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_364])).

tff(c_375,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_370])).

tff(c_376,plain,(
    k5_relat_1('#skF_8',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_663,plain,(
    ! [A_211,B_212,C_213] :
      ( r2_hidden(k4_tarski('#skF_5'(A_211,B_212,C_213),'#skF_4'(A_211,B_212,C_213)),B_212)
      | r2_hidden(k4_tarski('#skF_6'(A_211,B_212,C_213),'#skF_7'(A_211,B_212,C_213)),C_213)
      | k5_relat_1(A_211,B_212) = C_213
      | ~ v1_relat_1(C_213)
      | ~ v1_relat_1(B_212)
      | ~ v1_relat_1(A_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_377,plain,(
    k5_relat_1(k1_xboole_0,'#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_418,plain,(
    ! [D_183,B_184,A_185,E_186] :
      ( r2_hidden(k4_tarski(D_183,'#skF_2'(B_184,k5_relat_1(A_185,B_184),D_183,A_185,E_186)),A_185)
      | ~ r2_hidden(k4_tarski(D_183,E_186),k5_relat_1(A_185,B_184))
      | ~ v1_relat_1(k5_relat_1(A_185,B_184))
      | ~ v1_relat_1(B_184)
      | ~ v1_relat_1(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_430,plain,(
    ! [D_183,E_186] :
      ( r2_hidden(k4_tarski(D_183,'#skF_2'('#skF_8',k1_xboole_0,D_183,k1_xboole_0,E_186)),k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_183,E_186),k5_relat_1(k1_xboole_0,'#skF_8'))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,'#skF_8'))
      | ~ v1_relat_1('#skF_8')
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_418])).

tff(c_436,plain,(
    ! [D_187,E_188] :
      ( r2_hidden(k4_tarski(D_187,'#skF_2'('#skF_8',k1_xboole_0,D_187,k1_xboole_0,E_188)),k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_187,E_188),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_30,c_35,c_377,c_377,c_430])).

tff(c_441,plain,(
    ! [D_187,E_188] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_187,E_188),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_436,c_2])).

tff(c_447,plain,(
    ! [D_187,E_188] : ~ r2_hidden(k4_tarski(D_187,E_188),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_441])).

tff(c_702,plain,(
    ! [A_211,B_212] :
      ( r2_hidden(k4_tarski('#skF_5'(A_211,B_212,k1_xboole_0),'#skF_4'(A_211,B_212,k1_xboole_0)),B_212)
      | k5_relat_1(A_211,B_212) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(B_212)
      | ~ v1_relat_1(A_211) ) ),
    inference(resolution,[status(thm)],[c_663,c_447])).

tff(c_754,plain,(
    ! [A_222,B_223] :
      ( r2_hidden(k4_tarski('#skF_5'(A_222,B_223,k1_xboole_0),'#skF_4'(A_222,B_223,k1_xboole_0)),B_223)
      | k5_relat_1(A_222,B_223) = k1_xboole_0
      | ~ v1_relat_1(B_223)
      | ~ v1_relat_1(A_222) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_702])).

tff(c_770,plain,(
    ! [A_222] :
      ( k5_relat_1(A_222,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_222) ) ),
    inference(resolution,[status(thm)],[c_754,c_447])).

tff(c_789,plain,(
    ! [A_224] :
      ( k5_relat_1(A_224,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_224) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_770])).

tff(c_795,plain,(
    k5_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_789])).

tff(c_801,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_376,c_795])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:55:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.49  
% 2.97/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.49  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_tarski > #nlpp > k1_xboole_0 > #skF_6 > #skF_2 > #skF_1 > #skF_4 > #skF_5 > #skF_7 > #skF_8 > #skF_3
% 2.97/1.49  
% 2.97/1.49  %Foreground sorts:
% 2.97/1.49  
% 2.97/1.49  
% 2.97/1.49  %Background operators:
% 2.97/1.49  
% 2.97/1.49  
% 2.97/1.49  %Foreground operators:
% 2.97/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.97/1.49  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.97/1.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.97/1.49  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.97/1.49  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.97/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.97/1.49  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.97/1.49  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.97/1.49  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.97/1.49  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 2.97/1.49  tff('#skF_8', type, '#skF_8': $i).
% 2.97/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.97/1.49  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.97/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.97/1.49  
% 3.19/1.51  tff(f_61, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 3.19/1.51  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.19/1.51  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.19/1.51  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 3.19/1.51  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.19/1.51  tff(c_28, plain, (k5_relat_1('#skF_8', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_8')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.19/1.51  tff(c_42, plain, (k5_relat_1(k1_xboole_0, '#skF_8')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_28])).
% 3.19/1.51  tff(c_30, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.19/1.51  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.19/1.51  tff(c_31, plain, (![A_105]: (v1_relat_1(A_105) | ~v1_xboole_0(A_105))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.19/1.51  tff(c_35, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_31])).
% 3.19/1.51  tff(c_164, plain, (![A_153, B_154, C_155]: (r2_hidden(k4_tarski('#skF_3'(A_153, B_154, C_155), '#skF_5'(A_153, B_154, C_155)), A_153) | r2_hidden(k4_tarski('#skF_6'(A_153, B_154, C_155), '#skF_7'(A_153, B_154, C_155)), C_155) | k5_relat_1(A_153, B_154)=C_155 | ~v1_relat_1(C_155) | ~v1_relat_1(B_154) | ~v1_relat_1(A_153))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.19/1.51  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.19/1.51  tff(c_314, plain, (![A_159, B_160, C_161]: (~v1_xboole_0(A_159) | r2_hidden(k4_tarski('#skF_6'(A_159, B_160, C_161), '#skF_7'(A_159, B_160, C_161)), C_161) | k5_relat_1(A_159, B_160)=C_161 | ~v1_relat_1(C_161) | ~v1_relat_1(B_160) | ~v1_relat_1(A_159))), inference(resolution, [status(thm)], [c_164, c_2])).
% 3.19/1.51  tff(c_352, plain, (![C_162, A_163, B_164]: (~v1_xboole_0(C_162) | ~v1_xboole_0(A_163) | k5_relat_1(A_163, B_164)=C_162 | ~v1_relat_1(C_162) | ~v1_relat_1(B_164) | ~v1_relat_1(A_163))), inference(resolution, [status(thm)], [c_314, c_2])).
% 3.19/1.51  tff(c_354, plain, (![A_163, B_164]: (~v1_xboole_0(A_163) | k5_relat_1(A_163, B_164)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(B_164) | ~v1_relat_1(A_163))), inference(resolution, [status(thm)], [c_6, c_352])).
% 3.19/1.51  tff(c_358, plain, (![A_165, B_166]: (~v1_xboole_0(A_165) | k5_relat_1(A_165, B_166)=k1_xboole_0 | ~v1_relat_1(B_166) | ~v1_relat_1(A_165))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_354])).
% 3.19/1.51  tff(c_360, plain, (![B_166]: (k5_relat_1(k1_xboole_0, B_166)=k1_xboole_0 | ~v1_relat_1(B_166) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_358])).
% 3.19/1.51  tff(c_364, plain, (![B_167]: (k5_relat_1(k1_xboole_0, B_167)=k1_xboole_0 | ~v1_relat_1(B_167))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_360])).
% 3.19/1.51  tff(c_370, plain, (k5_relat_1(k1_xboole_0, '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_364])).
% 3.19/1.51  tff(c_375, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_370])).
% 3.19/1.51  tff(c_376, plain, (k5_relat_1('#skF_8', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_28])).
% 3.19/1.51  tff(c_663, plain, (![A_211, B_212, C_213]: (r2_hidden(k4_tarski('#skF_5'(A_211, B_212, C_213), '#skF_4'(A_211, B_212, C_213)), B_212) | r2_hidden(k4_tarski('#skF_6'(A_211, B_212, C_213), '#skF_7'(A_211, B_212, C_213)), C_213) | k5_relat_1(A_211, B_212)=C_213 | ~v1_relat_1(C_213) | ~v1_relat_1(B_212) | ~v1_relat_1(A_211))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.19/1.51  tff(c_377, plain, (k5_relat_1(k1_xboole_0, '#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_28])).
% 3.19/1.51  tff(c_418, plain, (![D_183, B_184, A_185, E_186]: (r2_hidden(k4_tarski(D_183, '#skF_2'(B_184, k5_relat_1(A_185, B_184), D_183, A_185, E_186)), A_185) | ~r2_hidden(k4_tarski(D_183, E_186), k5_relat_1(A_185, B_184)) | ~v1_relat_1(k5_relat_1(A_185, B_184)) | ~v1_relat_1(B_184) | ~v1_relat_1(A_185))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.19/1.51  tff(c_430, plain, (![D_183, E_186]: (r2_hidden(k4_tarski(D_183, '#skF_2'('#skF_8', k1_xboole_0, D_183, k1_xboole_0, E_186)), k1_xboole_0) | ~r2_hidden(k4_tarski(D_183, E_186), k5_relat_1(k1_xboole_0, '#skF_8')) | ~v1_relat_1(k5_relat_1(k1_xboole_0, '#skF_8')) | ~v1_relat_1('#skF_8') | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_377, c_418])).
% 3.19/1.51  tff(c_436, plain, (![D_187, E_188]: (r2_hidden(k4_tarski(D_187, '#skF_2'('#skF_8', k1_xboole_0, D_187, k1_xboole_0, E_188)), k1_xboole_0) | ~r2_hidden(k4_tarski(D_187, E_188), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_30, c_35, c_377, c_377, c_430])).
% 3.19/1.51  tff(c_441, plain, (![D_187, E_188]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(k4_tarski(D_187, E_188), k1_xboole_0))), inference(resolution, [status(thm)], [c_436, c_2])).
% 3.19/1.51  tff(c_447, plain, (![D_187, E_188]: (~r2_hidden(k4_tarski(D_187, E_188), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_441])).
% 3.19/1.51  tff(c_702, plain, (![A_211, B_212]: (r2_hidden(k4_tarski('#skF_5'(A_211, B_212, k1_xboole_0), '#skF_4'(A_211, B_212, k1_xboole_0)), B_212) | k5_relat_1(A_211, B_212)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(B_212) | ~v1_relat_1(A_211))), inference(resolution, [status(thm)], [c_663, c_447])).
% 3.19/1.51  tff(c_754, plain, (![A_222, B_223]: (r2_hidden(k4_tarski('#skF_5'(A_222, B_223, k1_xboole_0), '#skF_4'(A_222, B_223, k1_xboole_0)), B_223) | k5_relat_1(A_222, B_223)=k1_xboole_0 | ~v1_relat_1(B_223) | ~v1_relat_1(A_222))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_702])).
% 3.19/1.51  tff(c_770, plain, (![A_222]: (k5_relat_1(A_222, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_222))), inference(resolution, [status(thm)], [c_754, c_447])).
% 3.19/1.51  tff(c_789, plain, (![A_224]: (k5_relat_1(A_224, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_224))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_770])).
% 3.19/1.51  tff(c_795, plain, (k5_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_789])).
% 3.19/1.51  tff(c_801, plain, $false, inference(negUnitSimplification, [status(thm)], [c_376, c_795])).
% 3.19/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.51  
% 3.19/1.51  Inference rules
% 3.19/1.51  ----------------------
% 3.19/1.51  #Ref     : 0
% 3.19/1.51  #Sup     : 155
% 3.19/1.51  #Fact    : 0
% 3.19/1.51  #Define  : 0
% 3.19/1.51  #Split   : 2
% 3.19/1.51  #Chain   : 0
% 3.19/1.51  #Close   : 0
% 3.19/1.51  
% 3.19/1.51  Ordering : KBO
% 3.19/1.51  
% 3.19/1.51  Simplification rules
% 3.19/1.51  ----------------------
% 3.19/1.51  #Subsume      : 28
% 3.19/1.51  #Demod        : 90
% 3.19/1.51  #Tautology    : 7
% 3.19/1.51  #SimpNegUnit  : 5
% 3.19/1.51  #BackRed      : 0
% 3.19/1.51  
% 3.19/1.51  #Partial instantiations: 0
% 3.19/1.51  #Strategies tried      : 1
% 3.19/1.51  
% 3.19/1.51  Timing (in seconds)
% 3.19/1.51  ----------------------
% 3.19/1.51  Preprocessing        : 0.30
% 3.19/1.51  Parsing              : 0.16
% 3.19/1.51  CNF conversion       : 0.03
% 3.19/1.51  Main loop            : 0.40
% 3.19/1.51  Inferencing          : 0.16
% 3.19/1.51  Reduction            : 0.09
% 3.19/1.51  Demodulation         : 0.06
% 3.19/1.51  BG Simplification    : 0.02
% 3.19/1.51  Subsumption          : 0.11
% 3.19/1.51  Abstraction          : 0.02
% 3.19/1.51  MUC search           : 0.00
% 3.19/1.51  Cooper               : 0.00
% 3.19/1.51  Total                : 0.73
% 3.19/1.51  Index Insertion      : 0.00
% 3.19/1.51  Index Deletion       : 0.00
% 3.19/1.51  Index Matching       : 0.00
% 3.19/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
