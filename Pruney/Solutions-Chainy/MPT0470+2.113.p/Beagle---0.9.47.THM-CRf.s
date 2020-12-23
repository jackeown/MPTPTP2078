%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:16 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 162 expanded)
%              Number of leaves         :   25 (  68 expanded)
%              Depth                    :   12
%              Number of atoms          :  101 ( 314 expanded)
%              Number of equality atoms :   23 (  74 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_1 > #skF_5 > #skF_3 > #skF_7 > #skF_9 > #skF_8 > #skF_4 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_60,axiom,(
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

tff(c_32,plain,
    ( k5_relat_1('#skF_11',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_11') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_52,plain,(
    k5_relat_1(k1_xboole_0,'#skF_11') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_34,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_41,plain,(
    ! [A_125] :
      ( r2_hidden('#skF_2'(A_125),A_125)
      | v1_relat_1(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_47,plain,(
    ! [A_129] :
      ( ~ v1_xboole_0(A_129)
      | v1_relat_1(A_129) ) ),
    inference(resolution,[status(thm)],[c_41,c_2])).

tff(c_51,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_47])).

tff(c_135,plain,(
    ! [A_162,B_163,C_164] :
      ( r2_hidden(k4_tarski('#skF_6'(A_162,B_163,C_164),'#skF_8'(A_162,B_163,C_164)),A_162)
      | r2_hidden(k4_tarski('#skF_9'(A_162,B_163,C_164),'#skF_10'(A_162,B_163,C_164)),C_164)
      | k5_relat_1(A_162,B_163) = C_164
      | ~ v1_relat_1(C_164)
      | ~ v1_relat_1(B_163)
      | ~ v1_relat_1(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_276,plain,(
    ! [A_182,B_183,C_184] :
      ( ~ v1_xboole_0(A_182)
      | r2_hidden(k4_tarski('#skF_9'(A_182,B_183,C_184),'#skF_10'(A_182,B_183,C_184)),C_184)
      | k5_relat_1(A_182,B_183) = C_184
      | ~ v1_relat_1(C_184)
      | ~ v1_relat_1(B_183)
      | ~ v1_relat_1(A_182) ) ),
    inference(resolution,[status(thm)],[c_135,c_2])).

tff(c_302,plain,(
    ! [C_185,A_186,B_187] :
      ( ~ v1_xboole_0(C_185)
      | ~ v1_xboole_0(A_186)
      | k5_relat_1(A_186,B_187) = C_185
      | ~ v1_relat_1(C_185)
      | ~ v1_relat_1(B_187)
      | ~ v1_relat_1(A_186) ) ),
    inference(resolution,[status(thm)],[c_276,c_2])).

tff(c_308,plain,(
    ! [A_186,B_187] :
      ( ~ v1_xboole_0(A_186)
      | k5_relat_1(A_186,B_187) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(B_187)
      | ~ v1_relat_1(A_186) ) ),
    inference(resolution,[status(thm)],[c_6,c_302])).

tff(c_314,plain,(
    ! [A_188,B_189] :
      ( ~ v1_xboole_0(A_188)
      | k5_relat_1(A_188,B_189) = k1_xboole_0
      | ~ v1_relat_1(B_189)
      | ~ v1_relat_1(A_188) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_308])).

tff(c_320,plain,(
    ! [B_189] :
      ( k5_relat_1(k1_xboole_0,B_189) = k1_xboole_0
      | ~ v1_relat_1(B_189)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_314])).

tff(c_327,plain,(
    ! [B_193] :
      ( k5_relat_1(k1_xboole_0,B_193) = k1_xboole_0
      | ~ v1_relat_1(B_193) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_320])).

tff(c_333,plain,(
    k5_relat_1(k1_xboole_0,'#skF_11') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_327])).

tff(c_338,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_333])).

tff(c_339,plain,(
    k5_relat_1('#skF_11',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_909,plain,(
    ! [A_269,B_270,C_271] :
      ( r2_hidden(k4_tarski('#skF_8'(A_269,B_270,C_271),'#skF_7'(A_269,B_270,C_271)),B_270)
      | r2_hidden(k4_tarski('#skF_9'(A_269,B_270,C_271),'#skF_10'(A_269,B_270,C_271)),C_271)
      | k5_relat_1(A_269,B_270) = C_271
      | ~ v1_relat_1(C_271)
      | ~ v1_relat_1(B_270)
      | ~ v1_relat_1(A_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_340,plain,(
    k5_relat_1(k1_xboole_0,'#skF_11') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_368,plain,(
    ! [D_206,E_207,A_208,B_209] :
      ( r2_hidden(k4_tarski(D_206,'#skF_5'(D_206,E_207,k5_relat_1(A_208,B_209),B_209,A_208)),A_208)
      | ~ r2_hidden(k4_tarski(D_206,E_207),k5_relat_1(A_208,B_209))
      | ~ v1_relat_1(k5_relat_1(A_208,B_209))
      | ~ v1_relat_1(B_209)
      | ~ v1_relat_1(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_376,plain,(
    ! [D_206,E_207] :
      ( r2_hidden(k4_tarski(D_206,'#skF_5'(D_206,E_207,k1_xboole_0,'#skF_11',k1_xboole_0)),k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_206,E_207),k5_relat_1(k1_xboole_0,'#skF_11'))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,'#skF_11'))
      | ~ v1_relat_1('#skF_11')
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_340,c_368])).

tff(c_381,plain,(
    ! [D_210,E_211] :
      ( r2_hidden(k4_tarski(D_210,'#skF_5'(D_210,E_211,k1_xboole_0,'#skF_11',k1_xboole_0)),k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_210,E_211),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_34,c_51,c_340,c_340,c_376])).

tff(c_386,plain,(
    ! [D_210,E_211] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_210,E_211),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_381,c_2])).

tff(c_392,plain,(
    ! [D_210,E_211] : ~ r2_hidden(k4_tarski(D_210,E_211),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_386])).

tff(c_980,plain,(
    ! [A_269,B_270] :
      ( r2_hidden(k4_tarski('#skF_8'(A_269,B_270,k1_xboole_0),'#skF_7'(A_269,B_270,k1_xboole_0)),B_270)
      | k5_relat_1(A_269,B_270) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(B_270)
      | ~ v1_relat_1(A_269) ) ),
    inference(resolution,[status(thm)],[c_909,c_392])).

tff(c_1039,plain,(
    ! [A_280,B_281] :
      ( r2_hidden(k4_tarski('#skF_8'(A_280,B_281,k1_xboole_0),'#skF_7'(A_280,B_281,k1_xboole_0)),B_281)
      | k5_relat_1(A_280,B_281) = k1_xboole_0
      | ~ v1_relat_1(B_281)
      | ~ v1_relat_1(A_280) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_980])).

tff(c_1074,plain,(
    ! [A_280] :
      ( k5_relat_1(A_280,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_280) ) ),
    inference(resolution,[status(thm)],[c_1039,c_392])).

tff(c_1096,plain,(
    ! [A_282] :
      ( k5_relat_1(A_282,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_282) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_1074])).

tff(c_1102,plain,(
    k5_relat_1('#skF_11',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_1096])).

tff(c_1108,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_339,c_1102])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:09:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.50  
% 3.25/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.50  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_1 > #skF_5 > #skF_3 > #skF_7 > #skF_9 > #skF_8 > #skF_4 > #skF_10
% 3.25/1.50  
% 3.25/1.50  %Foreground sorts:
% 3.25/1.50  
% 3.25/1.50  
% 3.25/1.50  %Background operators:
% 3.25/1.50  
% 3.25/1.50  
% 3.25/1.50  %Foreground operators:
% 3.25/1.50  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.25/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.25/1.50  tff('#skF_11', type, '#skF_11': $i).
% 3.25/1.50  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.25/1.50  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.25/1.50  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.25/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.25/1.50  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.25/1.50  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i) > $i).
% 3.25/1.50  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.25/1.50  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.25/1.50  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 3.25/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.25/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.50  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 3.25/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.25/1.50  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.25/1.50  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 3.25/1.50  
% 3.25/1.52  tff(f_67, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 3.25/1.52  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.25/1.52  tff(f_42, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 3.25/1.52  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.25/1.52  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 3.25/1.52  tff(c_32, plain, (k5_relat_1('#skF_11', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_11')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.25/1.52  tff(c_52, plain, (k5_relat_1(k1_xboole_0, '#skF_11')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32])).
% 3.25/1.52  tff(c_34, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.25/1.52  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.25/1.52  tff(c_41, plain, (![A_125]: (r2_hidden('#skF_2'(A_125), A_125) | v1_relat_1(A_125))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.25/1.52  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.25/1.52  tff(c_47, plain, (![A_129]: (~v1_xboole_0(A_129) | v1_relat_1(A_129))), inference(resolution, [status(thm)], [c_41, c_2])).
% 3.25/1.52  tff(c_51, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_47])).
% 3.25/1.52  tff(c_135, plain, (![A_162, B_163, C_164]: (r2_hidden(k4_tarski('#skF_6'(A_162, B_163, C_164), '#skF_8'(A_162, B_163, C_164)), A_162) | r2_hidden(k4_tarski('#skF_9'(A_162, B_163, C_164), '#skF_10'(A_162, B_163, C_164)), C_164) | k5_relat_1(A_162, B_163)=C_164 | ~v1_relat_1(C_164) | ~v1_relat_1(B_163) | ~v1_relat_1(A_162))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.25/1.52  tff(c_276, plain, (![A_182, B_183, C_184]: (~v1_xboole_0(A_182) | r2_hidden(k4_tarski('#skF_9'(A_182, B_183, C_184), '#skF_10'(A_182, B_183, C_184)), C_184) | k5_relat_1(A_182, B_183)=C_184 | ~v1_relat_1(C_184) | ~v1_relat_1(B_183) | ~v1_relat_1(A_182))), inference(resolution, [status(thm)], [c_135, c_2])).
% 3.25/1.52  tff(c_302, plain, (![C_185, A_186, B_187]: (~v1_xboole_0(C_185) | ~v1_xboole_0(A_186) | k5_relat_1(A_186, B_187)=C_185 | ~v1_relat_1(C_185) | ~v1_relat_1(B_187) | ~v1_relat_1(A_186))), inference(resolution, [status(thm)], [c_276, c_2])).
% 3.25/1.52  tff(c_308, plain, (![A_186, B_187]: (~v1_xboole_0(A_186) | k5_relat_1(A_186, B_187)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(B_187) | ~v1_relat_1(A_186))), inference(resolution, [status(thm)], [c_6, c_302])).
% 3.25/1.52  tff(c_314, plain, (![A_188, B_189]: (~v1_xboole_0(A_188) | k5_relat_1(A_188, B_189)=k1_xboole_0 | ~v1_relat_1(B_189) | ~v1_relat_1(A_188))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_308])).
% 3.25/1.52  tff(c_320, plain, (![B_189]: (k5_relat_1(k1_xboole_0, B_189)=k1_xboole_0 | ~v1_relat_1(B_189) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_314])).
% 3.25/1.52  tff(c_327, plain, (![B_193]: (k5_relat_1(k1_xboole_0, B_193)=k1_xboole_0 | ~v1_relat_1(B_193))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_320])).
% 3.25/1.52  tff(c_333, plain, (k5_relat_1(k1_xboole_0, '#skF_11')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_327])).
% 3.25/1.52  tff(c_338, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_333])).
% 3.25/1.52  tff(c_339, plain, (k5_relat_1('#skF_11', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 3.25/1.52  tff(c_909, plain, (![A_269, B_270, C_271]: (r2_hidden(k4_tarski('#skF_8'(A_269, B_270, C_271), '#skF_7'(A_269, B_270, C_271)), B_270) | r2_hidden(k4_tarski('#skF_9'(A_269, B_270, C_271), '#skF_10'(A_269, B_270, C_271)), C_271) | k5_relat_1(A_269, B_270)=C_271 | ~v1_relat_1(C_271) | ~v1_relat_1(B_270) | ~v1_relat_1(A_269))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.25/1.52  tff(c_340, plain, (k5_relat_1(k1_xboole_0, '#skF_11')=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 3.25/1.52  tff(c_368, plain, (![D_206, E_207, A_208, B_209]: (r2_hidden(k4_tarski(D_206, '#skF_5'(D_206, E_207, k5_relat_1(A_208, B_209), B_209, A_208)), A_208) | ~r2_hidden(k4_tarski(D_206, E_207), k5_relat_1(A_208, B_209)) | ~v1_relat_1(k5_relat_1(A_208, B_209)) | ~v1_relat_1(B_209) | ~v1_relat_1(A_208))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.25/1.52  tff(c_376, plain, (![D_206, E_207]: (r2_hidden(k4_tarski(D_206, '#skF_5'(D_206, E_207, k1_xboole_0, '#skF_11', k1_xboole_0)), k1_xboole_0) | ~r2_hidden(k4_tarski(D_206, E_207), k5_relat_1(k1_xboole_0, '#skF_11')) | ~v1_relat_1(k5_relat_1(k1_xboole_0, '#skF_11')) | ~v1_relat_1('#skF_11') | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_340, c_368])).
% 3.25/1.52  tff(c_381, plain, (![D_210, E_211]: (r2_hidden(k4_tarski(D_210, '#skF_5'(D_210, E_211, k1_xboole_0, '#skF_11', k1_xboole_0)), k1_xboole_0) | ~r2_hidden(k4_tarski(D_210, E_211), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_34, c_51, c_340, c_340, c_376])).
% 3.25/1.52  tff(c_386, plain, (![D_210, E_211]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(k4_tarski(D_210, E_211), k1_xboole_0))), inference(resolution, [status(thm)], [c_381, c_2])).
% 3.25/1.52  tff(c_392, plain, (![D_210, E_211]: (~r2_hidden(k4_tarski(D_210, E_211), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_386])).
% 3.25/1.52  tff(c_980, plain, (![A_269, B_270]: (r2_hidden(k4_tarski('#skF_8'(A_269, B_270, k1_xboole_0), '#skF_7'(A_269, B_270, k1_xboole_0)), B_270) | k5_relat_1(A_269, B_270)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(B_270) | ~v1_relat_1(A_269))), inference(resolution, [status(thm)], [c_909, c_392])).
% 3.25/1.52  tff(c_1039, plain, (![A_280, B_281]: (r2_hidden(k4_tarski('#skF_8'(A_280, B_281, k1_xboole_0), '#skF_7'(A_280, B_281, k1_xboole_0)), B_281) | k5_relat_1(A_280, B_281)=k1_xboole_0 | ~v1_relat_1(B_281) | ~v1_relat_1(A_280))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_980])).
% 3.25/1.52  tff(c_1074, plain, (![A_280]: (k5_relat_1(A_280, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_280))), inference(resolution, [status(thm)], [c_1039, c_392])).
% 3.25/1.52  tff(c_1096, plain, (![A_282]: (k5_relat_1(A_282, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_282))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_1074])).
% 3.25/1.52  tff(c_1102, plain, (k5_relat_1('#skF_11', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_1096])).
% 3.25/1.52  tff(c_1108, plain, $false, inference(negUnitSimplification, [status(thm)], [c_339, c_1102])).
% 3.25/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.52  
% 3.25/1.52  Inference rules
% 3.25/1.52  ----------------------
% 3.25/1.52  #Ref     : 2
% 3.25/1.52  #Sup     : 233
% 3.25/1.52  #Fact    : 0
% 3.25/1.52  #Define  : 0
% 3.25/1.52  #Split   : 1
% 3.25/1.52  #Chain   : 0
% 3.25/1.52  #Close   : 0
% 3.25/1.52  
% 3.25/1.52  Ordering : KBO
% 3.25/1.52  
% 3.25/1.52  Simplification rules
% 3.25/1.52  ----------------------
% 3.25/1.52  #Subsume      : 39
% 3.25/1.52  #Demod        : 159
% 3.25/1.52  #Tautology    : 26
% 3.25/1.52  #SimpNegUnit  : 5
% 3.25/1.52  #BackRed      : 0
% 3.25/1.52  
% 3.25/1.52  #Partial instantiations: 0
% 3.25/1.52  #Strategies tried      : 1
% 3.25/1.52  
% 3.25/1.52  Timing (in seconds)
% 3.25/1.52  ----------------------
% 3.25/1.52  Preprocessing        : 0.29
% 3.25/1.52  Parsing              : 0.14
% 3.25/1.52  CNF conversion       : 0.03
% 3.25/1.52  Main loop            : 0.46
% 3.25/1.52  Inferencing          : 0.17
% 3.25/1.52  Reduction            : 0.11
% 3.25/1.52  Demodulation         : 0.07
% 3.25/1.52  BG Simplification    : 0.02
% 3.25/1.52  Subsumption          : 0.12
% 3.25/1.52  Abstraction          : 0.03
% 3.25/1.52  MUC search           : 0.00
% 3.25/1.52  Cooper               : 0.00
% 3.25/1.52  Total                : 0.78
% 3.25/1.52  Index Insertion      : 0.00
% 3.25/1.52  Index Deletion       : 0.00
% 3.25/1.52  Index Matching       : 0.00
% 3.25/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
