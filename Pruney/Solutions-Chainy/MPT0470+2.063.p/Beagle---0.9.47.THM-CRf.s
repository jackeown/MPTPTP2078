%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:09 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   47 (  83 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   73 ( 134 expanded)
%              Number of equality atoms :   23 (  44 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_1 > #skF_3

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_64,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_57,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_32,plain,
    ( k5_relat_1('#skF_7',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_70,plain,(
    k5_relat_1(k1_xboole_0,'#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_34,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_35,plain,(
    ! [A_105] :
      ( v1_relat_1(A_105)
      | ~ v1_xboole_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_39,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_35])).

tff(c_428,plain,(
    ! [A_161,B_162,C_163] :
      ( r2_hidden(k4_tarski('#skF_2'(A_161,B_162,C_163),'#skF_4'(A_161,B_162,C_163)),A_161)
      | r2_hidden(k4_tarski('#skF_5'(A_161,B_162,C_163),'#skF_6'(A_161,B_162,C_163)),C_163)
      | k5_relat_1(A_161,B_162) = C_163
      | ~ v1_relat_1(C_163)
      | ~ v1_relat_1(B_162)
      | ~ v1_relat_1(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_62,plain,(
    ! [A_108,B_109] : ~ r2_hidden(A_108,k2_zfmisc_1(A_108,B_109)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_65,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_62])).

tff(c_486,plain,(
    ! [A_161,B_162] :
      ( r2_hidden(k4_tarski('#skF_2'(A_161,B_162,k1_xboole_0),'#skF_4'(A_161,B_162,k1_xboole_0)),A_161)
      | k5_relat_1(A_161,B_162) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(B_162)
      | ~ v1_relat_1(A_161) ) ),
    inference(resolution,[status(thm)],[c_428,c_65])).

tff(c_504,plain,(
    ! [A_164,B_165] :
      ( r2_hidden(k4_tarski('#skF_2'(A_164,B_165,k1_xboole_0),'#skF_4'(A_164,B_165,k1_xboole_0)),A_164)
      | k5_relat_1(A_164,B_165) = k1_xboole_0
      | ~ v1_relat_1(B_165)
      | ~ v1_relat_1(A_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_486])).

tff(c_534,plain,(
    ! [B_165] :
      ( k5_relat_1(k1_xboole_0,B_165) = k1_xboole_0
      | ~ v1_relat_1(B_165)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_504,c_65])).

tff(c_545,plain,(
    ! [B_166] :
      ( k5_relat_1(k1_xboole_0,B_166) = k1_xboole_0
      | ~ v1_relat_1(B_166) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_534])).

tff(c_551,plain,(
    k5_relat_1(k1_xboole_0,'#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_545])).

tff(c_557,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_551])).

tff(c_558,plain,(
    k5_relat_1('#skF_7',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_904,plain,(
    ! [A_213,B_214,C_215] :
      ( r2_hidden(k4_tarski('#skF_4'(A_213,B_214,C_215),'#skF_3'(A_213,B_214,C_215)),B_214)
      | r2_hidden(k4_tarski('#skF_5'(A_213,B_214,C_215),'#skF_6'(A_213,B_214,C_215)),C_215)
      | k5_relat_1(A_213,B_214) = C_215
      | ~ v1_relat_1(C_215)
      | ~ v1_relat_1(B_214)
      | ~ v1_relat_1(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_934,plain,(
    ! [A_213,C_215] :
      ( r2_hidden(k4_tarski('#skF_5'(A_213,k1_xboole_0,C_215),'#skF_6'(A_213,k1_xboole_0,C_215)),C_215)
      | k5_relat_1(A_213,k1_xboole_0) = C_215
      | ~ v1_relat_1(C_215)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_213) ) ),
    inference(resolution,[status(thm)],[c_904,c_65])).

tff(c_994,plain,(
    ! [A_220,C_221] :
      ( r2_hidden(k4_tarski('#skF_5'(A_220,k1_xboole_0,C_221),'#skF_6'(A_220,k1_xboole_0,C_221)),C_221)
      | k5_relat_1(A_220,k1_xboole_0) = C_221
      | ~ v1_relat_1(C_221)
      | ~ v1_relat_1(A_220) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_934])).

tff(c_1024,plain,(
    ! [A_220] :
      ( k5_relat_1(A_220,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_220) ) ),
    inference(resolution,[status(thm)],[c_994,c_65])).

tff(c_1035,plain,(
    ! [A_222] :
      ( k5_relat_1(A_222,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_222) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_1024])).

tff(c_1041,plain,(
    k5_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_1035])).

tff(c_1047,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_558,c_1041])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:15:31 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.45  
% 3.13/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.45  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_1 > #skF_3
% 3.13/1.45  
% 3.13/1.45  %Foreground sorts:
% 3.13/1.45  
% 3.13/1.45  
% 3.13/1.45  %Background operators:
% 3.13/1.45  
% 3.13/1.45  
% 3.13/1.45  %Foreground operators:
% 3.13/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.13/1.45  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.13/1.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.13/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.13/1.45  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.13/1.45  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.13/1.45  tff('#skF_7', type, '#skF_7': $i).
% 3.13/1.45  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.13/1.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.13/1.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 3.13/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.13/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.13/1.45  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.13/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.13/1.45  
% 3.13/1.46  tff(f_64, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 3.13/1.46  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.13/1.46  tff(f_39, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.13/1.46  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 3.13/1.46  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.13/1.46  tff(f_35, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.13/1.46  tff(c_32, plain, (k5_relat_1('#skF_7', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.13/1.46  tff(c_70, plain, (k5_relat_1(k1_xboole_0, '#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32])).
% 3.13/1.46  tff(c_34, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.13/1.46  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.13/1.46  tff(c_35, plain, (![A_105]: (v1_relat_1(A_105) | ~v1_xboole_0(A_105))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.13/1.46  tff(c_39, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_35])).
% 3.13/1.46  tff(c_428, plain, (![A_161, B_162, C_163]: (r2_hidden(k4_tarski('#skF_2'(A_161, B_162, C_163), '#skF_4'(A_161, B_162, C_163)), A_161) | r2_hidden(k4_tarski('#skF_5'(A_161, B_162, C_163), '#skF_6'(A_161, B_162, C_163)), C_163) | k5_relat_1(A_161, B_162)=C_163 | ~v1_relat_1(C_163) | ~v1_relat_1(B_162) | ~v1_relat_1(A_161))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.13/1.46  tff(c_6, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.13/1.46  tff(c_62, plain, (![A_108, B_109]: (~r2_hidden(A_108, k2_zfmisc_1(A_108, B_109)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.13/1.46  tff(c_65, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_62])).
% 3.13/1.46  tff(c_486, plain, (![A_161, B_162]: (r2_hidden(k4_tarski('#skF_2'(A_161, B_162, k1_xboole_0), '#skF_4'(A_161, B_162, k1_xboole_0)), A_161) | k5_relat_1(A_161, B_162)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(B_162) | ~v1_relat_1(A_161))), inference(resolution, [status(thm)], [c_428, c_65])).
% 3.13/1.46  tff(c_504, plain, (![A_164, B_165]: (r2_hidden(k4_tarski('#skF_2'(A_164, B_165, k1_xboole_0), '#skF_4'(A_164, B_165, k1_xboole_0)), A_164) | k5_relat_1(A_164, B_165)=k1_xboole_0 | ~v1_relat_1(B_165) | ~v1_relat_1(A_164))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_486])).
% 3.13/1.46  tff(c_534, plain, (![B_165]: (k5_relat_1(k1_xboole_0, B_165)=k1_xboole_0 | ~v1_relat_1(B_165) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_504, c_65])).
% 3.13/1.46  tff(c_545, plain, (![B_166]: (k5_relat_1(k1_xboole_0, B_166)=k1_xboole_0 | ~v1_relat_1(B_166))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_534])).
% 3.13/1.46  tff(c_551, plain, (k5_relat_1(k1_xboole_0, '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_545])).
% 3.13/1.46  tff(c_557, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_551])).
% 3.13/1.46  tff(c_558, plain, (k5_relat_1('#skF_7', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 3.13/1.46  tff(c_904, plain, (![A_213, B_214, C_215]: (r2_hidden(k4_tarski('#skF_4'(A_213, B_214, C_215), '#skF_3'(A_213, B_214, C_215)), B_214) | r2_hidden(k4_tarski('#skF_5'(A_213, B_214, C_215), '#skF_6'(A_213, B_214, C_215)), C_215) | k5_relat_1(A_213, B_214)=C_215 | ~v1_relat_1(C_215) | ~v1_relat_1(B_214) | ~v1_relat_1(A_213))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.13/1.46  tff(c_934, plain, (![A_213, C_215]: (r2_hidden(k4_tarski('#skF_5'(A_213, k1_xboole_0, C_215), '#skF_6'(A_213, k1_xboole_0, C_215)), C_215) | k5_relat_1(A_213, k1_xboole_0)=C_215 | ~v1_relat_1(C_215) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_213))), inference(resolution, [status(thm)], [c_904, c_65])).
% 3.13/1.46  tff(c_994, plain, (![A_220, C_221]: (r2_hidden(k4_tarski('#skF_5'(A_220, k1_xboole_0, C_221), '#skF_6'(A_220, k1_xboole_0, C_221)), C_221) | k5_relat_1(A_220, k1_xboole_0)=C_221 | ~v1_relat_1(C_221) | ~v1_relat_1(A_220))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_934])).
% 3.13/1.46  tff(c_1024, plain, (![A_220]: (k5_relat_1(A_220, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_220))), inference(resolution, [status(thm)], [c_994, c_65])).
% 3.13/1.46  tff(c_1035, plain, (![A_222]: (k5_relat_1(A_222, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_222))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_1024])).
% 3.13/1.46  tff(c_1041, plain, (k5_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_1035])).
% 3.13/1.46  tff(c_1047, plain, $false, inference(negUnitSimplification, [status(thm)], [c_558, c_1041])).
% 3.13/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.46  
% 3.13/1.46  Inference rules
% 3.13/1.46  ----------------------
% 3.13/1.46  #Ref     : 0
% 3.13/1.46  #Sup     : 201
% 3.13/1.46  #Fact    : 0
% 3.13/1.46  #Define  : 0
% 3.13/1.46  #Split   : 1
% 3.13/1.46  #Chain   : 0
% 3.13/1.46  #Close   : 0
% 3.13/1.46  
% 3.13/1.46  Ordering : KBO
% 3.13/1.46  
% 3.13/1.46  Simplification rules
% 3.13/1.46  ----------------------
% 3.13/1.46  #Subsume      : 47
% 3.13/1.46  #Demod        : 141
% 3.13/1.46  #Tautology    : 21
% 3.13/1.46  #SimpNegUnit  : 8
% 3.13/1.46  #BackRed      : 0
% 3.13/1.46  
% 3.13/1.46  #Partial instantiations: 0
% 3.13/1.46  #Strategies tried      : 1
% 3.13/1.46  
% 3.13/1.46  Timing (in seconds)
% 3.13/1.46  ----------------------
% 3.13/1.46  Preprocessing        : 0.29
% 3.13/1.46  Parsing              : 0.15
% 3.13/1.46  CNF conversion       : 0.03
% 3.13/1.46  Main loop            : 0.42
% 3.13/1.46  Inferencing          : 0.16
% 3.13/1.46  Reduction            : 0.10
% 3.13/1.46  Demodulation         : 0.07
% 3.13/1.46  BG Simplification    : 0.02
% 3.13/1.46  Subsumption          : 0.11
% 3.13/1.46  Abstraction          : 0.02
% 3.13/1.46  MUC search           : 0.00
% 3.13/1.46  Cooper               : 0.00
% 3.13/1.46  Total                : 0.73
% 3.13/1.46  Index Insertion      : 0.00
% 3.13/1.46  Index Deletion       : 0.00
% 3.13/1.46  Index Matching       : 0.00
% 3.13/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
