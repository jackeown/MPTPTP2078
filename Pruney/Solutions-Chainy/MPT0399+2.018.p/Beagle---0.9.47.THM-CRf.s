%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:34 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 139 expanded)
%              Number of leaves         :   22 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :   63 ( 252 expanded)
%              Number of equality atoms :   17 (  55 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k4_xboole_0 > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_36,plain,(
    r1_setfam_1('#skF_7',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_32,plain,(
    ! [A_23,B_24] :
      ( r2_hidden('#skF_5'(A_23,B_24),A_23)
      | r1_setfam_1(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_143,plain,(
    ! [A_63,B_64,C_65] :
      ( r2_hidden('#skF_6'(A_63,B_64,C_65),B_64)
      | ~ r2_hidden(C_65,A_63)
      | ~ r1_setfam_1(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_44,plain,(
    ! [B_36,A_37] :
      ( ~ r2_hidden(B_36,A_37)
      | k4_xboole_0(A_37,k1_tarski(B_36)) != A_37 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_49,plain,(
    ! [B_36] : ~ r2_hidden(B_36,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_44])).

tff(c_167,plain,(
    ! [C_66,A_67] :
      ( ~ r2_hidden(C_66,A_67)
      | ~ r1_setfam_1(A_67,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_143,c_49])).

tff(c_184,plain,(
    ! [A_68,B_69] :
      ( ~ r1_setfam_1(A_68,k1_xboole_0)
      | r1_setfam_1(A_68,B_69) ) ),
    inference(resolution,[status(thm)],[c_32,c_167])).

tff(c_207,plain,(
    ! [B_69] : r1_setfam_1('#skF_7',B_69) ),
    inference(resolution,[status(thm)],[c_36,c_184])).

tff(c_18,plain,(
    ! [A_2,B_3] :
      ( r2_hidden('#skF_2'(A_2,B_3),A_2)
      | r2_hidden('#skF_3'(A_2,B_3),B_3)
      | k3_tarski(A_2) = B_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    ! [A_23,B_24,C_33] :
      ( r2_hidden('#skF_6'(A_23,B_24,C_33),B_24)
      | ~ r2_hidden(C_33,A_23)
      | ~ r1_setfam_1(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_785,plain,(
    ! [B_104,C_105,A_106] :
      ( ~ r1_setfam_1(B_104,k1_xboole_0)
      | ~ r2_hidden(C_105,A_106)
      | ~ r1_setfam_1(A_106,B_104) ) ),
    inference(resolution,[status(thm)],[c_28,c_167])).

tff(c_802,plain,(
    ! [C_107,A_108] :
      ( ~ r2_hidden(C_107,A_108)
      | ~ r1_setfam_1(A_108,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_207,c_785])).

tff(c_1842,plain,(
    ! [A_135,B_136] :
      ( ~ r1_setfam_1(A_135,'#skF_7')
      | r2_hidden('#skF_3'(A_135,B_136),B_136)
      | k3_tarski(A_135) = B_136 ) ),
    inference(resolution,[status(thm)],[c_18,c_802])).

tff(c_800,plain,(
    ! [C_105,A_106] :
      ( ~ r2_hidden(C_105,A_106)
      | ~ r1_setfam_1(A_106,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_207,c_785])).

tff(c_1894,plain,(
    ! [B_137,A_138] :
      ( ~ r1_setfam_1(B_137,'#skF_7')
      | ~ r1_setfam_1(A_138,'#skF_7')
      | k3_tarski(A_138) = B_137 ) ),
    inference(resolution,[status(thm)],[c_1842,c_800])).

tff(c_1923,plain,(
    ! [A_139] :
      ( ~ r1_setfam_1(A_139,'#skF_7')
      | k3_tarski(A_139) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_207,c_1894])).

tff(c_1957,plain,(
    k3_tarski('#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_207,c_1923])).

tff(c_244,plain,(
    ! [A_75,B_76] :
      ( r2_hidden('#skF_2'(A_75,B_76),A_75)
      | r2_hidden('#skF_3'(A_75,B_76),B_76)
      | k3_tarski(A_75) = B_76 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_425,plain,(
    ! [A_85] :
      ( r2_hidden('#skF_2'(A_85,k1_xboole_0),A_85)
      | k3_tarski(A_85) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_244,c_49])).

tff(c_166,plain,(
    ! [C_65,A_63] :
      ( ~ r2_hidden(C_65,A_63)
      | ~ r1_setfam_1(A_63,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_143,c_49])).

tff(c_513,plain,(
    ! [A_88] :
      ( ~ r1_setfam_1(A_88,k1_xboole_0)
      | k3_tarski(A_88) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_425,c_166])).

tff(c_527,plain,(
    k3_tarski('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_207,c_513])).

tff(c_1959,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1957,c_527])).

tff(c_1961,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1959])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:08:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.64  
% 3.22/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.64  %$ r2_hidden > r1_tarski > r1_setfam_1 > k4_xboole_0 > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5
% 3.22/1.64  
% 3.22/1.64  %Foreground sorts:
% 3.22/1.64  
% 3.22/1.64  
% 3.22/1.64  %Background operators:
% 3.22/1.64  
% 3.22/1.64  
% 3.22/1.64  %Foreground operators:
% 3.22/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.64  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 3.22/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.22/1.64  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.22/1.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.22/1.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.22/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.22/1.64  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.22/1.64  tff('#skF_7', type, '#skF_7': $i).
% 3.22/1.64  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.22/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.22/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.64  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.22/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.64  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.22/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.22/1.64  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.22/1.64  
% 3.22/1.65  tff(f_59, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_setfam_1)).
% 3.22/1.65  tff(f_54, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 3.22/1.65  tff(f_27, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 3.22/1.65  tff(f_42, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.22/1.65  tff(f_37, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 3.22/1.65  tff(c_34, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.22/1.65  tff(c_36, plain, (r1_setfam_1('#skF_7', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.22/1.65  tff(c_32, plain, (![A_23, B_24]: (r2_hidden('#skF_5'(A_23, B_24), A_23) | r1_setfam_1(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.22/1.65  tff(c_143, plain, (![A_63, B_64, C_65]: (r2_hidden('#skF_6'(A_63, B_64, C_65), B_64) | ~r2_hidden(C_65, A_63) | ~r1_setfam_1(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.22/1.65  tff(c_2, plain, (![A_1]: (k4_xboole_0(k1_xboole_0, A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.22/1.65  tff(c_44, plain, (![B_36, A_37]: (~r2_hidden(B_36, A_37) | k4_xboole_0(A_37, k1_tarski(B_36))!=A_37)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.22/1.65  tff(c_49, plain, (![B_36]: (~r2_hidden(B_36, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_44])).
% 3.22/1.65  tff(c_167, plain, (![C_66, A_67]: (~r2_hidden(C_66, A_67) | ~r1_setfam_1(A_67, k1_xboole_0))), inference(resolution, [status(thm)], [c_143, c_49])).
% 3.22/1.65  tff(c_184, plain, (![A_68, B_69]: (~r1_setfam_1(A_68, k1_xboole_0) | r1_setfam_1(A_68, B_69))), inference(resolution, [status(thm)], [c_32, c_167])).
% 3.22/1.65  tff(c_207, plain, (![B_69]: (r1_setfam_1('#skF_7', B_69))), inference(resolution, [status(thm)], [c_36, c_184])).
% 3.22/1.65  tff(c_18, plain, (![A_2, B_3]: (r2_hidden('#skF_2'(A_2, B_3), A_2) | r2_hidden('#skF_3'(A_2, B_3), B_3) | k3_tarski(A_2)=B_3)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.22/1.65  tff(c_28, plain, (![A_23, B_24, C_33]: (r2_hidden('#skF_6'(A_23, B_24, C_33), B_24) | ~r2_hidden(C_33, A_23) | ~r1_setfam_1(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.22/1.65  tff(c_785, plain, (![B_104, C_105, A_106]: (~r1_setfam_1(B_104, k1_xboole_0) | ~r2_hidden(C_105, A_106) | ~r1_setfam_1(A_106, B_104))), inference(resolution, [status(thm)], [c_28, c_167])).
% 3.22/1.65  tff(c_802, plain, (![C_107, A_108]: (~r2_hidden(C_107, A_108) | ~r1_setfam_1(A_108, '#skF_7'))), inference(resolution, [status(thm)], [c_207, c_785])).
% 3.22/1.65  tff(c_1842, plain, (![A_135, B_136]: (~r1_setfam_1(A_135, '#skF_7') | r2_hidden('#skF_3'(A_135, B_136), B_136) | k3_tarski(A_135)=B_136)), inference(resolution, [status(thm)], [c_18, c_802])).
% 3.22/1.65  tff(c_800, plain, (![C_105, A_106]: (~r2_hidden(C_105, A_106) | ~r1_setfam_1(A_106, '#skF_7'))), inference(resolution, [status(thm)], [c_207, c_785])).
% 3.22/1.65  tff(c_1894, plain, (![B_137, A_138]: (~r1_setfam_1(B_137, '#skF_7') | ~r1_setfam_1(A_138, '#skF_7') | k3_tarski(A_138)=B_137)), inference(resolution, [status(thm)], [c_1842, c_800])).
% 3.22/1.65  tff(c_1923, plain, (![A_139]: (~r1_setfam_1(A_139, '#skF_7') | k3_tarski(A_139)='#skF_7')), inference(resolution, [status(thm)], [c_207, c_1894])).
% 3.22/1.65  tff(c_1957, plain, (k3_tarski('#skF_7')='#skF_7'), inference(resolution, [status(thm)], [c_207, c_1923])).
% 3.22/1.65  tff(c_244, plain, (![A_75, B_76]: (r2_hidden('#skF_2'(A_75, B_76), A_75) | r2_hidden('#skF_3'(A_75, B_76), B_76) | k3_tarski(A_75)=B_76)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.22/1.65  tff(c_425, plain, (![A_85]: (r2_hidden('#skF_2'(A_85, k1_xboole_0), A_85) | k3_tarski(A_85)=k1_xboole_0)), inference(resolution, [status(thm)], [c_244, c_49])).
% 3.22/1.65  tff(c_166, plain, (![C_65, A_63]: (~r2_hidden(C_65, A_63) | ~r1_setfam_1(A_63, k1_xboole_0))), inference(resolution, [status(thm)], [c_143, c_49])).
% 3.22/1.65  tff(c_513, plain, (![A_88]: (~r1_setfam_1(A_88, k1_xboole_0) | k3_tarski(A_88)=k1_xboole_0)), inference(resolution, [status(thm)], [c_425, c_166])).
% 3.22/1.65  tff(c_527, plain, (k3_tarski('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_207, c_513])).
% 3.22/1.65  tff(c_1959, plain, (k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1957, c_527])).
% 3.22/1.65  tff(c_1961, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_1959])).
% 3.22/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.65  
% 3.22/1.65  Inference rules
% 3.22/1.65  ----------------------
% 3.22/1.65  #Ref     : 0
% 3.22/1.65  #Sup     : 438
% 3.22/1.65  #Fact    : 0
% 3.22/1.65  #Define  : 0
% 3.22/1.65  #Split   : 0
% 3.22/1.65  #Chain   : 0
% 3.22/1.65  #Close   : 0
% 3.22/1.65  
% 3.22/1.65  Ordering : KBO
% 3.22/1.65  
% 3.22/1.65  Simplification rules
% 3.22/1.65  ----------------------
% 3.22/1.65  #Subsume      : 119
% 3.22/1.65  #Demod        : 329
% 3.22/1.65  #Tautology    : 186
% 3.22/1.65  #SimpNegUnit  : 4
% 3.22/1.65  #BackRed      : 11
% 3.22/1.65  
% 3.22/1.65  #Partial instantiations: 0
% 3.22/1.65  #Strategies tried      : 1
% 3.22/1.65  
% 3.22/1.65  Timing (in seconds)
% 3.22/1.65  ----------------------
% 3.22/1.65  Preprocessing        : 0.27
% 3.22/1.65  Parsing              : 0.13
% 3.22/1.65  CNF conversion       : 0.02
% 3.22/1.65  Main loop            : 0.45
% 3.22/1.65  Inferencing          : 0.15
% 3.22/1.65  Reduction            : 0.13
% 3.22/1.65  Demodulation         : 0.08
% 3.22/1.65  BG Simplification    : 0.02
% 3.22/1.65  Subsumption          : 0.12
% 3.22/1.65  Abstraction          : 0.02
% 3.22/1.65  MUC search           : 0.00
% 3.22/1.65  Cooper               : 0.00
% 3.22/1.65  Total                : 0.75
% 3.22/1.65  Index Insertion      : 0.00
% 3.22/1.65  Index Deletion       : 0.00
% 3.22/1.65  Index Matching       : 0.00
% 3.22/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
