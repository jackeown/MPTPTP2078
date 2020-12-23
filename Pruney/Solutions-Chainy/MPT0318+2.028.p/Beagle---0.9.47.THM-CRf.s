%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:05 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 153 expanded)
%              Number of leaves         :   22 (  59 expanded)
%              Depth                    :    9
%              Number of atoms          :   65 ( 277 expanded)
%              Number of equality atoms :   55 ( 259 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_48,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_xboole_0
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_32,plain,(
    ! [B_18] : k2_zfmisc_1(k1_xboole_0,B_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_44,plain,
    ( k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_89,plain,(
    k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_103,plain,(
    ! [B_35,A_36] :
      ( k1_xboole_0 = B_35
      | k1_xboole_0 = A_36
      | k2_zfmisc_1(A_36,B_35) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_106,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_103])).

tff(c_115,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_106])).

tff(c_204,plain,(
    ! [A_53,B_54] :
      ( k4_xboole_0(k1_tarski(A_53),k1_tarski(B_54)) = k1_tarski(A_53)
      | B_54 = A_53 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_220,plain,(
    ! [B_54] :
      ( k4_xboole_0(k1_xboole_0,k1_tarski(B_54)) = k1_tarski('#skF_4')
      | B_54 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_204])).

tff(c_230,plain,(
    ! [B_55] :
      ( k4_xboole_0(k1_xboole_0,k1_tarski(B_55)) = k1_xboole_0
      | B_55 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_220])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_166,plain,(
    ! [A_43,C_44,B_45] :
      ( r2_hidden(A_43,C_44)
      | k4_xboole_0(k2_tarski(A_43,B_45),C_44) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_170,plain,(
    ! [A_46,C_47] :
      ( r2_hidden(A_46,C_47)
      | k4_xboole_0(k1_tarski(A_46),C_47) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_166])).

tff(c_174,plain,(
    ! [C_48] :
      ( r2_hidden('#skF_4',C_48)
      | k4_xboole_0(k1_xboole_0,C_48) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_170])).

tff(c_137,plain,(
    ! [D_37,B_38,A_39] :
      ( D_37 = B_38
      | D_37 = A_39
      | ~ r2_hidden(D_37,k2_tarski(A_39,B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_140,plain,(
    ! [D_37,A_7] :
      ( D_37 = A_7
      | D_37 = A_7
      | ~ r2_hidden(D_37,k1_tarski(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_137])).

tff(c_188,plain,(
    ! [A_7] :
      ( A_7 = '#skF_4'
      | k4_xboole_0(k1_xboole_0,k1_tarski(A_7)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_174,c_140])).

tff(c_244,plain,(
    ! [B_55] : B_55 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_188])).

tff(c_248,plain,(
    ! [B_56] : B_56 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_188])).

tff(c_34,plain,(
    ! [B_20] : k4_xboole_0(k1_tarski(B_20),k1_tarski(B_20)) != k1_tarski(B_20) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_125,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_4')) != k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_34])).

tff(c_134,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_115,c_125])).

tff(c_272,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_134])).

tff(c_310,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_272])).

tff(c_311,plain,(
    k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_326,plain,(
    ! [B_670,A_671] :
      ( k1_xboole_0 = B_670
      | k1_xboole_0 = A_671
      | k2_zfmisc_1(A_671,B_670) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_329,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_326])).

tff(c_338,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_329])).

tff(c_312,plain,(
    k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_343,plain,(
    k2_zfmisc_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_312])).

tff(c_347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_343])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:05:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.28  
% 2.08/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.28  %$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.08/1.28  
% 2.08/1.28  %Foreground sorts:
% 2.08/1.28  
% 2.08/1.28  
% 2.08/1.28  %Background operators:
% 2.08/1.28  
% 2.08/1.28  
% 2.08/1.28  %Foreground operators:
% 2.08/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.08/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.08/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.08/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.08/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.08/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.08/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.08/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.08/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.28  
% 2.08/1.29  tff(f_48, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.08/1.29  tff(f_69, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 2.08/1.29  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.08/1.29  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.08/1.29  tff(f_59, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_xboole_0) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 2.08/1.29  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.08/1.29  tff(c_32, plain, (![B_18]: (k2_zfmisc_1(k1_xboole_0, B_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.08/1.29  tff(c_46, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.08/1.29  tff(c_44, plain, (k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.08/1.29  tff(c_89, plain, (k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_44])).
% 2.08/1.29  tff(c_103, plain, (![B_35, A_36]: (k1_xboole_0=B_35 | k1_xboole_0=A_36 | k2_zfmisc_1(A_36, B_35)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.08/1.29  tff(c_106, plain, (k1_xboole_0='#skF_3' | k1_tarski('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_89, c_103])).
% 2.08/1.29  tff(c_115, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_46, c_106])).
% 2.08/1.29  tff(c_204, plain, (![A_53, B_54]: (k4_xboole_0(k1_tarski(A_53), k1_tarski(B_54))=k1_tarski(A_53) | B_54=A_53)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.08/1.29  tff(c_220, plain, (![B_54]: (k4_xboole_0(k1_xboole_0, k1_tarski(B_54))=k1_tarski('#skF_4') | B_54='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_115, c_204])).
% 2.08/1.29  tff(c_230, plain, (![B_55]: (k4_xboole_0(k1_xboole_0, k1_tarski(B_55))=k1_xboole_0 | B_55='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_115, c_220])).
% 2.08/1.29  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.08/1.29  tff(c_166, plain, (![A_43, C_44, B_45]: (r2_hidden(A_43, C_44) | k4_xboole_0(k2_tarski(A_43, B_45), C_44)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.08/1.29  tff(c_170, plain, (![A_46, C_47]: (r2_hidden(A_46, C_47) | k4_xboole_0(k1_tarski(A_46), C_47)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_166])).
% 2.08/1.29  tff(c_174, plain, (![C_48]: (r2_hidden('#skF_4', C_48) | k4_xboole_0(k1_xboole_0, C_48)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_115, c_170])).
% 2.08/1.29  tff(c_137, plain, (![D_37, B_38, A_39]: (D_37=B_38 | D_37=A_39 | ~r2_hidden(D_37, k2_tarski(A_39, B_38)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.08/1.29  tff(c_140, plain, (![D_37, A_7]: (D_37=A_7 | D_37=A_7 | ~r2_hidden(D_37, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_137])).
% 2.08/1.29  tff(c_188, plain, (![A_7]: (A_7='#skF_4' | k4_xboole_0(k1_xboole_0, k1_tarski(A_7))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_174, c_140])).
% 2.08/1.29  tff(c_244, plain, (![B_55]: (B_55='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_230, c_188])).
% 2.08/1.29  tff(c_248, plain, (![B_56]: (B_56='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_230, c_188])).
% 2.08/1.29  tff(c_34, plain, (![B_20]: (k4_xboole_0(k1_tarski(B_20), k1_tarski(B_20))!=k1_tarski(B_20))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.08/1.29  tff(c_125, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_4'))!=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_115, c_34])).
% 2.08/1.29  tff(c_134, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_115, c_115, c_125])).
% 2.08/1.29  tff(c_272, plain, (k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_248, c_134])).
% 2.08/1.29  tff(c_310, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_244, c_272])).
% 2.08/1.29  tff(c_311, plain, (k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_44])).
% 2.08/1.29  tff(c_326, plain, (![B_670, A_671]: (k1_xboole_0=B_670 | k1_xboole_0=A_671 | k2_zfmisc_1(A_671, B_670)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.08/1.29  tff(c_329, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_311, c_326])).
% 2.08/1.29  tff(c_338, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_46, c_329])).
% 2.08/1.29  tff(c_312, plain, (k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_44])).
% 2.08/1.29  tff(c_343, plain, (k2_zfmisc_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_338, c_312])).
% 2.08/1.29  tff(c_347, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_343])).
% 2.08/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.29  
% 2.08/1.29  Inference rules
% 2.08/1.29  ----------------------
% 2.08/1.29  #Ref     : 0
% 2.08/1.29  #Sup     : 83
% 2.08/1.29  #Fact    : 0
% 2.08/1.29  #Define  : 0
% 2.08/1.29  #Split   : 1
% 2.08/1.29  #Chain   : 0
% 2.08/1.29  #Close   : 0
% 2.08/1.29  
% 2.08/1.29  Ordering : KBO
% 2.08/1.29  
% 2.08/1.29  Simplification rules
% 2.08/1.29  ----------------------
% 2.08/1.29  #Subsume      : 13
% 2.08/1.29  #Demod        : 11
% 2.08/1.29  #Tautology    : 36
% 2.08/1.29  #SimpNegUnit  : 3
% 2.08/1.29  #BackRed      : 3
% 2.08/1.29  
% 2.08/1.29  #Partial instantiations: 0
% 2.08/1.29  #Strategies tried      : 1
% 2.08/1.29  
% 2.08/1.29  Timing (in seconds)
% 2.08/1.29  ----------------------
% 2.08/1.29  Preprocessing        : 0.32
% 2.08/1.29  Parsing              : 0.16
% 2.08/1.29  CNF conversion       : 0.02
% 2.08/1.29  Main loop            : 0.21
% 2.08/1.29  Inferencing          : 0.08
% 2.08/1.29  Reduction            : 0.06
% 2.08/1.29  Demodulation         : 0.04
% 2.08/1.29  BG Simplification    : 0.01
% 2.08/1.29  Subsumption          : 0.04
% 2.08/1.29  Abstraction          : 0.01
% 2.08/1.29  MUC search           : 0.00
% 2.08/1.29  Cooper               : 0.00
% 2.08/1.29  Total                : 0.55
% 2.08/1.29  Index Insertion      : 0.00
% 2.08/1.29  Index Deletion       : 0.00
% 2.08/1.29  Index Matching       : 0.00
% 2.08/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
