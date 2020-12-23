%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:07 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   54 (  74 expanded)
%              Number of leaves         :   29 (  40 expanded)
%              Depth                    :    6
%              Number of atoms          :   57 ( 102 expanded)
%              Number of equality atoms :   35 (  63 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_56,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_54,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_81,plain,(
    ! [A_58,B_59] : k1_enumset1(A_58,A_58,B_59) = k2_tarski(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18,plain,(
    ! [E_13,A_7,C_9] : r2_hidden(E_13,k1_enumset1(A_7,E_13,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_87,plain,(
    ! [A_58,B_59] : r2_hidden(A_58,k2_tarski(A_58,B_59)) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_18])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_110,plain,(
    ! [A_65,B_66] :
      ( k4_xboole_0(A_65,B_66) = k1_xboole_0
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_122,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_110])).

tff(c_380,plain,(
    ! [A_104,C_105,B_106] :
      ( ~ r2_hidden(A_104,C_105)
      | k4_xboole_0(k2_tarski(A_104,B_106),C_105) != k1_tarski(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_384,plain,(
    ! [A_104,B_106] :
      ( ~ r2_hidden(A_104,k2_tarski(A_104,B_106))
      | k1_tarski(A_104) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_380])).

tff(c_389,plain,(
    ! [A_104] : k1_tarski(A_104) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_384])).

tff(c_62,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_60,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_38,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_56,plain,(
    ! [B_43,C_44] :
      ( k4_xboole_0(k2_tarski(B_43,B_43),C_44) = k1_tarski(B_43)
      | r2_hidden(B_43,C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_170,plain,(
    ! [B_75,C_76] :
      ( k4_xboole_0(k1_tarski(B_75),C_76) = k1_tarski(B_75)
      | r2_hidden(B_75,C_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_56])).

tff(c_64,plain,(
    r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_121,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_110])).

tff(c_176,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | r2_hidden('#skF_3',k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_121])).

tff(c_195,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_40,plain,(
    ! [A_15,B_16] : k1_enumset1(A_15,A_15,B_16) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_272,plain,(
    ! [E_94,C_95,B_96,A_97] :
      ( E_94 = C_95
      | E_94 = B_96
      | E_94 = A_97
      | ~ r2_hidden(E_94,k1_enumset1(A_97,B_96,C_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_330,plain,(
    ! [E_101,B_102,A_103] :
      ( E_101 = B_102
      | E_101 = A_103
      | E_101 = A_103
      | ~ r2_hidden(E_101,k2_tarski(A_103,B_102)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_272])).

tff(c_333,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_195,c_330])).

tff(c_346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_62,c_60,c_333])).

tff(c_347,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_391,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_389,c_347])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:19:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.33  
% 2.33/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.33  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.33/1.33  
% 2.33/1.33  %Foreground sorts:
% 2.33/1.33  
% 2.33/1.33  
% 2.33/1.33  %Background operators:
% 2.33/1.33  
% 2.33/1.33  
% 2.33/1.33  %Foreground operators:
% 2.33/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.33/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.33/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.33/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.33/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.33/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.33/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.33/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.33/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.33/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.33/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.33/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.33/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.33/1.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.33/1.33  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.33/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.33/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.33/1.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.33/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.33/1.33  
% 2.33/1.34  tff(f_56, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.33/1.34  tff(f_52, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.33/1.34  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.33/1.34  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.33/1.34  tff(f_75, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 2.33/1.34  tff(f_85, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.33/1.34  tff(f_54, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.33/1.34  tff(c_81, plain, (![A_58, B_59]: (k1_enumset1(A_58, A_58, B_59)=k2_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.33/1.34  tff(c_18, plain, (![E_13, A_7, C_9]: (r2_hidden(E_13, k1_enumset1(A_7, E_13, C_9)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.33/1.34  tff(c_87, plain, (![A_58, B_59]: (r2_hidden(A_58, k2_tarski(A_58, B_59)))), inference(superposition, [status(thm), theory('equality')], [c_81, c_18])).
% 2.33/1.34  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.33/1.34  tff(c_110, plain, (![A_65, B_66]: (k4_xboole_0(A_65, B_66)=k1_xboole_0 | ~r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.33/1.34  tff(c_122, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_110])).
% 2.33/1.34  tff(c_380, plain, (![A_104, C_105, B_106]: (~r2_hidden(A_104, C_105) | k4_xboole_0(k2_tarski(A_104, B_106), C_105)!=k1_tarski(A_104))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.33/1.34  tff(c_384, plain, (![A_104, B_106]: (~r2_hidden(A_104, k2_tarski(A_104, B_106)) | k1_tarski(A_104)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_122, c_380])).
% 2.33/1.34  tff(c_389, plain, (![A_104]: (k1_tarski(A_104)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_87, c_384])).
% 2.33/1.34  tff(c_62, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.33/1.34  tff(c_60, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.33/1.34  tff(c_38, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.33/1.34  tff(c_56, plain, (![B_43, C_44]: (k4_xboole_0(k2_tarski(B_43, B_43), C_44)=k1_tarski(B_43) | r2_hidden(B_43, C_44))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.33/1.34  tff(c_170, plain, (![B_75, C_76]: (k4_xboole_0(k1_tarski(B_75), C_76)=k1_tarski(B_75) | r2_hidden(B_75, C_76))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_56])).
% 2.33/1.34  tff(c_64, plain, (r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.33/1.34  tff(c_121, plain, (k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_64, c_110])).
% 2.33/1.34  tff(c_176, plain, (k1_tarski('#skF_3')=k1_xboole_0 | r2_hidden('#skF_3', k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_170, c_121])).
% 2.33/1.34  tff(c_195, plain, (r2_hidden('#skF_3', k2_tarski('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_176])).
% 2.33/1.34  tff(c_40, plain, (![A_15, B_16]: (k1_enumset1(A_15, A_15, B_16)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.33/1.34  tff(c_272, plain, (![E_94, C_95, B_96, A_97]: (E_94=C_95 | E_94=B_96 | E_94=A_97 | ~r2_hidden(E_94, k1_enumset1(A_97, B_96, C_95)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.33/1.34  tff(c_330, plain, (![E_101, B_102, A_103]: (E_101=B_102 | E_101=A_103 | E_101=A_103 | ~r2_hidden(E_101, k2_tarski(A_103, B_102)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_272])).
% 2.33/1.34  tff(c_333, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_195, c_330])).
% 2.33/1.34  tff(c_346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_62, c_60, c_333])).
% 2.33/1.34  tff(c_347, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_176])).
% 2.33/1.34  tff(c_391, plain, $false, inference(negUnitSimplification, [status(thm)], [c_389, c_347])).
% 2.33/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.34  
% 2.33/1.34  Inference rules
% 2.33/1.34  ----------------------
% 2.33/1.34  #Ref     : 0
% 2.33/1.34  #Sup     : 73
% 2.33/1.34  #Fact    : 0
% 2.33/1.34  #Define  : 0
% 2.33/1.34  #Split   : 2
% 2.33/1.34  #Chain   : 0
% 2.33/1.34  #Close   : 0
% 2.33/1.34  
% 2.33/1.34  Ordering : KBO
% 2.33/1.34  
% 2.33/1.34  Simplification rules
% 2.33/1.34  ----------------------
% 2.33/1.34  #Subsume      : 9
% 2.33/1.34  #Demod        : 25
% 2.33/1.34  #Tautology    : 42
% 2.33/1.34  #SimpNegUnit  : 5
% 2.33/1.34  #BackRed      : 5
% 2.33/1.34  
% 2.33/1.34  #Partial instantiations: 0
% 2.33/1.34  #Strategies tried      : 1
% 2.33/1.34  
% 2.33/1.34  Timing (in seconds)
% 2.33/1.34  ----------------------
% 2.33/1.34  Preprocessing        : 0.31
% 2.33/1.34  Parsing              : 0.15
% 2.33/1.34  CNF conversion       : 0.02
% 2.33/1.34  Main loop            : 0.22
% 2.33/1.35  Inferencing          : 0.07
% 2.33/1.35  Reduction            : 0.08
% 2.33/1.35  Demodulation         : 0.06
% 2.33/1.35  BG Simplification    : 0.02
% 2.33/1.35  Subsumption          : 0.05
% 2.33/1.35  Abstraction          : 0.01
% 2.33/1.35  MUC search           : 0.00
% 2.33/1.35  Cooper               : 0.00
% 2.33/1.35  Total                : 0.56
% 2.33/1.35  Index Insertion      : 0.00
% 2.33/1.35  Index Deletion       : 0.00
% 2.33/1.35  Index Matching       : 0.00
% 2.33/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
