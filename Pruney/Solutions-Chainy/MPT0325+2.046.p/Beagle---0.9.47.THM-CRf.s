%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:27 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 186 expanded)
%              Number of leaves         :   19 (  70 expanded)
%              Depth                    :    9
%              Number of atoms          :   86 ( 412 expanded)
%              Number of equality atoms :   15 (  46 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_22,plain,
    ( ~ r1_tarski('#skF_3','#skF_5')
    | ~ r1_tarski('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_49,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_100,plain,(
    ! [A_47,B_48,C_49,D_50] :
      ( r2_hidden(k4_tarski(A_47,B_48),k2_zfmisc_1(C_49,D_50))
      | ~ r2_hidden(B_48,D_50)
      | ~ r2_hidden(A_47,C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_170,plain,(
    ! [B_63,B_62,A_60,D_61,C_64] :
      ( r2_hidden(k4_tarski(A_60,B_62),B_63)
      | ~ r1_tarski(k2_zfmisc_1(C_64,D_61),B_63)
      | ~ r2_hidden(B_62,D_61)
      | ~ r2_hidden(A_60,C_64) ) ),
    inference(resolution,[status(thm)],[c_100,c_2])).

tff(c_221,plain,(
    ! [A_70,B_71] :
      ( r2_hidden(k4_tarski(A_70,B_71),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(B_71,'#skF_3')
      | ~ r2_hidden(A_70,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_170])).

tff(c_14,plain,(
    ! [A_8,C_10,B_9,D_11] :
      ( r2_hidden(A_8,C_10)
      | ~ r2_hidden(k4_tarski(A_8,B_9),k2_zfmisc_1(C_10,D_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_236,plain,(
    ! [A_70,B_71] :
      ( r2_hidden(A_70,'#skF_4')
      | ~ r2_hidden(B_71,'#skF_3')
      | ~ r2_hidden(A_70,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_221,c_14])).

tff(c_240,plain,(
    ! [B_72] : ~ r2_hidden(B_72,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_236])).

tff(c_251,plain,(
    ! [B_73] : r1_tarski('#skF_3',B_73) ),
    inference(resolution,[status(thm)],[c_6,c_240])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k4_xboole_0(B_7,A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_256,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_251,c_8])).

tff(c_18,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_266,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_256,c_18])).

tff(c_24,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_268,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_24])).

tff(c_334,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_268])).

tff(c_336,plain,(
    ! [A_76] :
      ( r2_hidden(A_76,'#skF_4')
      | ~ r2_hidden(A_76,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_236])).

tff(c_378,plain,(
    ! [B_79] :
      ( r2_hidden('#skF_1'('#skF_2',B_79),'#skF_4')
      | r1_tarski('#skF_2',B_79) ) ),
    inference(resolution,[status(thm)],[c_6,c_336])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_388,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_378,c_4])).

tff(c_395,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_49,c_388])).

tff(c_396,plain,(
    ~ r1_tarski('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_440,plain,(
    ! [A_110,B_111,C_112,D_113] :
      ( r2_hidden(k4_tarski(A_110,B_111),k2_zfmisc_1(C_112,D_113))
      | ~ r2_hidden(B_111,D_113)
      | ~ r2_hidden(A_110,C_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_601,plain,(
    ! [C_140,A_139,B_142,D_143,B_141] :
      ( r2_hidden(k4_tarski(A_139,B_142),B_141)
      | ~ r1_tarski(k2_zfmisc_1(C_140,D_143),B_141)
      | ~ r2_hidden(B_142,D_143)
      | ~ r2_hidden(A_139,C_140) ) ),
    inference(resolution,[status(thm)],[c_440,c_2])).

tff(c_617,plain,(
    ! [A_144,B_145] :
      ( r2_hidden(k4_tarski(A_144,B_145),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(B_145,'#skF_3')
      | ~ r2_hidden(A_144,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_601])).

tff(c_12,plain,(
    ! [B_9,D_11,A_8,C_10] :
      ( r2_hidden(B_9,D_11)
      | ~ r2_hidden(k4_tarski(A_8,B_9),k2_zfmisc_1(C_10,D_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_627,plain,(
    ! [B_145,A_144] :
      ( r2_hidden(B_145,'#skF_5')
      | ~ r2_hidden(B_145,'#skF_3')
      | ~ r2_hidden(A_144,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_617,c_12])).

tff(c_667,plain,(
    ! [A_149] : ~ r2_hidden(A_149,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_627])).

tff(c_693,plain,(
    ! [B_154] : r1_tarski('#skF_2',B_154) ),
    inference(resolution,[status(thm)],[c_6,c_667])).

tff(c_706,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_693,c_8])).

tff(c_20,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_713,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_2',B_13) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_706,c_20])).

tff(c_714,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_24])).

tff(c_745,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_713,c_714])).

tff(c_747,plain,(
    ! [B_156] :
      ( r2_hidden(B_156,'#skF_5')
      | ~ r2_hidden(B_156,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_627])).

tff(c_756,plain,(
    ! [A_157] :
      ( r1_tarski(A_157,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_157,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_747,c_4])).

tff(c_764,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_756])).

tff(c_769,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_396,c_396,c_764])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:27:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.41  
% 2.67/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.42  %$ r2_hidden > r1_tarski > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.67/1.42  
% 2.67/1.42  %Foreground sorts:
% 2.67/1.42  
% 2.67/1.42  
% 2.67/1.42  %Background operators:
% 2.67/1.42  
% 2.67/1.42  
% 2.67/1.42  %Foreground operators:
% 2.67/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.67/1.42  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.67/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.67/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.67/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.67/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.67/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.67/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.67/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.67/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.67/1.42  
% 2.67/1.43  tff(f_57, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 2.67/1.43  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.67/1.43  tff(f_42, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.67/1.43  tff(f_36, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 2.67/1.43  tff(f_48, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.67/1.43  tff(c_22, plain, (~r1_tarski('#skF_3', '#skF_5') | ~r1_tarski('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.67/1.43  tff(c_49, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_22])).
% 2.67/1.43  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.67/1.43  tff(c_26, plain, (r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.67/1.43  tff(c_100, plain, (![A_47, B_48, C_49, D_50]: (r2_hidden(k4_tarski(A_47, B_48), k2_zfmisc_1(C_49, D_50)) | ~r2_hidden(B_48, D_50) | ~r2_hidden(A_47, C_49))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.67/1.43  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.67/1.43  tff(c_170, plain, (![B_63, B_62, A_60, D_61, C_64]: (r2_hidden(k4_tarski(A_60, B_62), B_63) | ~r1_tarski(k2_zfmisc_1(C_64, D_61), B_63) | ~r2_hidden(B_62, D_61) | ~r2_hidden(A_60, C_64))), inference(resolution, [status(thm)], [c_100, c_2])).
% 2.67/1.43  tff(c_221, plain, (![A_70, B_71]: (r2_hidden(k4_tarski(A_70, B_71), k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(B_71, '#skF_3') | ~r2_hidden(A_70, '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_170])).
% 2.67/1.43  tff(c_14, plain, (![A_8, C_10, B_9, D_11]: (r2_hidden(A_8, C_10) | ~r2_hidden(k4_tarski(A_8, B_9), k2_zfmisc_1(C_10, D_11)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.67/1.43  tff(c_236, plain, (![A_70, B_71]: (r2_hidden(A_70, '#skF_4') | ~r2_hidden(B_71, '#skF_3') | ~r2_hidden(A_70, '#skF_2'))), inference(resolution, [status(thm)], [c_221, c_14])).
% 2.67/1.43  tff(c_240, plain, (![B_72]: (~r2_hidden(B_72, '#skF_3'))), inference(splitLeft, [status(thm)], [c_236])).
% 2.67/1.43  tff(c_251, plain, (![B_73]: (r1_tarski('#skF_3', B_73))), inference(resolution, [status(thm)], [c_6, c_240])).
% 2.67/1.43  tff(c_8, plain, (![A_6, B_7]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k4_xboole_0(B_7, A_6)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.67/1.43  tff(c_256, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_251, c_8])).
% 2.67/1.43  tff(c_18, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.67/1.43  tff(c_266, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_256, c_256, c_18])).
% 2.67/1.43  tff(c_24, plain, (k2_zfmisc_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.67/1.43  tff(c_268, plain, (k2_zfmisc_1('#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_256, c_24])).
% 2.67/1.43  tff(c_334, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_266, c_268])).
% 2.67/1.43  tff(c_336, plain, (![A_76]: (r2_hidden(A_76, '#skF_4') | ~r2_hidden(A_76, '#skF_2'))), inference(splitRight, [status(thm)], [c_236])).
% 2.67/1.43  tff(c_378, plain, (![B_79]: (r2_hidden('#skF_1'('#skF_2', B_79), '#skF_4') | r1_tarski('#skF_2', B_79))), inference(resolution, [status(thm)], [c_6, c_336])).
% 2.67/1.43  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.67/1.43  tff(c_388, plain, (r1_tarski('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_378, c_4])).
% 2.67/1.43  tff(c_395, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_49, c_388])).
% 2.67/1.43  tff(c_396, plain, (~r1_tarski('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_22])).
% 2.67/1.43  tff(c_440, plain, (![A_110, B_111, C_112, D_113]: (r2_hidden(k4_tarski(A_110, B_111), k2_zfmisc_1(C_112, D_113)) | ~r2_hidden(B_111, D_113) | ~r2_hidden(A_110, C_112))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.67/1.43  tff(c_601, plain, (![C_140, A_139, B_142, D_143, B_141]: (r2_hidden(k4_tarski(A_139, B_142), B_141) | ~r1_tarski(k2_zfmisc_1(C_140, D_143), B_141) | ~r2_hidden(B_142, D_143) | ~r2_hidden(A_139, C_140))), inference(resolution, [status(thm)], [c_440, c_2])).
% 2.67/1.43  tff(c_617, plain, (![A_144, B_145]: (r2_hidden(k4_tarski(A_144, B_145), k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(B_145, '#skF_3') | ~r2_hidden(A_144, '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_601])).
% 2.67/1.43  tff(c_12, plain, (![B_9, D_11, A_8, C_10]: (r2_hidden(B_9, D_11) | ~r2_hidden(k4_tarski(A_8, B_9), k2_zfmisc_1(C_10, D_11)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.67/1.43  tff(c_627, plain, (![B_145, A_144]: (r2_hidden(B_145, '#skF_5') | ~r2_hidden(B_145, '#skF_3') | ~r2_hidden(A_144, '#skF_2'))), inference(resolution, [status(thm)], [c_617, c_12])).
% 2.67/1.43  tff(c_667, plain, (![A_149]: (~r2_hidden(A_149, '#skF_2'))), inference(splitLeft, [status(thm)], [c_627])).
% 2.67/1.43  tff(c_693, plain, (![B_154]: (r1_tarski('#skF_2', B_154))), inference(resolution, [status(thm)], [c_6, c_667])).
% 2.67/1.43  tff(c_706, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_693, c_8])).
% 2.67/1.43  tff(c_20, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.67/1.43  tff(c_713, plain, (![B_13]: (k2_zfmisc_1('#skF_2', B_13)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_706, c_706, c_20])).
% 2.67/1.43  tff(c_714, plain, (k2_zfmisc_1('#skF_2', '#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_706, c_24])).
% 2.67/1.43  tff(c_745, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_713, c_714])).
% 2.67/1.43  tff(c_747, plain, (![B_156]: (r2_hidden(B_156, '#skF_5') | ~r2_hidden(B_156, '#skF_3'))), inference(splitRight, [status(thm)], [c_627])).
% 2.67/1.43  tff(c_756, plain, (![A_157]: (r1_tarski(A_157, '#skF_5') | ~r2_hidden('#skF_1'(A_157, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_747, c_4])).
% 2.67/1.43  tff(c_764, plain, (r1_tarski('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_756])).
% 2.67/1.43  tff(c_769, plain, $false, inference(negUnitSimplification, [status(thm)], [c_396, c_396, c_764])).
% 2.67/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.43  
% 2.67/1.43  Inference rules
% 2.67/1.43  ----------------------
% 2.67/1.43  #Ref     : 0
% 2.67/1.43  #Sup     : 158
% 2.67/1.43  #Fact    : 0
% 2.67/1.43  #Define  : 0
% 2.67/1.43  #Split   : 8
% 2.67/1.43  #Chain   : 0
% 2.67/1.43  #Close   : 0
% 2.67/1.43  
% 2.67/1.43  Ordering : KBO
% 2.67/1.43  
% 2.67/1.43  Simplification rules
% 2.67/1.43  ----------------------
% 2.67/1.43  #Subsume      : 55
% 2.67/1.43  #Demod        : 78
% 2.67/1.43  #Tautology    : 55
% 2.67/1.43  #SimpNegUnit  : 16
% 2.67/1.43  #BackRed      : 32
% 2.67/1.43  
% 2.67/1.43  #Partial instantiations: 0
% 2.67/1.43  #Strategies tried      : 1
% 2.67/1.43  
% 2.67/1.43  Timing (in seconds)
% 2.67/1.43  ----------------------
% 2.67/1.43  Preprocessing        : 0.27
% 2.67/1.43  Parsing              : 0.15
% 2.67/1.43  CNF conversion       : 0.02
% 2.67/1.43  Main loop            : 0.34
% 2.67/1.43  Inferencing          : 0.12
% 2.67/1.43  Reduction            : 0.09
% 2.67/1.43  Demodulation         : 0.06
% 2.67/1.43  BG Simplification    : 0.02
% 2.67/1.43  Subsumption          : 0.08
% 2.67/1.43  Abstraction          : 0.01
% 2.67/1.43  MUC search           : 0.00
% 2.67/1.43  Cooper               : 0.00
% 2.67/1.43  Total                : 0.64
% 2.67/1.43  Index Insertion      : 0.00
% 2.67/1.43  Index Deletion       : 0.00
% 2.67/1.43  Index Matching       : 0.00
% 2.67/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
