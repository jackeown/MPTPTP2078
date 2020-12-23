%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:41 EST 2020

% Result     : Theorem 20.19s
% Output     : CNFRefutation 20.19s
% Verified   : 
% Statistics : Number of formulae       :   47 (  61 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   61 (  98 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k2_xboole_0 > k2_setfam_1 > #nlpp > #skF_6 > #skF_10 > #skF_5 > #skF_2 > #skF_11 > #skF_7 > #skF_9 > #skF_3 > #skF_8 > #skF_1 > #skF_12 > #skF_4

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

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_setfam_1,type,(
    k2_setfam_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( C = k2_setfam_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k2_xboole_0(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_setfam_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_68,negated_conjecture,(
    ~ ! [A] : r1_setfam_1(A,k2_setfam_1(A,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_setfam_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_4'(A_12,B_13),A_12)
      | r1_setfam_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_34,plain,(
    ! [E_56,F_57,A_24,B_25] :
      ( r2_hidden(k2_xboole_0(E_56,F_57),k2_setfam_1(A_24,B_25))
      | ~ r2_hidden(F_57,B_25)
      | ~ r2_hidden(E_56,A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | r2_hidden(D_11,k2_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_63,plain,(
    ! [A_68,B_69] :
      ( ~ r2_hidden('#skF_1'(A_68,B_69),B_69)
      | r1_tarski(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_210,plain,(
    ! [A_109,A_110,B_111] :
      ( r1_tarski(A_109,k2_xboole_0(A_110,B_111))
      | ~ r2_hidden('#skF_1'(A_109,k2_xboole_0(A_110,B_111)),B_111) ) ),
    inference(resolution,[status(thm)],[c_10,c_63])).

tff(c_231,plain,(
    ! [A_112,A_113] : r1_tarski(A_112,k2_xboole_0(A_113,A_112)) ),
    inference(resolution,[status(thm)],[c_6,c_210])).

tff(c_30,plain,(
    ! [A_12,B_13,D_21] :
      ( ~ r1_tarski('#skF_4'(A_12,B_13),D_21)
      | ~ r2_hidden(D_21,B_13)
      | r1_setfam_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_301,plain,(
    ! [A_129,A_130,B_131] :
      ( ~ r2_hidden(k2_xboole_0(A_129,'#skF_4'(A_130,B_131)),B_131)
      | r1_setfam_1(A_130,B_131) ) ),
    inference(resolution,[status(thm)],[c_231,c_30])).

tff(c_65805,plain,(
    ! [A_1573,A_1574,B_1575,E_1576] :
      ( r1_setfam_1(A_1573,k2_setfam_1(A_1574,B_1575))
      | ~ r2_hidden('#skF_4'(A_1573,k2_setfam_1(A_1574,B_1575)),B_1575)
      | ~ r2_hidden(E_1576,A_1574) ) ),
    inference(resolution,[status(thm)],[c_34,c_301])).

tff(c_65978,plain,(
    ! [E_1577,A_1578,A_1579] :
      ( ~ r2_hidden(E_1577,A_1578)
      | r1_setfam_1(A_1579,k2_setfam_1(A_1578,A_1579)) ) ),
    inference(resolution,[status(thm)],[c_32,c_65805])).

tff(c_66291,plain,(
    ! [A_1580,A_1581,B_1582] :
      ( r1_setfam_1(A_1580,k2_setfam_1(A_1581,A_1580))
      | r1_tarski(A_1581,B_1582) ) ),
    inference(resolution,[status(thm)],[c_6,c_65978])).

tff(c_58,plain,(
    ~ r1_setfam_1('#skF_12',k2_setfam_1('#skF_12','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_66739,plain,(
    ! [B_1583] : r1_tarski('#skF_12',B_1583) ),
    inference(resolution,[status(thm)],[c_66291,c_58])).

tff(c_80,plain,(
    ! [C_71,B_72,A_73] :
      ( r2_hidden(C_71,B_72)
      | ~ r2_hidden(C_71,A_73)
      | ~ r1_tarski(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_135,plain,(
    ! [A_83,B_84,B_85] :
      ( r2_hidden('#skF_4'(A_83,B_84),B_85)
      | ~ r1_tarski(A_83,B_85)
      | r1_setfam_1(A_83,B_84) ) ),
    inference(resolution,[status(thm)],[c_32,c_80])).

tff(c_76,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_63])).

tff(c_112,plain,(
    ! [A_77,B_78,D_79] :
      ( ~ r1_tarski('#skF_4'(A_77,B_78),D_79)
      | ~ r2_hidden(D_79,B_78)
      | r1_setfam_1(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_117,plain,(
    ! [A_77,B_78] :
      ( ~ r2_hidden('#skF_4'(A_77,B_78),B_78)
      | r1_setfam_1(A_77,B_78) ) ),
    inference(resolution,[status(thm)],[c_76,c_112])).

tff(c_146,plain,(
    ! [A_83,B_85] :
      ( ~ r1_tarski(A_83,B_85)
      | r1_setfam_1(A_83,B_85) ) ),
    inference(resolution,[status(thm)],[c_135,c_117])).

tff(c_66809,plain,(
    ! [B_1583] : r1_setfam_1('#skF_12',B_1583) ),
    inference(resolution,[status(thm)],[c_66739,c_146])).

tff(c_66812,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66809,c_58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:59:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.19/10.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.19/10.67  
% 20.19/10.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.19/10.67  %$ r2_hidden > r1_tarski > r1_setfam_1 > k2_xboole_0 > k2_setfam_1 > #nlpp > #skF_6 > #skF_10 > #skF_5 > #skF_2 > #skF_11 > #skF_7 > #skF_9 > #skF_3 > #skF_8 > #skF_1 > #skF_12 > #skF_4
% 20.19/10.67  
% 20.19/10.67  %Foreground sorts:
% 20.19/10.67  
% 20.19/10.67  
% 20.19/10.67  %Background operators:
% 20.19/10.67  
% 20.19/10.67  
% 20.19/10.67  %Foreground operators:
% 20.19/10.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.19/10.67  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 20.19/10.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 20.19/10.67  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 20.19/10.67  tff('#skF_10', type, '#skF_10': ($i * $i * $i * $i) > $i).
% 20.19/10.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.19/10.67  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 20.19/10.67  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 20.19/10.67  tff('#skF_11', type, '#skF_11': ($i * $i * $i * $i) > $i).
% 20.19/10.67  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 20.19/10.67  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 20.19/10.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.19/10.67  tff(k2_setfam_1, type, k2_setfam_1: ($i * $i) > $i).
% 20.19/10.67  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 20.19/10.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.19/10.67  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 20.19/10.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 20.19/10.67  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 20.19/10.67  tff('#skF_12', type, '#skF_12': $i).
% 20.19/10.67  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 20.19/10.67  
% 20.19/10.68  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 20.19/10.68  tff(f_53, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 20.19/10.68  tff(f_65, axiom, (![A, B, C]: ((C = k2_setfam_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k2_xboole_0(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_setfam_1)).
% 20.19/10.68  tff(f_41, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 20.19/10.68  tff(f_68, negated_conjecture, ~(![A]: r1_setfam_1(A, k2_setfam_1(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_setfam_1)).
% 20.19/10.68  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 20.19/10.68  tff(c_32, plain, (![A_12, B_13]: (r2_hidden('#skF_4'(A_12, B_13), A_12) | r1_setfam_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 20.19/10.68  tff(c_34, plain, (![E_56, F_57, A_24, B_25]: (r2_hidden(k2_xboole_0(E_56, F_57), k2_setfam_1(A_24, B_25)) | ~r2_hidden(F_57, B_25) | ~r2_hidden(E_56, A_24))), inference(cnfTransformation, [status(thm)], [f_65])).
% 20.19/10.68  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | r2_hidden(D_11, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 20.19/10.68  tff(c_63, plain, (![A_68, B_69]: (~r2_hidden('#skF_1'(A_68, B_69), B_69) | r1_tarski(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_32])).
% 20.19/10.68  tff(c_210, plain, (![A_109, A_110, B_111]: (r1_tarski(A_109, k2_xboole_0(A_110, B_111)) | ~r2_hidden('#skF_1'(A_109, k2_xboole_0(A_110, B_111)), B_111))), inference(resolution, [status(thm)], [c_10, c_63])).
% 20.19/10.68  tff(c_231, plain, (![A_112, A_113]: (r1_tarski(A_112, k2_xboole_0(A_113, A_112)))), inference(resolution, [status(thm)], [c_6, c_210])).
% 20.19/10.68  tff(c_30, plain, (![A_12, B_13, D_21]: (~r1_tarski('#skF_4'(A_12, B_13), D_21) | ~r2_hidden(D_21, B_13) | r1_setfam_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 20.19/10.68  tff(c_301, plain, (![A_129, A_130, B_131]: (~r2_hidden(k2_xboole_0(A_129, '#skF_4'(A_130, B_131)), B_131) | r1_setfam_1(A_130, B_131))), inference(resolution, [status(thm)], [c_231, c_30])).
% 20.19/10.68  tff(c_65805, plain, (![A_1573, A_1574, B_1575, E_1576]: (r1_setfam_1(A_1573, k2_setfam_1(A_1574, B_1575)) | ~r2_hidden('#skF_4'(A_1573, k2_setfam_1(A_1574, B_1575)), B_1575) | ~r2_hidden(E_1576, A_1574))), inference(resolution, [status(thm)], [c_34, c_301])).
% 20.19/10.68  tff(c_65978, plain, (![E_1577, A_1578, A_1579]: (~r2_hidden(E_1577, A_1578) | r1_setfam_1(A_1579, k2_setfam_1(A_1578, A_1579)))), inference(resolution, [status(thm)], [c_32, c_65805])).
% 20.19/10.68  tff(c_66291, plain, (![A_1580, A_1581, B_1582]: (r1_setfam_1(A_1580, k2_setfam_1(A_1581, A_1580)) | r1_tarski(A_1581, B_1582))), inference(resolution, [status(thm)], [c_6, c_65978])).
% 20.19/10.68  tff(c_58, plain, (~r1_setfam_1('#skF_12', k2_setfam_1('#skF_12', '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 20.19/10.68  tff(c_66739, plain, (![B_1583]: (r1_tarski('#skF_12', B_1583))), inference(resolution, [status(thm)], [c_66291, c_58])).
% 20.19/10.68  tff(c_80, plain, (![C_71, B_72, A_73]: (r2_hidden(C_71, B_72) | ~r2_hidden(C_71, A_73) | ~r1_tarski(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_32])).
% 20.19/10.68  tff(c_135, plain, (![A_83, B_84, B_85]: (r2_hidden('#skF_4'(A_83, B_84), B_85) | ~r1_tarski(A_83, B_85) | r1_setfam_1(A_83, B_84))), inference(resolution, [status(thm)], [c_32, c_80])).
% 20.19/10.68  tff(c_76, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_63])).
% 20.19/10.68  tff(c_112, plain, (![A_77, B_78, D_79]: (~r1_tarski('#skF_4'(A_77, B_78), D_79) | ~r2_hidden(D_79, B_78) | r1_setfam_1(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_53])).
% 20.19/10.68  tff(c_117, plain, (![A_77, B_78]: (~r2_hidden('#skF_4'(A_77, B_78), B_78) | r1_setfam_1(A_77, B_78))), inference(resolution, [status(thm)], [c_76, c_112])).
% 20.19/10.68  tff(c_146, plain, (![A_83, B_85]: (~r1_tarski(A_83, B_85) | r1_setfam_1(A_83, B_85))), inference(resolution, [status(thm)], [c_135, c_117])).
% 20.19/10.68  tff(c_66809, plain, (![B_1583]: (r1_setfam_1('#skF_12', B_1583))), inference(resolution, [status(thm)], [c_66739, c_146])).
% 20.19/10.68  tff(c_66812, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66809, c_58])).
% 20.19/10.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.19/10.68  
% 20.19/10.68  Inference rules
% 20.19/10.68  ----------------------
% 20.19/10.68  #Ref     : 0
% 20.19/10.68  #Sup     : 17315
% 20.19/10.68  #Fact    : 12
% 20.19/10.68  #Define  : 0
% 20.19/10.68  #Split   : 0
% 20.19/10.68  #Chain   : 0
% 20.19/10.68  #Close   : 0
% 20.19/10.68  
% 20.19/10.68  Ordering : KBO
% 20.19/10.68  
% 20.19/10.68  Simplification rules
% 20.19/10.68  ----------------------
% 20.19/10.68  #Subsume      : 4309
% 20.19/10.68  #Demod        : 3653
% 20.19/10.68  #Tautology    : 2879
% 20.19/10.68  #SimpNegUnit  : 0
% 20.19/10.68  #BackRed      : 3
% 20.19/10.68  
% 20.19/10.68  #Partial instantiations: 0
% 20.19/10.68  #Strategies tried      : 1
% 20.19/10.68  
% 20.19/10.68  Timing (in seconds)
% 20.19/10.68  ----------------------
% 20.19/10.68  Preprocessing        : 0.32
% 20.19/10.68  Parsing              : 0.16
% 20.19/10.68  CNF conversion       : 0.03
% 20.19/10.68  Main loop            : 9.54
% 20.19/10.68  Inferencing          : 1.55
% 20.19/10.68  Reduction            : 2.64
% 20.19/10.68  Demodulation         : 2.19
% 20.19/10.68  BG Simplification    : 0.19
% 20.19/10.68  Subsumption          : 4.62
% 20.19/10.68  Abstraction          : 0.25
% 20.19/10.68  MUC search           : 0.00
% 20.19/10.68  Cooper               : 0.00
% 20.19/10.68  Total                : 9.88
% 20.19/10.68  Index Insertion      : 0.00
% 20.19/10.68  Index Deletion       : 0.00
% 20.19/10.68  Index Matching       : 0.00
% 20.19/10.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
