%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:07 EST 2020

% Result     : Theorem 38.10s
% Output     : CNFRefutation 38.10s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 104 expanded)
%              Number of leaves         :   26 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :   84 ( 226 expanded)
%              Number of equality atoms :    9 (  23 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_11 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r2_hidden(D,C)
          & r1_tarski(C,k2_zfmisc_1(A,B))
          & ! [E] :
              ( m1_subset_1(E,A)
             => ! [F] :
                  ( m1_subset_1(F,B)
                 => D != k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_subset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(c_101,plain,(
    ! [A_68,B_69] :
      ( r2_hidden('#skF_2'(A_68,B_69),A_68)
      | r1_tarski(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_113,plain,(
    ! [A_68] : r1_tarski(A_68,A_68) ),
    inference(resolution,[status(thm)],[c_101,c_8])).

tff(c_46,plain,(
    r1_tarski('#skF_11',k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_48,plain,(
    r2_hidden('#skF_12','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_116,plain,(
    ! [C_71,B_72,A_73] :
      ( r2_hidden(C_71,B_72)
      | ~ r2_hidden(C_71,A_73)
      | ~ r1_tarski(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_130,plain,(
    ! [B_76] :
      ( r2_hidden('#skF_12',B_76)
      | ~ r1_tarski('#skF_11',B_76) ) ),
    inference(resolution,[status(thm)],[c_48,c_116])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_206,plain,(
    ! [B_83,B_84] :
      ( r2_hidden('#skF_12',B_83)
      | ~ r1_tarski(B_84,B_83)
      | ~ r1_tarski('#skF_11',B_84) ) ),
    inference(resolution,[status(thm)],[c_130,c_6])).

tff(c_212,plain,
    ( r2_hidden('#skF_12',k2_zfmisc_1('#skF_9','#skF_10'))
    | ~ r1_tarski('#skF_11','#skF_11') ),
    inference(resolution,[status(thm)],[c_46,c_206])).

tff(c_217,plain,(
    r2_hidden('#skF_12',k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_212])).

tff(c_260,plain,(
    ! [A_92,B_93,D_94] :
      ( r2_hidden('#skF_7'(A_92,B_93,k2_zfmisc_1(A_92,B_93),D_94),A_92)
      | ~ r2_hidden(D_94,k2_zfmisc_1(A_92,B_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_272,plain,(
    ! [A_95,D_96,B_97] :
      ( ~ v1_xboole_0(A_95)
      | ~ r2_hidden(D_96,k2_zfmisc_1(A_95,B_97)) ) ),
    inference(resolution,[status(thm)],[c_260,c_2])).

tff(c_304,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_217,c_272])).

tff(c_36,plain,(
    ! [B_45,A_44] :
      ( m1_subset_1(B_45,A_44)
      | ~ r2_hidden(B_45,A_44)
      | v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_270,plain,(
    ! [A_92,B_93,D_94] :
      ( m1_subset_1('#skF_7'(A_92,B_93,k2_zfmisc_1(A_92,B_93),D_94),A_92)
      | v1_xboole_0(A_92)
      | ~ r2_hidden(D_94,k2_zfmisc_1(A_92,B_93)) ) ),
    inference(resolution,[status(thm)],[c_260,c_36])).

tff(c_338,plain,(
    ! [A_105,B_106,D_107] :
      ( r2_hidden('#skF_8'(A_105,B_106,k2_zfmisc_1(A_105,B_106),D_107),B_106)
      | ~ r2_hidden(D_107,k2_zfmisc_1(A_105,B_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_355,plain,(
    ! [B_108,D_109,A_110] :
      ( ~ v1_xboole_0(B_108)
      | ~ r2_hidden(D_109,k2_zfmisc_1(A_110,B_108)) ) ),
    inference(resolution,[status(thm)],[c_338,c_2])).

tff(c_392,plain,(
    ~ v1_xboole_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_217,c_355])).

tff(c_4040,plain,(
    ! [A_526,B_527,D_528] :
      ( m1_subset_1('#skF_8'(A_526,B_527,k2_zfmisc_1(A_526,B_527),D_528),B_527)
      | v1_xboole_0(B_527)
      | ~ r2_hidden(D_528,k2_zfmisc_1(A_526,B_527)) ) ),
    inference(resolution,[status(thm)],[c_338,c_36])).

tff(c_1210,plain,(
    ! [A_217,B_218,D_219] :
      ( k4_tarski('#skF_7'(A_217,B_218,k2_zfmisc_1(A_217,B_218),D_219),'#skF_8'(A_217,B_218,k2_zfmisc_1(A_217,B_218),D_219)) = D_219
      | ~ r2_hidden(D_219,k2_zfmisc_1(A_217,B_218)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_44,plain,(
    ! [E_49,F_51] :
      ( k4_tarski(E_49,F_51) != '#skF_12'
      | ~ m1_subset_1(F_51,'#skF_10')
      | ~ m1_subset_1(E_49,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1218,plain,(
    ! [D_219,A_217,B_218] :
      ( D_219 != '#skF_12'
      | ~ m1_subset_1('#skF_8'(A_217,B_218,k2_zfmisc_1(A_217,B_218),D_219),'#skF_10')
      | ~ m1_subset_1('#skF_7'(A_217,B_218,k2_zfmisc_1(A_217,B_218),D_219),'#skF_9')
      | ~ r2_hidden(D_219,k2_zfmisc_1(A_217,B_218)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1210,c_44])).

tff(c_4044,plain,(
    ! [D_528,A_526] :
      ( D_528 != '#skF_12'
      | ~ m1_subset_1('#skF_7'(A_526,'#skF_10',k2_zfmisc_1(A_526,'#skF_10'),D_528),'#skF_9')
      | v1_xboole_0('#skF_10')
      | ~ r2_hidden(D_528,k2_zfmisc_1(A_526,'#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_4040,c_1218])).

tff(c_77299,plain,(
    ! [D_1994,A_1995] :
      ( D_1994 != '#skF_12'
      | ~ m1_subset_1('#skF_7'(A_1995,'#skF_10',k2_zfmisc_1(A_1995,'#skF_10'),D_1994),'#skF_9')
      | ~ r2_hidden(D_1994,k2_zfmisc_1(A_1995,'#skF_10')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_392,c_4044])).

tff(c_77351,plain,(
    ! [D_94] :
      ( D_94 != '#skF_12'
      | v1_xboole_0('#skF_9')
      | ~ r2_hidden(D_94,k2_zfmisc_1('#skF_9','#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_270,c_77299])).

tff(c_77359,plain,(
    ~ r2_hidden('#skF_12',k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_304,c_77351])).

tff(c_77361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77359,c_217])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:39:30 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 38.10/28.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 38.10/28.33  
% 38.10/28.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 38.10/28.33  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_11 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_12
% 38.10/28.33  
% 38.10/28.33  %Foreground sorts:
% 38.10/28.33  
% 38.10/28.33  
% 38.10/28.33  %Background operators:
% 38.10/28.33  
% 38.10/28.33  
% 38.10/28.33  %Foreground operators:
% 38.10/28.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 38.10/28.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 38.10/28.33  tff('#skF_11', type, '#skF_11': $i).
% 38.10/28.33  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 38.10/28.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 38.10/28.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 38.10/28.33  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 38.10/28.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 38.10/28.33  tff('#skF_10', type, '#skF_10': $i).
% 38.10/28.33  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 38.10/28.33  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 38.10/28.33  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 38.10/28.33  tff('#skF_9', type, '#skF_9': $i).
% 38.10/28.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 38.10/28.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 38.10/28.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 38.10/28.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 38.10/28.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 38.10/28.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 38.10/28.33  tff('#skF_12', type, '#skF_12': $i).
% 38.10/28.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 38.10/28.33  
% 38.10/28.34  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 38.10/28.34  tff(f_78, negated_conjecture, ~(![A, B, C, D]: ~((r2_hidden(D, C) & r1_tarski(C, k2_zfmisc_1(A, B))) & (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, B) => ~(D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_subset_1)).
% 38.10/28.34  tff(f_50, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 38.10/28.34  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 38.10/28.34  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 38.10/28.34  tff(c_101, plain, (![A_68, B_69]: (r2_hidden('#skF_2'(A_68, B_69), A_68) | r1_tarski(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_38])).
% 38.10/28.34  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 38.10/28.34  tff(c_113, plain, (![A_68]: (r1_tarski(A_68, A_68))), inference(resolution, [status(thm)], [c_101, c_8])).
% 38.10/28.34  tff(c_46, plain, (r1_tarski('#skF_11', k2_zfmisc_1('#skF_9', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 38.10/28.34  tff(c_48, plain, (r2_hidden('#skF_12', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_78])).
% 38.10/28.34  tff(c_116, plain, (![C_71, B_72, A_73]: (r2_hidden(C_71, B_72) | ~r2_hidden(C_71, A_73) | ~r1_tarski(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_38])).
% 38.10/28.34  tff(c_130, plain, (![B_76]: (r2_hidden('#skF_12', B_76) | ~r1_tarski('#skF_11', B_76))), inference(resolution, [status(thm)], [c_48, c_116])).
% 38.10/28.34  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 38.10/28.34  tff(c_206, plain, (![B_83, B_84]: (r2_hidden('#skF_12', B_83) | ~r1_tarski(B_84, B_83) | ~r1_tarski('#skF_11', B_84))), inference(resolution, [status(thm)], [c_130, c_6])).
% 38.10/28.34  tff(c_212, plain, (r2_hidden('#skF_12', k2_zfmisc_1('#skF_9', '#skF_10')) | ~r1_tarski('#skF_11', '#skF_11')), inference(resolution, [status(thm)], [c_46, c_206])).
% 38.10/28.34  tff(c_217, plain, (r2_hidden('#skF_12', k2_zfmisc_1('#skF_9', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_212])).
% 38.10/28.34  tff(c_260, plain, (![A_92, B_93, D_94]: (r2_hidden('#skF_7'(A_92, B_93, k2_zfmisc_1(A_92, B_93), D_94), A_92) | ~r2_hidden(D_94, k2_zfmisc_1(A_92, B_93)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 38.10/28.34  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 38.10/28.34  tff(c_272, plain, (![A_95, D_96, B_97]: (~v1_xboole_0(A_95) | ~r2_hidden(D_96, k2_zfmisc_1(A_95, B_97)))), inference(resolution, [status(thm)], [c_260, c_2])).
% 38.10/28.34  tff(c_304, plain, (~v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_217, c_272])).
% 38.10/28.34  tff(c_36, plain, (![B_45, A_44]: (m1_subset_1(B_45, A_44) | ~r2_hidden(B_45, A_44) | v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_63])).
% 38.10/28.34  tff(c_270, plain, (![A_92, B_93, D_94]: (m1_subset_1('#skF_7'(A_92, B_93, k2_zfmisc_1(A_92, B_93), D_94), A_92) | v1_xboole_0(A_92) | ~r2_hidden(D_94, k2_zfmisc_1(A_92, B_93)))), inference(resolution, [status(thm)], [c_260, c_36])).
% 38.10/28.34  tff(c_338, plain, (![A_105, B_106, D_107]: (r2_hidden('#skF_8'(A_105, B_106, k2_zfmisc_1(A_105, B_106), D_107), B_106) | ~r2_hidden(D_107, k2_zfmisc_1(A_105, B_106)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 38.10/28.34  tff(c_355, plain, (![B_108, D_109, A_110]: (~v1_xboole_0(B_108) | ~r2_hidden(D_109, k2_zfmisc_1(A_110, B_108)))), inference(resolution, [status(thm)], [c_338, c_2])).
% 38.10/28.34  tff(c_392, plain, (~v1_xboole_0('#skF_10')), inference(resolution, [status(thm)], [c_217, c_355])).
% 38.10/28.34  tff(c_4040, plain, (![A_526, B_527, D_528]: (m1_subset_1('#skF_8'(A_526, B_527, k2_zfmisc_1(A_526, B_527), D_528), B_527) | v1_xboole_0(B_527) | ~r2_hidden(D_528, k2_zfmisc_1(A_526, B_527)))), inference(resolution, [status(thm)], [c_338, c_36])).
% 38.10/28.34  tff(c_1210, plain, (![A_217, B_218, D_219]: (k4_tarski('#skF_7'(A_217, B_218, k2_zfmisc_1(A_217, B_218), D_219), '#skF_8'(A_217, B_218, k2_zfmisc_1(A_217, B_218), D_219))=D_219 | ~r2_hidden(D_219, k2_zfmisc_1(A_217, B_218)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 38.10/28.34  tff(c_44, plain, (![E_49, F_51]: (k4_tarski(E_49, F_51)!='#skF_12' | ~m1_subset_1(F_51, '#skF_10') | ~m1_subset_1(E_49, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 38.10/28.34  tff(c_1218, plain, (![D_219, A_217, B_218]: (D_219!='#skF_12' | ~m1_subset_1('#skF_8'(A_217, B_218, k2_zfmisc_1(A_217, B_218), D_219), '#skF_10') | ~m1_subset_1('#skF_7'(A_217, B_218, k2_zfmisc_1(A_217, B_218), D_219), '#skF_9') | ~r2_hidden(D_219, k2_zfmisc_1(A_217, B_218)))), inference(superposition, [status(thm), theory('equality')], [c_1210, c_44])).
% 38.10/28.34  tff(c_4044, plain, (![D_528, A_526]: (D_528!='#skF_12' | ~m1_subset_1('#skF_7'(A_526, '#skF_10', k2_zfmisc_1(A_526, '#skF_10'), D_528), '#skF_9') | v1_xboole_0('#skF_10') | ~r2_hidden(D_528, k2_zfmisc_1(A_526, '#skF_10')))), inference(resolution, [status(thm)], [c_4040, c_1218])).
% 38.10/28.34  tff(c_77299, plain, (![D_1994, A_1995]: (D_1994!='#skF_12' | ~m1_subset_1('#skF_7'(A_1995, '#skF_10', k2_zfmisc_1(A_1995, '#skF_10'), D_1994), '#skF_9') | ~r2_hidden(D_1994, k2_zfmisc_1(A_1995, '#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_392, c_4044])).
% 38.10/28.34  tff(c_77351, plain, (![D_94]: (D_94!='#skF_12' | v1_xboole_0('#skF_9') | ~r2_hidden(D_94, k2_zfmisc_1('#skF_9', '#skF_10')))), inference(resolution, [status(thm)], [c_270, c_77299])).
% 38.10/28.34  tff(c_77359, plain, (~r2_hidden('#skF_12', k2_zfmisc_1('#skF_9', '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_304, c_77351])).
% 38.10/28.34  tff(c_77361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77359, c_217])).
% 38.10/28.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 38.10/28.34  
% 38.10/28.34  Inference rules
% 38.10/28.34  ----------------------
% 38.10/28.34  #Ref     : 3
% 38.10/28.34  #Sup     : 23661
% 38.10/28.34  #Fact    : 0
% 38.10/28.34  #Define  : 0
% 38.10/28.34  #Split   : 3
% 38.10/28.34  #Chain   : 0
% 38.10/28.34  #Close   : 0
% 38.10/28.34  
% 38.10/28.34  Ordering : KBO
% 38.10/28.34  
% 38.10/28.34  Simplification rules
% 38.10/28.34  ----------------------
% 38.10/28.34  #Subsume      : 12742
% 38.10/28.34  #Demod        : 16
% 38.10/28.34  #Tautology    : 40
% 38.10/28.34  #SimpNegUnit  : 54
% 38.10/28.34  #BackRed      : 1
% 38.10/28.34  
% 38.10/28.34  #Partial instantiations: 0
% 38.10/28.34  #Strategies tried      : 1
% 38.10/28.34  
% 38.10/28.34  Timing (in seconds)
% 38.10/28.34  ----------------------
% 38.10/28.35  Preprocessing        : 0.32
% 38.10/28.35  Parsing              : 0.16
% 38.10/28.35  CNF conversion       : 0.03
% 38.10/28.35  Main loop            : 27.24
% 38.10/28.35  Inferencing          : 2.21
% 38.10/28.35  Reduction            : 1.52
% 38.10/28.35  Demodulation         : 0.95
% 38.10/28.35  BG Simplification    : 0.27
% 38.10/28.35  Subsumption          : 22.60
% 38.10/28.35  Abstraction          : 0.38
% 38.10/28.35  MUC search           : 0.00
% 38.10/28.35  Cooper               : 0.00
% 38.10/28.35  Total                : 27.59
% 38.10/28.35  Index Insertion      : 0.00
% 38.10/28.35  Index Deletion       : 0.00
% 38.10/28.35  Index Matching       : 0.00
% 38.10/28.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
