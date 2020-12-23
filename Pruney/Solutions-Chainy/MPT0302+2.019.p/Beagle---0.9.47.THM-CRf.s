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
% DateTime   : Thu Dec  3 09:53:49 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 241 expanded)
%              Number of leaves         :   24 (  90 expanded)
%              Depth                    :   17
%              Number of atoms          :  112 ( 620 expanded)
%              Number of equality atoms :   37 ( 297 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_9 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(B,A)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_41,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( k4_tarski(A,B) = k4_tarski(C,D)
     => ( A = C
        & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_zfmisc_1)).

tff(c_42,plain,(
    '#skF_11' != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_10,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r2_hidden('#skF_2'(A_1,B_2),A_1)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_12,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_3'(A_4),A_4)
      | k1_xboole_0 = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_48,plain,(
    k2_zfmisc_1('#skF_11','#skF_10') = k2_zfmisc_1('#skF_10','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_85,plain,(
    ! [E_61,F_62,A_63,B_64] :
      ( r2_hidden(k4_tarski(E_61,F_62),k2_zfmisc_1(A_63,B_64))
      | ~ r2_hidden(F_62,B_64)
      | ~ r2_hidden(E_61,A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_88,plain,(
    ! [E_61,F_62] :
      ( r2_hidden(k4_tarski(E_61,F_62),k2_zfmisc_1('#skF_10','#skF_11'))
      | ~ r2_hidden(F_62,'#skF_10')
      | ~ r2_hidden(E_61,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_85])).

tff(c_105,plain,(
    ! [A_84,B_85,D_86] :
      ( k4_tarski('#skF_8'(A_84,B_85,k2_zfmisc_1(A_84,B_85),D_86),'#skF_9'(A_84,B_85,k2_zfmisc_1(A_84,B_85),D_86)) = D_86
      | ~ r2_hidden(D_86,k2_zfmisc_1(A_84,B_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_38,plain,(
    ! [D_43,B_41,C_42,A_40] :
      ( D_43 = B_41
      | k4_tarski(C_42,D_43) != k4_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_123,plain,(
    ! [D_86,B_85,A_40,A_84,B_41] :
      ( B_41 = '#skF_9'(A_84,B_85,k2_zfmisc_1(A_84,B_85),D_86)
      | k4_tarski(A_40,B_41) != D_86
      | ~ r2_hidden(D_86,k2_zfmisc_1(A_84,B_85)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_38])).

tff(c_187,plain,(
    ! [A_100,B_101,A_102,B_103] :
      ( '#skF_9'(A_100,B_101,k2_zfmisc_1(A_100,B_101),k4_tarski(A_102,B_103)) = B_103
      | ~ r2_hidden(k4_tarski(A_102,B_103),k2_zfmisc_1(A_100,B_101)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_123])).

tff(c_201,plain,(
    ! [E_104,F_105] :
      ( '#skF_9'('#skF_10','#skF_11',k2_zfmisc_1('#skF_10','#skF_11'),k4_tarski(E_104,F_105)) = F_105
      | ~ r2_hidden(F_105,'#skF_10')
      | ~ r2_hidden(E_104,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_88,c_187])).

tff(c_18,plain,(
    ! [A_6,B_7,D_33] :
      ( r2_hidden('#skF_9'(A_6,B_7,k2_zfmisc_1(A_6,B_7),D_33),B_7)
      | ~ r2_hidden(D_33,k2_zfmisc_1(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_271,plain,(
    ! [F_112,E_113] :
      ( r2_hidden(F_112,'#skF_11')
      | ~ r2_hidden(k4_tarski(E_113,F_112),k2_zfmisc_1('#skF_10','#skF_11'))
      | ~ r2_hidden(F_112,'#skF_10')
      | ~ r2_hidden(E_113,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_18])).

tff(c_285,plain,(
    ! [F_62,E_61] :
      ( r2_hidden(F_62,'#skF_11')
      | ~ r2_hidden(F_62,'#skF_10')
      | ~ r2_hidden(E_61,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_88,c_271])).

tff(c_290,plain,(
    ! [E_114] : ~ r2_hidden(E_114,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_285])).

tff(c_324,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_12,c_290])).

tff(c_334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_324])).

tff(c_336,plain,(
    ! [F_115] :
      ( r2_hidden(F_115,'#skF_11')
      | ~ r2_hidden(F_115,'#skF_10') ) ),
    inference(splitRight,[status(thm)],[c_285])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_356,plain,(
    ! [A_121] :
      ( r2_hidden('#skF_1'(A_121,'#skF_11'),'#skF_11')
      | A_121 = '#skF_11'
      | ~ r2_hidden('#skF_2'(A_121,'#skF_11'),'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_336,c_6])).

tff(c_360,plain,
    ( r2_hidden('#skF_1'('#skF_10','#skF_11'),'#skF_11')
    | '#skF_11' = '#skF_10' ),
    inference(resolution,[status(thm)],[c_10,c_356])).

tff(c_367,plain,(
    r2_hidden('#skF_1'('#skF_10','#skF_11'),'#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_42,c_360])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_14,plain,(
    ! [E_38,F_39,A_6,B_7] :
      ( r2_hidden(k4_tarski(E_38,F_39),k2_zfmisc_1(A_6,B_7))
      | ~ r2_hidden(F_39,B_7)
      | ~ r2_hidden(E_38,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_197,plain,(
    ! [A_102,B_103] :
      ( '#skF_9'('#skF_11','#skF_10',k2_zfmisc_1('#skF_11','#skF_10'),k4_tarski(A_102,B_103)) = B_103
      | ~ r2_hidden(k4_tarski(A_102,B_103),k2_zfmisc_1('#skF_10','#skF_11')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_187])).

tff(c_222,plain,(
    ! [A_106,B_107] :
      ( '#skF_9'('#skF_11','#skF_10',k2_zfmisc_1('#skF_10','#skF_11'),k4_tarski(A_106,B_107)) = B_107
      | ~ r2_hidden(k4_tarski(A_106,B_107),k2_zfmisc_1('#skF_10','#skF_11')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_197])).

tff(c_406,plain,(
    ! [E_125,F_126] :
      ( '#skF_9'('#skF_11','#skF_10',k2_zfmisc_1('#skF_10','#skF_11'),k4_tarski(E_125,F_126)) = F_126
      | ~ r2_hidden(F_126,'#skF_11')
      | ~ r2_hidden(E_125,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_14,c_222])).

tff(c_90,plain,(
    ! [A_67,B_68,D_69] :
      ( r2_hidden('#skF_9'(A_67,B_68,k2_zfmisc_1(A_67,B_68),D_69),B_68)
      | ~ r2_hidden(D_69,k2_zfmisc_1(A_67,B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_93,plain,(
    ! [D_69] :
      ( r2_hidden('#skF_9'('#skF_11','#skF_10',k2_zfmisc_1('#skF_10','#skF_11'),D_69),'#skF_10')
      | ~ r2_hidden(D_69,k2_zfmisc_1('#skF_11','#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_90])).

tff(c_94,plain,(
    ! [D_69] :
      ( r2_hidden('#skF_9'('#skF_11','#skF_10',k2_zfmisc_1('#skF_10','#skF_11'),D_69),'#skF_10')
      | ~ r2_hidden(D_69,k2_zfmisc_1('#skF_10','#skF_11')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_93])).

tff(c_432,plain,(
    ! [F_127,E_128] :
      ( r2_hidden(F_127,'#skF_10')
      | ~ r2_hidden(k4_tarski(E_128,F_127),k2_zfmisc_1('#skF_10','#skF_11'))
      | ~ r2_hidden(F_127,'#skF_11')
      | ~ r2_hidden(E_128,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_94])).

tff(c_447,plain,(
    ! [F_39,E_38] :
      ( r2_hidden(F_39,'#skF_10')
      | ~ r2_hidden(F_39,'#skF_11')
      | ~ r2_hidden(E_38,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_14,c_432])).

tff(c_451,plain,(
    ! [E_129] : ~ r2_hidden(E_129,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_447])).

tff(c_485,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_12,c_451])).

tff(c_495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_485])).

tff(c_502,plain,(
    ! [F_135] :
      ( r2_hidden(F_135,'#skF_10')
      | ~ r2_hidden(F_135,'#skF_11') ) ),
    inference(splitRight,[status(thm)],[c_447])).

tff(c_546,plain,(
    r2_hidden('#skF_1'('#skF_10','#skF_11'),'#skF_10') ),
    inference(resolution,[status(thm)],[c_367,c_502])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r2_hidden('#skF_2'(A_1,B_2),A_1)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_335,plain,(
    ! [F_62] :
      ( r2_hidden(F_62,'#skF_11')
      | ~ r2_hidden(F_62,'#skF_10') ) ),
    inference(splitRight,[status(thm)],[c_285])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),A_1)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_559,plain,
    ( ~ r2_hidden('#skF_2'('#skF_10','#skF_11'),'#skF_11')
    | '#skF_11' = '#skF_10' ),
    inference(resolution,[status(thm)],[c_546,c_4])).

tff(c_562,plain,(
    ~ r2_hidden('#skF_2'('#skF_10','#skF_11'),'#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_559])).

tff(c_566,plain,(
    ~ r2_hidden('#skF_2'('#skF_10','#skF_11'),'#skF_10') ),
    inference(resolution,[status(thm)],[c_335,c_562])).

tff(c_572,plain,
    ( ~ r2_hidden('#skF_1'('#skF_10','#skF_11'),'#skF_10')
    | '#skF_11' = '#skF_10' ),
    inference(resolution,[status(thm)],[c_8,c_566])).

tff(c_578,plain,(
    '#skF_11' = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_572])).

tff(c_580,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_578])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:57:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.38  
% 2.59/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.38  %$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_9 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_3 > #skF_2 > #skF_1
% 2.59/1.38  
% 2.59/1.38  %Foreground sorts:
% 2.59/1.38  
% 2.59/1.38  
% 2.59/1.38  %Background operators:
% 2.59/1.38  
% 2.59/1.38  
% 2.59/1.38  %Foreground operators:
% 2.59/1.38  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 2.59/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.59/1.38  tff('#skF_11', type, '#skF_11': $i).
% 2.59/1.38  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.59/1.38  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.59/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.59/1.38  tff('#skF_9', type, '#skF_9': ($i * $i * $i * $i) > $i).
% 2.59/1.38  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.59/1.38  tff('#skF_10', type, '#skF_10': $i).
% 2.59/1.38  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 2.59/1.38  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.59/1.38  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 2.59/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.59/1.38  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.59/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.59/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.59/1.38  
% 2.83/1.40  tff(f_68, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(B, A)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 2.83/1.40  tff(f_33, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 2.83/1.40  tff(f_41, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.83/1.40  tff(f_53, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 2.83/1.40  tff(f_59, axiom, (![A, B, C, D]: ((k4_tarski(A, B) = k4_tarski(C, D)) => ((A = C) & (B = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_zfmisc_1)).
% 2.83/1.40  tff(c_42, plain, ('#skF_11'!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.83/1.40  tff(c_10, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r2_hidden('#skF_2'(A_1, B_2), A_1) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.83/1.40  tff(c_44, plain, (k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.83/1.40  tff(c_12, plain, (![A_4]: (r2_hidden('#skF_3'(A_4), A_4) | k1_xboole_0=A_4)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.83/1.40  tff(c_48, plain, (k2_zfmisc_1('#skF_11', '#skF_10')=k2_zfmisc_1('#skF_10', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.83/1.40  tff(c_85, plain, (![E_61, F_62, A_63, B_64]: (r2_hidden(k4_tarski(E_61, F_62), k2_zfmisc_1(A_63, B_64)) | ~r2_hidden(F_62, B_64) | ~r2_hidden(E_61, A_63))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.83/1.40  tff(c_88, plain, (![E_61, F_62]: (r2_hidden(k4_tarski(E_61, F_62), k2_zfmisc_1('#skF_10', '#skF_11')) | ~r2_hidden(F_62, '#skF_10') | ~r2_hidden(E_61, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_85])).
% 2.83/1.40  tff(c_105, plain, (![A_84, B_85, D_86]: (k4_tarski('#skF_8'(A_84, B_85, k2_zfmisc_1(A_84, B_85), D_86), '#skF_9'(A_84, B_85, k2_zfmisc_1(A_84, B_85), D_86))=D_86 | ~r2_hidden(D_86, k2_zfmisc_1(A_84, B_85)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.83/1.40  tff(c_38, plain, (![D_43, B_41, C_42, A_40]: (D_43=B_41 | k4_tarski(C_42, D_43)!=k4_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.83/1.40  tff(c_123, plain, (![D_86, B_85, A_40, A_84, B_41]: (B_41='#skF_9'(A_84, B_85, k2_zfmisc_1(A_84, B_85), D_86) | k4_tarski(A_40, B_41)!=D_86 | ~r2_hidden(D_86, k2_zfmisc_1(A_84, B_85)))), inference(superposition, [status(thm), theory('equality')], [c_105, c_38])).
% 2.83/1.40  tff(c_187, plain, (![A_100, B_101, A_102, B_103]: ('#skF_9'(A_100, B_101, k2_zfmisc_1(A_100, B_101), k4_tarski(A_102, B_103))=B_103 | ~r2_hidden(k4_tarski(A_102, B_103), k2_zfmisc_1(A_100, B_101)))), inference(reflexivity, [status(thm), theory('equality')], [c_123])).
% 2.83/1.40  tff(c_201, plain, (![E_104, F_105]: ('#skF_9'('#skF_10', '#skF_11', k2_zfmisc_1('#skF_10', '#skF_11'), k4_tarski(E_104, F_105))=F_105 | ~r2_hidden(F_105, '#skF_10') | ~r2_hidden(E_104, '#skF_11'))), inference(resolution, [status(thm)], [c_88, c_187])).
% 2.83/1.40  tff(c_18, plain, (![A_6, B_7, D_33]: (r2_hidden('#skF_9'(A_6, B_7, k2_zfmisc_1(A_6, B_7), D_33), B_7) | ~r2_hidden(D_33, k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.83/1.40  tff(c_271, plain, (![F_112, E_113]: (r2_hidden(F_112, '#skF_11') | ~r2_hidden(k4_tarski(E_113, F_112), k2_zfmisc_1('#skF_10', '#skF_11')) | ~r2_hidden(F_112, '#skF_10') | ~r2_hidden(E_113, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_201, c_18])).
% 2.83/1.40  tff(c_285, plain, (![F_62, E_61]: (r2_hidden(F_62, '#skF_11') | ~r2_hidden(F_62, '#skF_10') | ~r2_hidden(E_61, '#skF_11'))), inference(resolution, [status(thm)], [c_88, c_271])).
% 2.83/1.40  tff(c_290, plain, (![E_114]: (~r2_hidden(E_114, '#skF_11'))), inference(splitLeft, [status(thm)], [c_285])).
% 2.83/1.40  tff(c_324, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_12, c_290])).
% 2.83/1.40  tff(c_334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_324])).
% 2.83/1.40  tff(c_336, plain, (![F_115]: (r2_hidden(F_115, '#skF_11') | ~r2_hidden(F_115, '#skF_10'))), inference(splitRight, [status(thm)], [c_285])).
% 2.83/1.40  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.83/1.40  tff(c_356, plain, (![A_121]: (r2_hidden('#skF_1'(A_121, '#skF_11'), '#skF_11') | A_121='#skF_11' | ~r2_hidden('#skF_2'(A_121, '#skF_11'), '#skF_10'))), inference(resolution, [status(thm)], [c_336, c_6])).
% 2.83/1.40  tff(c_360, plain, (r2_hidden('#skF_1'('#skF_10', '#skF_11'), '#skF_11') | '#skF_11'='#skF_10'), inference(resolution, [status(thm)], [c_10, c_356])).
% 2.83/1.40  tff(c_367, plain, (r2_hidden('#skF_1'('#skF_10', '#skF_11'), '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_42, c_42, c_360])).
% 2.83/1.40  tff(c_46, plain, (k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.83/1.40  tff(c_14, plain, (![E_38, F_39, A_6, B_7]: (r2_hidden(k4_tarski(E_38, F_39), k2_zfmisc_1(A_6, B_7)) | ~r2_hidden(F_39, B_7) | ~r2_hidden(E_38, A_6))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.83/1.40  tff(c_197, plain, (![A_102, B_103]: ('#skF_9'('#skF_11', '#skF_10', k2_zfmisc_1('#skF_11', '#skF_10'), k4_tarski(A_102, B_103))=B_103 | ~r2_hidden(k4_tarski(A_102, B_103), k2_zfmisc_1('#skF_10', '#skF_11')))), inference(superposition, [status(thm), theory('equality')], [c_48, c_187])).
% 2.83/1.40  tff(c_222, plain, (![A_106, B_107]: ('#skF_9'('#skF_11', '#skF_10', k2_zfmisc_1('#skF_10', '#skF_11'), k4_tarski(A_106, B_107))=B_107 | ~r2_hidden(k4_tarski(A_106, B_107), k2_zfmisc_1('#skF_10', '#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_197])).
% 2.83/1.40  tff(c_406, plain, (![E_125, F_126]: ('#skF_9'('#skF_11', '#skF_10', k2_zfmisc_1('#skF_10', '#skF_11'), k4_tarski(E_125, F_126))=F_126 | ~r2_hidden(F_126, '#skF_11') | ~r2_hidden(E_125, '#skF_10'))), inference(resolution, [status(thm)], [c_14, c_222])).
% 2.83/1.40  tff(c_90, plain, (![A_67, B_68, D_69]: (r2_hidden('#skF_9'(A_67, B_68, k2_zfmisc_1(A_67, B_68), D_69), B_68) | ~r2_hidden(D_69, k2_zfmisc_1(A_67, B_68)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.83/1.40  tff(c_93, plain, (![D_69]: (r2_hidden('#skF_9'('#skF_11', '#skF_10', k2_zfmisc_1('#skF_10', '#skF_11'), D_69), '#skF_10') | ~r2_hidden(D_69, k2_zfmisc_1('#skF_11', '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_48, c_90])).
% 2.83/1.40  tff(c_94, plain, (![D_69]: (r2_hidden('#skF_9'('#skF_11', '#skF_10', k2_zfmisc_1('#skF_10', '#skF_11'), D_69), '#skF_10') | ~r2_hidden(D_69, k2_zfmisc_1('#skF_10', '#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_93])).
% 2.83/1.40  tff(c_432, plain, (![F_127, E_128]: (r2_hidden(F_127, '#skF_10') | ~r2_hidden(k4_tarski(E_128, F_127), k2_zfmisc_1('#skF_10', '#skF_11')) | ~r2_hidden(F_127, '#skF_11') | ~r2_hidden(E_128, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_406, c_94])).
% 2.83/1.40  tff(c_447, plain, (![F_39, E_38]: (r2_hidden(F_39, '#skF_10') | ~r2_hidden(F_39, '#skF_11') | ~r2_hidden(E_38, '#skF_10'))), inference(resolution, [status(thm)], [c_14, c_432])).
% 2.83/1.40  tff(c_451, plain, (![E_129]: (~r2_hidden(E_129, '#skF_10'))), inference(splitLeft, [status(thm)], [c_447])).
% 2.83/1.40  tff(c_485, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_12, c_451])).
% 2.83/1.40  tff(c_495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_485])).
% 2.83/1.40  tff(c_502, plain, (![F_135]: (r2_hidden(F_135, '#skF_10') | ~r2_hidden(F_135, '#skF_11'))), inference(splitRight, [status(thm)], [c_447])).
% 2.83/1.40  tff(c_546, plain, (r2_hidden('#skF_1'('#skF_10', '#skF_11'), '#skF_10')), inference(resolution, [status(thm)], [c_367, c_502])).
% 2.83/1.40  tff(c_8, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), A_1) | r2_hidden('#skF_2'(A_1, B_2), A_1) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.83/1.40  tff(c_335, plain, (![F_62]: (r2_hidden(F_62, '#skF_11') | ~r2_hidden(F_62, '#skF_10'))), inference(splitRight, [status(thm)], [c_285])).
% 2.83/1.40  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), A_1) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.83/1.40  tff(c_559, plain, (~r2_hidden('#skF_2'('#skF_10', '#skF_11'), '#skF_11') | '#skF_11'='#skF_10'), inference(resolution, [status(thm)], [c_546, c_4])).
% 2.83/1.40  tff(c_562, plain, (~r2_hidden('#skF_2'('#skF_10', '#skF_11'), '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_42, c_559])).
% 2.83/1.40  tff(c_566, plain, (~r2_hidden('#skF_2'('#skF_10', '#skF_11'), '#skF_10')), inference(resolution, [status(thm)], [c_335, c_562])).
% 2.83/1.40  tff(c_572, plain, (~r2_hidden('#skF_1'('#skF_10', '#skF_11'), '#skF_10') | '#skF_11'='#skF_10'), inference(resolution, [status(thm)], [c_8, c_566])).
% 2.83/1.40  tff(c_578, plain, ('#skF_11'='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_546, c_572])).
% 2.83/1.40  tff(c_580, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_578])).
% 2.83/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.40  
% 2.83/1.40  Inference rules
% 2.83/1.40  ----------------------
% 2.83/1.40  #Ref     : 4
% 2.83/1.40  #Sup     : 115
% 2.83/1.40  #Fact    : 0
% 2.83/1.40  #Define  : 0
% 2.83/1.40  #Split   : 2
% 2.83/1.40  #Chain   : 0
% 2.83/1.40  #Close   : 0
% 2.83/1.40  
% 2.83/1.40  Ordering : KBO
% 2.83/1.40  
% 2.83/1.40  Simplification rules
% 2.83/1.40  ----------------------
% 2.83/1.40  #Subsume      : 20
% 2.83/1.40  #Demod        : 9
% 2.83/1.40  #Tautology    : 32
% 2.83/1.40  #SimpNegUnit  : 12
% 2.83/1.40  #BackRed      : 2
% 2.83/1.40  
% 2.83/1.40  #Partial instantiations: 0
% 2.83/1.40  #Strategies tried      : 1
% 2.83/1.40  
% 2.83/1.40  Timing (in seconds)
% 2.83/1.40  ----------------------
% 2.83/1.40  Preprocessing        : 0.30
% 2.83/1.40  Parsing              : 0.16
% 2.83/1.40  CNF conversion       : 0.02
% 2.83/1.40  Main loop            : 0.33
% 2.83/1.40  Inferencing          : 0.13
% 2.83/1.40  Reduction            : 0.08
% 2.83/1.40  Demodulation         : 0.05
% 2.83/1.40  BG Simplification    : 0.03
% 2.83/1.40  Subsumption          : 0.07
% 2.83/1.40  Abstraction          : 0.02
% 2.83/1.40  MUC search           : 0.00
% 2.83/1.40  Cooper               : 0.00
% 2.83/1.40  Total                : 0.66
% 2.83/1.40  Index Insertion      : 0.00
% 2.83/1.40  Index Deletion       : 0.00
% 2.83/1.40  Index Matching       : 0.00
% 2.83/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
