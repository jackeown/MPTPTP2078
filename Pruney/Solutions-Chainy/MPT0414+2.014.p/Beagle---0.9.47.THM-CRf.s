%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:44 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 239 expanded)
%              Number of leaves         :   21 (  89 expanded)
%              Depth                    :   13
%              Number of atoms          :  115 ( 579 expanded)
%              Number of equality atoms :    9 (  42 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > #nlpp > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(A))
                 => ( r2_hidden(D,B)
                  <=> r2_hidden(D,C) ) )
             => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_setfam_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(c_34,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_36,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_46,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,B_29)
      | ~ m1_subset_1(A_28,k1_zfmisc_1(B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_57,plain,(
    r1_tarski('#skF_7',k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_36,c_46])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_117,plain,(
    ! [C_46,B_47,A_48] :
      ( r2_hidden(C_46,B_47)
      | ~ r2_hidden(C_46,A_48)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_270,plain,(
    ! [A_76,B_77,B_78] :
      ( r2_hidden('#skF_1'(A_76,B_77),B_78)
      | ~ r1_tarski(A_76,B_78)
      | r1_tarski(A_76,B_77) ) ),
    inference(resolution,[status(thm)],[c_6,c_117])).

tff(c_18,plain,(
    ! [C_15,A_11] :
      ( r1_tarski(C_15,A_11)
      | ~ r2_hidden(C_15,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_315,plain,(
    ! [A_83,B_84,A_85] :
      ( r1_tarski('#skF_1'(A_83,B_84),A_85)
      | ~ r1_tarski(A_83,k1_zfmisc_1(A_85))
      | r1_tarski(A_83,B_84) ) ),
    inference(resolution,[status(thm)],[c_270,c_18])).

tff(c_32,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_127,plain,(
    ! [D_49] :
      ( r2_hidden(D_49,'#skF_6')
      | ~ r2_hidden(D_49,'#skF_7')
      | ~ m1_subset_1(D_49,k1_zfmisc_1('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_147,plain,(
    ! [A_51] :
      ( r2_hidden(A_51,'#skF_6')
      | ~ r2_hidden(A_51,'#skF_7')
      | ~ r1_tarski(A_51,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_32,c_127])).

tff(c_302,plain,(
    ! [B_82] :
      ( r2_hidden('#skF_1'('#skF_7',B_82),'#skF_6')
      | ~ r1_tarski('#skF_1'('#skF_7',B_82),'#skF_5')
      | r1_tarski('#skF_7',B_82) ) ),
    inference(resolution,[status(thm)],[c_6,c_147])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_313,plain,
    ( ~ r1_tarski('#skF_1'('#skF_7','#skF_6'),'#skF_5')
    | r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_302,c_4])).

tff(c_314,plain,(
    ~ r1_tarski('#skF_1'('#skF_7','#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_313])).

tff(c_318,plain,
    ( ~ r1_tarski('#skF_7',k1_zfmisc_1('#skF_5'))
    | r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_315,c_314])).

tff(c_327,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_318])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_xboole_0(A_6,B_7)
      | B_7 = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_2'(A_8,B_9),B_9)
      | ~ r2_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_191,plain,(
    ! [A_65,B_66,B_67] :
      ( r2_hidden('#skF_2'(A_65,B_66),B_67)
      | ~ r1_tarski(B_66,B_67)
      | ~ r2_xboole_0(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_16,c_117])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9),A_8)
      | ~ r2_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_223,plain,(
    ! [B_70,B_71] :
      ( ~ r1_tarski(B_70,B_71)
      | ~ r2_xboole_0(B_71,B_70) ) ),
    inference(resolution,[status(thm)],[c_191,c_14])).

tff(c_227,plain,(
    ! [B_7,A_6] :
      ( ~ r1_tarski(B_7,A_6)
      | B_7 = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_8,c_223])).

tff(c_331,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_327,c_227])).

tff(c_334,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_331])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_58,plain,(
    r1_tarski('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_38,c_46])).

tff(c_292,plain,(
    ! [A_76,B_77,A_11] :
      ( r1_tarski('#skF_1'(A_76,B_77),A_11)
      | ~ r1_tarski(A_76,k1_zfmisc_1(A_11))
      | r1_tarski(A_76,B_77) ) ),
    inference(resolution,[status(thm)],[c_270,c_18])).

tff(c_59,plain,(
    ! [D_30] :
      ( r2_hidden(D_30,'#skF_7')
      | ~ r2_hidden(D_30,'#skF_6')
      | ~ m1_subset_1(D_30,k1_zfmisc_1('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_133,plain,(
    ! [A_50] :
      ( r2_hidden(A_50,'#skF_7')
      | ~ r2_hidden(A_50,'#skF_6')
      | ~ r1_tarski(A_50,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_32,c_59])).

tff(c_363,plain,(
    ! [A_91] :
      ( r1_tarski(A_91,'#skF_7')
      | ~ r2_hidden('#skF_1'(A_91,'#skF_7'),'#skF_6')
      | ~ r1_tarski('#skF_1'(A_91,'#skF_7'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_133,c_4])).

tff(c_375,plain,
    ( ~ r1_tarski('#skF_1'('#skF_6','#skF_7'),'#skF_5')
    | r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_6,c_363])).

tff(c_381,plain,(
    ~ r1_tarski('#skF_1'('#skF_6','#skF_7'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_334,c_334,c_375])).

tff(c_389,plain,
    ( ~ r1_tarski('#skF_6',k1_zfmisc_1('#skF_5'))
    | r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_292,c_381])).

tff(c_392,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_389])).

tff(c_394,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_334,c_392])).

tff(c_395,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_313])).

tff(c_426,plain,(
    ! [B_97] :
      ( ~ r2_xboole_0('#skF_7',B_97)
      | ~ r2_hidden('#skF_2'('#skF_7',B_97),'#skF_6')
      | ~ r1_tarski('#skF_2'('#skF_7',B_97),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_133,c_14])).

tff(c_436,plain,
    ( ~ r1_tarski('#skF_2'('#skF_7','#skF_6'),'#skF_5')
    | ~ r2_xboole_0('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_16,c_426])).

tff(c_437,plain,(
    ~ r2_xboole_0('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_436])).

tff(c_440,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_8,c_437])).

tff(c_443,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_440])).

tff(c_445,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_443])).

tff(c_447,plain,(
    r2_xboole_0('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_436])).

tff(c_209,plain,(
    ! [A_65,B_66,A_11] :
      ( r1_tarski('#skF_2'(A_65,B_66),A_11)
      | ~ r1_tarski(B_66,k1_zfmisc_1(A_11))
      | ~ r2_xboole_0(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_191,c_18])).

tff(c_446,plain,(
    ~ r1_tarski('#skF_2'('#skF_7','#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_436])).

tff(c_459,plain,
    ( ~ r1_tarski('#skF_6',k1_zfmisc_1('#skF_5'))
    | ~ r2_xboole_0('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_209,c_446])).

tff(c_463,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_58,c_459])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:42:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.36  
% 2.25/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.37  %$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > #nlpp > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 2.25/1.37  
% 2.25/1.37  %Foreground sorts:
% 2.25/1.37  
% 2.25/1.37  
% 2.25/1.37  %Background operators:
% 2.25/1.37  
% 2.25/1.37  
% 2.25/1.37  %Foreground operators:
% 2.25/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.25/1.37  tff('#skF_7', type, '#skF_7': $i).
% 2.25/1.37  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.25/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.25/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.25/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.25/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.25/1.37  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.25/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.25/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.25/1.37  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.25/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.25/1.37  
% 2.60/1.38  tff(f_75, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_setfam_1)).
% 2.60/1.38  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.60/1.38  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.60/1.38  tff(f_56, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.60/1.38  tff(f_39, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.60/1.38  tff(f_49, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 2.60/1.38  tff(c_34, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.60/1.38  tff(c_36, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.60/1.38  tff(c_46, plain, (![A_28, B_29]: (r1_tarski(A_28, B_29) | ~m1_subset_1(A_28, k1_zfmisc_1(B_29)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.60/1.38  tff(c_57, plain, (r1_tarski('#skF_7', k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_36, c_46])).
% 2.60/1.38  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.60/1.38  tff(c_117, plain, (![C_46, B_47, A_48]: (r2_hidden(C_46, B_47) | ~r2_hidden(C_46, A_48) | ~r1_tarski(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.60/1.38  tff(c_270, plain, (![A_76, B_77, B_78]: (r2_hidden('#skF_1'(A_76, B_77), B_78) | ~r1_tarski(A_76, B_78) | r1_tarski(A_76, B_77))), inference(resolution, [status(thm)], [c_6, c_117])).
% 2.60/1.38  tff(c_18, plain, (![C_15, A_11]: (r1_tarski(C_15, A_11) | ~r2_hidden(C_15, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.60/1.38  tff(c_315, plain, (![A_83, B_84, A_85]: (r1_tarski('#skF_1'(A_83, B_84), A_85) | ~r1_tarski(A_83, k1_zfmisc_1(A_85)) | r1_tarski(A_83, B_84))), inference(resolution, [status(thm)], [c_270, c_18])).
% 2.60/1.38  tff(c_32, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.60/1.38  tff(c_127, plain, (![D_49]: (r2_hidden(D_49, '#skF_6') | ~r2_hidden(D_49, '#skF_7') | ~m1_subset_1(D_49, k1_zfmisc_1('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.60/1.38  tff(c_147, plain, (![A_51]: (r2_hidden(A_51, '#skF_6') | ~r2_hidden(A_51, '#skF_7') | ~r1_tarski(A_51, '#skF_5'))), inference(resolution, [status(thm)], [c_32, c_127])).
% 2.60/1.38  tff(c_302, plain, (![B_82]: (r2_hidden('#skF_1'('#skF_7', B_82), '#skF_6') | ~r1_tarski('#skF_1'('#skF_7', B_82), '#skF_5') | r1_tarski('#skF_7', B_82))), inference(resolution, [status(thm)], [c_6, c_147])).
% 2.60/1.38  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.60/1.38  tff(c_313, plain, (~r1_tarski('#skF_1'('#skF_7', '#skF_6'), '#skF_5') | r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_302, c_4])).
% 2.60/1.38  tff(c_314, plain, (~r1_tarski('#skF_1'('#skF_7', '#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_313])).
% 2.60/1.38  tff(c_318, plain, (~r1_tarski('#skF_7', k1_zfmisc_1('#skF_5')) | r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_315, c_314])).
% 2.60/1.38  tff(c_327, plain, (r1_tarski('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_318])).
% 2.60/1.38  tff(c_8, plain, (![A_6, B_7]: (r2_xboole_0(A_6, B_7) | B_7=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.60/1.38  tff(c_16, plain, (![A_8, B_9]: (r2_hidden('#skF_2'(A_8, B_9), B_9) | ~r2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.60/1.38  tff(c_191, plain, (![A_65, B_66, B_67]: (r2_hidden('#skF_2'(A_65, B_66), B_67) | ~r1_tarski(B_66, B_67) | ~r2_xboole_0(A_65, B_66))), inference(resolution, [status(thm)], [c_16, c_117])).
% 2.60/1.38  tff(c_14, plain, (![A_8, B_9]: (~r2_hidden('#skF_2'(A_8, B_9), A_8) | ~r2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.60/1.38  tff(c_223, plain, (![B_70, B_71]: (~r1_tarski(B_70, B_71) | ~r2_xboole_0(B_71, B_70))), inference(resolution, [status(thm)], [c_191, c_14])).
% 2.60/1.38  tff(c_227, plain, (![B_7, A_6]: (~r1_tarski(B_7, A_6) | B_7=A_6 | ~r1_tarski(A_6, B_7))), inference(resolution, [status(thm)], [c_8, c_223])).
% 2.60/1.38  tff(c_331, plain, ('#skF_7'='#skF_6' | ~r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_327, c_227])).
% 2.60/1.38  tff(c_334, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_34, c_331])).
% 2.60/1.38  tff(c_38, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.60/1.38  tff(c_58, plain, (r1_tarski('#skF_6', k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_46])).
% 2.60/1.38  tff(c_292, plain, (![A_76, B_77, A_11]: (r1_tarski('#skF_1'(A_76, B_77), A_11) | ~r1_tarski(A_76, k1_zfmisc_1(A_11)) | r1_tarski(A_76, B_77))), inference(resolution, [status(thm)], [c_270, c_18])).
% 2.60/1.38  tff(c_59, plain, (![D_30]: (r2_hidden(D_30, '#skF_7') | ~r2_hidden(D_30, '#skF_6') | ~m1_subset_1(D_30, k1_zfmisc_1('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.60/1.38  tff(c_133, plain, (![A_50]: (r2_hidden(A_50, '#skF_7') | ~r2_hidden(A_50, '#skF_6') | ~r1_tarski(A_50, '#skF_5'))), inference(resolution, [status(thm)], [c_32, c_59])).
% 2.60/1.38  tff(c_363, plain, (![A_91]: (r1_tarski(A_91, '#skF_7') | ~r2_hidden('#skF_1'(A_91, '#skF_7'), '#skF_6') | ~r1_tarski('#skF_1'(A_91, '#skF_7'), '#skF_5'))), inference(resolution, [status(thm)], [c_133, c_4])).
% 2.60/1.38  tff(c_375, plain, (~r1_tarski('#skF_1'('#skF_6', '#skF_7'), '#skF_5') | r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_6, c_363])).
% 2.60/1.38  tff(c_381, plain, (~r1_tarski('#skF_1'('#skF_6', '#skF_7'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_334, c_334, c_375])).
% 2.60/1.38  tff(c_389, plain, (~r1_tarski('#skF_6', k1_zfmisc_1('#skF_5')) | r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_292, c_381])).
% 2.60/1.38  tff(c_392, plain, (r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_389])).
% 2.60/1.38  tff(c_394, plain, $false, inference(negUnitSimplification, [status(thm)], [c_334, c_392])).
% 2.60/1.38  tff(c_395, plain, (r1_tarski('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_313])).
% 2.60/1.38  tff(c_426, plain, (![B_97]: (~r2_xboole_0('#skF_7', B_97) | ~r2_hidden('#skF_2'('#skF_7', B_97), '#skF_6') | ~r1_tarski('#skF_2'('#skF_7', B_97), '#skF_5'))), inference(resolution, [status(thm)], [c_133, c_14])).
% 2.60/1.38  tff(c_436, plain, (~r1_tarski('#skF_2'('#skF_7', '#skF_6'), '#skF_5') | ~r2_xboole_0('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_16, c_426])).
% 2.60/1.38  tff(c_437, plain, (~r2_xboole_0('#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_436])).
% 2.60/1.38  tff(c_440, plain, ('#skF_7'='#skF_6' | ~r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_8, c_437])).
% 2.60/1.38  tff(c_443, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_395, c_440])).
% 2.60/1.38  tff(c_445, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_443])).
% 2.60/1.38  tff(c_447, plain, (r2_xboole_0('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_436])).
% 2.60/1.38  tff(c_209, plain, (![A_65, B_66, A_11]: (r1_tarski('#skF_2'(A_65, B_66), A_11) | ~r1_tarski(B_66, k1_zfmisc_1(A_11)) | ~r2_xboole_0(A_65, B_66))), inference(resolution, [status(thm)], [c_191, c_18])).
% 2.60/1.38  tff(c_446, plain, (~r1_tarski('#skF_2'('#skF_7', '#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_436])).
% 2.60/1.38  tff(c_459, plain, (~r1_tarski('#skF_6', k1_zfmisc_1('#skF_5')) | ~r2_xboole_0('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_209, c_446])).
% 2.60/1.38  tff(c_463, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_447, c_58, c_459])).
% 2.60/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.38  
% 2.60/1.38  Inference rules
% 2.60/1.38  ----------------------
% 2.60/1.38  #Ref     : 0
% 2.60/1.38  #Sup     : 83
% 2.60/1.38  #Fact    : 0
% 2.60/1.38  #Define  : 0
% 2.60/1.38  #Split   : 6
% 2.60/1.38  #Chain   : 0
% 2.60/1.38  #Close   : 0
% 2.60/1.38  
% 2.60/1.38  Ordering : KBO
% 2.60/1.38  
% 2.60/1.38  Simplification rules
% 2.60/1.38  ----------------------
% 2.60/1.38  #Subsume      : 8
% 2.60/1.38  #Demod        : 9
% 2.60/1.38  #Tautology    : 12
% 2.60/1.38  #SimpNegUnit  : 6
% 2.60/1.38  #BackRed      : 0
% 2.60/1.38  
% 2.60/1.38  #Partial instantiations: 0
% 2.60/1.38  #Strategies tried      : 1
% 2.60/1.38  
% 2.60/1.38  Timing (in seconds)
% 2.60/1.38  ----------------------
% 2.60/1.38  Preprocessing        : 0.28
% 2.60/1.38  Parsing              : 0.14
% 2.60/1.38  CNF conversion       : 0.02
% 2.60/1.38  Main loop            : 0.29
% 2.60/1.38  Inferencing          : 0.11
% 2.60/1.38  Reduction            : 0.07
% 2.60/1.38  Demodulation         : 0.05
% 2.60/1.38  BG Simplification    : 0.02
% 2.60/1.38  Subsumption          : 0.07
% 2.60/1.38  Abstraction          : 0.01
% 2.60/1.38  MUC search           : 0.00
% 2.60/1.39  Cooper               : 0.00
% 2.60/1.39  Total                : 0.60
% 2.60/1.39  Index Insertion      : 0.00
% 2.60/1.39  Index Deletion       : 0.00
% 2.60/1.39  Index Matching       : 0.00
% 2.60/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
