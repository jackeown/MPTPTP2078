%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:07 EST 2020

% Result     : Theorem 4.84s
% Output     : CNFRefutation 4.84s
% Verified   : 
% Statistics : Number of formulae       :   64 (  87 expanded)
%              Number of leaves         :   24 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :  128 ( 216 expanded)
%              Number of equality atoms :   12 (  17 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] :
        ( v3_ordinal1(B)
       => ~ ( r1_tarski(A,B)
            & A != k1_xboole_0
            & ! [C] :
                ( v3_ordinal1(C)
               => ~ ( r2_hidden(C,A)
                    & ! [D] :
                        ( v3_ordinal1(D)
                       => ( r2_hidden(D,A)
                         => r1_ordinal1(C,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_61,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v3_ordinal1(B)
     => ( r2_hidden(A,B)
       => v3_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

tff(f_76,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_97,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_1'(A_44,B_45),A_44)
      | r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_65,plain,(
    ! [A_32,B_33] : ~ r2_hidden(A_32,k2_zfmisc_1(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_68,plain,(
    ! [A_9] : ~ r2_hidden(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_65])).

tff(c_111,plain,(
    ! [B_45] : r1_tarski(k1_xboole_0,B_45) ),
    inference(resolution,[status(thm)],[c_97,c_68])).

tff(c_351,plain,(
    ! [A_94,B_95] :
      ( r2_hidden('#skF_2'(A_94,B_95),B_95)
      | r2_hidden('#skF_3'(A_94,B_95),A_94)
      | B_95 = A_94 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1655,plain,(
    ! [A_227,B_228,B_229] :
      ( r2_hidden('#skF_2'(A_227,B_228),B_229)
      | ~ r1_tarski(B_228,B_229)
      | r2_hidden('#skF_3'(A_227,B_228),A_227)
      | B_228 = A_227 ) ),
    inference(resolution,[status(thm)],[c_351,c_2])).

tff(c_22,plain,(
    ! [A_11,B_12] : ~ r2_hidden(A_11,k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1787,plain,(
    ! [B_241,A_242,B_243] :
      ( ~ r1_tarski(B_241,k2_zfmisc_1('#skF_2'(A_242,B_241),B_243))
      | r2_hidden('#skF_3'(A_242,B_241),A_242)
      | B_241 = A_242 ) ),
    inference(resolution,[status(thm)],[c_1655,c_22])).

tff(c_1793,plain,(
    ! [A_242] :
      ( r2_hidden('#skF_3'(A_242,k1_xboole_0),A_242)
      | k1_xboole_0 = A_242 ) ),
    inference(resolution,[status(thm)],[c_111,c_1787])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_109,plain,(
    ! [A_44] : r1_tarski(A_44,A_44) ),
    inference(resolution,[status(thm)],[c_97,c_4])).

tff(c_36,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_34,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_4'(A_13,B_14),B_14)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_120,plain,(
    ! [C_50,B_51,A_52] :
      ( r2_hidden(C_50,B_51)
      | ~ r2_hidden(C_50,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_249,plain,(
    ! [A_74,B_75,B_76] :
      ( r2_hidden('#skF_4'(A_74,B_75),B_76)
      | ~ r1_tarski(B_75,B_76)
      | ~ r2_hidden(A_74,B_75) ) ),
    inference(resolution,[status(thm)],[c_26,c_120])).

tff(c_2028,plain,(
    ! [A_266,B_267,B_268,B_269] :
      ( r2_hidden('#skF_4'(A_266,B_267),B_268)
      | ~ r1_tarski(B_269,B_268)
      | ~ r1_tarski(B_267,B_269)
      | ~ r2_hidden(A_266,B_267) ) ),
    inference(resolution,[status(thm)],[c_249,c_2])).

tff(c_2059,plain,(
    ! [A_273,B_274] :
      ( r2_hidden('#skF_4'(A_273,B_274),'#skF_6')
      | ~ r1_tarski(B_274,'#skF_5')
      | ~ r2_hidden(A_273,B_274) ) ),
    inference(resolution,[status(thm)],[c_34,c_2028])).

tff(c_28,plain,(
    ! [A_20,B_21] :
      ( v3_ordinal1(A_20)
      | ~ r2_hidden(A_20,B_21)
      | ~ v3_ordinal1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2067,plain,(
    ! [A_273,B_274] :
      ( v3_ordinal1('#skF_4'(A_273,B_274))
      | ~ v3_ordinal1('#skF_6')
      | ~ r1_tarski(B_274,'#skF_5')
      | ~ r2_hidden(A_273,B_274) ) ),
    inference(resolution,[status(thm)],[c_2059,c_28])).

tff(c_2072,plain,(
    ! [A_273,B_274] :
      ( v3_ordinal1('#skF_4'(A_273,B_274))
      | ~ r1_tarski(B_274,'#skF_5')
      | ~ r2_hidden(A_273,B_274) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2067])).

tff(c_129,plain,(
    ! [A_13,B_14,B_51] :
      ( r2_hidden('#skF_4'(A_13,B_14),B_51)
      | ~ r1_tarski(B_14,B_51)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(resolution,[status(thm)],[c_26,c_120])).

tff(c_42,plain,(
    ! [C_28] :
      ( v3_ordinal1('#skF_7'(C_28))
      | ~ r2_hidden(C_28,'#skF_5')
      | ~ v3_ordinal1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_40,plain,(
    ! [C_28] :
      ( r2_hidden('#skF_7'(C_28),'#skF_5')
      | ~ r2_hidden(C_28,'#skF_5')
      | ~ v3_ordinal1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_30,plain,(
    ! [B_24,A_22] :
      ( r2_hidden(B_24,A_22)
      | r1_ordinal1(A_22,B_24)
      | ~ v3_ordinal1(B_24)
      | ~ v3_ordinal1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_174,plain,(
    ! [D_61,A_62,B_63] :
      ( ~ r2_hidden(D_61,'#skF_4'(A_62,B_63))
      | ~ r2_hidden(D_61,B_63)
      | ~ r2_hidden(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2372,plain,(
    ! [B_309,B_310,A_311] :
      ( ~ r2_hidden(B_309,B_310)
      | ~ r2_hidden(A_311,B_310)
      | r1_ordinal1('#skF_4'(A_311,B_310),B_309)
      | ~ v3_ordinal1(B_309)
      | ~ v3_ordinal1('#skF_4'(A_311,B_310)) ) ),
    inference(resolution,[status(thm)],[c_30,c_174])).

tff(c_38,plain,(
    ! [C_28] :
      ( ~ r1_ordinal1(C_28,'#skF_7'(C_28))
      | ~ r2_hidden(C_28,'#skF_5')
      | ~ v3_ordinal1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2391,plain,(
    ! [A_316,B_317] :
      ( ~ r2_hidden('#skF_4'(A_316,B_317),'#skF_5')
      | ~ r2_hidden('#skF_7'('#skF_4'(A_316,B_317)),B_317)
      | ~ r2_hidden(A_316,B_317)
      | ~ v3_ordinal1('#skF_7'('#skF_4'(A_316,B_317)))
      | ~ v3_ordinal1('#skF_4'(A_316,B_317)) ) ),
    inference(resolution,[status(thm)],[c_2372,c_38])).

tff(c_2546,plain,(
    ! [A_329] :
      ( ~ r2_hidden(A_329,'#skF_5')
      | ~ v3_ordinal1('#skF_7'('#skF_4'(A_329,'#skF_5')))
      | ~ r2_hidden('#skF_4'(A_329,'#skF_5'),'#skF_5')
      | ~ v3_ordinal1('#skF_4'(A_329,'#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_40,c_2391])).

tff(c_2551,plain,(
    ! [A_330] :
      ( ~ r2_hidden(A_330,'#skF_5')
      | ~ r2_hidden('#skF_4'(A_330,'#skF_5'),'#skF_5')
      | ~ v3_ordinal1('#skF_4'(A_330,'#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_42,c_2546])).

tff(c_2559,plain,(
    ! [A_13] :
      ( ~ v3_ordinal1('#skF_4'(A_13,'#skF_5'))
      | ~ r1_tarski('#skF_5','#skF_5')
      | ~ r2_hidden(A_13,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_129,c_2551])).

tff(c_2575,plain,(
    ! [A_331] :
      ( ~ v3_ordinal1('#skF_4'(A_331,'#skF_5'))
      | ~ r2_hidden(A_331,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_2559])).

tff(c_2579,plain,(
    ! [A_273] :
      ( ~ r1_tarski('#skF_5','#skF_5')
      | ~ r2_hidden(A_273,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2072,c_2575])).

tff(c_2593,plain,(
    ! [A_332] : ~ r2_hidden(A_332,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_2579])).

tff(c_2609,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1793,c_2593])).

tff(c_2706,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_2609])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:25:05 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.84/1.94  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.84/1.94  
% 4.84/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.84/1.95  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 4.84/1.95  
% 4.84/1.95  %Foreground sorts:
% 4.84/1.95  
% 4.84/1.95  
% 4.84/1.95  %Background operators:
% 4.84/1.95  
% 4.84/1.95  
% 4.84/1.95  %Foreground operators:
% 4.84/1.95  tff('#skF_7', type, '#skF_7': $i > $i).
% 4.84/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.84/1.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.84/1.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.84/1.95  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.84/1.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.84/1.95  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 4.84/1.95  tff('#skF_5', type, '#skF_5': $i).
% 4.84/1.95  tff('#skF_6', type, '#skF_6': $i).
% 4.84/1.95  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 4.84/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.84/1.95  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.84/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.84/1.95  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.84/1.95  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.84/1.95  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.84/1.95  
% 4.84/1.96  tff(f_98, negated_conjecture, ~(![A, B]: (v3_ordinal1(B) => ~((r1_tarski(A, B) & ~(A = k1_xboole_0)) & (![C]: (v3_ordinal1(C) => ~(r2_hidden(C, A) & (![D]: (v3_ordinal1(D) => (r2_hidden(D, A) => r1_ordinal1(C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_ordinal1)).
% 4.84/1.96  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.84/1.96  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.84/1.96  tff(f_48, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 4.84/1.96  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 4.84/1.96  tff(f_61, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 4.84/1.96  tff(f_67, axiom, (![A, B]: (v3_ordinal1(B) => (r2_hidden(A, B) => v3_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_ordinal1)).
% 4.84/1.96  tff(f_76, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 4.84/1.96  tff(c_32, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.84/1.96  tff(c_97, plain, (![A_44, B_45]: (r2_hidden('#skF_1'(A_44, B_45), A_44) | r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.84/1.96  tff(c_18, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.84/1.96  tff(c_65, plain, (![A_32, B_33]: (~r2_hidden(A_32, k2_zfmisc_1(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.84/1.96  tff(c_68, plain, (![A_9]: (~r2_hidden(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_65])).
% 4.84/1.96  tff(c_111, plain, (![B_45]: (r1_tarski(k1_xboole_0, B_45))), inference(resolution, [status(thm)], [c_97, c_68])).
% 4.84/1.96  tff(c_351, plain, (![A_94, B_95]: (r2_hidden('#skF_2'(A_94, B_95), B_95) | r2_hidden('#skF_3'(A_94, B_95), A_94) | B_95=A_94)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.84/1.96  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.84/1.96  tff(c_1655, plain, (![A_227, B_228, B_229]: (r2_hidden('#skF_2'(A_227, B_228), B_229) | ~r1_tarski(B_228, B_229) | r2_hidden('#skF_3'(A_227, B_228), A_227) | B_228=A_227)), inference(resolution, [status(thm)], [c_351, c_2])).
% 4.84/1.96  tff(c_22, plain, (![A_11, B_12]: (~r2_hidden(A_11, k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.84/1.96  tff(c_1787, plain, (![B_241, A_242, B_243]: (~r1_tarski(B_241, k2_zfmisc_1('#skF_2'(A_242, B_241), B_243)) | r2_hidden('#skF_3'(A_242, B_241), A_242) | B_241=A_242)), inference(resolution, [status(thm)], [c_1655, c_22])).
% 4.84/1.96  tff(c_1793, plain, (![A_242]: (r2_hidden('#skF_3'(A_242, k1_xboole_0), A_242) | k1_xboole_0=A_242)), inference(resolution, [status(thm)], [c_111, c_1787])).
% 4.84/1.96  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.84/1.96  tff(c_109, plain, (![A_44]: (r1_tarski(A_44, A_44))), inference(resolution, [status(thm)], [c_97, c_4])).
% 4.84/1.96  tff(c_36, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.84/1.96  tff(c_34, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.84/1.96  tff(c_26, plain, (![A_13, B_14]: (r2_hidden('#skF_4'(A_13, B_14), B_14) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.84/1.96  tff(c_120, plain, (![C_50, B_51, A_52]: (r2_hidden(C_50, B_51) | ~r2_hidden(C_50, A_52) | ~r1_tarski(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.84/1.96  tff(c_249, plain, (![A_74, B_75, B_76]: (r2_hidden('#skF_4'(A_74, B_75), B_76) | ~r1_tarski(B_75, B_76) | ~r2_hidden(A_74, B_75))), inference(resolution, [status(thm)], [c_26, c_120])).
% 4.84/1.96  tff(c_2028, plain, (![A_266, B_267, B_268, B_269]: (r2_hidden('#skF_4'(A_266, B_267), B_268) | ~r1_tarski(B_269, B_268) | ~r1_tarski(B_267, B_269) | ~r2_hidden(A_266, B_267))), inference(resolution, [status(thm)], [c_249, c_2])).
% 4.84/1.96  tff(c_2059, plain, (![A_273, B_274]: (r2_hidden('#skF_4'(A_273, B_274), '#skF_6') | ~r1_tarski(B_274, '#skF_5') | ~r2_hidden(A_273, B_274))), inference(resolution, [status(thm)], [c_34, c_2028])).
% 4.84/1.96  tff(c_28, plain, (![A_20, B_21]: (v3_ordinal1(A_20) | ~r2_hidden(A_20, B_21) | ~v3_ordinal1(B_21))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.84/1.96  tff(c_2067, plain, (![A_273, B_274]: (v3_ordinal1('#skF_4'(A_273, B_274)) | ~v3_ordinal1('#skF_6') | ~r1_tarski(B_274, '#skF_5') | ~r2_hidden(A_273, B_274))), inference(resolution, [status(thm)], [c_2059, c_28])).
% 4.84/1.96  tff(c_2072, plain, (![A_273, B_274]: (v3_ordinal1('#skF_4'(A_273, B_274)) | ~r1_tarski(B_274, '#skF_5') | ~r2_hidden(A_273, B_274))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2067])).
% 4.84/1.96  tff(c_129, plain, (![A_13, B_14, B_51]: (r2_hidden('#skF_4'(A_13, B_14), B_51) | ~r1_tarski(B_14, B_51) | ~r2_hidden(A_13, B_14))), inference(resolution, [status(thm)], [c_26, c_120])).
% 4.84/1.96  tff(c_42, plain, (![C_28]: (v3_ordinal1('#skF_7'(C_28)) | ~r2_hidden(C_28, '#skF_5') | ~v3_ordinal1(C_28))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.84/1.96  tff(c_40, plain, (![C_28]: (r2_hidden('#skF_7'(C_28), '#skF_5') | ~r2_hidden(C_28, '#skF_5') | ~v3_ordinal1(C_28))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.84/1.96  tff(c_30, plain, (![B_24, A_22]: (r2_hidden(B_24, A_22) | r1_ordinal1(A_22, B_24) | ~v3_ordinal1(B_24) | ~v3_ordinal1(A_22))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.84/1.96  tff(c_174, plain, (![D_61, A_62, B_63]: (~r2_hidden(D_61, '#skF_4'(A_62, B_63)) | ~r2_hidden(D_61, B_63) | ~r2_hidden(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.84/1.96  tff(c_2372, plain, (![B_309, B_310, A_311]: (~r2_hidden(B_309, B_310) | ~r2_hidden(A_311, B_310) | r1_ordinal1('#skF_4'(A_311, B_310), B_309) | ~v3_ordinal1(B_309) | ~v3_ordinal1('#skF_4'(A_311, B_310)))), inference(resolution, [status(thm)], [c_30, c_174])).
% 4.84/1.96  tff(c_38, plain, (![C_28]: (~r1_ordinal1(C_28, '#skF_7'(C_28)) | ~r2_hidden(C_28, '#skF_5') | ~v3_ordinal1(C_28))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.84/1.96  tff(c_2391, plain, (![A_316, B_317]: (~r2_hidden('#skF_4'(A_316, B_317), '#skF_5') | ~r2_hidden('#skF_7'('#skF_4'(A_316, B_317)), B_317) | ~r2_hidden(A_316, B_317) | ~v3_ordinal1('#skF_7'('#skF_4'(A_316, B_317))) | ~v3_ordinal1('#skF_4'(A_316, B_317)))), inference(resolution, [status(thm)], [c_2372, c_38])).
% 4.84/1.96  tff(c_2546, plain, (![A_329]: (~r2_hidden(A_329, '#skF_5') | ~v3_ordinal1('#skF_7'('#skF_4'(A_329, '#skF_5'))) | ~r2_hidden('#skF_4'(A_329, '#skF_5'), '#skF_5') | ~v3_ordinal1('#skF_4'(A_329, '#skF_5')))), inference(resolution, [status(thm)], [c_40, c_2391])).
% 4.84/1.96  tff(c_2551, plain, (![A_330]: (~r2_hidden(A_330, '#skF_5') | ~r2_hidden('#skF_4'(A_330, '#skF_5'), '#skF_5') | ~v3_ordinal1('#skF_4'(A_330, '#skF_5')))), inference(resolution, [status(thm)], [c_42, c_2546])).
% 4.84/1.96  tff(c_2559, plain, (![A_13]: (~v3_ordinal1('#skF_4'(A_13, '#skF_5')) | ~r1_tarski('#skF_5', '#skF_5') | ~r2_hidden(A_13, '#skF_5'))), inference(resolution, [status(thm)], [c_129, c_2551])).
% 4.84/1.96  tff(c_2575, plain, (![A_331]: (~v3_ordinal1('#skF_4'(A_331, '#skF_5')) | ~r2_hidden(A_331, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_2559])).
% 4.84/1.96  tff(c_2579, plain, (![A_273]: (~r1_tarski('#skF_5', '#skF_5') | ~r2_hidden(A_273, '#skF_5'))), inference(resolution, [status(thm)], [c_2072, c_2575])).
% 4.84/1.96  tff(c_2593, plain, (![A_332]: (~r2_hidden(A_332, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_2579])).
% 4.84/1.96  tff(c_2609, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1793, c_2593])).
% 4.84/1.96  tff(c_2706, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_2609])).
% 4.84/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.84/1.96  
% 4.84/1.96  Inference rules
% 4.84/1.96  ----------------------
% 4.84/1.96  #Ref     : 0
% 4.84/1.96  #Sup     : 549
% 4.84/1.96  #Fact    : 0
% 4.84/1.96  #Define  : 0
% 4.84/1.96  #Split   : 8
% 4.84/1.96  #Chain   : 0
% 4.84/1.96  #Close   : 0
% 4.84/1.96  
% 4.84/1.96  Ordering : KBO
% 4.84/1.96  
% 4.84/1.96  Simplification rules
% 4.84/1.96  ----------------------
% 4.84/1.96  #Subsume      : 235
% 4.84/1.96  #Demod        : 53
% 4.84/1.96  #Tautology    : 46
% 4.84/1.96  #SimpNegUnit  : 15
% 4.84/1.96  #BackRed      : 0
% 4.84/1.96  
% 4.84/1.96  #Partial instantiations: 0
% 4.84/1.96  #Strategies tried      : 1
% 4.84/1.96  
% 4.84/1.96  Timing (in seconds)
% 4.84/1.96  ----------------------
% 4.84/1.96  Preprocessing        : 0.35
% 4.84/1.96  Parsing              : 0.17
% 4.84/1.96  CNF conversion       : 0.03
% 4.84/1.96  Main loop            : 0.84
% 4.84/1.96  Inferencing          : 0.32
% 4.84/1.96  Reduction            : 0.20
% 4.84/1.96  Demodulation         : 0.12
% 4.84/1.96  BG Simplification    : 0.03
% 4.84/1.96  Subsumption          : 0.23
% 4.84/1.96  Abstraction          : 0.04
% 4.84/1.96  MUC search           : 0.00
% 4.84/1.96  Cooper               : 0.00
% 4.84/1.96  Total                : 1.22
% 4.84/1.96  Index Insertion      : 0.00
% 4.84/1.96  Index Deletion       : 0.00
% 4.84/1.96  Index Matching       : 0.00
% 4.84/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
