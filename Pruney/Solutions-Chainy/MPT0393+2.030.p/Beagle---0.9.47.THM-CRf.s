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
% DateTime   : Thu Dec  3 09:57:20 EST 2020

% Result     : Theorem 4.61s
% Output     : CNFRefutation 4.61s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 387 expanded)
%              Number of leaves         :   27 ( 139 expanded)
%              Depth                    :   13
%              Number of atoms          :  119 (1019 expanded)
%              Number of equality atoms :   60 ( 635 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( A != k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ! [D] :
                  ( r2_hidden(D,A)
                 => r2_hidden(C,D) ) ) ) )
      & ( A = k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_83,plain,(
    ! [D_44,B_45] : r2_hidden(D_44,k2_tarski(D_44,B_45)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_86,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_83])).

tff(c_30,plain,(
    ! [B_14] : r1_tarski(k1_xboole_0,k1_tarski(B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_445,plain,(
    ! [A_112,B_113,D_114] :
      ( r2_hidden('#skF_4'(A_112,B_113),D_114)
      | ~ r2_hidden(D_114,A_112)
      | r2_hidden('#skF_6'(A_112,B_113),A_112)
      | k1_setfam_1(A_112) = B_113
      | k1_xboole_0 = A_112 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_48,plain,(
    ! [A_22,B_23] :
      ( ~ r2_hidden('#skF_4'(A_22,B_23),B_23)
      | r2_hidden('#skF_6'(A_22,B_23),A_22)
      | k1_setfam_1(A_22) = B_23
      | k1_xboole_0 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_931,plain,(
    ! [D_1195,A_1196] :
      ( ~ r2_hidden(D_1195,A_1196)
      | r2_hidden('#skF_6'(A_1196,D_1195),A_1196)
      | k1_setfam_1(A_1196) = D_1195
      | k1_xboole_0 = A_1196 ) ),
    inference(resolution,[status(thm)],[c_445,c_48])).

tff(c_112,plain,(
    ! [A_59,B_60] :
      ( k4_xboole_0(k1_tarski(A_59),k1_tarski(B_60)) = k1_tarski(A_59)
      | B_60 = A_59 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_38,plain,(
    ! [C_19,B_18] : ~ r2_hidden(C_19,k4_xboole_0(B_18,k1_tarski(C_19))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_125,plain,(
    ! [B_60,A_59] :
      ( ~ r2_hidden(B_60,k1_tarski(A_59))
      | B_60 = A_59 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_38])).

tff(c_2738,plain,(
    ! [A_4722,D_4723] :
      ( '#skF_6'(k1_tarski(A_4722),D_4723) = A_4722
      | ~ r2_hidden(D_4723,k1_tarski(A_4722))
      | k1_setfam_1(k1_tarski(A_4722)) = D_4723
      | k1_tarski(A_4722) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_931,c_125])).

tff(c_2833,plain,(
    ! [A_4808] :
      ( '#skF_6'(k1_tarski(A_4808),A_4808) = A_4808
      | k1_setfam_1(k1_tarski(A_4808)) = A_4808
      | k1_tarski(A_4808) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_86,c_2738])).

tff(c_66,plain,(
    k1_setfam_1(k1_tarski('#skF_7')) != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2977,plain,
    ( '#skF_6'(k1_tarski('#skF_7'),'#skF_7') = '#skF_7'
    | k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2833,c_66])).

tff(c_2981,plain,(
    k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2977])).

tff(c_42,plain,(
    ! [B_21,A_20] :
      ( B_21 = A_20
      | ~ r1_tarski(k1_tarski(A_20),k1_tarski(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3035,plain,(
    ! [B_21] :
      ( B_21 = '#skF_7'
      | ~ r1_tarski(k1_xboole_0,k1_tarski(B_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2981,c_42])).

tff(c_3110,plain,(
    ! [B_5061] : B_5061 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3035])).

tff(c_64,plain,(
    k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2982,plain,(
    k1_setfam_1(k1_xboole_0) != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2981,c_66])).

tff(c_2983,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2982])).

tff(c_3304,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_3110,c_2983])).

tff(c_3306,plain,(
    k1_tarski('#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2977])).

tff(c_54,plain,(
    ! [A_22,B_23,D_39] :
      ( r2_hidden('#skF_4'(A_22,B_23),D_39)
      | ~ r2_hidden(D_39,A_22)
      | r2_hidden('#skF_5'(A_22,B_23),B_23)
      | k1_setfam_1(A_22) = B_23
      | k1_xboole_0 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3305,plain,(
    '#skF_6'(k1_tarski('#skF_7'),'#skF_7') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_2977])).

tff(c_44,plain,(
    ! [A_22,B_23] :
      ( ~ r2_hidden('#skF_4'(A_22,B_23),B_23)
      | ~ r2_hidden('#skF_5'(A_22,B_23),'#skF_6'(A_22,B_23))
      | k1_setfam_1(A_22) = B_23
      | k1_xboole_0 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3323,plain,
    ( ~ r2_hidden('#skF_4'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7')
    | ~ r2_hidden('#skF_5'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7')
    | k1_setfam_1(k1_tarski('#skF_7')) = '#skF_7'
    | k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3305,c_44])).

tff(c_3367,plain,
    ( ~ r2_hidden('#skF_4'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7')
    | ~ r2_hidden('#skF_5'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_3306,c_66,c_3323])).

tff(c_3476,plain,(
    ~ r2_hidden('#skF_5'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_3367])).

tff(c_3487,plain,(
    ! [D_39] :
      ( r2_hidden('#skF_4'(k1_tarski('#skF_7'),'#skF_7'),D_39)
      | ~ r2_hidden(D_39,k1_tarski('#skF_7'))
      | k1_setfam_1(k1_tarski('#skF_7')) = '#skF_7'
      | k1_tarski('#skF_7') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_54,c_3476])).

tff(c_3507,plain,(
    ! [D_7250] :
      ( r2_hidden('#skF_4'(k1_tarski('#skF_7'),'#skF_7'),D_7250)
      | ~ r2_hidden(D_7250,k1_tarski('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3306,c_66,c_3487])).

tff(c_52,plain,(
    ! [A_22,B_23] :
      ( ~ r2_hidden('#skF_4'(A_22,B_23),B_23)
      | r2_hidden('#skF_5'(A_22,B_23),B_23)
      | k1_setfam_1(A_22) = B_23
      | k1_xboole_0 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3490,plain,
    ( ~ r2_hidden('#skF_4'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7')
    | k1_setfam_1(k1_tarski('#skF_7')) = '#skF_7'
    | k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_3476])).

tff(c_3496,plain,(
    ~ r2_hidden('#skF_4'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_3306,c_66,c_3490])).

tff(c_3510,plain,(
    ~ r2_hidden('#skF_7',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_3507,c_3496])).

tff(c_3594,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_3510])).

tff(c_3596,plain,(
    r2_hidden('#skF_5'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_3367])).

tff(c_46,plain,(
    ! [A_22,B_23,D_39] :
      ( r2_hidden('#skF_4'(A_22,B_23),D_39)
      | ~ r2_hidden(D_39,A_22)
      | ~ r2_hidden('#skF_5'(A_22,B_23),'#skF_6'(A_22,B_23))
      | k1_setfam_1(A_22) = B_23
      | k1_xboole_0 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3314,plain,(
    ! [D_39] :
      ( r2_hidden('#skF_4'(k1_tarski('#skF_7'),'#skF_7'),D_39)
      | ~ r2_hidden(D_39,k1_tarski('#skF_7'))
      | ~ r2_hidden('#skF_5'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7')
      | k1_setfam_1(k1_tarski('#skF_7')) = '#skF_7'
      | k1_tarski('#skF_7') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3305,c_46])).

tff(c_3361,plain,(
    ! [D_39] :
      ( r2_hidden('#skF_4'(k1_tarski('#skF_7'),'#skF_7'),D_39)
      | ~ r2_hidden(D_39,k1_tarski('#skF_7'))
      | ~ r2_hidden('#skF_5'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_3306,c_66,c_3314])).

tff(c_3694,plain,(
    ! [D_7839] :
      ( r2_hidden('#skF_4'(k1_tarski('#skF_7'),'#skF_7'),D_7839)
      | ~ r2_hidden(D_7839,k1_tarski('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3596,c_3361])).

tff(c_3595,plain,(
    ~ r2_hidden('#skF_4'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_3367])).

tff(c_3697,plain,(
    ~ r2_hidden('#skF_7',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_3694,c_3595])).

tff(c_3756,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_3697])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:42:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.61/1.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.61/1.88  
% 4.61/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.61/1.88  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_3 > #skF_5 > #skF_4
% 4.61/1.88  
% 4.61/1.88  %Foreground sorts:
% 4.61/1.88  
% 4.61/1.88  
% 4.61/1.88  %Background operators:
% 4.61/1.88  
% 4.61/1.88  
% 4.61/1.88  %Foreground operators:
% 4.61/1.88  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.61/1.88  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.61/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.61/1.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.61/1.88  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.61/1.88  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.61/1.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.61/1.88  tff('#skF_7', type, '#skF_7': $i).
% 4.61/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.61/1.88  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.61/1.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.61/1.88  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.61/1.88  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.61/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.61/1.88  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.61/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.61/1.88  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.61/1.88  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.61/1.88  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.61/1.88  
% 4.61/1.91  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.61/1.91  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 4.61/1.91  tff(f_46, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.61/1.91  tff(f_81, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_setfam_1)).
% 4.61/1.91  tff(f_51, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 4.61/1.91  tff(f_58, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 4.61/1.91  tff(f_84, negated_conjecture, ~(![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 4.61/1.91  tff(f_62, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 4.61/1.91  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.61/1.91  tff(c_83, plain, (![D_44, B_45]: (r2_hidden(D_44, k2_tarski(D_44, B_45)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.61/1.91  tff(c_86, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_83])).
% 4.61/1.91  tff(c_30, plain, (![B_14]: (r1_tarski(k1_xboole_0, k1_tarski(B_14)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.61/1.91  tff(c_445, plain, (![A_112, B_113, D_114]: (r2_hidden('#skF_4'(A_112, B_113), D_114) | ~r2_hidden(D_114, A_112) | r2_hidden('#skF_6'(A_112, B_113), A_112) | k1_setfam_1(A_112)=B_113 | k1_xboole_0=A_112)), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.61/1.91  tff(c_48, plain, (![A_22, B_23]: (~r2_hidden('#skF_4'(A_22, B_23), B_23) | r2_hidden('#skF_6'(A_22, B_23), A_22) | k1_setfam_1(A_22)=B_23 | k1_xboole_0=A_22)), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.61/1.91  tff(c_931, plain, (![D_1195, A_1196]: (~r2_hidden(D_1195, A_1196) | r2_hidden('#skF_6'(A_1196, D_1195), A_1196) | k1_setfam_1(A_1196)=D_1195 | k1_xboole_0=A_1196)), inference(resolution, [status(thm)], [c_445, c_48])).
% 4.61/1.91  tff(c_112, plain, (![A_59, B_60]: (k4_xboole_0(k1_tarski(A_59), k1_tarski(B_60))=k1_tarski(A_59) | B_60=A_59)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.61/1.91  tff(c_38, plain, (![C_19, B_18]: (~r2_hidden(C_19, k4_xboole_0(B_18, k1_tarski(C_19))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.61/1.91  tff(c_125, plain, (![B_60, A_59]: (~r2_hidden(B_60, k1_tarski(A_59)) | B_60=A_59)), inference(superposition, [status(thm), theory('equality')], [c_112, c_38])).
% 4.61/1.91  tff(c_2738, plain, (![A_4722, D_4723]: ('#skF_6'(k1_tarski(A_4722), D_4723)=A_4722 | ~r2_hidden(D_4723, k1_tarski(A_4722)) | k1_setfam_1(k1_tarski(A_4722))=D_4723 | k1_tarski(A_4722)=k1_xboole_0)), inference(resolution, [status(thm)], [c_931, c_125])).
% 4.61/1.91  tff(c_2833, plain, (![A_4808]: ('#skF_6'(k1_tarski(A_4808), A_4808)=A_4808 | k1_setfam_1(k1_tarski(A_4808))=A_4808 | k1_tarski(A_4808)=k1_xboole_0)), inference(resolution, [status(thm)], [c_86, c_2738])).
% 4.61/1.91  tff(c_66, plain, (k1_setfam_1(k1_tarski('#skF_7'))!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.61/1.91  tff(c_2977, plain, ('#skF_6'(k1_tarski('#skF_7'), '#skF_7')='#skF_7' | k1_tarski('#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2833, c_66])).
% 4.61/1.91  tff(c_2981, plain, (k1_tarski('#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2977])).
% 4.61/1.91  tff(c_42, plain, (![B_21, A_20]: (B_21=A_20 | ~r1_tarski(k1_tarski(A_20), k1_tarski(B_21)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.61/1.91  tff(c_3035, plain, (![B_21]: (B_21='#skF_7' | ~r1_tarski(k1_xboole_0, k1_tarski(B_21)))), inference(superposition, [status(thm), theory('equality')], [c_2981, c_42])).
% 4.61/1.91  tff(c_3110, plain, (![B_5061]: (B_5061='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3035])).
% 4.61/1.91  tff(c_64, plain, (k1_setfam_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.61/1.91  tff(c_2982, plain, (k1_setfam_1(k1_xboole_0)!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2981, c_66])).
% 4.61/1.91  tff(c_2983, plain, (k1_xboole_0!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2982])).
% 4.61/1.91  tff(c_3304, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_3110, c_2983])).
% 4.61/1.91  tff(c_3306, plain, (k1_tarski('#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_2977])).
% 4.61/1.91  tff(c_54, plain, (![A_22, B_23, D_39]: (r2_hidden('#skF_4'(A_22, B_23), D_39) | ~r2_hidden(D_39, A_22) | r2_hidden('#skF_5'(A_22, B_23), B_23) | k1_setfam_1(A_22)=B_23 | k1_xboole_0=A_22)), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.61/1.91  tff(c_3305, plain, ('#skF_6'(k1_tarski('#skF_7'), '#skF_7')='#skF_7'), inference(splitRight, [status(thm)], [c_2977])).
% 4.61/1.91  tff(c_44, plain, (![A_22, B_23]: (~r2_hidden('#skF_4'(A_22, B_23), B_23) | ~r2_hidden('#skF_5'(A_22, B_23), '#skF_6'(A_22, B_23)) | k1_setfam_1(A_22)=B_23 | k1_xboole_0=A_22)), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.61/1.91  tff(c_3323, plain, (~r2_hidden('#skF_4'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7') | ~r2_hidden('#skF_5'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7') | k1_setfam_1(k1_tarski('#skF_7'))='#skF_7' | k1_tarski('#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3305, c_44])).
% 4.61/1.91  tff(c_3367, plain, (~r2_hidden('#skF_4'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7') | ~r2_hidden('#skF_5'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_3306, c_66, c_3323])).
% 4.61/1.91  tff(c_3476, plain, (~r2_hidden('#skF_5'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7')), inference(splitLeft, [status(thm)], [c_3367])).
% 4.61/1.91  tff(c_3487, plain, (![D_39]: (r2_hidden('#skF_4'(k1_tarski('#skF_7'), '#skF_7'), D_39) | ~r2_hidden(D_39, k1_tarski('#skF_7')) | k1_setfam_1(k1_tarski('#skF_7'))='#skF_7' | k1_tarski('#skF_7')=k1_xboole_0)), inference(resolution, [status(thm)], [c_54, c_3476])).
% 4.61/1.91  tff(c_3507, plain, (![D_7250]: (r2_hidden('#skF_4'(k1_tarski('#skF_7'), '#skF_7'), D_7250) | ~r2_hidden(D_7250, k1_tarski('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_3306, c_66, c_3487])).
% 4.61/1.91  tff(c_52, plain, (![A_22, B_23]: (~r2_hidden('#skF_4'(A_22, B_23), B_23) | r2_hidden('#skF_5'(A_22, B_23), B_23) | k1_setfam_1(A_22)=B_23 | k1_xboole_0=A_22)), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.61/1.91  tff(c_3490, plain, (~r2_hidden('#skF_4'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7') | k1_setfam_1(k1_tarski('#skF_7'))='#skF_7' | k1_tarski('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_3476])).
% 4.61/1.91  tff(c_3496, plain, (~r2_hidden('#skF_4'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_3306, c_66, c_3490])).
% 4.61/1.91  tff(c_3510, plain, (~r2_hidden('#skF_7', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_3507, c_3496])).
% 4.61/1.91  tff(c_3594, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_3510])).
% 4.61/1.91  tff(c_3596, plain, (r2_hidden('#skF_5'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7')), inference(splitRight, [status(thm)], [c_3367])).
% 4.61/1.91  tff(c_46, plain, (![A_22, B_23, D_39]: (r2_hidden('#skF_4'(A_22, B_23), D_39) | ~r2_hidden(D_39, A_22) | ~r2_hidden('#skF_5'(A_22, B_23), '#skF_6'(A_22, B_23)) | k1_setfam_1(A_22)=B_23 | k1_xboole_0=A_22)), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.61/1.91  tff(c_3314, plain, (![D_39]: (r2_hidden('#skF_4'(k1_tarski('#skF_7'), '#skF_7'), D_39) | ~r2_hidden(D_39, k1_tarski('#skF_7')) | ~r2_hidden('#skF_5'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7') | k1_setfam_1(k1_tarski('#skF_7'))='#skF_7' | k1_tarski('#skF_7')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3305, c_46])).
% 4.61/1.91  tff(c_3361, plain, (![D_39]: (r2_hidden('#skF_4'(k1_tarski('#skF_7'), '#skF_7'), D_39) | ~r2_hidden(D_39, k1_tarski('#skF_7')) | ~r2_hidden('#skF_5'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_3306, c_66, c_3314])).
% 4.61/1.91  tff(c_3694, plain, (![D_7839]: (r2_hidden('#skF_4'(k1_tarski('#skF_7'), '#skF_7'), D_7839) | ~r2_hidden(D_7839, k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_3596, c_3361])).
% 4.61/1.91  tff(c_3595, plain, (~r2_hidden('#skF_4'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7')), inference(splitRight, [status(thm)], [c_3367])).
% 4.61/1.91  tff(c_3697, plain, (~r2_hidden('#skF_7', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_3694, c_3595])).
% 4.61/1.91  tff(c_3756, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_3697])).
% 4.61/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.61/1.91  
% 4.61/1.91  Inference rules
% 4.61/1.91  ----------------------
% 4.61/1.91  #Ref     : 0
% 4.61/1.91  #Sup     : 530
% 4.61/1.91  #Fact    : 4
% 4.61/1.91  #Define  : 0
% 4.61/1.91  #Split   : 6
% 4.61/1.91  #Chain   : 0
% 4.61/1.91  #Close   : 0
% 4.61/1.91  
% 4.61/1.91  Ordering : KBO
% 4.61/1.91  
% 4.61/1.91  Simplification rules
% 4.61/1.91  ----------------------
% 4.61/1.91  #Subsume      : 50
% 4.61/1.91  #Demod        : 133
% 4.61/1.91  #Tautology    : 118
% 4.61/1.91  #SimpNegUnit  : 6
% 4.61/1.91  #BackRed      : 29
% 4.61/1.91  
% 4.61/1.91  #Partial instantiations: 3066
% 4.61/1.91  #Strategies tried      : 1
% 4.61/1.91  
% 4.61/1.91  Timing (in seconds)
% 4.61/1.91  ----------------------
% 4.61/1.91  Preprocessing        : 0.34
% 4.61/1.91  Parsing              : 0.18
% 4.61/1.91  CNF conversion       : 0.03
% 4.61/1.91  Main loop            : 0.73
% 4.61/1.91  Inferencing          : 0.37
% 4.61/1.91  Reduction            : 0.16
% 4.61/1.91  Demodulation         : 0.11
% 4.61/1.91  BG Simplification    : 0.04
% 4.61/1.91  Subsumption          : 0.11
% 4.61/1.91  Abstraction          : 0.04
% 4.61/1.91  MUC search           : 0.00
% 4.61/1.92  Cooper               : 0.00
% 4.61/1.92  Total                : 1.12
% 4.61/1.92  Index Insertion      : 0.00
% 4.61/1.92  Index Deletion       : 0.00
% 4.61/1.92  Index Matching       : 0.00
% 4.61/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
