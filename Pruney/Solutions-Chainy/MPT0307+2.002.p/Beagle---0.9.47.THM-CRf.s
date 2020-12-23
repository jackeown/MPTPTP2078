%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:52 EST 2020

% Result     : Theorem 11.24s
% Output     : CNFRefutation 11.24s
% Verified   : 
% Statistics : Number of formulae       :   50 (  71 expanded)
%              Number of leaves         :   21 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   76 ( 151 expanded)
%              Number of equality atoms :    3 (  18 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_51,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_34,plain,(
    r1_tarski('#skF_10','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ! [A_6,B_7,D_33] :
      ( r2_hidden('#skF_6'(A_6,B_7,k2_zfmisc_1(A_6,B_7),D_33),A_6)
      | ~ r2_hidden(D_33,k2_zfmisc_1(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_62,plain,(
    ! [A_55,B_56,D_57] :
      ( r2_hidden('#skF_7'(A_55,B_56,k2_zfmisc_1(A_55,B_56),D_57),B_56)
      | ~ r2_hidden(D_57,k2_zfmisc_1(A_55,B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_65,plain,(
    ! [A_55,B_56,D_57,B_2] :
      ( r2_hidden('#skF_7'(A_55,B_56,k2_zfmisc_1(A_55,B_56),D_57),B_2)
      | ~ r1_tarski(B_56,B_2)
      | ~ r2_hidden(D_57,k2_zfmisc_1(A_55,B_56)) ) ),
    inference(resolution,[status(thm)],[c_62,c_2])).

tff(c_260,plain,(
    ! [A_105,B_106,D_107] :
      ( k4_tarski('#skF_6'(A_105,B_106,k2_zfmisc_1(A_105,B_106),D_107),'#skF_7'(A_105,B_106,k2_zfmisc_1(A_105,B_106),D_107)) = D_107
      | ~ r2_hidden(D_107,k2_zfmisc_1(A_105,B_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [E_38,F_39,A_6,B_7] :
      ( r2_hidden(k4_tarski(E_38,F_39),k2_zfmisc_1(A_6,B_7))
      | ~ r2_hidden(F_39,B_7)
      | ~ r2_hidden(E_38,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2122,plain,(
    ! [D_324,B_327,A_325,A_328,B_326] :
      ( r2_hidden(D_324,k2_zfmisc_1(A_328,B_327))
      | ~ r2_hidden('#skF_7'(A_325,B_326,k2_zfmisc_1(A_325,B_326),D_324),B_327)
      | ~ r2_hidden('#skF_6'(A_325,B_326,k2_zfmisc_1(A_325,B_326),D_324),A_328)
      | ~ r2_hidden(D_324,k2_zfmisc_1(A_325,B_326)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_8])).

tff(c_7326,plain,(
    ! [D_544,A_543,A_541,B_540,B_542] :
      ( r2_hidden(D_544,k2_zfmisc_1(A_543,B_542))
      | ~ r2_hidden('#skF_6'(A_541,B_540,k2_zfmisc_1(A_541,B_540),D_544),A_543)
      | ~ r1_tarski(B_540,B_542)
      | ~ r2_hidden(D_544,k2_zfmisc_1(A_541,B_540)) ) ),
    inference(resolution,[status(thm)],[c_65,c_2122])).

tff(c_7361,plain,(
    ! [D_545,A_546,B_547,B_548] :
      ( r2_hidden(D_545,k2_zfmisc_1(A_546,B_547))
      | ~ r1_tarski(B_548,B_547)
      | ~ r2_hidden(D_545,k2_zfmisc_1(A_546,B_548)) ) ),
    inference(resolution,[status(thm)],[c_14,c_7326])).

tff(c_7395,plain,(
    ! [D_549,A_550] :
      ( r2_hidden(D_549,k2_zfmisc_1(A_550,'#skF_11'))
      | ~ r2_hidden(D_549,k2_zfmisc_1(A_550,'#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_34,c_7361])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_13729,plain,(
    ! [A_697,A_698] :
      ( r1_tarski(A_697,k2_zfmisc_1(A_698,'#skF_11'))
      | ~ r2_hidden('#skF_1'(A_697,k2_zfmisc_1(A_698,'#skF_11')),k2_zfmisc_1(A_698,'#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_7395,c_4])).

tff(c_13789,plain,(
    ! [A_698] : r1_tarski(k2_zfmisc_1(A_698,'#skF_10'),k2_zfmisc_1(A_698,'#skF_11')) ),
    inference(resolution,[status(thm)],[c_6,c_13729])).

tff(c_44,plain,(
    ! [C_44,B_45,A_46] :
      ( r2_hidden(C_44,B_45)
      | ~ r2_hidden(C_44,A_46)
      | ~ r1_tarski(A_46,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_47,plain,(
    ! [A_1,B_2,B_45] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_45)
      | ~ r1_tarski(A_1,B_45)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_44])).

tff(c_36,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_66,plain,(
    ! [A_58,B_59,D_60] :
      ( r2_hidden('#skF_6'(A_58,B_59,k2_zfmisc_1(A_58,B_59),D_60),A_58)
      | ~ r2_hidden(D_60,k2_zfmisc_1(A_58,B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_69,plain,(
    ! [A_58,B_59,D_60,B_2] :
      ( r2_hidden('#skF_6'(A_58,B_59,k2_zfmisc_1(A_58,B_59),D_60),B_2)
      | ~ r1_tarski(A_58,B_2)
      | ~ r2_hidden(D_60,k2_zfmisc_1(A_58,B_59)) ) ),
    inference(resolution,[status(thm)],[c_66,c_2])).

tff(c_12,plain,(
    ! [A_6,B_7,D_33] :
      ( r2_hidden('#skF_7'(A_6,B_7,k2_zfmisc_1(A_6,B_7),D_33),B_7)
      | ~ r2_hidden(D_33,k2_zfmisc_1(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2141,plain,(
    ! [D_329,A_330,B_331,A_332] :
      ( r2_hidden(D_329,k2_zfmisc_1(A_330,B_331))
      | ~ r2_hidden('#skF_6'(A_332,B_331,k2_zfmisc_1(A_332,B_331),D_329),A_330)
      | ~ r2_hidden(D_329,k2_zfmisc_1(A_332,B_331)) ) ),
    inference(resolution,[status(thm)],[c_12,c_2122])).

tff(c_2166,plain,(
    ! [D_333,B_334,B_335,A_336] :
      ( r2_hidden(D_333,k2_zfmisc_1(B_334,B_335))
      | ~ r1_tarski(A_336,B_334)
      | ~ r2_hidden(D_333,k2_zfmisc_1(A_336,B_335)) ) ),
    inference(resolution,[status(thm)],[c_69,c_2141])).

tff(c_2238,plain,(
    ! [D_339,B_340] :
      ( r2_hidden(D_339,k2_zfmisc_1('#skF_9',B_340))
      | ~ r2_hidden(D_339,k2_zfmisc_1('#skF_8',B_340)) ) ),
    inference(resolution,[status(thm)],[c_36,c_2166])).

tff(c_3585,plain,(
    ! [A_369,B_370] :
      ( r1_tarski(A_369,k2_zfmisc_1('#skF_9',B_370))
      | ~ r2_hidden('#skF_1'(A_369,k2_zfmisc_1('#skF_9',B_370)),k2_zfmisc_1('#skF_8',B_370)) ) ),
    inference(resolution,[status(thm)],[c_2238,c_4])).

tff(c_3658,plain,(
    ! [A_372,B_373] :
      ( ~ r1_tarski(A_372,k2_zfmisc_1('#skF_8',B_373))
      | r1_tarski(A_372,k2_zfmisc_1('#skF_9',B_373)) ) ),
    inference(resolution,[status(thm)],[c_47,c_3585])).

tff(c_32,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_8','#skF_10'),k2_zfmisc_1('#skF_9','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3738,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_8','#skF_10'),k2_zfmisc_1('#skF_8','#skF_11')) ),
    inference(resolution,[status(thm)],[c_3658,c_32])).

tff(c_13792,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13789,c_3738])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:34:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.24/4.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.24/4.42  
% 11.24/4.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.24/4.42  %$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1
% 11.24/4.42  
% 11.24/4.42  %Foreground sorts:
% 11.24/4.42  
% 11.24/4.42  
% 11.24/4.42  %Background operators:
% 11.24/4.42  
% 11.24/4.42  
% 11.24/4.42  %Foreground operators:
% 11.24/4.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.24/4.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.24/4.42  tff('#skF_11', type, '#skF_11': $i).
% 11.24/4.42  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 11.24/4.42  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 11.24/4.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.24/4.42  tff('#skF_10', type, '#skF_10': $i).
% 11.24/4.42  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 11.24/4.42  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.24/4.42  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 11.24/4.42  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 11.24/4.42  tff('#skF_9', type, '#skF_9': $i).
% 11.24/4.42  tff('#skF_8', type, '#skF_8': $i).
% 11.24/4.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.24/4.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.24/4.42  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 11.24/4.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.24/4.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.24/4.42  
% 11.24/4.44  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 11.24/4.44  tff(f_51, negated_conjecture, ~(![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_zfmisc_1)).
% 11.24/4.44  tff(f_44, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 11.24/4.44  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.24/4.44  tff(c_34, plain, (r1_tarski('#skF_10', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.24/4.44  tff(c_14, plain, (![A_6, B_7, D_33]: (r2_hidden('#skF_6'(A_6, B_7, k2_zfmisc_1(A_6, B_7), D_33), A_6) | ~r2_hidden(D_33, k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.24/4.44  tff(c_62, plain, (![A_55, B_56, D_57]: (r2_hidden('#skF_7'(A_55, B_56, k2_zfmisc_1(A_55, B_56), D_57), B_56) | ~r2_hidden(D_57, k2_zfmisc_1(A_55, B_56)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.24/4.44  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.24/4.44  tff(c_65, plain, (![A_55, B_56, D_57, B_2]: (r2_hidden('#skF_7'(A_55, B_56, k2_zfmisc_1(A_55, B_56), D_57), B_2) | ~r1_tarski(B_56, B_2) | ~r2_hidden(D_57, k2_zfmisc_1(A_55, B_56)))), inference(resolution, [status(thm)], [c_62, c_2])).
% 11.24/4.44  tff(c_260, plain, (![A_105, B_106, D_107]: (k4_tarski('#skF_6'(A_105, B_106, k2_zfmisc_1(A_105, B_106), D_107), '#skF_7'(A_105, B_106, k2_zfmisc_1(A_105, B_106), D_107))=D_107 | ~r2_hidden(D_107, k2_zfmisc_1(A_105, B_106)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.24/4.44  tff(c_8, plain, (![E_38, F_39, A_6, B_7]: (r2_hidden(k4_tarski(E_38, F_39), k2_zfmisc_1(A_6, B_7)) | ~r2_hidden(F_39, B_7) | ~r2_hidden(E_38, A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.24/4.44  tff(c_2122, plain, (![D_324, B_327, A_325, A_328, B_326]: (r2_hidden(D_324, k2_zfmisc_1(A_328, B_327)) | ~r2_hidden('#skF_7'(A_325, B_326, k2_zfmisc_1(A_325, B_326), D_324), B_327) | ~r2_hidden('#skF_6'(A_325, B_326, k2_zfmisc_1(A_325, B_326), D_324), A_328) | ~r2_hidden(D_324, k2_zfmisc_1(A_325, B_326)))), inference(superposition, [status(thm), theory('equality')], [c_260, c_8])).
% 11.24/4.44  tff(c_7326, plain, (![D_544, A_543, A_541, B_540, B_542]: (r2_hidden(D_544, k2_zfmisc_1(A_543, B_542)) | ~r2_hidden('#skF_6'(A_541, B_540, k2_zfmisc_1(A_541, B_540), D_544), A_543) | ~r1_tarski(B_540, B_542) | ~r2_hidden(D_544, k2_zfmisc_1(A_541, B_540)))), inference(resolution, [status(thm)], [c_65, c_2122])).
% 11.24/4.44  tff(c_7361, plain, (![D_545, A_546, B_547, B_548]: (r2_hidden(D_545, k2_zfmisc_1(A_546, B_547)) | ~r1_tarski(B_548, B_547) | ~r2_hidden(D_545, k2_zfmisc_1(A_546, B_548)))), inference(resolution, [status(thm)], [c_14, c_7326])).
% 11.24/4.44  tff(c_7395, plain, (![D_549, A_550]: (r2_hidden(D_549, k2_zfmisc_1(A_550, '#skF_11')) | ~r2_hidden(D_549, k2_zfmisc_1(A_550, '#skF_10')))), inference(resolution, [status(thm)], [c_34, c_7361])).
% 11.24/4.44  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.24/4.44  tff(c_13729, plain, (![A_697, A_698]: (r1_tarski(A_697, k2_zfmisc_1(A_698, '#skF_11')) | ~r2_hidden('#skF_1'(A_697, k2_zfmisc_1(A_698, '#skF_11')), k2_zfmisc_1(A_698, '#skF_10')))), inference(resolution, [status(thm)], [c_7395, c_4])).
% 11.24/4.44  tff(c_13789, plain, (![A_698]: (r1_tarski(k2_zfmisc_1(A_698, '#skF_10'), k2_zfmisc_1(A_698, '#skF_11')))), inference(resolution, [status(thm)], [c_6, c_13729])).
% 11.24/4.44  tff(c_44, plain, (![C_44, B_45, A_46]: (r2_hidden(C_44, B_45) | ~r2_hidden(C_44, A_46) | ~r1_tarski(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.24/4.44  tff(c_47, plain, (![A_1, B_2, B_45]: (r2_hidden('#skF_1'(A_1, B_2), B_45) | ~r1_tarski(A_1, B_45) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_44])).
% 11.24/4.44  tff(c_36, plain, (r1_tarski('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.24/4.44  tff(c_66, plain, (![A_58, B_59, D_60]: (r2_hidden('#skF_6'(A_58, B_59, k2_zfmisc_1(A_58, B_59), D_60), A_58) | ~r2_hidden(D_60, k2_zfmisc_1(A_58, B_59)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.24/4.44  tff(c_69, plain, (![A_58, B_59, D_60, B_2]: (r2_hidden('#skF_6'(A_58, B_59, k2_zfmisc_1(A_58, B_59), D_60), B_2) | ~r1_tarski(A_58, B_2) | ~r2_hidden(D_60, k2_zfmisc_1(A_58, B_59)))), inference(resolution, [status(thm)], [c_66, c_2])).
% 11.24/4.44  tff(c_12, plain, (![A_6, B_7, D_33]: (r2_hidden('#skF_7'(A_6, B_7, k2_zfmisc_1(A_6, B_7), D_33), B_7) | ~r2_hidden(D_33, k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.24/4.44  tff(c_2141, plain, (![D_329, A_330, B_331, A_332]: (r2_hidden(D_329, k2_zfmisc_1(A_330, B_331)) | ~r2_hidden('#skF_6'(A_332, B_331, k2_zfmisc_1(A_332, B_331), D_329), A_330) | ~r2_hidden(D_329, k2_zfmisc_1(A_332, B_331)))), inference(resolution, [status(thm)], [c_12, c_2122])).
% 11.24/4.44  tff(c_2166, plain, (![D_333, B_334, B_335, A_336]: (r2_hidden(D_333, k2_zfmisc_1(B_334, B_335)) | ~r1_tarski(A_336, B_334) | ~r2_hidden(D_333, k2_zfmisc_1(A_336, B_335)))), inference(resolution, [status(thm)], [c_69, c_2141])).
% 11.24/4.44  tff(c_2238, plain, (![D_339, B_340]: (r2_hidden(D_339, k2_zfmisc_1('#skF_9', B_340)) | ~r2_hidden(D_339, k2_zfmisc_1('#skF_8', B_340)))), inference(resolution, [status(thm)], [c_36, c_2166])).
% 11.24/4.44  tff(c_3585, plain, (![A_369, B_370]: (r1_tarski(A_369, k2_zfmisc_1('#skF_9', B_370)) | ~r2_hidden('#skF_1'(A_369, k2_zfmisc_1('#skF_9', B_370)), k2_zfmisc_1('#skF_8', B_370)))), inference(resolution, [status(thm)], [c_2238, c_4])).
% 11.24/4.44  tff(c_3658, plain, (![A_372, B_373]: (~r1_tarski(A_372, k2_zfmisc_1('#skF_8', B_373)) | r1_tarski(A_372, k2_zfmisc_1('#skF_9', B_373)))), inference(resolution, [status(thm)], [c_47, c_3585])).
% 11.24/4.44  tff(c_32, plain, (~r1_tarski(k2_zfmisc_1('#skF_8', '#skF_10'), k2_zfmisc_1('#skF_9', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.24/4.44  tff(c_3738, plain, (~r1_tarski(k2_zfmisc_1('#skF_8', '#skF_10'), k2_zfmisc_1('#skF_8', '#skF_11'))), inference(resolution, [status(thm)], [c_3658, c_32])).
% 11.24/4.44  tff(c_13792, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13789, c_3738])).
% 11.24/4.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.24/4.44  
% 11.24/4.44  Inference rules
% 11.24/4.44  ----------------------
% 11.24/4.44  #Ref     : 3
% 11.24/4.44  #Sup     : 3732
% 11.24/4.44  #Fact    : 0
% 11.24/4.44  #Define  : 0
% 11.24/4.44  #Split   : 18
% 11.24/4.44  #Chain   : 0
% 11.24/4.44  #Close   : 0
% 11.24/4.44  
% 11.24/4.44  Ordering : KBO
% 11.24/4.44  
% 11.24/4.44  Simplification rules
% 11.24/4.44  ----------------------
% 11.24/4.44  #Subsume      : 394
% 11.24/4.44  #Demod        : 1
% 11.24/4.44  #Tautology    : 8
% 11.24/4.44  #SimpNegUnit  : 0
% 11.24/4.44  #BackRed      : 1
% 11.24/4.44  
% 11.24/4.44  #Partial instantiations: 0
% 11.24/4.44  #Strategies tried      : 1
% 11.24/4.44  
% 11.24/4.44  Timing (in seconds)
% 11.24/4.44  ----------------------
% 11.24/4.44  Preprocessing        : 0.29
% 11.24/4.44  Parsing              : 0.14
% 11.24/4.44  CNF conversion       : 0.03
% 11.24/4.44  Main loop            : 3.38
% 11.24/4.44  Inferencing          : 0.57
% 11.24/4.44  Reduction            : 0.55
% 11.24/4.44  Demodulation         : 0.32
% 11.24/4.44  BG Simplification    : 0.10
% 11.24/4.44  Subsumption          : 1.96
% 11.24/4.44  Abstraction          : 0.12
% 11.24/4.44  MUC search           : 0.00
% 11.24/4.44  Cooper               : 0.00
% 11.24/4.44  Total                : 3.70
% 11.24/4.44  Index Insertion      : 0.00
% 11.24/4.44  Index Deletion       : 0.00
% 11.24/4.44  Index Matching       : 0.00
% 11.24/4.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
