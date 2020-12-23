%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:42 EST 2020

% Result     : Theorem 7.05s
% Output     : CNFRefutation 7.05s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 115 expanded)
%              Number of leaves         :   24 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          :  138 ( 404 expanded)
%              Number of equality atoms :    2 (   8 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_tarski > #nlpp > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_5 > #skF_9 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_1

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => ( r1_tarski(A,B)
                 => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( C = k5_relat_1(A,B)
              <=> ! [D,E] :
                    ( r2_hidden(k4_tarski(D,E),C)
                  <=> ? [F] :
                        ( r2_hidden(k4_tarski(D,F),A)
                        & r2_hidden(k4_tarski(F,E),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_40,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_32,plain,(
    ! [A_119,B_120] :
      ( v1_relat_1(k5_relat_1(A_119,B_120))
      | ~ v1_relat_1(B_120)
      | ~ v1_relat_1(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_42,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_3,B_13] :
      ( r2_hidden(k4_tarski('#skF_1'(A_3,B_13),'#skF_2'(A_3,B_13)),A_3)
      | r1_tarski(A_3,B_13)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_30,plain,(
    ! [D_111,A_20,B_72,E_112] :
      ( r2_hidden(k4_tarski(D_111,'#skF_3'(k5_relat_1(A_20,B_72),B_72,E_112,A_20,D_111)),A_20)
      | ~ r2_hidden(k4_tarski(D_111,E_112),k5_relat_1(A_20,B_72))
      | ~ v1_relat_1(k5_relat_1(A_20,B_72))
      | ~ v1_relat_1(B_72)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_36,plain,(
    r1_tarski('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_186,plain,(
    ! [A_170,B_171,E_172,D_173] :
      ( r2_hidden(k4_tarski('#skF_3'(k5_relat_1(A_170,B_171),B_171,E_172,A_170,D_173),E_172),B_171)
      | ~ r2_hidden(k4_tarski(D_173,E_172),k5_relat_1(A_170,B_171))
      | ~ v1_relat_1(k5_relat_1(A_170,B_171))
      | ~ v1_relat_1(B_171)
      | ~ v1_relat_1(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8,plain,(
    ! [C_18,D_19,B_13,A_3] :
      ( r2_hidden(k4_tarski(C_18,D_19),B_13)
      | ~ r2_hidden(k4_tarski(C_18,D_19),A_3)
      | ~ r1_tarski(A_3,B_13)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_207,plain,(
    ! [B_183,E_185,D_186,A_184,B_187] :
      ( r2_hidden(k4_tarski('#skF_3'(k5_relat_1(A_184,B_187),B_187,E_185,A_184,D_186),E_185),B_183)
      | ~ r1_tarski(B_187,B_183)
      | ~ r2_hidden(k4_tarski(D_186,E_185),k5_relat_1(A_184,B_187))
      | ~ v1_relat_1(k5_relat_1(A_184,B_187))
      | ~ v1_relat_1(B_187)
      | ~ v1_relat_1(A_184) ) ),
    inference(resolution,[status(thm)],[c_186,c_8])).

tff(c_392,plain,(
    ! [A_269,B_267,B_266,E_271,D_270,B_268] :
      ( r2_hidden(k4_tarski('#skF_3'(k5_relat_1(A_269,B_266),B_266,E_271,A_269,D_270),E_271),B_267)
      | ~ r1_tarski(B_268,B_267)
      | ~ v1_relat_1(B_268)
      | ~ r1_tarski(B_266,B_268)
      | ~ r2_hidden(k4_tarski(D_270,E_271),k5_relat_1(A_269,B_266))
      | ~ v1_relat_1(k5_relat_1(A_269,B_266))
      | ~ v1_relat_1(B_266)
      | ~ v1_relat_1(A_269) ) ),
    inference(resolution,[status(thm)],[c_207,c_8])).

tff(c_398,plain,(
    ! [A_269,B_266,E_271,D_270] :
      ( r2_hidden(k4_tarski('#skF_3'(k5_relat_1(A_269,B_266),B_266,E_271,A_269,D_270),E_271),'#skF_10')
      | ~ v1_relat_1('#skF_9')
      | ~ r1_tarski(B_266,'#skF_9')
      | ~ r2_hidden(k4_tarski(D_270,E_271),k5_relat_1(A_269,B_266))
      | ~ v1_relat_1(k5_relat_1(A_269,B_266))
      | ~ v1_relat_1(B_266)
      | ~ v1_relat_1(A_269) ) ),
    inference(resolution,[status(thm)],[c_36,c_392])).

tff(c_404,plain,(
    ! [A_272,B_273,E_274,D_275] :
      ( r2_hidden(k4_tarski('#skF_3'(k5_relat_1(A_272,B_273),B_273,E_274,A_272,D_275),E_274),'#skF_10')
      | ~ r1_tarski(B_273,'#skF_9')
      | ~ r2_hidden(k4_tarski(D_275,E_274),k5_relat_1(A_272,B_273))
      | ~ v1_relat_1(k5_relat_1(A_272,B_273))
      | ~ v1_relat_1(B_273)
      | ~ v1_relat_1(A_272) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_398])).

tff(c_26,plain,(
    ! [D_111,A_20,F_115,B_72,E_112] :
      ( r2_hidden(k4_tarski(D_111,E_112),k5_relat_1(A_20,B_72))
      | ~ r2_hidden(k4_tarski(F_115,E_112),B_72)
      | ~ r2_hidden(k4_tarski(D_111,F_115),A_20)
      | ~ v1_relat_1(k5_relat_1(A_20,B_72))
      | ~ v1_relat_1(B_72)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_412,plain,(
    ! [E_274,D_111,A_20,A_272,D_275,B_273] :
      ( r2_hidden(k4_tarski(D_111,E_274),k5_relat_1(A_20,'#skF_10'))
      | ~ r2_hidden(k4_tarski(D_111,'#skF_3'(k5_relat_1(A_272,B_273),B_273,E_274,A_272,D_275)),A_20)
      | ~ v1_relat_1(k5_relat_1(A_20,'#skF_10'))
      | ~ v1_relat_1('#skF_10')
      | ~ v1_relat_1(A_20)
      | ~ r1_tarski(B_273,'#skF_9')
      | ~ r2_hidden(k4_tarski(D_275,E_274),k5_relat_1(A_272,B_273))
      | ~ v1_relat_1(k5_relat_1(A_272,B_273))
      | ~ v1_relat_1(B_273)
      | ~ v1_relat_1(A_272) ) ),
    inference(resolution,[status(thm)],[c_404,c_26])).

tff(c_585,plain,(
    ! [E_320,A_318,A_322,D_319,B_321,D_323] :
      ( r2_hidden(k4_tarski(D_323,E_320),k5_relat_1(A_322,'#skF_10'))
      | ~ r2_hidden(k4_tarski(D_323,'#skF_3'(k5_relat_1(A_318,B_321),B_321,E_320,A_318,D_319)),A_322)
      | ~ v1_relat_1(k5_relat_1(A_322,'#skF_10'))
      | ~ v1_relat_1(A_322)
      | ~ r1_tarski(B_321,'#skF_9')
      | ~ r2_hidden(k4_tarski(D_319,E_320),k5_relat_1(A_318,B_321))
      | ~ v1_relat_1(k5_relat_1(A_318,B_321))
      | ~ v1_relat_1(B_321)
      | ~ v1_relat_1(A_318) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_412])).

tff(c_626,plain,(
    ! [D_324,E_325,A_326,B_327] :
      ( r2_hidden(k4_tarski(D_324,E_325),k5_relat_1(A_326,'#skF_10'))
      | ~ v1_relat_1(k5_relat_1(A_326,'#skF_10'))
      | ~ r1_tarski(B_327,'#skF_9')
      | ~ r2_hidden(k4_tarski(D_324,E_325),k5_relat_1(A_326,B_327))
      | ~ v1_relat_1(k5_relat_1(A_326,B_327))
      | ~ v1_relat_1(B_327)
      | ~ v1_relat_1(A_326) ) ),
    inference(resolution,[status(thm)],[c_30,c_585])).

tff(c_3569,plain,(
    ! [A_582,B_583,B_584] :
      ( r2_hidden(k4_tarski('#skF_1'(k5_relat_1(A_582,B_583),B_584),'#skF_2'(k5_relat_1(A_582,B_583),B_584)),k5_relat_1(A_582,'#skF_10'))
      | ~ v1_relat_1(k5_relat_1(A_582,'#skF_10'))
      | ~ r1_tarski(B_583,'#skF_9')
      | ~ v1_relat_1(B_583)
      | ~ v1_relat_1(A_582)
      | r1_tarski(k5_relat_1(A_582,B_583),B_584)
      | ~ v1_relat_1(k5_relat_1(A_582,B_583)) ) ),
    inference(resolution,[status(thm)],[c_12,c_626])).

tff(c_10,plain,(
    ! [A_3,B_13] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_3,B_13),'#skF_2'(A_3,B_13)),B_13)
      | r1_tarski(A_3,B_13)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3624,plain,(
    ! [A_585,B_586] :
      ( ~ v1_relat_1(k5_relat_1(A_585,'#skF_10'))
      | ~ r1_tarski(B_586,'#skF_9')
      | ~ v1_relat_1(B_586)
      | ~ v1_relat_1(A_585)
      | r1_tarski(k5_relat_1(A_585,B_586),k5_relat_1(A_585,'#skF_10'))
      | ~ v1_relat_1(k5_relat_1(A_585,B_586)) ) ),
    inference(resolution,[status(thm)],[c_3569,c_10])).

tff(c_34,plain,(
    ~ r1_tarski(k5_relat_1('#skF_11','#skF_9'),k5_relat_1('#skF_11','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3691,plain,
    ( ~ v1_relat_1(k5_relat_1('#skF_11','#skF_10'))
    | ~ r1_tarski('#skF_9','#skF_9')
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_11')
    | ~ v1_relat_1(k5_relat_1('#skF_11','#skF_9')) ),
    inference(resolution,[status(thm)],[c_3624,c_34])).

tff(c_3743,plain,
    ( ~ v1_relat_1(k5_relat_1('#skF_11','#skF_10'))
    | ~ v1_relat_1(k5_relat_1('#skF_11','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42,c_6,c_3691])).

tff(c_3826,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_11','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_3743])).

tff(c_3829,plain,
    ( ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_32,c_3826])).

tff(c_3833,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42,c_3829])).

tff(c_3834,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_11','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_3743])).

tff(c_3838,plain,
    ( ~ v1_relat_1('#skF_10')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_32,c_3834])).

tff(c_3842,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40,c_3838])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:12:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.05/2.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.05/2.55  
% 7.05/2.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.05/2.56  %$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_tarski > #nlpp > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_5 > #skF_9 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_1
% 7.05/2.56  
% 7.05/2.56  %Foreground sorts:
% 7.05/2.56  
% 7.05/2.56  
% 7.05/2.56  %Background operators:
% 7.05/2.56  
% 7.05/2.56  
% 7.05/2.56  %Foreground operators:
% 7.05/2.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.05/2.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.05/2.56  tff('#skF_11', type, '#skF_11': $i).
% 7.05/2.56  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 7.05/2.56  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.05/2.56  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.05/2.56  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 7.05/2.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.05/2.56  tff('#skF_10', type, '#skF_10': $i).
% 7.05/2.56  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 7.05/2.56  tff('#skF_9', type, '#skF_9': $i).
% 7.05/2.56  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 7.05/2.56  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 7.05/2.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.05/2.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.05/2.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.05/2.56  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.05/2.56  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 7.05/2.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.05/2.56  
% 7.05/2.57  tff(f_78, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relat_1)).
% 7.05/2.57  tff(f_65, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 7.05/2.57  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.05/2.57  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 7.05/2.57  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 7.05/2.57  tff(c_38, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.05/2.57  tff(c_40, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.05/2.57  tff(c_32, plain, (![A_119, B_120]: (v1_relat_1(k5_relat_1(A_119, B_120)) | ~v1_relat_1(B_120) | ~v1_relat_1(A_119))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.05/2.57  tff(c_42, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.05/2.57  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.05/2.57  tff(c_12, plain, (![A_3, B_13]: (r2_hidden(k4_tarski('#skF_1'(A_3, B_13), '#skF_2'(A_3, B_13)), A_3) | r1_tarski(A_3, B_13) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.05/2.57  tff(c_30, plain, (![D_111, A_20, B_72, E_112]: (r2_hidden(k4_tarski(D_111, '#skF_3'(k5_relat_1(A_20, B_72), B_72, E_112, A_20, D_111)), A_20) | ~r2_hidden(k4_tarski(D_111, E_112), k5_relat_1(A_20, B_72)) | ~v1_relat_1(k5_relat_1(A_20, B_72)) | ~v1_relat_1(B_72) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.05/2.57  tff(c_36, plain, (r1_tarski('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.05/2.57  tff(c_186, plain, (![A_170, B_171, E_172, D_173]: (r2_hidden(k4_tarski('#skF_3'(k5_relat_1(A_170, B_171), B_171, E_172, A_170, D_173), E_172), B_171) | ~r2_hidden(k4_tarski(D_173, E_172), k5_relat_1(A_170, B_171)) | ~v1_relat_1(k5_relat_1(A_170, B_171)) | ~v1_relat_1(B_171) | ~v1_relat_1(A_170))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.05/2.57  tff(c_8, plain, (![C_18, D_19, B_13, A_3]: (r2_hidden(k4_tarski(C_18, D_19), B_13) | ~r2_hidden(k4_tarski(C_18, D_19), A_3) | ~r1_tarski(A_3, B_13) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.05/2.57  tff(c_207, plain, (![B_183, E_185, D_186, A_184, B_187]: (r2_hidden(k4_tarski('#skF_3'(k5_relat_1(A_184, B_187), B_187, E_185, A_184, D_186), E_185), B_183) | ~r1_tarski(B_187, B_183) | ~r2_hidden(k4_tarski(D_186, E_185), k5_relat_1(A_184, B_187)) | ~v1_relat_1(k5_relat_1(A_184, B_187)) | ~v1_relat_1(B_187) | ~v1_relat_1(A_184))), inference(resolution, [status(thm)], [c_186, c_8])).
% 7.05/2.57  tff(c_392, plain, (![A_269, B_267, B_266, E_271, D_270, B_268]: (r2_hidden(k4_tarski('#skF_3'(k5_relat_1(A_269, B_266), B_266, E_271, A_269, D_270), E_271), B_267) | ~r1_tarski(B_268, B_267) | ~v1_relat_1(B_268) | ~r1_tarski(B_266, B_268) | ~r2_hidden(k4_tarski(D_270, E_271), k5_relat_1(A_269, B_266)) | ~v1_relat_1(k5_relat_1(A_269, B_266)) | ~v1_relat_1(B_266) | ~v1_relat_1(A_269))), inference(resolution, [status(thm)], [c_207, c_8])).
% 7.05/2.57  tff(c_398, plain, (![A_269, B_266, E_271, D_270]: (r2_hidden(k4_tarski('#skF_3'(k5_relat_1(A_269, B_266), B_266, E_271, A_269, D_270), E_271), '#skF_10') | ~v1_relat_1('#skF_9') | ~r1_tarski(B_266, '#skF_9') | ~r2_hidden(k4_tarski(D_270, E_271), k5_relat_1(A_269, B_266)) | ~v1_relat_1(k5_relat_1(A_269, B_266)) | ~v1_relat_1(B_266) | ~v1_relat_1(A_269))), inference(resolution, [status(thm)], [c_36, c_392])).
% 7.05/2.57  tff(c_404, plain, (![A_272, B_273, E_274, D_275]: (r2_hidden(k4_tarski('#skF_3'(k5_relat_1(A_272, B_273), B_273, E_274, A_272, D_275), E_274), '#skF_10') | ~r1_tarski(B_273, '#skF_9') | ~r2_hidden(k4_tarski(D_275, E_274), k5_relat_1(A_272, B_273)) | ~v1_relat_1(k5_relat_1(A_272, B_273)) | ~v1_relat_1(B_273) | ~v1_relat_1(A_272))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_398])).
% 7.05/2.57  tff(c_26, plain, (![D_111, A_20, F_115, B_72, E_112]: (r2_hidden(k4_tarski(D_111, E_112), k5_relat_1(A_20, B_72)) | ~r2_hidden(k4_tarski(F_115, E_112), B_72) | ~r2_hidden(k4_tarski(D_111, F_115), A_20) | ~v1_relat_1(k5_relat_1(A_20, B_72)) | ~v1_relat_1(B_72) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.05/2.57  tff(c_412, plain, (![E_274, D_111, A_20, A_272, D_275, B_273]: (r2_hidden(k4_tarski(D_111, E_274), k5_relat_1(A_20, '#skF_10')) | ~r2_hidden(k4_tarski(D_111, '#skF_3'(k5_relat_1(A_272, B_273), B_273, E_274, A_272, D_275)), A_20) | ~v1_relat_1(k5_relat_1(A_20, '#skF_10')) | ~v1_relat_1('#skF_10') | ~v1_relat_1(A_20) | ~r1_tarski(B_273, '#skF_9') | ~r2_hidden(k4_tarski(D_275, E_274), k5_relat_1(A_272, B_273)) | ~v1_relat_1(k5_relat_1(A_272, B_273)) | ~v1_relat_1(B_273) | ~v1_relat_1(A_272))), inference(resolution, [status(thm)], [c_404, c_26])).
% 7.05/2.57  tff(c_585, plain, (![E_320, A_318, A_322, D_319, B_321, D_323]: (r2_hidden(k4_tarski(D_323, E_320), k5_relat_1(A_322, '#skF_10')) | ~r2_hidden(k4_tarski(D_323, '#skF_3'(k5_relat_1(A_318, B_321), B_321, E_320, A_318, D_319)), A_322) | ~v1_relat_1(k5_relat_1(A_322, '#skF_10')) | ~v1_relat_1(A_322) | ~r1_tarski(B_321, '#skF_9') | ~r2_hidden(k4_tarski(D_319, E_320), k5_relat_1(A_318, B_321)) | ~v1_relat_1(k5_relat_1(A_318, B_321)) | ~v1_relat_1(B_321) | ~v1_relat_1(A_318))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_412])).
% 7.05/2.57  tff(c_626, plain, (![D_324, E_325, A_326, B_327]: (r2_hidden(k4_tarski(D_324, E_325), k5_relat_1(A_326, '#skF_10')) | ~v1_relat_1(k5_relat_1(A_326, '#skF_10')) | ~r1_tarski(B_327, '#skF_9') | ~r2_hidden(k4_tarski(D_324, E_325), k5_relat_1(A_326, B_327)) | ~v1_relat_1(k5_relat_1(A_326, B_327)) | ~v1_relat_1(B_327) | ~v1_relat_1(A_326))), inference(resolution, [status(thm)], [c_30, c_585])).
% 7.05/2.57  tff(c_3569, plain, (![A_582, B_583, B_584]: (r2_hidden(k4_tarski('#skF_1'(k5_relat_1(A_582, B_583), B_584), '#skF_2'(k5_relat_1(A_582, B_583), B_584)), k5_relat_1(A_582, '#skF_10')) | ~v1_relat_1(k5_relat_1(A_582, '#skF_10')) | ~r1_tarski(B_583, '#skF_9') | ~v1_relat_1(B_583) | ~v1_relat_1(A_582) | r1_tarski(k5_relat_1(A_582, B_583), B_584) | ~v1_relat_1(k5_relat_1(A_582, B_583)))), inference(resolution, [status(thm)], [c_12, c_626])).
% 7.05/2.57  tff(c_10, plain, (![A_3, B_13]: (~r2_hidden(k4_tarski('#skF_1'(A_3, B_13), '#skF_2'(A_3, B_13)), B_13) | r1_tarski(A_3, B_13) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.05/2.57  tff(c_3624, plain, (![A_585, B_586]: (~v1_relat_1(k5_relat_1(A_585, '#skF_10')) | ~r1_tarski(B_586, '#skF_9') | ~v1_relat_1(B_586) | ~v1_relat_1(A_585) | r1_tarski(k5_relat_1(A_585, B_586), k5_relat_1(A_585, '#skF_10')) | ~v1_relat_1(k5_relat_1(A_585, B_586)))), inference(resolution, [status(thm)], [c_3569, c_10])).
% 7.05/2.57  tff(c_34, plain, (~r1_tarski(k5_relat_1('#skF_11', '#skF_9'), k5_relat_1('#skF_11', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.05/2.57  tff(c_3691, plain, (~v1_relat_1(k5_relat_1('#skF_11', '#skF_10')) | ~r1_tarski('#skF_9', '#skF_9') | ~v1_relat_1('#skF_9') | ~v1_relat_1('#skF_11') | ~v1_relat_1(k5_relat_1('#skF_11', '#skF_9'))), inference(resolution, [status(thm)], [c_3624, c_34])).
% 7.05/2.57  tff(c_3743, plain, (~v1_relat_1(k5_relat_1('#skF_11', '#skF_10')) | ~v1_relat_1(k5_relat_1('#skF_11', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_42, c_6, c_3691])).
% 7.05/2.57  tff(c_3826, plain, (~v1_relat_1(k5_relat_1('#skF_11', '#skF_9'))), inference(splitLeft, [status(thm)], [c_3743])).
% 7.05/2.57  tff(c_3829, plain, (~v1_relat_1('#skF_9') | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_32, c_3826])).
% 7.05/2.57  tff(c_3833, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_42, c_3829])).
% 7.05/2.57  tff(c_3834, plain, (~v1_relat_1(k5_relat_1('#skF_11', '#skF_10'))), inference(splitRight, [status(thm)], [c_3743])).
% 7.05/2.57  tff(c_3838, plain, (~v1_relat_1('#skF_10') | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_32, c_3834])).
% 7.05/2.57  tff(c_3842, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_40, c_3838])).
% 7.05/2.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.05/2.57  
% 7.05/2.57  Inference rules
% 7.05/2.57  ----------------------
% 7.05/2.57  #Ref     : 0
% 7.05/2.57  #Sup     : 855
% 7.05/2.57  #Fact    : 0
% 7.05/2.57  #Define  : 0
% 7.05/2.57  #Split   : 7
% 7.05/2.57  #Chain   : 0
% 7.05/2.57  #Close   : 0
% 7.05/2.57  
% 7.05/2.57  Ordering : KBO
% 7.05/2.57  
% 7.05/2.57  Simplification rules
% 7.05/2.57  ----------------------
% 7.05/2.57  #Subsume      : 179
% 7.05/2.57  #Demod        : 318
% 7.05/2.57  #Tautology    : 13
% 7.05/2.57  #SimpNegUnit  : 0
% 7.05/2.57  #BackRed      : 0
% 7.05/2.57  
% 7.05/2.57  #Partial instantiations: 0
% 7.05/2.57  #Strategies tried      : 1
% 7.05/2.57  
% 7.05/2.57  Timing (in seconds)
% 7.05/2.57  ----------------------
% 7.05/2.57  Preprocessing        : 0.30
% 7.05/2.57  Parsing              : 0.16
% 7.05/2.57  CNF conversion       : 0.03
% 7.05/2.57  Main loop            : 1.52
% 7.05/2.57  Inferencing          : 0.40
% 7.05/2.57  Reduction            : 0.30
% 7.05/2.57  Demodulation         : 0.19
% 7.05/2.57  BG Simplification    : 0.05
% 7.05/2.57  Subsumption          : 0.68
% 7.05/2.57  Abstraction          : 0.06
% 7.05/2.57  MUC search           : 0.00
% 7.05/2.57  Cooper               : 0.00
% 7.05/2.57  Total                : 1.85
% 7.05/2.57  Index Insertion      : 0.00
% 7.05/2.57  Index Deletion       : 0.00
% 7.05/2.57  Index Matching       : 0.00
% 7.05/2.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
