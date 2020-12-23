%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:07 EST 2020

% Result     : Theorem 8.18s
% Output     : CNFRefutation 8.18s
% Verified   : 
% Statistics : Number of formulae       :   49 (  67 expanded)
%              Number of leaves         :   20 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  118 ( 185 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k9_relat_1(C,A),k9_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_26,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_24,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_30,plain,(
    ! [A_18,B_19] :
      ( r2_hidden('#skF_1'(A_18,B_19),A_18)
      | r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_35,plain,(
    ! [A_18] : r1_tarski(A_18,A_18) ),
    inference(resolution,[status(thm)],[c_30,c_4])).

tff(c_18,plain,(
    ! [A_12,B_14] :
      ( r1_tarski(k1_relat_1(A_12),k1_relat_1(B_14))
      | ~ r1_tarski(A_12,B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_56,plain,(
    ! [A_34,B_35,C_36] :
      ( r2_hidden('#skF_2'(A_34,B_35,C_36),k1_relat_1(C_36))
      | ~ r2_hidden(A_34,k9_relat_1(C_36,B_35))
      | ~ v1_relat_1(C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_175,plain,(
    ! [A_68,B_69,C_70,B_71] :
      ( r2_hidden('#skF_2'(A_68,B_69,C_70),B_71)
      | ~ r1_tarski(k1_relat_1(C_70),B_71)
      | ~ r2_hidden(A_68,k9_relat_1(C_70,B_69))
      | ~ v1_relat_1(C_70) ) ),
    inference(resolution,[status(thm)],[c_56,c_2])).

tff(c_268,plain,(
    ! [B_110,A_111,B_108,B_109,C_107] :
      ( r2_hidden('#skF_2'(A_111,B_108,C_107),B_109)
      | ~ r1_tarski(B_110,B_109)
      | ~ r1_tarski(k1_relat_1(C_107),B_110)
      | ~ r2_hidden(A_111,k9_relat_1(C_107,B_108))
      | ~ v1_relat_1(C_107) ) ),
    inference(resolution,[status(thm)],[c_175,c_2])).

tff(c_3602,plain,(
    ! [A_460,B_456,B_458,C_459,A_457] :
      ( r2_hidden('#skF_2'(A_460,B_458,C_459),k1_relat_1(B_456))
      | ~ r1_tarski(k1_relat_1(C_459),k1_relat_1(A_457))
      | ~ r2_hidden(A_460,k9_relat_1(C_459,B_458))
      | ~ v1_relat_1(C_459)
      | ~ r1_tarski(A_457,B_456)
      | ~ v1_relat_1(B_456)
      | ~ v1_relat_1(A_457) ) ),
    inference(resolution,[status(thm)],[c_18,c_268])).

tff(c_3609,plain,(
    ! [A_460,B_458,C_459,B_456] :
      ( r2_hidden('#skF_2'(A_460,B_458,C_459),k1_relat_1(B_456))
      | ~ r2_hidden(A_460,k9_relat_1(C_459,B_458))
      | ~ r1_tarski(C_459,B_456)
      | ~ v1_relat_1(B_456)
      | ~ v1_relat_1(C_459) ) ),
    inference(resolution,[status(thm)],[c_35,c_3602])).

tff(c_76,plain,(
    ! [A_41,B_42,C_43] :
      ( r2_hidden(k4_tarski('#skF_2'(A_41,B_42,C_43),A_41),C_43)
      | ~ r2_hidden(A_41,k9_relat_1(C_43,B_42))
      | ~ v1_relat_1(C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_79,plain,(
    ! [A_41,B_42,C_43,B_2] :
      ( r2_hidden(k4_tarski('#skF_2'(A_41,B_42,C_43),A_41),B_2)
      | ~ r1_tarski(C_43,B_2)
      | ~ r2_hidden(A_41,k9_relat_1(C_43,B_42))
      | ~ v1_relat_1(C_43) ) ),
    inference(resolution,[status(thm)],[c_76,c_2])).

tff(c_52,plain,(
    ! [A_31,B_32,C_33] :
      ( r2_hidden('#skF_2'(A_31,B_32,C_33),B_32)
      | ~ r2_hidden(A_31,k9_relat_1(C_33,B_32))
      | ~ v1_relat_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_55,plain,(
    ! [A_31,B_32,C_33,B_2] :
      ( r2_hidden('#skF_2'(A_31,B_32,C_33),B_2)
      | ~ r1_tarski(B_32,B_2)
      | ~ r2_hidden(A_31,k9_relat_1(C_33,B_32))
      | ~ v1_relat_1(C_33) ) ),
    inference(resolution,[status(thm)],[c_52,c_2])).

tff(c_144,plain,(
    ! [A_64,C_65,B_66,D_67] :
      ( r2_hidden(A_64,k9_relat_1(C_65,B_66))
      | ~ r2_hidden(D_67,B_66)
      | ~ r2_hidden(k4_tarski(D_67,A_64),C_65)
      | ~ r2_hidden(D_67,k1_relat_1(C_65))
      | ~ v1_relat_1(C_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1247,plain,(
    ! [A_274,A_271,C_270,B_269,C_272,B_273] :
      ( r2_hidden(A_274,k9_relat_1(C_270,B_273))
      | ~ r2_hidden(k4_tarski('#skF_2'(A_271,B_269,C_272),A_274),C_270)
      | ~ r2_hidden('#skF_2'(A_271,B_269,C_272),k1_relat_1(C_270))
      | ~ v1_relat_1(C_270)
      | ~ r1_tarski(B_269,B_273)
      | ~ r2_hidden(A_271,k9_relat_1(C_272,B_269))
      | ~ v1_relat_1(C_272) ) ),
    inference(resolution,[status(thm)],[c_55,c_144])).

tff(c_4721,plain,(
    ! [B_526,A_522,B_525,B_524,C_523] :
      ( r2_hidden(A_522,k9_relat_1(B_525,B_524))
      | ~ r2_hidden('#skF_2'(A_522,B_526,C_523),k1_relat_1(B_525))
      | ~ v1_relat_1(B_525)
      | ~ r1_tarski(B_526,B_524)
      | ~ r1_tarski(C_523,B_525)
      | ~ r2_hidden(A_522,k9_relat_1(C_523,B_526))
      | ~ v1_relat_1(C_523) ) ),
    inference(resolution,[status(thm)],[c_79,c_1247])).

tff(c_5122,plain,(
    ! [B_543,C_546,A_544,B_547,B_545] :
      ( r2_hidden(A_544,k9_relat_1(B_543,B_547))
      | ~ r1_tarski(B_545,B_547)
      | ~ r2_hidden(A_544,k9_relat_1(C_546,B_545))
      | ~ r1_tarski(C_546,B_543)
      | ~ v1_relat_1(B_543)
      | ~ v1_relat_1(C_546) ) ),
    inference(resolution,[status(thm)],[c_3609,c_4721])).

tff(c_5351,plain,(
    ! [A_556,B_557,C_558] :
      ( r2_hidden(A_556,k9_relat_1(B_557,'#skF_4'))
      | ~ r2_hidden(A_556,k9_relat_1(C_558,'#skF_3'))
      | ~ r1_tarski(C_558,B_557)
      | ~ v1_relat_1(B_557)
      | ~ v1_relat_1(C_558) ) ),
    inference(resolution,[status(thm)],[c_22,c_5122])).

tff(c_5823,plain,(
    ! [C_578,B_579,B_580] :
      ( r2_hidden('#skF_1'(k9_relat_1(C_578,'#skF_3'),B_579),k9_relat_1(B_580,'#skF_4'))
      | ~ r1_tarski(C_578,B_580)
      | ~ v1_relat_1(B_580)
      | ~ v1_relat_1(C_578)
      | r1_tarski(k9_relat_1(C_578,'#skF_3'),B_579) ) ),
    inference(resolution,[status(thm)],[c_6,c_5351])).

tff(c_5854,plain,(
    ! [C_581,B_582] :
      ( ~ r1_tarski(C_581,B_582)
      | ~ v1_relat_1(B_582)
      | ~ v1_relat_1(C_581)
      | r1_tarski(k9_relat_1(C_581,'#skF_3'),k9_relat_1(B_582,'#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_5823,c_4])).

tff(c_20,plain,(
    ~ r1_tarski(k9_relat_1('#skF_5','#skF_3'),k9_relat_1('#skF_6','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_5890,plain,
    ( ~ r1_tarski('#skF_5','#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_5854,c_20])).

tff(c_5918,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_5890])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:45:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.18/2.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.18/2.85  
% 8.18/2.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.18/2.85  %$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 8.18/2.85  
% 8.18/2.85  %Foreground sorts:
% 8.18/2.85  
% 8.18/2.85  
% 8.18/2.85  %Background operators:
% 8.18/2.85  
% 8.18/2.85  
% 8.18/2.85  %Foreground operators:
% 8.18/2.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.18/2.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.18/2.85  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.18/2.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.18/2.85  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.18/2.85  tff('#skF_5', type, '#skF_5': $i).
% 8.18/2.85  tff('#skF_6', type, '#skF_6': $i).
% 8.18/2.85  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.18/2.85  tff('#skF_3', type, '#skF_3': $i).
% 8.18/2.85  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.18/2.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.18/2.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.18/2.85  tff('#skF_4', type, '#skF_4': $i).
% 8.18/2.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.18/2.85  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.18/2.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.18/2.85  
% 8.18/2.86  tff(f_66, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k9_relat_1(C, A), k9_relat_1(D, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_relat_1)).
% 8.18/2.86  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.18/2.86  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 8.18/2.86  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 8.18/2.86  tff(c_28, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.18/2.86  tff(c_26, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.18/2.86  tff(c_24, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.18/2.86  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.18/2.86  tff(c_22, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.18/2.86  tff(c_30, plain, (![A_18, B_19]: (r2_hidden('#skF_1'(A_18, B_19), A_18) | r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.18/2.86  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.18/2.86  tff(c_35, plain, (![A_18]: (r1_tarski(A_18, A_18))), inference(resolution, [status(thm)], [c_30, c_4])).
% 8.18/2.86  tff(c_18, plain, (![A_12, B_14]: (r1_tarski(k1_relat_1(A_12), k1_relat_1(B_14)) | ~r1_tarski(A_12, B_14) | ~v1_relat_1(B_14) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.18/2.86  tff(c_56, plain, (![A_34, B_35, C_36]: (r2_hidden('#skF_2'(A_34, B_35, C_36), k1_relat_1(C_36)) | ~r2_hidden(A_34, k9_relat_1(C_36, B_35)) | ~v1_relat_1(C_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.18/2.86  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.18/2.86  tff(c_175, plain, (![A_68, B_69, C_70, B_71]: (r2_hidden('#skF_2'(A_68, B_69, C_70), B_71) | ~r1_tarski(k1_relat_1(C_70), B_71) | ~r2_hidden(A_68, k9_relat_1(C_70, B_69)) | ~v1_relat_1(C_70))), inference(resolution, [status(thm)], [c_56, c_2])).
% 8.18/2.86  tff(c_268, plain, (![B_110, A_111, B_108, B_109, C_107]: (r2_hidden('#skF_2'(A_111, B_108, C_107), B_109) | ~r1_tarski(B_110, B_109) | ~r1_tarski(k1_relat_1(C_107), B_110) | ~r2_hidden(A_111, k9_relat_1(C_107, B_108)) | ~v1_relat_1(C_107))), inference(resolution, [status(thm)], [c_175, c_2])).
% 8.18/2.86  tff(c_3602, plain, (![A_460, B_456, B_458, C_459, A_457]: (r2_hidden('#skF_2'(A_460, B_458, C_459), k1_relat_1(B_456)) | ~r1_tarski(k1_relat_1(C_459), k1_relat_1(A_457)) | ~r2_hidden(A_460, k9_relat_1(C_459, B_458)) | ~v1_relat_1(C_459) | ~r1_tarski(A_457, B_456) | ~v1_relat_1(B_456) | ~v1_relat_1(A_457))), inference(resolution, [status(thm)], [c_18, c_268])).
% 8.18/2.86  tff(c_3609, plain, (![A_460, B_458, C_459, B_456]: (r2_hidden('#skF_2'(A_460, B_458, C_459), k1_relat_1(B_456)) | ~r2_hidden(A_460, k9_relat_1(C_459, B_458)) | ~r1_tarski(C_459, B_456) | ~v1_relat_1(B_456) | ~v1_relat_1(C_459))), inference(resolution, [status(thm)], [c_35, c_3602])).
% 8.18/2.86  tff(c_76, plain, (![A_41, B_42, C_43]: (r2_hidden(k4_tarski('#skF_2'(A_41, B_42, C_43), A_41), C_43) | ~r2_hidden(A_41, k9_relat_1(C_43, B_42)) | ~v1_relat_1(C_43))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.18/2.86  tff(c_79, plain, (![A_41, B_42, C_43, B_2]: (r2_hidden(k4_tarski('#skF_2'(A_41, B_42, C_43), A_41), B_2) | ~r1_tarski(C_43, B_2) | ~r2_hidden(A_41, k9_relat_1(C_43, B_42)) | ~v1_relat_1(C_43))), inference(resolution, [status(thm)], [c_76, c_2])).
% 8.18/2.86  tff(c_52, plain, (![A_31, B_32, C_33]: (r2_hidden('#skF_2'(A_31, B_32, C_33), B_32) | ~r2_hidden(A_31, k9_relat_1(C_33, B_32)) | ~v1_relat_1(C_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.18/2.86  tff(c_55, plain, (![A_31, B_32, C_33, B_2]: (r2_hidden('#skF_2'(A_31, B_32, C_33), B_2) | ~r1_tarski(B_32, B_2) | ~r2_hidden(A_31, k9_relat_1(C_33, B_32)) | ~v1_relat_1(C_33))), inference(resolution, [status(thm)], [c_52, c_2])).
% 8.18/2.86  tff(c_144, plain, (![A_64, C_65, B_66, D_67]: (r2_hidden(A_64, k9_relat_1(C_65, B_66)) | ~r2_hidden(D_67, B_66) | ~r2_hidden(k4_tarski(D_67, A_64), C_65) | ~r2_hidden(D_67, k1_relat_1(C_65)) | ~v1_relat_1(C_65))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.18/2.86  tff(c_1247, plain, (![A_274, A_271, C_270, B_269, C_272, B_273]: (r2_hidden(A_274, k9_relat_1(C_270, B_273)) | ~r2_hidden(k4_tarski('#skF_2'(A_271, B_269, C_272), A_274), C_270) | ~r2_hidden('#skF_2'(A_271, B_269, C_272), k1_relat_1(C_270)) | ~v1_relat_1(C_270) | ~r1_tarski(B_269, B_273) | ~r2_hidden(A_271, k9_relat_1(C_272, B_269)) | ~v1_relat_1(C_272))), inference(resolution, [status(thm)], [c_55, c_144])).
% 8.18/2.86  tff(c_4721, plain, (![B_526, A_522, B_525, B_524, C_523]: (r2_hidden(A_522, k9_relat_1(B_525, B_524)) | ~r2_hidden('#skF_2'(A_522, B_526, C_523), k1_relat_1(B_525)) | ~v1_relat_1(B_525) | ~r1_tarski(B_526, B_524) | ~r1_tarski(C_523, B_525) | ~r2_hidden(A_522, k9_relat_1(C_523, B_526)) | ~v1_relat_1(C_523))), inference(resolution, [status(thm)], [c_79, c_1247])).
% 8.18/2.86  tff(c_5122, plain, (![B_543, C_546, A_544, B_547, B_545]: (r2_hidden(A_544, k9_relat_1(B_543, B_547)) | ~r1_tarski(B_545, B_547) | ~r2_hidden(A_544, k9_relat_1(C_546, B_545)) | ~r1_tarski(C_546, B_543) | ~v1_relat_1(B_543) | ~v1_relat_1(C_546))), inference(resolution, [status(thm)], [c_3609, c_4721])).
% 8.18/2.86  tff(c_5351, plain, (![A_556, B_557, C_558]: (r2_hidden(A_556, k9_relat_1(B_557, '#skF_4')) | ~r2_hidden(A_556, k9_relat_1(C_558, '#skF_3')) | ~r1_tarski(C_558, B_557) | ~v1_relat_1(B_557) | ~v1_relat_1(C_558))), inference(resolution, [status(thm)], [c_22, c_5122])).
% 8.18/2.86  tff(c_5823, plain, (![C_578, B_579, B_580]: (r2_hidden('#skF_1'(k9_relat_1(C_578, '#skF_3'), B_579), k9_relat_1(B_580, '#skF_4')) | ~r1_tarski(C_578, B_580) | ~v1_relat_1(B_580) | ~v1_relat_1(C_578) | r1_tarski(k9_relat_1(C_578, '#skF_3'), B_579))), inference(resolution, [status(thm)], [c_6, c_5351])).
% 8.18/2.86  tff(c_5854, plain, (![C_581, B_582]: (~r1_tarski(C_581, B_582) | ~v1_relat_1(B_582) | ~v1_relat_1(C_581) | r1_tarski(k9_relat_1(C_581, '#skF_3'), k9_relat_1(B_582, '#skF_4')))), inference(resolution, [status(thm)], [c_5823, c_4])).
% 8.18/2.86  tff(c_20, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_3'), k9_relat_1('#skF_6', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.18/2.86  tff(c_5890, plain, (~r1_tarski('#skF_5', '#skF_6') | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_5854, c_20])).
% 8.18/2.86  tff(c_5918, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_5890])).
% 8.18/2.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.18/2.86  
% 8.18/2.86  Inference rules
% 8.18/2.86  ----------------------
% 8.18/2.86  #Ref     : 0
% 8.18/2.86  #Sup     : 1382
% 8.18/2.86  #Fact    : 0
% 8.18/2.86  #Define  : 0
% 8.18/2.86  #Split   : 12
% 8.18/2.86  #Chain   : 0
% 8.18/2.86  #Close   : 0
% 8.18/2.86  
% 8.18/2.86  Ordering : KBO
% 8.18/2.86  
% 8.18/2.86  Simplification rules
% 8.18/2.86  ----------------------
% 8.18/2.86  #Subsume      : 278
% 8.18/2.86  #Demod        : 289
% 8.18/2.86  #Tautology    : 17
% 8.18/2.86  #SimpNegUnit  : 1
% 8.18/2.86  #BackRed      : 0
% 8.18/2.86  
% 8.18/2.86  #Partial instantiations: 0
% 8.18/2.86  #Strategies tried      : 1
% 8.18/2.86  
% 8.18/2.86  Timing (in seconds)
% 8.18/2.86  ----------------------
% 8.18/2.87  Preprocessing        : 0.28
% 8.18/2.87  Parsing              : 0.16
% 8.18/2.87  CNF conversion       : 0.02
% 8.18/2.87  Main loop            : 1.78
% 8.18/2.87  Inferencing          : 0.49
% 8.18/2.87  Reduction            : 0.38
% 8.18/2.87  Demodulation         : 0.23
% 8.18/2.87  BG Simplification    : 0.05
% 8.18/2.87  Subsumption          : 0.74
% 8.18/2.87  Abstraction          : 0.06
% 8.18/2.87  MUC search           : 0.00
% 8.18/2.87  Cooper               : 0.00
% 8.18/2.87  Total                : 2.09
% 8.18/2.87  Index Insertion      : 0.00
% 8.18/2.87  Index Deletion       : 0.00
% 8.18/2.87  Index Matching       : 0.00
% 8.18/2.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
