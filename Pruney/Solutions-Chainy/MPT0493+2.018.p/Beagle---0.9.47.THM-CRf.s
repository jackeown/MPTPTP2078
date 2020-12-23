%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:38 EST 2020

% Result     : Theorem 5.51s
% Output     : CNFRefutation 5.51s
% Verified   : 
% Statistics : Number of formulae       :   55 (  98 expanded)
%              Number of leaves         :   17 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :  124 ( 245 expanded)
%              Number of equality atoms :   18 (  30 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( ~ r2_hidden('#skF_1'(A_14,B_15),B_15)
      | r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_33,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_28])).

tff(c_26,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_24,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_34,plain,(
    ! [C_16,B_17,A_18] :
      ( r2_hidden(C_16,B_17)
      | ~ r2_hidden(C_16,A_18)
      | ~ r1_tarski(A_18,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_45,plain,(
    ! [A_23,B_24,B_25] :
      ( r2_hidden('#skF_1'(A_23,B_24),B_25)
      | ~ r1_tarski(A_23,B_25)
      | r1_tarski(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_6,c_34])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_126,plain,(
    ! [A_37,B_38,B_39,B_40] :
      ( r2_hidden('#skF_1'(A_37,B_38),B_39)
      | ~ r1_tarski(B_40,B_39)
      | ~ r1_tarski(A_37,B_40)
      | r1_tarski(A_37,B_38) ) ),
    inference(resolution,[status(thm)],[c_45,c_2])).

tff(c_132,plain,(
    ! [A_37,B_38] :
      ( r2_hidden('#skF_1'(A_37,B_38),k1_relat_1('#skF_5'))
      | ~ r1_tarski(A_37,'#skF_4')
      | r1_tarski(A_37,B_38) ) ),
    inference(resolution,[status(thm)],[c_24,c_126])).

tff(c_133,plain,(
    ! [A_41,C_42,B_43] :
      ( r2_hidden(A_41,k1_relat_1(k7_relat_1(C_42,B_43)))
      | ~ r2_hidden(A_41,k1_relat_1(C_42))
      | ~ r2_hidden(A_41,B_43)
      | ~ v1_relat_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2155,plain,(
    ! [A_240,C_241,B_242] :
      ( r1_tarski(A_240,k1_relat_1(k7_relat_1(C_241,B_242)))
      | ~ r2_hidden('#skF_1'(A_240,k1_relat_1(k7_relat_1(C_241,B_242))),k1_relat_1(C_241))
      | ~ r2_hidden('#skF_1'(A_240,k1_relat_1(k7_relat_1(C_241,B_242))),B_242)
      | ~ v1_relat_1(C_241) ) ),
    inference(resolution,[status(thm)],[c_133,c_4])).

tff(c_2173,plain,(
    ! [A_37,B_242] :
      ( ~ r2_hidden('#skF_1'(A_37,k1_relat_1(k7_relat_1('#skF_5',B_242))),B_242)
      | ~ v1_relat_1('#skF_5')
      | ~ r1_tarski(A_37,'#skF_4')
      | r1_tarski(A_37,k1_relat_1(k7_relat_1('#skF_5',B_242))) ) ),
    inference(resolution,[status(thm)],[c_132,c_2155])).

tff(c_2194,plain,(
    ! [A_243,B_244] :
      ( ~ r2_hidden('#skF_1'(A_243,k1_relat_1(k7_relat_1('#skF_5',B_244))),B_244)
      | ~ r1_tarski(A_243,'#skF_4')
      | r1_tarski(A_243,k1_relat_1(k7_relat_1('#skF_5',B_244))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2173])).

tff(c_2240,plain,(
    ! [A_245] :
      ( ~ r1_tarski(A_245,'#skF_4')
      | r1_tarski(A_245,k1_relat_1(k7_relat_1('#skF_5',A_245))) ) ),
    inference(resolution,[status(thm)],[c_6,c_2194])).

tff(c_39,plain,(
    ! [A_20,B_21,C_22] :
      ( r2_hidden(A_20,B_21)
      | ~ r2_hidden(A_20,k1_relat_1(k7_relat_1(C_22,B_21)))
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_388,plain,(
    ! [C_75,B_76,B_77] :
      ( r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(C_75,B_76)),B_77),B_76)
      | ~ v1_relat_1(C_75)
      | r1_tarski(k1_relat_1(k7_relat_1(C_75,B_76)),B_77) ) ),
    inference(resolution,[status(thm)],[c_6,c_39])).

tff(c_1053,plain,(
    ! [C_159,B_160,B_161,B_162] :
      ( r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(C_159,B_160)),B_161),B_162)
      | ~ r1_tarski(B_160,B_162)
      | ~ v1_relat_1(C_159)
      | r1_tarski(k1_relat_1(k7_relat_1(C_159,B_160)),B_161) ) ),
    inference(resolution,[status(thm)],[c_388,c_2])).

tff(c_1072,plain,(
    ! [B_163,B_164,C_165] :
      ( ~ r1_tarski(B_163,B_164)
      | ~ v1_relat_1(C_165)
      | r1_tarski(k1_relat_1(k7_relat_1(C_165,B_163)),B_164) ) ),
    inference(resolution,[status(thm)],[c_1053,c_4])).

tff(c_70,plain,(
    ! [A_29,B_30] :
      ( r2_hidden('#skF_2'(A_29,B_30),B_30)
      | r2_hidden('#skF_3'(A_29,B_30),A_29)
      | B_30 = A_29 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_234,plain,(
    ! [A_55,B_56,B_57] :
      ( r2_hidden('#skF_3'(A_55,B_56),B_57)
      | ~ r1_tarski(A_55,B_57)
      | r2_hidden('#skF_2'(A_55,B_56),B_56)
      | B_56 = A_55 ) ),
    inference(resolution,[status(thm)],[c_70,c_2])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | ~ r2_hidden('#skF_3'(A_6,B_7),B_7)
      | B_7 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_270,plain,(
    ! [A_58,B_59] :
      ( ~ r1_tarski(A_58,B_59)
      | r2_hidden('#skF_2'(A_58,B_59),B_59)
      | B_59 = A_58 ) ),
    inference(resolution,[status(thm)],[c_234,c_10])).

tff(c_290,plain,(
    ! [A_58,B_59,B_2] :
      ( r2_hidden('#skF_2'(A_58,B_59),B_2)
      | ~ r1_tarski(B_59,B_2)
      | ~ r1_tarski(A_58,B_59)
      | B_59 = A_58 ) ),
    inference(resolution,[status(thm)],[c_270,c_2])).

tff(c_97,plain,(
    ! [A_31,B_32] :
      ( ~ r2_hidden('#skF_2'(A_31,B_32),A_31)
      | r2_hidden('#skF_3'(A_31,B_32),A_31)
      | B_32 = A_31 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_344,plain,(
    ! [A_65,B_66,B_67] :
      ( r2_hidden('#skF_3'(A_65,B_66),B_67)
      | ~ r1_tarski(A_65,B_67)
      | ~ r2_hidden('#skF_2'(A_65,B_66),A_65)
      | B_66 = A_65 ) ),
    inference(resolution,[status(thm)],[c_97,c_2])).

tff(c_487,plain,(
    ! [B_95,B_96,B_97] :
      ( r2_hidden('#skF_3'(B_95,B_96),B_97)
      | ~ r1_tarski(B_95,B_97)
      | ~ r1_tarski(B_96,B_95)
      | ~ r1_tarski(B_95,B_96)
      | B_96 = B_95 ) ),
    inference(resolution,[status(thm)],[c_290,c_344])).

tff(c_291,plain,(
    ! [A_60,B_61,B_62] :
      ( r2_hidden('#skF_2'(A_60,B_61),B_62)
      | ~ r1_tarski(B_61,B_62)
      | ~ r1_tarski(A_60,B_61)
      | B_61 = A_60 ) ),
    inference(resolution,[status(thm)],[c_270,c_2])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7),A_6)
      | ~ r2_hidden('#skF_3'(A_6,B_7),B_7)
      | B_7 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_305,plain,(
    ! [B_62,B_61] :
      ( ~ r2_hidden('#skF_3'(B_62,B_61),B_61)
      | ~ r1_tarski(B_61,B_62)
      | ~ r1_tarski(B_62,B_61)
      | B_62 = B_61 ) ),
    inference(resolution,[status(thm)],[c_291,c_8])).

tff(c_506,plain,(
    ! [B_97,B_95] :
      ( ~ r1_tarski(B_97,B_95)
      | ~ r1_tarski(B_95,B_97)
      | B_97 = B_95 ) ),
    inference(resolution,[status(thm)],[c_487,c_305])).

tff(c_1116,plain,(
    ! [B_164,C_165,B_163] :
      ( ~ r1_tarski(B_164,k1_relat_1(k7_relat_1(C_165,B_163)))
      | k1_relat_1(k7_relat_1(C_165,B_163)) = B_164
      | ~ r1_tarski(B_163,B_164)
      | ~ v1_relat_1(C_165) ) ),
    inference(resolution,[status(thm)],[c_1072,c_506])).

tff(c_2260,plain,(
    ! [A_245] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_245)) = A_245
      | ~ r1_tarski(A_245,A_245)
      | ~ v1_relat_1('#skF_5')
      | ~ r1_tarski(A_245,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2240,c_1116])).

tff(c_2347,plain,(
    ! [A_246] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_246)) = A_246
      | ~ r1_tarski(A_246,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_33,c_2260])).

tff(c_22,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_4')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2486,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2347,c_22])).

tff(c_2569,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_2486])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:13:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.51/1.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.51/1.98  
% 5.51/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.51/1.99  %$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 5.51/1.99  
% 5.51/1.99  %Foreground sorts:
% 5.51/1.99  
% 5.51/1.99  
% 5.51/1.99  %Background operators:
% 5.51/1.99  
% 5.51/1.99  
% 5.51/1.99  %Foreground operators:
% 5.51/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.51/1.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.51/1.99  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.51/1.99  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.51/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.51/1.99  tff('#skF_5', type, '#skF_5': $i).
% 5.51/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.51/1.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.51/1.99  tff('#skF_4', type, '#skF_4': $i).
% 5.51/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.51/1.99  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.51/1.99  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.51/1.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.51/1.99  
% 5.51/2.00  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.51/2.00  tff(f_54, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 5.51/2.00  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 5.51/2.00  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 5.51/2.00  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.51/2.00  tff(c_28, plain, (![A_14, B_15]: (~r2_hidden('#skF_1'(A_14, B_15), B_15) | r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.51/2.00  tff(c_33, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_28])).
% 5.51/2.00  tff(c_26, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.51/2.00  tff(c_24, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.51/2.00  tff(c_34, plain, (![C_16, B_17, A_18]: (r2_hidden(C_16, B_17) | ~r2_hidden(C_16, A_18) | ~r1_tarski(A_18, B_17))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.51/2.00  tff(c_45, plain, (![A_23, B_24, B_25]: (r2_hidden('#skF_1'(A_23, B_24), B_25) | ~r1_tarski(A_23, B_25) | r1_tarski(A_23, B_24))), inference(resolution, [status(thm)], [c_6, c_34])).
% 5.51/2.00  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.51/2.00  tff(c_126, plain, (![A_37, B_38, B_39, B_40]: (r2_hidden('#skF_1'(A_37, B_38), B_39) | ~r1_tarski(B_40, B_39) | ~r1_tarski(A_37, B_40) | r1_tarski(A_37, B_38))), inference(resolution, [status(thm)], [c_45, c_2])).
% 5.51/2.00  tff(c_132, plain, (![A_37, B_38]: (r2_hidden('#skF_1'(A_37, B_38), k1_relat_1('#skF_5')) | ~r1_tarski(A_37, '#skF_4') | r1_tarski(A_37, B_38))), inference(resolution, [status(thm)], [c_24, c_126])).
% 5.51/2.00  tff(c_133, plain, (![A_41, C_42, B_43]: (r2_hidden(A_41, k1_relat_1(k7_relat_1(C_42, B_43))) | ~r2_hidden(A_41, k1_relat_1(C_42)) | ~r2_hidden(A_41, B_43) | ~v1_relat_1(C_42))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.51/2.00  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.51/2.00  tff(c_2155, plain, (![A_240, C_241, B_242]: (r1_tarski(A_240, k1_relat_1(k7_relat_1(C_241, B_242))) | ~r2_hidden('#skF_1'(A_240, k1_relat_1(k7_relat_1(C_241, B_242))), k1_relat_1(C_241)) | ~r2_hidden('#skF_1'(A_240, k1_relat_1(k7_relat_1(C_241, B_242))), B_242) | ~v1_relat_1(C_241))), inference(resolution, [status(thm)], [c_133, c_4])).
% 5.51/2.00  tff(c_2173, plain, (![A_37, B_242]: (~r2_hidden('#skF_1'(A_37, k1_relat_1(k7_relat_1('#skF_5', B_242))), B_242) | ~v1_relat_1('#skF_5') | ~r1_tarski(A_37, '#skF_4') | r1_tarski(A_37, k1_relat_1(k7_relat_1('#skF_5', B_242))))), inference(resolution, [status(thm)], [c_132, c_2155])).
% 5.51/2.00  tff(c_2194, plain, (![A_243, B_244]: (~r2_hidden('#skF_1'(A_243, k1_relat_1(k7_relat_1('#skF_5', B_244))), B_244) | ~r1_tarski(A_243, '#skF_4') | r1_tarski(A_243, k1_relat_1(k7_relat_1('#skF_5', B_244))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2173])).
% 5.51/2.00  tff(c_2240, plain, (![A_245]: (~r1_tarski(A_245, '#skF_4') | r1_tarski(A_245, k1_relat_1(k7_relat_1('#skF_5', A_245))))), inference(resolution, [status(thm)], [c_6, c_2194])).
% 5.51/2.00  tff(c_39, plain, (![A_20, B_21, C_22]: (r2_hidden(A_20, B_21) | ~r2_hidden(A_20, k1_relat_1(k7_relat_1(C_22, B_21))) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.51/2.00  tff(c_388, plain, (![C_75, B_76, B_77]: (r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(C_75, B_76)), B_77), B_76) | ~v1_relat_1(C_75) | r1_tarski(k1_relat_1(k7_relat_1(C_75, B_76)), B_77))), inference(resolution, [status(thm)], [c_6, c_39])).
% 5.51/2.00  tff(c_1053, plain, (![C_159, B_160, B_161, B_162]: (r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(C_159, B_160)), B_161), B_162) | ~r1_tarski(B_160, B_162) | ~v1_relat_1(C_159) | r1_tarski(k1_relat_1(k7_relat_1(C_159, B_160)), B_161))), inference(resolution, [status(thm)], [c_388, c_2])).
% 5.51/2.00  tff(c_1072, plain, (![B_163, B_164, C_165]: (~r1_tarski(B_163, B_164) | ~v1_relat_1(C_165) | r1_tarski(k1_relat_1(k7_relat_1(C_165, B_163)), B_164))), inference(resolution, [status(thm)], [c_1053, c_4])).
% 5.51/2.00  tff(c_70, plain, (![A_29, B_30]: (r2_hidden('#skF_2'(A_29, B_30), B_30) | r2_hidden('#skF_3'(A_29, B_30), A_29) | B_30=A_29)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.51/2.00  tff(c_234, plain, (![A_55, B_56, B_57]: (r2_hidden('#skF_3'(A_55, B_56), B_57) | ~r1_tarski(A_55, B_57) | r2_hidden('#skF_2'(A_55, B_56), B_56) | B_56=A_55)), inference(resolution, [status(thm)], [c_70, c_2])).
% 5.51/2.00  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | ~r2_hidden('#skF_3'(A_6, B_7), B_7) | B_7=A_6)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.51/2.00  tff(c_270, plain, (![A_58, B_59]: (~r1_tarski(A_58, B_59) | r2_hidden('#skF_2'(A_58, B_59), B_59) | B_59=A_58)), inference(resolution, [status(thm)], [c_234, c_10])).
% 5.51/2.00  tff(c_290, plain, (![A_58, B_59, B_2]: (r2_hidden('#skF_2'(A_58, B_59), B_2) | ~r1_tarski(B_59, B_2) | ~r1_tarski(A_58, B_59) | B_59=A_58)), inference(resolution, [status(thm)], [c_270, c_2])).
% 5.51/2.00  tff(c_97, plain, (![A_31, B_32]: (~r2_hidden('#skF_2'(A_31, B_32), A_31) | r2_hidden('#skF_3'(A_31, B_32), A_31) | B_32=A_31)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.51/2.00  tff(c_344, plain, (![A_65, B_66, B_67]: (r2_hidden('#skF_3'(A_65, B_66), B_67) | ~r1_tarski(A_65, B_67) | ~r2_hidden('#skF_2'(A_65, B_66), A_65) | B_66=A_65)), inference(resolution, [status(thm)], [c_97, c_2])).
% 5.51/2.00  tff(c_487, plain, (![B_95, B_96, B_97]: (r2_hidden('#skF_3'(B_95, B_96), B_97) | ~r1_tarski(B_95, B_97) | ~r1_tarski(B_96, B_95) | ~r1_tarski(B_95, B_96) | B_96=B_95)), inference(resolution, [status(thm)], [c_290, c_344])).
% 5.51/2.00  tff(c_291, plain, (![A_60, B_61, B_62]: (r2_hidden('#skF_2'(A_60, B_61), B_62) | ~r1_tarski(B_61, B_62) | ~r1_tarski(A_60, B_61) | B_61=A_60)), inference(resolution, [status(thm)], [c_270, c_2])).
% 5.51/2.00  tff(c_8, plain, (![A_6, B_7]: (~r2_hidden('#skF_2'(A_6, B_7), A_6) | ~r2_hidden('#skF_3'(A_6, B_7), B_7) | B_7=A_6)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.51/2.00  tff(c_305, plain, (![B_62, B_61]: (~r2_hidden('#skF_3'(B_62, B_61), B_61) | ~r1_tarski(B_61, B_62) | ~r1_tarski(B_62, B_61) | B_62=B_61)), inference(resolution, [status(thm)], [c_291, c_8])).
% 5.51/2.00  tff(c_506, plain, (![B_97, B_95]: (~r1_tarski(B_97, B_95) | ~r1_tarski(B_95, B_97) | B_97=B_95)), inference(resolution, [status(thm)], [c_487, c_305])).
% 5.51/2.00  tff(c_1116, plain, (![B_164, C_165, B_163]: (~r1_tarski(B_164, k1_relat_1(k7_relat_1(C_165, B_163))) | k1_relat_1(k7_relat_1(C_165, B_163))=B_164 | ~r1_tarski(B_163, B_164) | ~v1_relat_1(C_165))), inference(resolution, [status(thm)], [c_1072, c_506])).
% 5.51/2.00  tff(c_2260, plain, (![A_245]: (k1_relat_1(k7_relat_1('#skF_5', A_245))=A_245 | ~r1_tarski(A_245, A_245) | ~v1_relat_1('#skF_5') | ~r1_tarski(A_245, '#skF_4'))), inference(resolution, [status(thm)], [c_2240, c_1116])).
% 5.51/2.00  tff(c_2347, plain, (![A_246]: (k1_relat_1(k7_relat_1('#skF_5', A_246))=A_246 | ~r1_tarski(A_246, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_33, c_2260])).
% 5.51/2.00  tff(c_22, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.51/2.00  tff(c_2486, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2347, c_22])).
% 5.51/2.00  tff(c_2569, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33, c_2486])).
% 5.51/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.51/2.00  
% 5.51/2.00  Inference rules
% 5.51/2.00  ----------------------
% 5.51/2.00  #Ref     : 0
% 5.51/2.00  #Sup     : 561
% 5.51/2.00  #Fact    : 0
% 5.51/2.00  #Define  : 0
% 5.51/2.00  #Split   : 1
% 5.51/2.00  #Chain   : 0
% 5.51/2.00  #Close   : 0
% 5.51/2.00  
% 5.51/2.00  Ordering : KBO
% 5.51/2.00  
% 5.51/2.00  Simplification rules
% 5.51/2.00  ----------------------
% 5.51/2.00  #Subsume      : 142
% 5.51/2.00  #Demod        : 101
% 5.51/2.00  #Tautology    : 56
% 5.51/2.00  #SimpNegUnit  : 0
% 5.51/2.00  #BackRed      : 0
% 5.51/2.00  
% 5.51/2.00  #Partial instantiations: 0
% 5.51/2.00  #Strategies tried      : 1
% 5.51/2.00  
% 5.51/2.00  Timing (in seconds)
% 5.51/2.00  ----------------------
% 5.51/2.00  Preprocessing        : 0.27
% 5.51/2.00  Parsing              : 0.15
% 5.51/2.00  CNF conversion       : 0.02
% 5.51/2.00  Main loop            : 1.03
% 5.51/2.00  Inferencing          : 0.32
% 5.51/2.00  Reduction            : 0.20
% 5.51/2.00  Demodulation         : 0.13
% 5.51/2.00  BG Simplification    : 0.03
% 5.51/2.00  Subsumption          : 0.41
% 5.51/2.00  Abstraction          : 0.05
% 5.51/2.00  MUC search           : 0.00
% 5.51/2.00  Cooper               : 0.00
% 5.51/2.00  Total                : 1.33
% 5.51/2.00  Index Insertion      : 0.00
% 5.51/2.00  Index Deletion       : 0.00
% 5.51/2.00  Index Matching       : 0.00
% 5.51/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
