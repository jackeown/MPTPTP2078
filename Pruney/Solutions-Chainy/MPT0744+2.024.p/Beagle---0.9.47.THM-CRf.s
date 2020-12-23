%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:18 EST 2020

% Result     : Theorem 6.88s
% Output     : CNFRefutation 6.88s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 161 expanded)
%              Number of leaves         :   28 (  64 expanded)
%              Depth                    :    9
%              Number of atoms          :  129 ( 328 expanded)
%              Number of equality atoms :   21 (  57 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_88,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_50,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_93,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_56,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_79,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_58,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2492,plain,(
    ! [B_251,A_252] :
      ( r2_hidden(B_251,A_252)
      | r1_ordinal1(A_252,B_251)
      | ~ v3_ordinal1(B_251)
      | ~ v3_ordinal1(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2306,plain,(
    ! [A_221,B_222] :
      ( r1_tarski(k1_tarski(A_221),B_222)
      | ~ r2_hidden(A_221,B_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_71,plain,(
    ! [A_34] : k2_tarski(A_34,A_34) = k1_tarski(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_24,plain,(
    ! [D_14,A_9] : r2_hidden(D_14,k2_tarski(A_9,D_14)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_77,plain,(
    ! [A_34] : r2_hidden(A_34,k1_tarski(A_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_24])).

tff(c_97,plain,(
    ! [B_37,A_38] :
      ( ~ r1_tarski(B_37,A_38)
      | ~ r2_hidden(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_107,plain,(
    ! [A_34] : ~ r1_tarski(k1_tarski(A_34),A_34) ),
    inference(resolution,[status(thm)],[c_77,c_97])).

tff(c_2311,plain,(
    ! [B_222] : ~ r2_hidden(B_222,B_222) ),
    inference(resolution,[status(thm)],[c_2306,c_107])).

tff(c_2566,plain,(
    ! [A_252] :
      ( r1_ordinal1(A_252,A_252)
      | ~ v3_ordinal1(A_252) ) ),
    inference(resolution,[status(thm)],[c_2492,c_2311])).

tff(c_46,plain,(
    ! [A_18] : k2_xboole_0(A_18,k1_tarski(A_18)) = k1_ordinal1(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_152,plain,(
    ! [D_56,B_57,A_58] :
      ( ~ r2_hidden(D_56,B_57)
      | r2_hidden(D_56,k2_xboole_0(A_58,B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2243,plain,(
    ! [D_209,A_210] :
      ( ~ r2_hidden(D_209,k1_tarski(A_210))
      | r2_hidden(D_209,k1_ordinal1(A_210)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_152])).

tff(c_2267,plain,(
    ! [A_34] : r2_hidden(A_34,k1_ordinal1(A_34)) ),
    inference(resolution,[status(thm)],[c_77,c_2243])).

tff(c_60,plain,(
    v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_62,plain,
    ( ~ r1_ordinal1('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_110,plain,(
    ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_68,plain,
    ( r2_hidden('#skF_5',k1_ordinal1('#skF_6'))
    | r1_ordinal1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_142,plain,(
    r1_ordinal1('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_68])).

tff(c_50,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ r1_ordinal1(A_19,B_20)
      | ~ v3_ordinal1(B_20)
      | ~ v3_ordinal1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_888,plain,(
    ! [B_121,A_122] :
      ( r2_hidden(B_121,A_122)
      | B_121 = A_122
      | r2_hidden(A_122,B_121)
      | ~ v3_ordinal1(B_121)
      | ~ v3_ordinal1(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_193,plain,(
    ! [D_62,A_63,B_64] :
      ( ~ r2_hidden(D_62,A_63)
      | r2_hidden(D_62,k2_xboole_0(A_63,B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_446,plain,(
    ! [D_86,A_87] :
      ( ~ r2_hidden(D_86,A_87)
      | r2_hidden(D_86,k1_ordinal1(A_87)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_193])).

tff(c_521,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_446,c_110])).

tff(c_939,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_888,c_521])).

tff(c_1139,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_60,c_939])).

tff(c_1195,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1139])).

tff(c_56,plain,(
    ! [B_28,A_27] :
      ( ~ r1_tarski(B_28,A_27)
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1202,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_1195,c_56])).

tff(c_1205,plain,
    ( ~ r1_ordinal1('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_1202])).

tff(c_1209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_142,c_1205])).

tff(c_1210,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1139])).

tff(c_1215,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1210,c_110])).

tff(c_2270,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2267,c_1215])).

tff(c_2271,plain,(
    ~ r1_ordinal1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_2273,plain,(
    r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_2271,c_68])).

tff(c_2961,plain,(
    ! [D_284,B_285,A_286] :
      ( r2_hidden(D_284,B_285)
      | r2_hidden(D_284,A_286)
      | ~ r2_hidden(D_284,k2_xboole_0(A_286,B_285)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6190,plain,(
    ! [D_493,A_494] :
      ( r2_hidden(D_493,k1_tarski(A_494))
      | r2_hidden(D_493,A_494)
      | ~ r2_hidden(D_493,k1_ordinal1(A_494)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2961])).

tff(c_40,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2424,plain,(
    ! [D_240,B_241,A_242] :
      ( D_240 = B_241
      | D_240 = A_242
      | ~ r2_hidden(D_240,k2_tarski(A_242,B_241)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2427,plain,(
    ! [D_240,A_15] :
      ( D_240 = A_15
      | D_240 = A_15
      | ~ r2_hidden(D_240,k1_tarski(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_2424])).

tff(c_8525,plain,(
    ! [D_572,A_573] :
      ( D_572 = A_573
      | r2_hidden(D_572,A_573)
      | ~ r2_hidden(D_572,k1_ordinal1(A_573)) ) ),
    inference(resolution,[status(thm)],[c_6190,c_2427])).

tff(c_8605,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_2273,c_8525])).

tff(c_8606,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_8605])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2572,plain,(
    ! [A_252,B_251] :
      ( ~ r2_hidden(A_252,B_251)
      | r1_ordinal1(A_252,B_251)
      | ~ v3_ordinal1(B_251)
      | ~ v3_ordinal1(A_252) ) ),
    inference(resolution,[status(thm)],[c_2492,c_2])).

tff(c_8609,plain,
    ( r1_ordinal1('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_8606,c_2572])).

tff(c_8617,plain,(
    r1_ordinal1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_8609])).

tff(c_8619,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2271,c_8617])).

tff(c_8620,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_8605])).

tff(c_8625,plain,(
    ~ r1_ordinal1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8620,c_2271])).

tff(c_8636,plain,(
    ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2566,c_8625])).

tff(c_8640,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_8636])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:46:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.88/2.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.88/2.62  
% 6.88/2.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.88/2.62  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 6.88/2.62  
% 6.88/2.62  %Foreground sorts:
% 6.88/2.62  
% 6.88/2.62  
% 6.88/2.62  %Background operators:
% 6.88/2.62  
% 6.88/2.62  
% 6.88/2.62  %Foreground operators:
% 6.88/2.62  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.88/2.62  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 6.88/2.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.88/2.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.88/2.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.88/2.62  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.88/2.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.88/2.62  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 6.88/2.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.88/2.62  tff('#skF_5', type, '#skF_5': $i).
% 6.88/2.62  tff('#skF_6', type, '#skF_6': $i).
% 6.88/2.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.88/2.62  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 6.88/2.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.88/2.62  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.88/2.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.88/2.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.88/2.62  
% 6.88/2.64  tff(f_103, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 6.88/2.64  tff(f_88, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 6.88/2.64  tff(f_54, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 6.88/2.64  tff(f_50, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.88/2.64  tff(f_48, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 6.88/2.64  tff(f_93, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.88/2.64  tff(f_56, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 6.88/2.64  tff(f_39, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 6.88/2.64  tff(f_64, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 6.88/2.64  tff(f_79, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 6.88/2.64  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 6.88/2.64  tff(c_58, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.88/2.64  tff(c_2492, plain, (![B_251, A_252]: (r2_hidden(B_251, A_252) | r1_ordinal1(A_252, B_251) | ~v3_ordinal1(B_251) | ~v3_ordinal1(A_252))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.88/2.64  tff(c_2306, plain, (![A_221, B_222]: (r1_tarski(k1_tarski(A_221), B_222) | ~r2_hidden(A_221, B_222))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.88/2.64  tff(c_71, plain, (![A_34]: (k2_tarski(A_34, A_34)=k1_tarski(A_34))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.88/2.64  tff(c_24, plain, (![D_14, A_9]: (r2_hidden(D_14, k2_tarski(A_9, D_14)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.88/2.64  tff(c_77, plain, (![A_34]: (r2_hidden(A_34, k1_tarski(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_71, c_24])).
% 6.88/2.64  tff(c_97, plain, (![B_37, A_38]: (~r1_tarski(B_37, A_38) | ~r2_hidden(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.88/2.64  tff(c_107, plain, (![A_34]: (~r1_tarski(k1_tarski(A_34), A_34))), inference(resolution, [status(thm)], [c_77, c_97])).
% 6.88/2.64  tff(c_2311, plain, (![B_222]: (~r2_hidden(B_222, B_222))), inference(resolution, [status(thm)], [c_2306, c_107])).
% 6.88/2.64  tff(c_2566, plain, (![A_252]: (r1_ordinal1(A_252, A_252) | ~v3_ordinal1(A_252))), inference(resolution, [status(thm)], [c_2492, c_2311])).
% 6.88/2.64  tff(c_46, plain, (![A_18]: (k2_xboole_0(A_18, k1_tarski(A_18))=k1_ordinal1(A_18))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.88/2.64  tff(c_152, plain, (![D_56, B_57, A_58]: (~r2_hidden(D_56, B_57) | r2_hidden(D_56, k2_xboole_0(A_58, B_57)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.88/2.64  tff(c_2243, plain, (![D_209, A_210]: (~r2_hidden(D_209, k1_tarski(A_210)) | r2_hidden(D_209, k1_ordinal1(A_210)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_152])).
% 6.88/2.64  tff(c_2267, plain, (![A_34]: (r2_hidden(A_34, k1_ordinal1(A_34)))), inference(resolution, [status(thm)], [c_77, c_2243])).
% 6.88/2.64  tff(c_60, plain, (v3_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.88/2.64  tff(c_62, plain, (~r1_ordinal1('#skF_5', '#skF_6') | ~r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.88/2.64  tff(c_110, plain, (~r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(splitLeft, [status(thm)], [c_62])).
% 6.88/2.64  tff(c_68, plain, (r2_hidden('#skF_5', k1_ordinal1('#skF_6')) | r1_ordinal1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.88/2.64  tff(c_142, plain, (r1_ordinal1('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_110, c_68])).
% 6.88/2.64  tff(c_50, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | ~r1_ordinal1(A_19, B_20) | ~v3_ordinal1(B_20) | ~v3_ordinal1(A_19))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.88/2.64  tff(c_888, plain, (![B_121, A_122]: (r2_hidden(B_121, A_122) | B_121=A_122 | r2_hidden(A_122, B_121) | ~v3_ordinal1(B_121) | ~v3_ordinal1(A_122))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.88/2.64  tff(c_193, plain, (![D_62, A_63, B_64]: (~r2_hidden(D_62, A_63) | r2_hidden(D_62, k2_xboole_0(A_63, B_64)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.88/2.64  tff(c_446, plain, (![D_86, A_87]: (~r2_hidden(D_86, A_87) | r2_hidden(D_86, k1_ordinal1(A_87)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_193])).
% 6.88/2.64  tff(c_521, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_446, c_110])).
% 6.88/2.64  tff(c_939, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_888, c_521])).
% 6.88/2.64  tff(c_1139, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_60, c_939])).
% 6.88/2.64  tff(c_1195, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_1139])).
% 6.88/2.64  tff(c_56, plain, (![B_28, A_27]: (~r1_tarski(B_28, A_27) | ~r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.88/2.64  tff(c_1202, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_1195, c_56])).
% 6.88/2.64  tff(c_1205, plain, (~r1_ordinal1('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_1202])).
% 6.88/2.64  tff(c_1209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_142, c_1205])).
% 6.88/2.64  tff(c_1210, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_1139])).
% 6.88/2.64  tff(c_1215, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1210, c_110])).
% 6.88/2.64  tff(c_2270, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2267, c_1215])).
% 6.88/2.64  tff(c_2271, plain, (~r1_ordinal1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_62])).
% 6.88/2.64  tff(c_2273, plain, (r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_2271, c_68])).
% 6.88/2.64  tff(c_2961, plain, (![D_284, B_285, A_286]: (r2_hidden(D_284, B_285) | r2_hidden(D_284, A_286) | ~r2_hidden(D_284, k2_xboole_0(A_286, B_285)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.88/2.64  tff(c_6190, plain, (![D_493, A_494]: (r2_hidden(D_493, k1_tarski(A_494)) | r2_hidden(D_493, A_494) | ~r2_hidden(D_493, k1_ordinal1(A_494)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_2961])).
% 6.88/2.64  tff(c_40, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.88/2.64  tff(c_2424, plain, (![D_240, B_241, A_242]: (D_240=B_241 | D_240=A_242 | ~r2_hidden(D_240, k2_tarski(A_242, B_241)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.88/2.64  tff(c_2427, plain, (![D_240, A_15]: (D_240=A_15 | D_240=A_15 | ~r2_hidden(D_240, k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_2424])).
% 6.88/2.64  tff(c_8525, plain, (![D_572, A_573]: (D_572=A_573 | r2_hidden(D_572, A_573) | ~r2_hidden(D_572, k1_ordinal1(A_573)))), inference(resolution, [status(thm)], [c_6190, c_2427])).
% 6.88/2.64  tff(c_8605, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_2273, c_8525])).
% 6.88/2.64  tff(c_8606, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_8605])).
% 6.88/2.64  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 6.88/2.64  tff(c_2572, plain, (![A_252, B_251]: (~r2_hidden(A_252, B_251) | r1_ordinal1(A_252, B_251) | ~v3_ordinal1(B_251) | ~v3_ordinal1(A_252))), inference(resolution, [status(thm)], [c_2492, c_2])).
% 6.88/2.64  tff(c_8609, plain, (r1_ordinal1('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_8606, c_2572])).
% 6.88/2.64  tff(c_8617, plain, (r1_ordinal1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_8609])).
% 6.88/2.64  tff(c_8619, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2271, c_8617])).
% 6.88/2.64  tff(c_8620, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_8605])).
% 6.88/2.64  tff(c_8625, plain, (~r1_ordinal1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8620, c_2271])).
% 6.88/2.64  tff(c_8636, plain, (~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_2566, c_8625])).
% 6.88/2.64  tff(c_8640, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_8636])).
% 6.88/2.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.88/2.64  
% 6.88/2.64  Inference rules
% 6.88/2.64  ----------------------
% 6.88/2.64  #Ref     : 0
% 6.88/2.64  #Sup     : 1742
% 6.88/2.64  #Fact    : 10
% 6.88/2.64  #Define  : 0
% 6.88/2.64  #Split   : 5
% 6.88/2.64  #Chain   : 0
% 6.88/2.64  #Close   : 0
% 6.88/2.64  
% 6.88/2.64  Ordering : KBO
% 6.88/2.64  
% 6.88/2.64  Simplification rules
% 6.88/2.64  ----------------------
% 6.88/2.64  #Subsume      : 208
% 6.88/2.64  #Demod        : 56
% 6.88/2.64  #Tautology    : 61
% 6.88/2.64  #SimpNegUnit  : 32
% 6.88/2.64  #BackRed      : 11
% 6.88/2.64  
% 6.88/2.64  #Partial instantiations: 0
% 6.88/2.64  #Strategies tried      : 1
% 6.88/2.64  
% 6.88/2.64  Timing (in seconds)
% 6.88/2.64  ----------------------
% 6.88/2.64  Preprocessing        : 0.34
% 6.88/2.64  Parsing              : 0.16
% 6.88/2.64  CNF conversion       : 0.02
% 6.88/2.64  Main loop            : 1.48
% 6.88/2.64  Inferencing          : 0.42
% 6.88/2.64  Reduction            : 0.41
% 6.88/2.64  Demodulation         : 0.22
% 6.88/2.64  BG Simplification    : 0.07
% 6.88/2.64  Subsumption          : 0.45
% 6.88/2.64  Abstraction          : 0.08
% 6.88/2.64  MUC search           : 0.00
% 6.88/2.64  Cooper               : 0.00
% 6.88/2.64  Total                : 1.85
% 6.88/2.64  Index Insertion      : 0.00
% 6.88/2.64  Index Deletion       : 0.00
% 6.88/2.64  Index Matching       : 0.00
% 6.88/2.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
