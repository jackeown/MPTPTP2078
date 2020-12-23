%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:14 EST 2020

% Result     : Theorem 11.87s
% Output     : CNFRefutation 11.94s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 220 expanded)
%              Number of leaves         :   33 (  86 expanded)
%              Depth                    :   11
%              Number of atoms          :  209 ( 517 expanded)
%              Number of equality atoms :   17 (  44 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_117,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_102,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_89,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_64,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_107,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_74,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_98,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(c_58,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_60,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_885,plain,(
    ! [A_199,B_200] :
      ( r1_tarski(A_199,B_200)
      | ~ r1_ordinal1(A_199,B_200)
      | ~ v3_ordinal1(B_200)
      | ~ v3_ordinal1(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_54,plain,(
    ! [A_51] :
      ( v3_ordinal1(k1_ordinal1(A_51))
      | ~ v3_ordinal1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_381,plain,(
    ! [B_122,A_123] :
      ( r2_hidden(B_122,A_123)
      | B_122 = A_123
      | r2_hidden(A_123,B_122)
      | ~ v3_ordinal1(B_122)
      | ~ v3_ordinal1(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_68,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | r1_ordinal1(k1_ordinal1('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_107,plain,(
    r1_ordinal1(k1_ordinal1('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_62,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_3'),'#skF_4')
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_141,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_62])).

tff(c_404,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_381,c_141])).

tff(c_441,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_60,c_404])).

tff(c_452,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_441])).

tff(c_202,plain,(
    ! [A_94,B_95] :
      ( r1_tarski(A_94,B_95)
      | ~ r1_ordinal1(A_94,B_95)
      | ~ v3_ordinal1(B_95)
      | ~ v3_ordinal1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_42,plain,(
    ! [A_41] : k2_xboole_0(A_41,k1_tarski(A_41)) = k1_ordinal1(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_153,plain,(
    ! [D_74,A_75,B_76] :
      ( ~ r2_hidden(D_74,A_75)
      | r2_hidden(D_74,k2_xboole_0(A_75,B_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_164,plain,(
    ! [D_77,A_78] :
      ( ~ r2_hidden(D_77,A_78)
      | r2_hidden(D_77,k1_ordinal1(A_78)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_153])).

tff(c_56,plain,(
    ! [B_53,A_52] :
      ( ~ r1_tarski(B_53,A_52)
      | ~ r2_hidden(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_168,plain,(
    ! [A_78,D_77] :
      ( ~ r1_tarski(k1_ordinal1(A_78),D_77)
      | ~ r2_hidden(D_77,A_78) ) ),
    inference(resolution,[status(thm)],[c_164,c_56])).

tff(c_673,plain,(
    ! [B_154,A_155] :
      ( ~ r2_hidden(B_154,A_155)
      | ~ r1_ordinal1(k1_ordinal1(A_155),B_154)
      | ~ v3_ordinal1(B_154)
      | ~ v3_ordinal1(k1_ordinal1(A_155)) ) ),
    inference(resolution,[status(thm)],[c_202,c_168])).

tff(c_700,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_107,c_673])).

tff(c_709,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_452,c_700])).

tff(c_712,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_709])).

tff(c_716,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_712])).

tff(c_717,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_441])).

tff(c_721,plain,(
    r1_ordinal1(k1_ordinal1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_717,c_107])).

tff(c_48,plain,(
    ! [A_44] : r2_hidden(A_44,k1_ordinal1(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_80,plain,(
    ! [B_58,A_59] :
      ( ~ r1_tarski(B_58,A_59)
      | ~ r2_hidden(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_84,plain,(
    ! [A_44] : ~ r1_tarski(k1_ordinal1(A_44),A_44) ),
    inference(resolution,[status(thm)],[c_48,c_80])).

tff(c_227,plain,(
    ! [B_95] :
      ( ~ r1_ordinal1(k1_ordinal1(B_95),B_95)
      | ~ v3_ordinal1(B_95)
      | ~ v3_ordinal1(k1_ordinal1(B_95)) ) ),
    inference(resolution,[status(thm)],[c_202,c_84])).

tff(c_749,plain,
    ( ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_721,c_227])).

tff(c_752,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_749])).

tff(c_755,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_752])).

tff(c_759,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_755])).

tff(c_760,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_765,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_760,c_56])).

tff(c_911,plain,
    ( ~ r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_885,c_765])).

tff(c_924,plain,(
    ~ r1_ordinal1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_60,c_911])).

tff(c_941,plain,(
    ! [B_202,A_203] :
      ( r1_ordinal1(B_202,A_203)
      | r1_ordinal1(A_203,B_202)
      | ~ v3_ordinal1(B_202)
      | ~ v3_ordinal1(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_767,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_760,c_62])).

tff(c_949,plain,
    ( r1_ordinal1('#skF_4',k1_ordinal1('#skF_3'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_3'))
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_941,c_767])).

tff(c_961,plain,
    ( r1_ordinal1('#skF_4',k1_ordinal1('#skF_3'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_949])).

tff(c_967,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_961])).

tff(c_971,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_967])).

tff(c_975,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_971])).

tff(c_977,plain,(
    v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_961])).

tff(c_36,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(k1_tarski(A_35),B_36)
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_52,plain,(
    ! [B_50,A_48] :
      ( r2_hidden(B_50,A_48)
      | r1_ordinal1(A_48,B_50)
      | ~ v3_ordinal1(B_50)
      | ~ v3_ordinal1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_981,plain,(
    ! [D_206,B_207,A_208] :
      ( r2_hidden(D_206,B_207)
      | r2_hidden(D_206,A_208)
      | ~ r2_hidden(D_206,k2_xboole_0(A_208,B_207)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6476,plain,(
    ! [B_456,B_457,A_458] :
      ( r2_hidden(B_456,B_457)
      | r2_hidden(B_456,A_458)
      | r1_ordinal1(k2_xboole_0(A_458,B_457),B_456)
      | ~ v3_ordinal1(B_456)
      | ~ v3_ordinal1(k2_xboole_0(A_458,B_457)) ) ),
    inference(resolution,[status(thm)],[c_52,c_981])).

tff(c_6490,plain,(
    ! [B_456,A_41] :
      ( r2_hidden(B_456,k1_tarski(A_41))
      | r2_hidden(B_456,A_41)
      | r1_ordinal1(k1_ordinal1(A_41),B_456)
      | ~ v3_ordinal1(B_456)
      | ~ v3_ordinal1(k2_xboole_0(A_41,k1_tarski(A_41))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_6476])).

tff(c_16754,plain,(
    ! [B_737,A_738] :
      ( r2_hidden(B_737,k1_tarski(A_738))
      | r2_hidden(B_737,A_738)
      | r1_ordinal1(k1_ordinal1(A_738),B_737)
      | ~ v3_ordinal1(B_737)
      | ~ v3_ordinal1(k1_ordinal1(A_738)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_6490])).

tff(c_17970,plain,(
    ! [A_746,B_747] :
      ( ~ r1_tarski(k1_tarski(A_746),B_747)
      | r2_hidden(B_747,A_746)
      | r1_ordinal1(k1_ordinal1(A_746),B_747)
      | ~ v3_ordinal1(B_747)
      | ~ v3_ordinal1(k1_ordinal1(A_746)) ) ),
    inference(resolution,[status(thm)],[c_16754,c_56])).

tff(c_17980,plain,(
    ! [B_748,A_749] :
      ( r2_hidden(B_748,A_749)
      | r1_ordinal1(k1_ordinal1(A_749),B_748)
      | ~ v3_ordinal1(B_748)
      | ~ v3_ordinal1(k1_ordinal1(A_749))
      | ~ r2_hidden(A_749,B_748) ) ),
    inference(resolution,[status(thm)],[c_36,c_17970])).

tff(c_18012,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1(k1_ordinal1('#skF_3'))
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_17980,c_767])).

tff(c_18025,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_760,c_977,c_58,c_18012])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3297,plain,(
    ! [B_337,C_338] :
      ( r2_hidden('#skF_2'(B_337,B_337,C_338),C_338)
      | k2_xboole_0(B_337,B_337) = C_338
      | r2_hidden('#skF_1'(B_337,B_337,C_338),B_337) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_18])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3377,plain,(
    ! [B_339] :
      ( r2_hidden('#skF_2'(B_339,B_339,B_339),B_339)
      | k2_xboole_0(B_339,B_339) = B_339 ) ),
    inference(resolution,[status(thm)],[c_3297,c_16])).

tff(c_10,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2610,plain,(
    ! [B_312,C_313] :
      ( ~ r2_hidden('#skF_2'(B_312,B_312,C_313),B_312)
      | k2_xboole_0(B_312,B_312) = C_313
      | r2_hidden('#skF_1'(B_312,B_312,C_313),B_312) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_10])).

tff(c_12,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2644,plain,(
    ! [B_312] :
      ( ~ r2_hidden('#skF_2'(B_312,B_312,B_312),B_312)
      | k2_xboole_0(B_312,B_312) = B_312 ) ),
    inference(resolution,[status(thm)],[c_2610,c_12])).

tff(c_3406,plain,(
    ! [B_339] : k2_xboole_0(B_339,B_339) = B_339 ),
    inference(resolution,[status(thm)],[c_3377,c_2644])).

tff(c_40,plain,(
    ! [B_40,A_39] :
      ( r1_ordinal1(B_40,A_39)
      | r1_ordinal1(A_39,B_40)
      | ~ v3_ordinal1(B_40)
      | ~ v3_ordinal1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_811,plain,(
    ! [D_171,A_172,B_173] :
      ( ~ r2_hidden(D_171,A_172)
      | r2_hidden(D_171,k2_xboole_0(A_172,B_173)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_821,plain,(
    ! [A_172,B_173,D_171] :
      ( ~ r1_tarski(k2_xboole_0(A_172,B_173),D_171)
      | ~ r2_hidden(D_171,A_172) ) ),
    inference(resolution,[status(thm)],[c_811,c_56])).

tff(c_5927,plain,(
    ! [B_436,A_437,B_438] :
      ( ~ r2_hidden(B_436,A_437)
      | ~ r1_ordinal1(k2_xboole_0(A_437,B_438),B_436)
      | ~ v3_ordinal1(B_436)
      | ~ v3_ordinal1(k2_xboole_0(A_437,B_438)) ) ),
    inference(resolution,[status(thm)],[c_885,c_821])).

tff(c_6162,plain,(
    ! [B_446,A_447,B_448] :
      ( ~ r2_hidden(B_446,A_447)
      | r1_ordinal1(B_446,k2_xboole_0(A_447,B_448))
      | ~ v3_ordinal1(B_446)
      | ~ v3_ordinal1(k2_xboole_0(A_447,B_448)) ) ),
    inference(resolution,[status(thm)],[c_40,c_5927])).

tff(c_6191,plain,(
    ! [B_446,B_339] :
      ( ~ r2_hidden(B_446,B_339)
      | r1_ordinal1(B_446,B_339)
      | ~ v3_ordinal1(B_446)
      | ~ v3_ordinal1(k2_xboole_0(B_339,B_339)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3406,c_6162])).

tff(c_6202,plain,(
    ! [B_446,B_339] :
      ( ~ r2_hidden(B_446,B_339)
      | r1_ordinal1(B_446,B_339)
      | ~ v3_ordinal1(B_446)
      | ~ v3_ordinal1(B_339) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3406,c_6191])).

tff(c_18028,plain,
    ( r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18025,c_6202])).

tff(c_18037,plain,(
    r1_ordinal1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_18028])).

tff(c_18039,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_924,c_18037])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:39:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.87/4.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.87/4.90  
% 11.87/4.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.94/4.90  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 11.94/4.90  
% 11.94/4.90  %Foreground sorts:
% 11.94/4.90  
% 11.94/4.90  
% 11.94/4.90  %Background operators:
% 11.94/4.90  
% 11.94/4.90  
% 11.94/4.90  %Foreground operators:
% 11.94/4.90  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 11.94/4.90  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 11.94/4.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.94/4.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.94/4.90  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.94/4.90  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.94/4.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.94/4.90  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.94/4.90  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 11.94/4.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.94/4.90  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.94/4.90  tff('#skF_3', type, '#skF_3': $i).
% 11.94/4.90  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.94/4.90  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 11.94/4.90  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.94/4.90  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.94/4.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.94/4.90  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.94/4.90  tff('#skF_4', type, '#skF_4': $i).
% 11.94/4.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.94/4.90  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.94/4.90  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 11.94/4.90  
% 11.94/4.92  tff(f_117, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_ordinal1)).
% 11.94/4.92  tff(f_72, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 11.94/4.92  tff(f_102, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 11.94/4.92  tff(f_89, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 11.94/4.92  tff(f_64, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 11.94/4.92  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 11.94/4.92  tff(f_107, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 11.94/4.92  tff(f_74, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 11.94/4.92  tff(f_62, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 11.94/4.92  tff(f_52, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 11.94/4.92  tff(f_98, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 11.94/4.92  tff(c_58, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 11.94/4.92  tff(c_60, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 11.94/4.92  tff(c_885, plain, (![A_199, B_200]: (r1_tarski(A_199, B_200) | ~r1_ordinal1(A_199, B_200) | ~v3_ordinal1(B_200) | ~v3_ordinal1(A_199))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.94/4.92  tff(c_54, plain, (![A_51]: (v3_ordinal1(k1_ordinal1(A_51)) | ~v3_ordinal1(A_51))), inference(cnfTransformation, [status(thm)], [f_102])).
% 11.94/4.92  tff(c_381, plain, (![B_122, A_123]: (r2_hidden(B_122, A_123) | B_122=A_123 | r2_hidden(A_123, B_122) | ~v3_ordinal1(B_122) | ~v3_ordinal1(A_123))), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.94/4.92  tff(c_68, plain, (r2_hidden('#skF_3', '#skF_4') | r1_ordinal1(k1_ordinal1('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 11.94/4.92  tff(c_107, plain, (r1_ordinal1(k1_ordinal1('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_68])).
% 11.94/4.92  tff(c_62, plain, (~r1_ordinal1(k1_ordinal1('#skF_3'), '#skF_4') | ~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 11.94/4.92  tff(c_141, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_62])).
% 11.94/4.92  tff(c_404, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_381, c_141])).
% 11.94/4.92  tff(c_441, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_60, c_404])).
% 11.94/4.92  tff(c_452, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_441])).
% 11.94/4.92  tff(c_202, plain, (![A_94, B_95]: (r1_tarski(A_94, B_95) | ~r1_ordinal1(A_94, B_95) | ~v3_ordinal1(B_95) | ~v3_ordinal1(A_94))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.94/4.92  tff(c_42, plain, (![A_41]: (k2_xboole_0(A_41, k1_tarski(A_41))=k1_ordinal1(A_41))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.94/4.92  tff(c_153, plain, (![D_74, A_75, B_76]: (~r2_hidden(D_74, A_75) | r2_hidden(D_74, k2_xboole_0(A_75, B_76)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.94/4.92  tff(c_164, plain, (![D_77, A_78]: (~r2_hidden(D_77, A_78) | r2_hidden(D_77, k1_ordinal1(A_78)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_153])).
% 11.94/4.92  tff(c_56, plain, (![B_53, A_52]: (~r1_tarski(B_53, A_52) | ~r2_hidden(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_107])).
% 11.94/4.92  tff(c_168, plain, (![A_78, D_77]: (~r1_tarski(k1_ordinal1(A_78), D_77) | ~r2_hidden(D_77, A_78))), inference(resolution, [status(thm)], [c_164, c_56])).
% 11.94/4.92  tff(c_673, plain, (![B_154, A_155]: (~r2_hidden(B_154, A_155) | ~r1_ordinal1(k1_ordinal1(A_155), B_154) | ~v3_ordinal1(B_154) | ~v3_ordinal1(k1_ordinal1(A_155)))), inference(resolution, [status(thm)], [c_202, c_168])).
% 11.94/4.92  tff(c_700, plain, (~r2_hidden('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(resolution, [status(thm)], [c_107, c_673])).
% 11.94/4.92  tff(c_709, plain, (~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_452, c_700])).
% 11.94/4.92  tff(c_712, plain, (~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_709])).
% 11.94/4.92  tff(c_716, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_712])).
% 11.94/4.92  tff(c_717, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_441])).
% 11.94/4.92  tff(c_721, plain, (r1_ordinal1(k1_ordinal1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_717, c_107])).
% 11.94/4.92  tff(c_48, plain, (![A_44]: (r2_hidden(A_44, k1_ordinal1(A_44)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.94/4.92  tff(c_80, plain, (![B_58, A_59]: (~r1_tarski(B_58, A_59) | ~r2_hidden(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_107])).
% 11.94/4.92  tff(c_84, plain, (![A_44]: (~r1_tarski(k1_ordinal1(A_44), A_44))), inference(resolution, [status(thm)], [c_48, c_80])).
% 11.94/4.92  tff(c_227, plain, (![B_95]: (~r1_ordinal1(k1_ordinal1(B_95), B_95) | ~v3_ordinal1(B_95) | ~v3_ordinal1(k1_ordinal1(B_95)))), inference(resolution, [status(thm)], [c_202, c_84])).
% 11.94/4.92  tff(c_749, plain, (~v3_ordinal1('#skF_4') | ~v3_ordinal1(k1_ordinal1('#skF_4'))), inference(resolution, [status(thm)], [c_721, c_227])).
% 11.94/4.92  tff(c_752, plain, (~v3_ordinal1(k1_ordinal1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_749])).
% 11.94/4.92  tff(c_755, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_752])).
% 11.94/4.92  tff(c_759, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_755])).
% 11.94/4.92  tff(c_760, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_68])).
% 11.94/4.92  tff(c_765, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_760, c_56])).
% 11.94/4.92  tff(c_911, plain, (~r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_885, c_765])).
% 11.94/4.92  tff(c_924, plain, (~r1_ordinal1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_60, c_911])).
% 11.94/4.92  tff(c_941, plain, (![B_202, A_203]: (r1_ordinal1(B_202, A_203) | r1_ordinal1(A_203, B_202) | ~v3_ordinal1(B_202) | ~v3_ordinal1(A_203))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.94/4.92  tff(c_767, plain, (~r1_ordinal1(k1_ordinal1('#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_760, c_62])).
% 11.94/4.92  tff(c_949, plain, (r1_ordinal1('#skF_4', k1_ordinal1('#skF_3')) | ~v3_ordinal1(k1_ordinal1('#skF_3')) | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_941, c_767])).
% 11.94/4.92  tff(c_961, plain, (r1_ordinal1('#skF_4', k1_ordinal1('#skF_3')) | ~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_949])).
% 11.94/4.92  tff(c_967, plain, (~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(splitLeft, [status(thm)], [c_961])).
% 11.94/4.92  tff(c_971, plain, (~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_967])).
% 11.94/4.92  tff(c_975, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_971])).
% 11.94/4.92  tff(c_977, plain, (v3_ordinal1(k1_ordinal1('#skF_3'))), inference(splitRight, [status(thm)], [c_961])).
% 11.94/4.92  tff(c_36, plain, (![A_35, B_36]: (r1_tarski(k1_tarski(A_35), B_36) | ~r2_hidden(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.94/4.92  tff(c_52, plain, (![B_50, A_48]: (r2_hidden(B_50, A_48) | r1_ordinal1(A_48, B_50) | ~v3_ordinal1(B_50) | ~v3_ordinal1(A_48))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.94/4.92  tff(c_981, plain, (![D_206, B_207, A_208]: (r2_hidden(D_206, B_207) | r2_hidden(D_206, A_208) | ~r2_hidden(D_206, k2_xboole_0(A_208, B_207)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.94/4.92  tff(c_6476, plain, (![B_456, B_457, A_458]: (r2_hidden(B_456, B_457) | r2_hidden(B_456, A_458) | r1_ordinal1(k2_xboole_0(A_458, B_457), B_456) | ~v3_ordinal1(B_456) | ~v3_ordinal1(k2_xboole_0(A_458, B_457)))), inference(resolution, [status(thm)], [c_52, c_981])).
% 11.94/4.92  tff(c_6490, plain, (![B_456, A_41]: (r2_hidden(B_456, k1_tarski(A_41)) | r2_hidden(B_456, A_41) | r1_ordinal1(k1_ordinal1(A_41), B_456) | ~v3_ordinal1(B_456) | ~v3_ordinal1(k2_xboole_0(A_41, k1_tarski(A_41))))), inference(superposition, [status(thm), theory('equality')], [c_42, c_6476])).
% 11.94/4.92  tff(c_16754, plain, (![B_737, A_738]: (r2_hidden(B_737, k1_tarski(A_738)) | r2_hidden(B_737, A_738) | r1_ordinal1(k1_ordinal1(A_738), B_737) | ~v3_ordinal1(B_737) | ~v3_ordinal1(k1_ordinal1(A_738)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_6490])).
% 11.94/4.92  tff(c_17970, plain, (![A_746, B_747]: (~r1_tarski(k1_tarski(A_746), B_747) | r2_hidden(B_747, A_746) | r1_ordinal1(k1_ordinal1(A_746), B_747) | ~v3_ordinal1(B_747) | ~v3_ordinal1(k1_ordinal1(A_746)))), inference(resolution, [status(thm)], [c_16754, c_56])).
% 11.94/4.92  tff(c_17980, plain, (![B_748, A_749]: (r2_hidden(B_748, A_749) | r1_ordinal1(k1_ordinal1(A_749), B_748) | ~v3_ordinal1(B_748) | ~v3_ordinal1(k1_ordinal1(A_749)) | ~r2_hidden(A_749, B_748))), inference(resolution, [status(thm)], [c_36, c_17970])).
% 11.94/4.92  tff(c_18012, plain, (r2_hidden('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1(k1_ordinal1('#skF_3')) | ~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_17980, c_767])).
% 11.94/4.92  tff(c_18025, plain, (r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_760, c_977, c_58, c_18012])).
% 11.94/4.92  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.94/4.92  tff(c_3297, plain, (![B_337, C_338]: (r2_hidden('#skF_2'(B_337, B_337, C_338), C_338) | k2_xboole_0(B_337, B_337)=C_338 | r2_hidden('#skF_1'(B_337, B_337, C_338), B_337))), inference(factorization, [status(thm), theory('equality')], [c_18])).
% 11.94/4.92  tff(c_16, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.94/4.92  tff(c_3377, plain, (![B_339]: (r2_hidden('#skF_2'(B_339, B_339, B_339), B_339) | k2_xboole_0(B_339, B_339)=B_339)), inference(resolution, [status(thm)], [c_3297, c_16])).
% 11.94/4.92  tff(c_10, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.94/4.92  tff(c_2610, plain, (![B_312, C_313]: (~r2_hidden('#skF_2'(B_312, B_312, C_313), B_312) | k2_xboole_0(B_312, B_312)=C_313 | r2_hidden('#skF_1'(B_312, B_312, C_313), B_312))), inference(factorization, [status(thm), theory('equality')], [c_10])).
% 11.94/4.92  tff(c_12, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.94/4.92  tff(c_2644, plain, (![B_312]: (~r2_hidden('#skF_2'(B_312, B_312, B_312), B_312) | k2_xboole_0(B_312, B_312)=B_312)), inference(resolution, [status(thm)], [c_2610, c_12])).
% 11.94/4.92  tff(c_3406, plain, (![B_339]: (k2_xboole_0(B_339, B_339)=B_339)), inference(resolution, [status(thm)], [c_3377, c_2644])).
% 11.94/4.92  tff(c_40, plain, (![B_40, A_39]: (r1_ordinal1(B_40, A_39) | r1_ordinal1(A_39, B_40) | ~v3_ordinal1(B_40) | ~v3_ordinal1(A_39))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.94/4.92  tff(c_811, plain, (![D_171, A_172, B_173]: (~r2_hidden(D_171, A_172) | r2_hidden(D_171, k2_xboole_0(A_172, B_173)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.94/4.92  tff(c_821, plain, (![A_172, B_173, D_171]: (~r1_tarski(k2_xboole_0(A_172, B_173), D_171) | ~r2_hidden(D_171, A_172))), inference(resolution, [status(thm)], [c_811, c_56])).
% 11.94/4.92  tff(c_5927, plain, (![B_436, A_437, B_438]: (~r2_hidden(B_436, A_437) | ~r1_ordinal1(k2_xboole_0(A_437, B_438), B_436) | ~v3_ordinal1(B_436) | ~v3_ordinal1(k2_xboole_0(A_437, B_438)))), inference(resolution, [status(thm)], [c_885, c_821])).
% 11.94/4.92  tff(c_6162, plain, (![B_446, A_447, B_448]: (~r2_hidden(B_446, A_447) | r1_ordinal1(B_446, k2_xboole_0(A_447, B_448)) | ~v3_ordinal1(B_446) | ~v3_ordinal1(k2_xboole_0(A_447, B_448)))), inference(resolution, [status(thm)], [c_40, c_5927])).
% 11.94/4.92  tff(c_6191, plain, (![B_446, B_339]: (~r2_hidden(B_446, B_339) | r1_ordinal1(B_446, B_339) | ~v3_ordinal1(B_446) | ~v3_ordinal1(k2_xboole_0(B_339, B_339)))), inference(superposition, [status(thm), theory('equality')], [c_3406, c_6162])).
% 11.94/4.92  tff(c_6202, plain, (![B_446, B_339]: (~r2_hidden(B_446, B_339) | r1_ordinal1(B_446, B_339) | ~v3_ordinal1(B_446) | ~v3_ordinal1(B_339))), inference(demodulation, [status(thm), theory('equality')], [c_3406, c_6191])).
% 11.94/4.92  tff(c_18028, plain, (r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_18025, c_6202])).
% 11.94/4.92  tff(c_18037, plain, (r1_ordinal1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_18028])).
% 11.94/4.92  tff(c_18039, plain, $false, inference(negUnitSimplification, [status(thm)], [c_924, c_18037])).
% 11.94/4.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.94/4.92  
% 11.94/4.92  Inference rules
% 11.94/4.92  ----------------------
% 11.94/4.92  #Ref     : 0
% 11.94/4.92  #Sup     : 3679
% 11.94/4.92  #Fact    : 18
% 11.94/4.92  #Define  : 0
% 11.94/4.92  #Split   : 4
% 11.94/4.92  #Chain   : 0
% 11.94/4.92  #Close   : 0
% 11.94/4.92  
% 11.94/4.92  Ordering : KBO
% 11.94/4.92  
% 11.94/4.92  Simplification rules
% 11.94/4.92  ----------------------
% 11.94/4.92  #Subsume      : 620
% 11.94/4.92  #Demod        : 513
% 11.94/4.92  #Tautology    : 159
% 11.94/4.92  #SimpNegUnit  : 1
% 11.94/4.92  #BackRed      : 22
% 11.94/4.92  
% 11.94/4.92  #Partial instantiations: 0
% 11.94/4.92  #Strategies tried      : 1
% 11.94/4.92  
% 11.94/4.92  Timing (in seconds)
% 11.94/4.92  ----------------------
% 11.94/4.92  Preprocessing        : 0.54
% 11.94/4.92  Parsing              : 0.27
% 11.94/4.92  CNF conversion       : 0.04
% 11.94/4.92  Main loop            : 3.49
% 11.94/4.92  Inferencing          : 0.88
% 11.94/4.92  Reduction            : 0.72
% 11.94/4.92  Demodulation         : 0.52
% 11.94/4.92  BG Simplification    : 0.12
% 11.94/4.92  Subsumption          : 1.50
% 11.94/4.92  Abstraction          : 0.16
% 11.94/4.92  MUC search           : 0.00
% 11.94/4.92  Cooper               : 0.00
% 11.94/4.92  Total                : 4.08
% 11.94/4.92  Index Insertion      : 0.00
% 11.94/4.92  Index Deletion       : 0.00
% 11.94/4.92  Index Matching       : 0.00
% 11.94/4.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
