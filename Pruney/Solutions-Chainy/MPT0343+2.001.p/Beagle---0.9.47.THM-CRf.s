%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:17 EST 2020

% Result     : Theorem 5.92s
% Output     : CNFRefutation 6.04s
% Verified   : 
% Statistics : Number of formulae       :  203 (1093 expanded)
%              Number of leaves         :   21 ( 339 expanded)
%              Depth                    :   16
%              Number of atoms          :  352 (2866 expanded)
%              Number of equality atoms :   37 ( 210 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ! [D] :
                  ( m1_subset_1(D,A)
                 => ( r2_hidden(D,B)
                  <=> r2_hidden(D,C) ) )
             => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_26,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_20,plain,(
    ! [B_15,A_14] :
      ( m1_subset_1(B_15,A_14)
      | ~ v1_xboole_0(B_15)
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_112,plain,(
    ! [A_41,B_42] :
      ( r2_hidden('#skF_2'(A_41,B_42),A_41)
      | r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( ~ r2_hidden('#skF_2'(A_7,B_8),B_8)
      | r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_124,plain,(
    ! [A_41] : r1_tarski(A_41,A_41) ),
    inference(resolution,[status(thm)],[c_112,c_10])).

tff(c_146,plain,(
    ! [D_47] :
      ( r2_hidden(D_47,'#skF_5')
      | ~ r2_hidden(D_47,'#skF_4')
      | ~ m1_subset_1(D_47,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_159,plain,(
    ! [D_47] :
      ( ~ v1_xboole_0('#skF_5')
      | ~ r2_hidden(D_47,'#skF_4')
      | ~ m1_subset_1(D_47,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_146,c_4])).

tff(c_183,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_159])).

tff(c_84,plain,(
    ! [D_32] :
      ( r2_hidden(D_32,'#skF_4')
      | ~ r2_hidden(D_32,'#skF_5')
      | ~ m1_subset_1(D_32,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_89,plain,
    ( r2_hidden('#skF_1'('#skF_5'),'#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_3')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_84])).

tff(c_239,plain,
    ( r2_hidden('#skF_1'('#skF_5'),'#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_89])).

tff(c_240,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_239])).

tff(c_161,plain,(
    ! [B_50,A_51] :
      ( m1_subset_1(B_50,A_51)
      | ~ r2_hidden(B_50,A_51)
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_177,plain,(
    ! [A_3] :
      ( m1_subset_1('#skF_1'(A_3),A_3)
      | v1_xboole_0(A_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_161])).

tff(c_244,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_5'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_240])).

tff(c_245,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_244])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_18,plain,(
    ! [B_15,A_14] :
      ( r2_hidden(B_15,A_14)
      | ~ m1_subset_1(B_15,A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_223,plain,(
    ! [C_60,A_61,B_62] :
      ( r2_hidden(C_60,A_61)
      | ~ r2_hidden(C_60,B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_413,plain,(
    ! [B_83,A_84,A_85] :
      ( r2_hidden(B_83,A_84)
      | ~ m1_subset_1(A_85,k1_zfmisc_1(A_84))
      | ~ m1_subset_1(B_83,A_85)
      | v1_xboole_0(A_85) ) ),
    inference(resolution,[status(thm)],[c_18,c_223])).

tff(c_424,plain,(
    ! [B_83] :
      ( r2_hidden(B_83,'#skF_3')
      | ~ m1_subset_1(B_83,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_413])).

tff(c_434,plain,(
    ! [B_86] :
      ( r2_hidden(B_86,'#skF_3')
      | ~ m1_subset_1(B_86,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_424])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( m1_subset_1(B_15,A_14)
      | ~ r2_hidden(B_15,A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_441,plain,(
    ! [B_86] :
      ( m1_subset_1(B_86,'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(B_86,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_434,c_16])).

tff(c_456,plain,(
    ! [B_87] :
      ( m1_subset_1(B_87,'#skF_3')
      | ~ m1_subset_1(B_87,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_245,c_441])).

tff(c_464,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),'#skF_3')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_177,c_456])).

tff(c_475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_240,c_464])).

tff(c_477,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_244])).

tff(c_646,plain,(
    ! [A_97,A_98] :
      ( r2_hidden('#skF_1'(A_97),A_98)
      | ~ m1_subset_1(A_97,k1_zfmisc_1(A_98))
      | v1_xboole_0(A_97) ) ),
    inference(resolution,[status(thm)],[c_6,c_223])).

tff(c_671,plain,(
    ! [A_99,A_100] :
      ( ~ v1_xboole_0(A_99)
      | ~ m1_subset_1(A_100,k1_zfmisc_1(A_99))
      | v1_xboole_0(A_100) ) ),
    inference(resolution,[status(thm)],[c_646,c_4])).

tff(c_686,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_671])).

tff(c_695,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_686])).

tff(c_697,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_695])).

tff(c_698,plain,(
    r2_hidden('#skF_1'('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_713,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_698,c_4])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_2'(A_7,B_8),A_7)
      | r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_175,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1('#skF_2'(A_7,B_8),A_7)
      | v1_xboole_0(A_7)
      | r1_tarski(A_7,B_8) ) ),
    inference(resolution,[status(thm)],[c_12,c_161])).

tff(c_699,plain,(
    m1_subset_1('#skF_1'('#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_22,plain,(
    ! [B_15,A_14] :
      ( v1_xboole_0(B_15)
      | ~ m1_subset_1(B_15,A_14)
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_740,plain,
    ( v1_xboole_0('#skF_1'('#skF_5'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_699,c_22])).

tff(c_741,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_740])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_4691,plain,(
    ! [B_279,A_280,A_281] :
      ( r2_hidden(B_279,A_280)
      | ~ m1_subset_1(A_281,k1_zfmisc_1(A_280))
      | ~ m1_subset_1(B_279,A_281)
      | v1_xboole_0(A_281) ) ),
    inference(resolution,[status(thm)],[c_18,c_223])).

tff(c_4713,plain,(
    ! [B_279] :
      ( r2_hidden(B_279,'#skF_3')
      | ~ m1_subset_1(B_279,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_4691])).

tff(c_4749,plain,(
    ! [B_283] :
      ( r2_hidden(B_283,'#skF_3')
      | ~ m1_subset_1(B_283,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_713,c_4713])).

tff(c_4756,plain,(
    ! [B_283] :
      ( m1_subset_1(B_283,'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(B_283,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4749,c_16])).

tff(c_4862,plain,(
    ! [B_287] :
      ( m1_subset_1(B_287,'#skF_3')
      | ~ m1_subset_1(B_287,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_741,c_4756])).

tff(c_4264,plain,(
    ! [A_262] :
      ( r1_tarski(A_262,'#skF_5')
      | ~ r2_hidden('#skF_2'(A_262,'#skF_5'),'#skF_4')
      | ~ m1_subset_1('#skF_2'(A_262,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_146,c_10])).

tff(c_4287,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_4','#skF_5'),'#skF_3')
    | r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_4264])).

tff(c_4444,plain,(
    ~ m1_subset_1('#skF_2'('#skF_4','#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_4287])).

tff(c_4873,plain,(
    ~ m1_subset_1('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_4862,c_4444])).

tff(c_4880,plain,
    ( v1_xboole_0('#skF_4')
    | r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_175,c_4873])).

tff(c_4886,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_713,c_4880])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4908,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4886,c_14])).

tff(c_2407,plain,(
    ! [B_199,A_200,A_201] :
      ( r2_hidden(B_199,A_200)
      | ~ m1_subset_1(A_201,k1_zfmisc_1(A_200))
      | ~ m1_subset_1(B_199,A_201)
      | v1_xboole_0(A_201) ) ),
    inference(resolution,[status(thm)],[c_18,c_223])).

tff(c_2438,plain,(
    ! [B_199] :
      ( r2_hidden(B_199,'#skF_3')
      | ~ m1_subset_1(B_199,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_2407])).

tff(c_2508,plain,(
    ! [B_204] :
      ( r2_hidden(B_204,'#skF_3')
      | ~ m1_subset_1(B_204,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_713,c_2438])).

tff(c_2515,plain,(
    ! [B_204] :
      ( m1_subset_1(B_204,'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(B_204,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2508,c_16])).

tff(c_2651,plain,(
    ! [B_209] :
      ( m1_subset_1(B_209,'#skF_3')
      | ~ m1_subset_1(B_209,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_741,c_2515])).

tff(c_2120,plain,(
    ! [A_191] :
      ( r1_tarski(A_191,'#skF_5')
      | ~ r2_hidden('#skF_2'(A_191,'#skF_5'),'#skF_4')
      | ~ m1_subset_1('#skF_2'(A_191,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_146,c_10])).

tff(c_2143,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_4','#skF_5'),'#skF_3')
    | r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_2120])).

tff(c_2147,plain,(
    ~ m1_subset_1('#skF_2'('#skF_4','#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2143])).

tff(c_2669,plain,(
    ~ m1_subset_1('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_2651,c_2147])).

tff(c_2677,plain,
    ( v1_xboole_0('#skF_4')
    | r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_175,c_2669])).

tff(c_2683,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_713,c_2677])).

tff(c_2721,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2683,c_14])).

tff(c_2436,plain,(
    ! [B_199] :
      ( r2_hidden(B_199,'#skF_3')
      | ~ m1_subset_1(B_199,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_2407])).

tff(c_2486,plain,(
    ! [B_203] :
      ( r2_hidden(B_203,'#skF_3')
      | ~ m1_subset_1(B_203,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_2436])).

tff(c_2493,plain,(
    ! [B_203] :
      ( m1_subset_1(B_203,'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(B_203,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2486,c_16])).

tff(c_2530,plain,(
    ! [B_205] :
      ( m1_subset_1(B_205,'#skF_3')
      | ~ m1_subset_1(B_205,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_741,c_2493])).

tff(c_2564,plain,(
    ! [B_8] :
      ( m1_subset_1('#skF_2'('#skF_5',B_8),'#skF_3')
      | v1_xboole_0('#skF_5')
      | r1_tarski('#skF_5',B_8) ) ),
    inference(resolution,[status(thm)],[c_175,c_2530])).

tff(c_3130,plain,(
    ! [B_226] :
      ( m1_subset_1('#skF_2'('#skF_5',B_226),'#skF_3')
      | r1_tarski('#skF_5',B_226) ) ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_2564])).

tff(c_32,plain,(
    ! [D_24] :
      ( r2_hidden(D_24,'#skF_4')
      | ~ r2_hidden(D_24,'#skF_5')
      | ~ m1_subset_1(D_24,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2015,plain,(
    ! [B_177] :
      ( r2_hidden('#skF_2'('#skF_5',B_177),'#skF_4')
      | ~ m1_subset_1('#skF_2'('#skF_5',B_177),'#skF_3')
      | r1_tarski('#skF_5',B_177) ) ),
    inference(resolution,[status(thm)],[c_112,c_32])).

tff(c_2042,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_5','#skF_4'),'#skF_3')
    | r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_2015,c_10])).

tff(c_2044,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2042])).

tff(c_3147,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_3130,c_2044])).

tff(c_3214,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3147,c_14])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_3218,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_3214,c_2])).

tff(c_3230,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2721,c_3218])).

tff(c_3232,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_3230])).

tff(c_3233,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_2143])).

tff(c_3271,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3233,c_14])).

tff(c_3374,plain,(
    ! [B_230,A_231,A_232] :
      ( r2_hidden(B_230,A_231)
      | ~ m1_subset_1(A_232,k1_zfmisc_1(A_231))
      | ~ m1_subset_1(B_230,A_232)
      | v1_xboole_0(A_232) ) ),
    inference(resolution,[status(thm)],[c_18,c_223])).

tff(c_3400,plain,(
    ! [B_230] :
      ( r2_hidden(B_230,'#skF_3')
      | ~ m1_subset_1(B_230,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_3374])).

tff(c_3417,plain,(
    ! [B_233] :
      ( r2_hidden(B_233,'#skF_3')
      | ~ m1_subset_1(B_233,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_3400])).

tff(c_3424,plain,(
    ! [B_233] :
      ( m1_subset_1(B_233,'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(B_233,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3417,c_16])).

tff(c_3461,plain,(
    ! [B_235] :
      ( m1_subset_1(B_235,'#skF_3')
      | ~ m1_subset_1(B_235,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_741,c_3424])).

tff(c_3491,plain,(
    ! [B_8] :
      ( m1_subset_1('#skF_2'('#skF_5',B_8),'#skF_3')
      | v1_xboole_0('#skF_5')
      | r1_tarski('#skF_5',B_8) ) ),
    inference(resolution,[status(thm)],[c_175,c_3461])).

tff(c_4143,plain,(
    ! [B_260] :
      ( m1_subset_1('#skF_2'('#skF_5',B_260),'#skF_3')
      | r1_tarski('#skF_5',B_260) ) ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_3491])).

tff(c_4154,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_4143,c_2044])).

tff(c_4227,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_4154,c_14])).

tff(c_4231,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_4227,c_2])).

tff(c_4243,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3271,c_4231])).

tff(c_4245,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_4243])).

tff(c_4246,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_2042])).

tff(c_4263,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_4246,c_14])).

tff(c_4294,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_4263,c_2])).

tff(c_4909,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4908,c_4294])).

tff(c_4911,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_4909])).

tff(c_4912,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_4287])).

tff(c_4973,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4912,c_14])).

tff(c_4974,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4973,c_4294])).

tff(c_4976,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_4974])).

tff(c_4977,plain,(
    v1_xboole_0('#skF_1'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_740])).

tff(c_141,plain,(
    ! [A_45,B_46] :
      ( ~ v1_xboole_0(A_45)
      | r1_tarski(A_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_112,c_4])).

tff(c_145,plain,(
    ! [A_45,B_46] :
      ( k3_xboole_0(A_45,B_46) = A_45
      | ~ v1_xboole_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_141,c_14])).

tff(c_5144,plain,(
    ! [B_298] : k3_xboole_0('#skF_1'('#skF_5'),B_298) = '#skF_1'('#skF_5') ),
    inference(resolution,[status(thm)],[c_4977,c_145])).

tff(c_4978,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_740])).

tff(c_5026,plain,(
    ! [B_292] : k3_xboole_0('#skF_3',B_292) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4978,c_145])).

tff(c_5035,plain,(
    ! [B_292] : k3_xboole_0(B_292,'#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_5026,c_2])).

tff(c_5149,plain,(
    '#skF_1'('#skF_5') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_5144,c_5035])).

tff(c_5185,plain,(
    m1_subset_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5149,c_699])).

tff(c_5186,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5149,c_698])).

tff(c_8,plain,(
    ! [C_11,B_8,A_7] :
      ( r2_hidden(C_11,B_8)
      | ~ r2_hidden(C_11,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_5277,plain,(
    ! [B_8] :
      ( r2_hidden('#skF_3',B_8)
      | ~ r1_tarski('#skF_4',B_8) ) ),
    inference(resolution,[status(thm)],[c_5186,c_8])).

tff(c_34,plain,(
    ! [D_24] :
      ( r2_hidden(D_24,'#skF_5')
      | ~ r2_hidden(D_24,'#skF_4')
      | ~ m1_subset_1(D_24,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_5304,plain,(
    ! [D_301,A_302] :
      ( r2_hidden(D_301,A_302)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_302))
      | ~ r2_hidden(D_301,'#skF_4')
      | ~ m1_subset_1(D_301,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_223])).

tff(c_5409,plain,(
    ! [D_308] :
      ( r2_hidden(D_308,'#skF_3')
      | ~ r2_hidden(D_308,'#skF_4')
      | ~ m1_subset_1(D_308,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_5304])).

tff(c_5423,plain,(
    ! [D_308] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(D_308,'#skF_4')
      | ~ m1_subset_1(D_308,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_5409,c_4])).

tff(c_5443,plain,(
    ! [D_310] :
      ( ~ r2_hidden(D_310,'#skF_4')
      | ~ m1_subset_1(D_310,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4978,c_5423])).

tff(c_5451,plain,
    ( ~ m1_subset_1('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_5277,c_5443])).

tff(c_5484,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_5185,c_5451])).

tff(c_5581,plain,(
    ! [D_316] :
      ( ~ r2_hidden(D_316,'#skF_4')
      | ~ m1_subset_1(D_316,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_5596,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_4'),'#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_5581])).

tff(c_5597,plain,(
    ~ m1_subset_1('#skF_1'('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_5596])).

tff(c_5601,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_4'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_5597])).

tff(c_5602,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_5601])).

tff(c_5595,plain,(
    ! [B_15] :
      ( ~ m1_subset_1(B_15,'#skF_3')
      | ~ m1_subset_1(B_15,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_5581])).

tff(c_5619,plain,(
    ! [B_321] :
      ( ~ m1_subset_1(B_321,'#skF_3')
      | ~ m1_subset_1(B_321,'#skF_4') ) ),
    inference(splitLeft,[status(thm)],[c_5595])).

tff(c_5623,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_3'),'#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_177,c_5619])).

tff(c_5630,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_5602,c_5623])).

tff(c_5636,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_3'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_5630])).

tff(c_5637,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5636])).

tff(c_5603,plain,(
    ! [C_317,A_318,B_319] :
      ( r2_hidden(C_317,A_318)
      | ~ r2_hidden(C_317,B_319)
      | ~ m1_subset_1(B_319,k1_zfmisc_1(A_318)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_5923,plain,(
    ! [B_353,A_354,A_355] :
      ( r2_hidden(B_353,A_354)
      | ~ m1_subset_1(A_355,k1_zfmisc_1(A_354))
      | ~ m1_subset_1(B_353,A_355)
      | v1_xboole_0(A_355) ) ),
    inference(resolution,[status(thm)],[c_18,c_5603])).

tff(c_5939,plain,(
    ! [B_353] :
      ( r2_hidden(B_353,'#skF_3')
      | ~ m1_subset_1(B_353,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_5923])).

tff(c_5949,plain,(
    ! [B_356] :
      ( r2_hidden(B_356,'#skF_3')
      | ~ m1_subset_1(B_356,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_5637,c_5939])).

tff(c_5956,plain,(
    ! [B_356] :
      ( m1_subset_1(B_356,'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(B_356,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5949,c_16])).

tff(c_5971,plain,(
    ! [B_357] :
      ( m1_subset_1(B_357,'#skF_3')
      | ~ m1_subset_1(B_357,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_5602,c_5956])).

tff(c_5618,plain,(
    ! [B_15] :
      ( ~ m1_subset_1(B_15,'#skF_3')
      | ~ m1_subset_1(B_15,'#skF_4') ) ),
    inference(splitLeft,[status(thm)],[c_5595])).

tff(c_6007,plain,(
    ! [B_358] : ~ m1_subset_1(B_358,'#skF_4') ),
    inference(resolution,[status(thm)],[c_5971,c_5618])).

tff(c_6019,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_177,c_6007])).

tff(c_6033,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5637,c_6019])).

tff(c_6035,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_5636])).

tff(c_6040,plain,(
    ! [B_359] : k3_xboole_0('#skF_4',B_359) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6035,c_145])).

tff(c_5486,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_5490,plain,(
    ! [B_311] : k3_xboole_0('#skF_5',B_311) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_5486,c_145])).

tff(c_5499,plain,(
    ! [B_311] : k3_xboole_0(B_311,'#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_5490,c_2])).

tff(c_6045,plain,(
    '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_6040,c_5499])).

tff(c_6075,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_6045])).

tff(c_6076,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_5595])).

tff(c_6080,plain,(
    ! [B_360] : k3_xboole_0('#skF_4',B_360) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6076,c_145])).

tff(c_6085,plain,(
    '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_6080,c_5499])).

tff(c_6115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_6085])).

tff(c_6117,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_5601])).

tff(c_6131,plain,(
    ! [B_364] : k3_xboole_0('#skF_3',B_364) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6117,c_145])).

tff(c_6136,plain,(
    '#skF_5' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_6131,c_5499])).

tff(c_6174,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6136,c_26])).

tff(c_6320,plain,(
    ! [B_375] :
      ( ~ m1_subset_1(B_375,'#skF_3')
      | ~ m1_subset_1(B_375,'#skF_4') ) ),
    inference(splitLeft,[status(thm)],[c_5595])).

tff(c_6328,plain,(
    ! [B_15] :
      ( ~ m1_subset_1(B_15,'#skF_4')
      | ~ v1_xboole_0(B_15)
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_6320])).

tff(c_6334,plain,(
    ! [B_376] :
      ( ~ m1_subset_1(B_376,'#skF_4')
      | ~ v1_xboole_0(B_376) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6117,c_6328])).

tff(c_6344,plain,(
    ! [B_15] :
      ( ~ v1_xboole_0(B_15)
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_20,c_6334])).

tff(c_6345,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_6344])).

tff(c_6118,plain,(
    ! [C_361,A_362,B_363] :
      ( r2_hidden(C_361,A_362)
      | ~ r2_hidden(C_361,B_363)
      | ~ m1_subset_1(B_363,k1_zfmisc_1(A_362)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6295,plain,(
    ! [A_373,A_374] :
      ( r2_hidden('#skF_1'(A_373),A_374)
      | ~ m1_subset_1(A_373,k1_zfmisc_1(A_374))
      | v1_xboole_0(A_373) ) ),
    inference(resolution,[status(thm)],[c_6,c_6118])).

tff(c_6347,plain,(
    ! [A_377,A_378] :
      ( ~ v1_xboole_0(A_377)
      | ~ m1_subset_1(A_378,k1_zfmisc_1(A_377))
      | v1_xboole_0(A_378) ) ),
    inference(resolution,[status(thm)],[c_6295,c_4])).

tff(c_6361,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_6347])).

tff(c_6369,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6117,c_6361])).

tff(c_6371,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6345,c_6369])).

tff(c_6372,plain,(
    ! [B_15] : ~ v1_xboole_0(B_15) ),
    inference(splitRight,[status(thm)],[c_6344])).

tff(c_6373,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_6344])).

tff(c_6387,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6372,c_6373])).

tff(c_6388,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_5595])).

tff(c_6417,plain,(
    ! [B_381] : k3_xboole_0('#skF_4',B_381) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6388,c_145])).

tff(c_6146,plain,(
    ! [B_364] : k3_xboole_0(B_364,'#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_6131,c_2])).

tff(c_6422,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_6417,c_6146])).

tff(c_6452,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6174,c_6422])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:43:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.92/2.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.04/2.15  
% 6.04/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.04/2.15  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 6.04/2.15  
% 6.04/2.15  %Foreground sorts:
% 6.04/2.15  
% 6.04/2.15  
% 6.04/2.15  %Background operators:
% 6.04/2.15  
% 6.04/2.15  
% 6.04/2.15  %Foreground operators:
% 6.04/2.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.04/2.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.04/2.15  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.04/2.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.04/2.15  tff('#skF_5', type, '#skF_5': $i).
% 6.04/2.15  tff('#skF_3', type, '#skF_3': $i).
% 6.04/2.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.04/2.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.04/2.15  tff('#skF_4', type, '#skF_4': $i).
% 6.04/2.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.04/2.15  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.04/2.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.04/2.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.04/2.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.04/2.15  
% 6.04/2.18  tff(f_79, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_subset_1)).
% 6.04/2.18  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 6.04/2.18  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.04/2.18  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.04/2.18  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 6.04/2.18  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.04/2.18  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.04/2.18  tff(c_26, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.04/2.18  tff(c_20, plain, (![B_15, A_14]: (m1_subset_1(B_15, A_14) | ~v1_xboole_0(B_15) | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.04/2.18  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.04/2.18  tff(c_112, plain, (![A_41, B_42]: (r2_hidden('#skF_2'(A_41, B_42), A_41) | r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.04/2.18  tff(c_10, plain, (![A_7, B_8]: (~r2_hidden('#skF_2'(A_7, B_8), B_8) | r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.04/2.18  tff(c_124, plain, (![A_41]: (r1_tarski(A_41, A_41))), inference(resolution, [status(thm)], [c_112, c_10])).
% 6.04/2.18  tff(c_146, plain, (![D_47]: (r2_hidden(D_47, '#skF_5') | ~r2_hidden(D_47, '#skF_4') | ~m1_subset_1(D_47, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.04/2.18  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.04/2.18  tff(c_159, plain, (![D_47]: (~v1_xboole_0('#skF_5') | ~r2_hidden(D_47, '#skF_4') | ~m1_subset_1(D_47, '#skF_3'))), inference(resolution, [status(thm)], [c_146, c_4])).
% 6.04/2.18  tff(c_183, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_159])).
% 6.04/2.18  tff(c_84, plain, (![D_32]: (r2_hidden(D_32, '#skF_4') | ~r2_hidden(D_32, '#skF_5') | ~m1_subset_1(D_32, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.04/2.18  tff(c_89, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_5'), '#skF_3') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_6, c_84])).
% 6.04/2.18  tff(c_239, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_183, c_89])).
% 6.04/2.18  tff(c_240, plain, (~m1_subset_1('#skF_1'('#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_239])).
% 6.04/2.18  tff(c_161, plain, (![B_50, A_51]: (m1_subset_1(B_50, A_51) | ~r2_hidden(B_50, A_51) | v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.04/2.18  tff(c_177, plain, (![A_3]: (m1_subset_1('#skF_1'(A_3), A_3) | v1_xboole_0(A_3))), inference(resolution, [status(thm)], [c_6, c_161])).
% 6.04/2.18  tff(c_244, plain, (~v1_xboole_0('#skF_1'('#skF_5')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_20, c_240])).
% 6.04/2.18  tff(c_245, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_244])).
% 6.04/2.18  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.04/2.18  tff(c_18, plain, (![B_15, A_14]: (r2_hidden(B_15, A_14) | ~m1_subset_1(B_15, A_14) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.04/2.18  tff(c_223, plain, (![C_60, A_61, B_62]: (r2_hidden(C_60, A_61) | ~r2_hidden(C_60, B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.04/2.18  tff(c_413, plain, (![B_83, A_84, A_85]: (r2_hidden(B_83, A_84) | ~m1_subset_1(A_85, k1_zfmisc_1(A_84)) | ~m1_subset_1(B_83, A_85) | v1_xboole_0(A_85))), inference(resolution, [status(thm)], [c_18, c_223])).
% 6.04/2.18  tff(c_424, plain, (![B_83]: (r2_hidden(B_83, '#skF_3') | ~m1_subset_1(B_83, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_28, c_413])).
% 6.04/2.18  tff(c_434, plain, (![B_86]: (r2_hidden(B_86, '#skF_3') | ~m1_subset_1(B_86, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_183, c_424])).
% 6.04/2.18  tff(c_16, plain, (![B_15, A_14]: (m1_subset_1(B_15, A_14) | ~r2_hidden(B_15, A_14) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.04/2.18  tff(c_441, plain, (![B_86]: (m1_subset_1(B_86, '#skF_3') | v1_xboole_0('#skF_3') | ~m1_subset_1(B_86, '#skF_5'))), inference(resolution, [status(thm)], [c_434, c_16])).
% 6.04/2.18  tff(c_456, plain, (![B_87]: (m1_subset_1(B_87, '#skF_3') | ~m1_subset_1(B_87, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_245, c_441])).
% 6.04/2.18  tff(c_464, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_3') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_177, c_456])).
% 6.04/2.18  tff(c_475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_183, c_240, c_464])).
% 6.04/2.18  tff(c_477, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_244])).
% 6.04/2.18  tff(c_646, plain, (![A_97, A_98]: (r2_hidden('#skF_1'(A_97), A_98) | ~m1_subset_1(A_97, k1_zfmisc_1(A_98)) | v1_xboole_0(A_97))), inference(resolution, [status(thm)], [c_6, c_223])).
% 6.04/2.18  tff(c_671, plain, (![A_99, A_100]: (~v1_xboole_0(A_99) | ~m1_subset_1(A_100, k1_zfmisc_1(A_99)) | v1_xboole_0(A_100))), inference(resolution, [status(thm)], [c_646, c_4])).
% 6.04/2.18  tff(c_686, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_28, c_671])).
% 6.04/2.18  tff(c_695, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_477, c_686])).
% 6.04/2.18  tff(c_697, plain, $false, inference(negUnitSimplification, [status(thm)], [c_183, c_695])).
% 6.04/2.18  tff(c_698, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_239])).
% 6.04/2.18  tff(c_713, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_698, c_4])).
% 6.04/2.18  tff(c_12, plain, (![A_7, B_8]: (r2_hidden('#skF_2'(A_7, B_8), A_7) | r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.04/2.18  tff(c_175, plain, (![A_7, B_8]: (m1_subset_1('#skF_2'(A_7, B_8), A_7) | v1_xboole_0(A_7) | r1_tarski(A_7, B_8))), inference(resolution, [status(thm)], [c_12, c_161])).
% 6.04/2.18  tff(c_699, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_239])).
% 6.04/2.18  tff(c_22, plain, (![B_15, A_14]: (v1_xboole_0(B_15) | ~m1_subset_1(B_15, A_14) | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.04/2.18  tff(c_740, plain, (v1_xboole_0('#skF_1'('#skF_5')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_699, c_22])).
% 6.04/2.18  tff(c_741, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_740])).
% 6.04/2.18  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.04/2.18  tff(c_4691, plain, (![B_279, A_280, A_281]: (r2_hidden(B_279, A_280) | ~m1_subset_1(A_281, k1_zfmisc_1(A_280)) | ~m1_subset_1(B_279, A_281) | v1_xboole_0(A_281))), inference(resolution, [status(thm)], [c_18, c_223])).
% 6.04/2.18  tff(c_4713, plain, (![B_279]: (r2_hidden(B_279, '#skF_3') | ~m1_subset_1(B_279, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_4691])).
% 6.04/2.18  tff(c_4749, plain, (![B_283]: (r2_hidden(B_283, '#skF_3') | ~m1_subset_1(B_283, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_713, c_4713])).
% 6.04/2.18  tff(c_4756, plain, (![B_283]: (m1_subset_1(B_283, '#skF_3') | v1_xboole_0('#skF_3') | ~m1_subset_1(B_283, '#skF_4'))), inference(resolution, [status(thm)], [c_4749, c_16])).
% 6.04/2.18  tff(c_4862, plain, (![B_287]: (m1_subset_1(B_287, '#skF_3') | ~m1_subset_1(B_287, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_741, c_4756])).
% 6.04/2.18  tff(c_4264, plain, (![A_262]: (r1_tarski(A_262, '#skF_5') | ~r2_hidden('#skF_2'(A_262, '#skF_5'), '#skF_4') | ~m1_subset_1('#skF_2'(A_262, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_146, c_10])).
% 6.04/2.18  tff(c_4287, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_5'), '#skF_3') | r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_12, c_4264])).
% 6.04/2.18  tff(c_4444, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_4287])).
% 6.04/2.18  tff(c_4873, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_4862, c_4444])).
% 6.04/2.18  tff(c_4880, plain, (v1_xboole_0('#skF_4') | r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_175, c_4873])).
% 6.04/2.18  tff(c_4886, plain, (r1_tarski('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_713, c_4880])).
% 6.04/2.18  tff(c_14, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.04/2.18  tff(c_4908, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_4886, c_14])).
% 6.04/2.18  tff(c_2407, plain, (![B_199, A_200, A_201]: (r2_hidden(B_199, A_200) | ~m1_subset_1(A_201, k1_zfmisc_1(A_200)) | ~m1_subset_1(B_199, A_201) | v1_xboole_0(A_201))), inference(resolution, [status(thm)], [c_18, c_223])).
% 6.04/2.18  tff(c_2438, plain, (![B_199]: (r2_hidden(B_199, '#skF_3') | ~m1_subset_1(B_199, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_2407])).
% 6.04/2.18  tff(c_2508, plain, (![B_204]: (r2_hidden(B_204, '#skF_3') | ~m1_subset_1(B_204, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_713, c_2438])).
% 6.04/2.18  tff(c_2515, plain, (![B_204]: (m1_subset_1(B_204, '#skF_3') | v1_xboole_0('#skF_3') | ~m1_subset_1(B_204, '#skF_4'))), inference(resolution, [status(thm)], [c_2508, c_16])).
% 6.04/2.18  tff(c_2651, plain, (![B_209]: (m1_subset_1(B_209, '#skF_3') | ~m1_subset_1(B_209, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_741, c_2515])).
% 6.04/2.18  tff(c_2120, plain, (![A_191]: (r1_tarski(A_191, '#skF_5') | ~r2_hidden('#skF_2'(A_191, '#skF_5'), '#skF_4') | ~m1_subset_1('#skF_2'(A_191, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_146, c_10])).
% 6.04/2.18  tff(c_2143, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_5'), '#skF_3') | r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_12, c_2120])).
% 6.04/2.18  tff(c_2147, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_2143])).
% 6.04/2.18  tff(c_2669, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_2651, c_2147])).
% 6.04/2.18  tff(c_2677, plain, (v1_xboole_0('#skF_4') | r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_175, c_2669])).
% 6.04/2.18  tff(c_2683, plain, (r1_tarski('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_713, c_2677])).
% 6.04/2.18  tff(c_2721, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_2683, c_14])).
% 6.04/2.18  tff(c_2436, plain, (![B_199]: (r2_hidden(B_199, '#skF_3') | ~m1_subset_1(B_199, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_28, c_2407])).
% 6.04/2.18  tff(c_2486, plain, (![B_203]: (r2_hidden(B_203, '#skF_3') | ~m1_subset_1(B_203, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_183, c_2436])).
% 6.04/2.18  tff(c_2493, plain, (![B_203]: (m1_subset_1(B_203, '#skF_3') | v1_xboole_0('#skF_3') | ~m1_subset_1(B_203, '#skF_5'))), inference(resolution, [status(thm)], [c_2486, c_16])).
% 6.04/2.18  tff(c_2530, plain, (![B_205]: (m1_subset_1(B_205, '#skF_3') | ~m1_subset_1(B_205, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_741, c_2493])).
% 6.04/2.18  tff(c_2564, plain, (![B_8]: (m1_subset_1('#skF_2'('#skF_5', B_8), '#skF_3') | v1_xboole_0('#skF_5') | r1_tarski('#skF_5', B_8))), inference(resolution, [status(thm)], [c_175, c_2530])).
% 6.04/2.18  tff(c_3130, plain, (![B_226]: (m1_subset_1('#skF_2'('#skF_5', B_226), '#skF_3') | r1_tarski('#skF_5', B_226))), inference(negUnitSimplification, [status(thm)], [c_183, c_2564])).
% 6.04/2.18  tff(c_32, plain, (![D_24]: (r2_hidden(D_24, '#skF_4') | ~r2_hidden(D_24, '#skF_5') | ~m1_subset_1(D_24, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.04/2.18  tff(c_2015, plain, (![B_177]: (r2_hidden('#skF_2'('#skF_5', B_177), '#skF_4') | ~m1_subset_1('#skF_2'('#skF_5', B_177), '#skF_3') | r1_tarski('#skF_5', B_177))), inference(resolution, [status(thm)], [c_112, c_32])).
% 6.04/2.18  tff(c_2042, plain, (~m1_subset_1('#skF_2'('#skF_5', '#skF_4'), '#skF_3') | r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_2015, c_10])).
% 6.04/2.18  tff(c_2044, plain, (~m1_subset_1('#skF_2'('#skF_5', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_2042])).
% 6.04/2.18  tff(c_3147, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_3130, c_2044])).
% 6.04/2.18  tff(c_3214, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_3147, c_14])).
% 6.04/2.18  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.04/2.18  tff(c_3218, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_3214, c_2])).
% 6.04/2.18  tff(c_3230, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2721, c_3218])).
% 6.04/2.18  tff(c_3232, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_3230])).
% 6.04/2.18  tff(c_3233, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_2143])).
% 6.04/2.18  tff(c_3271, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_3233, c_14])).
% 6.04/2.18  tff(c_3374, plain, (![B_230, A_231, A_232]: (r2_hidden(B_230, A_231) | ~m1_subset_1(A_232, k1_zfmisc_1(A_231)) | ~m1_subset_1(B_230, A_232) | v1_xboole_0(A_232))), inference(resolution, [status(thm)], [c_18, c_223])).
% 6.04/2.18  tff(c_3400, plain, (![B_230]: (r2_hidden(B_230, '#skF_3') | ~m1_subset_1(B_230, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_28, c_3374])).
% 6.04/2.18  tff(c_3417, plain, (![B_233]: (r2_hidden(B_233, '#skF_3') | ~m1_subset_1(B_233, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_183, c_3400])).
% 6.04/2.18  tff(c_3424, plain, (![B_233]: (m1_subset_1(B_233, '#skF_3') | v1_xboole_0('#skF_3') | ~m1_subset_1(B_233, '#skF_5'))), inference(resolution, [status(thm)], [c_3417, c_16])).
% 6.04/2.18  tff(c_3461, plain, (![B_235]: (m1_subset_1(B_235, '#skF_3') | ~m1_subset_1(B_235, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_741, c_3424])).
% 6.04/2.18  tff(c_3491, plain, (![B_8]: (m1_subset_1('#skF_2'('#skF_5', B_8), '#skF_3') | v1_xboole_0('#skF_5') | r1_tarski('#skF_5', B_8))), inference(resolution, [status(thm)], [c_175, c_3461])).
% 6.04/2.18  tff(c_4143, plain, (![B_260]: (m1_subset_1('#skF_2'('#skF_5', B_260), '#skF_3') | r1_tarski('#skF_5', B_260))), inference(negUnitSimplification, [status(thm)], [c_183, c_3491])).
% 6.04/2.18  tff(c_4154, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_4143, c_2044])).
% 6.04/2.18  tff(c_4227, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_4154, c_14])).
% 6.04/2.18  tff(c_4231, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_4227, c_2])).
% 6.04/2.18  tff(c_4243, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3271, c_4231])).
% 6.04/2.18  tff(c_4245, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_4243])).
% 6.04/2.18  tff(c_4246, plain, (r1_tarski('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_2042])).
% 6.04/2.18  tff(c_4263, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_4246, c_14])).
% 6.04/2.18  tff(c_4294, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_4263, c_2])).
% 6.04/2.18  tff(c_4909, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4908, c_4294])).
% 6.04/2.18  tff(c_4911, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_4909])).
% 6.04/2.18  tff(c_4912, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_4287])).
% 6.04/2.18  tff(c_4973, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_4912, c_14])).
% 6.04/2.18  tff(c_4974, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4973, c_4294])).
% 6.04/2.18  tff(c_4976, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_4974])).
% 6.04/2.18  tff(c_4977, plain, (v1_xboole_0('#skF_1'('#skF_5'))), inference(splitRight, [status(thm)], [c_740])).
% 6.04/2.18  tff(c_141, plain, (![A_45, B_46]: (~v1_xboole_0(A_45) | r1_tarski(A_45, B_46))), inference(resolution, [status(thm)], [c_112, c_4])).
% 6.04/2.18  tff(c_145, plain, (![A_45, B_46]: (k3_xboole_0(A_45, B_46)=A_45 | ~v1_xboole_0(A_45))), inference(resolution, [status(thm)], [c_141, c_14])).
% 6.04/2.18  tff(c_5144, plain, (![B_298]: (k3_xboole_0('#skF_1'('#skF_5'), B_298)='#skF_1'('#skF_5'))), inference(resolution, [status(thm)], [c_4977, c_145])).
% 6.04/2.18  tff(c_4978, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_740])).
% 6.04/2.18  tff(c_5026, plain, (![B_292]: (k3_xboole_0('#skF_3', B_292)='#skF_3')), inference(resolution, [status(thm)], [c_4978, c_145])).
% 6.04/2.18  tff(c_5035, plain, (![B_292]: (k3_xboole_0(B_292, '#skF_3')='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5026, c_2])).
% 6.04/2.18  tff(c_5149, plain, ('#skF_1'('#skF_5')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_5144, c_5035])).
% 6.04/2.18  tff(c_5185, plain, (m1_subset_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5149, c_699])).
% 6.04/2.18  tff(c_5186, plain, (r2_hidden('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5149, c_698])).
% 6.04/2.18  tff(c_8, plain, (![C_11, B_8, A_7]: (r2_hidden(C_11, B_8) | ~r2_hidden(C_11, A_7) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.04/2.18  tff(c_5277, plain, (![B_8]: (r2_hidden('#skF_3', B_8) | ~r1_tarski('#skF_4', B_8))), inference(resolution, [status(thm)], [c_5186, c_8])).
% 6.04/2.18  tff(c_34, plain, (![D_24]: (r2_hidden(D_24, '#skF_5') | ~r2_hidden(D_24, '#skF_4') | ~m1_subset_1(D_24, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.04/2.18  tff(c_5304, plain, (![D_301, A_302]: (r2_hidden(D_301, A_302) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_302)) | ~r2_hidden(D_301, '#skF_4') | ~m1_subset_1(D_301, '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_223])).
% 6.04/2.18  tff(c_5409, plain, (![D_308]: (r2_hidden(D_308, '#skF_3') | ~r2_hidden(D_308, '#skF_4') | ~m1_subset_1(D_308, '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_5304])).
% 6.04/2.18  tff(c_5423, plain, (![D_308]: (~v1_xboole_0('#skF_3') | ~r2_hidden(D_308, '#skF_4') | ~m1_subset_1(D_308, '#skF_3'))), inference(resolution, [status(thm)], [c_5409, c_4])).
% 6.04/2.18  tff(c_5443, plain, (![D_310]: (~r2_hidden(D_310, '#skF_4') | ~m1_subset_1(D_310, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4978, c_5423])).
% 6.04/2.18  tff(c_5451, plain, (~m1_subset_1('#skF_3', '#skF_3') | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_5277, c_5443])).
% 6.04/2.18  tff(c_5484, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_5185, c_5451])).
% 6.04/2.18  tff(c_5581, plain, (![D_316]: (~r2_hidden(D_316, '#skF_4') | ~m1_subset_1(D_316, '#skF_3'))), inference(splitRight, [status(thm)], [c_159])).
% 6.04/2.18  tff(c_5596, plain, (~m1_subset_1('#skF_1'('#skF_4'), '#skF_3') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_6, c_5581])).
% 6.04/2.18  tff(c_5597, plain, (~m1_subset_1('#skF_1'('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_5596])).
% 6.04/2.18  tff(c_5601, plain, (~v1_xboole_0('#skF_1'('#skF_4')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_20, c_5597])).
% 6.04/2.18  tff(c_5602, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_5601])).
% 6.04/2.18  tff(c_5595, plain, (![B_15]: (~m1_subset_1(B_15, '#skF_3') | ~m1_subset_1(B_15, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_5581])).
% 6.04/2.18  tff(c_5619, plain, (![B_321]: (~m1_subset_1(B_321, '#skF_3') | ~m1_subset_1(B_321, '#skF_4'))), inference(splitLeft, [status(thm)], [c_5595])).
% 6.04/2.18  tff(c_5623, plain, (~m1_subset_1('#skF_1'('#skF_3'), '#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_177, c_5619])).
% 6.04/2.18  tff(c_5630, plain, (~m1_subset_1('#skF_1'('#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_5602, c_5623])).
% 6.04/2.18  tff(c_5636, plain, (~v1_xboole_0('#skF_1'('#skF_3')) | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_20, c_5630])).
% 6.04/2.18  tff(c_5637, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_5636])).
% 6.04/2.18  tff(c_5603, plain, (![C_317, A_318, B_319]: (r2_hidden(C_317, A_318) | ~r2_hidden(C_317, B_319) | ~m1_subset_1(B_319, k1_zfmisc_1(A_318)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.04/2.18  tff(c_5923, plain, (![B_353, A_354, A_355]: (r2_hidden(B_353, A_354) | ~m1_subset_1(A_355, k1_zfmisc_1(A_354)) | ~m1_subset_1(B_353, A_355) | v1_xboole_0(A_355))), inference(resolution, [status(thm)], [c_18, c_5603])).
% 6.04/2.18  tff(c_5939, plain, (![B_353]: (r2_hidden(B_353, '#skF_3') | ~m1_subset_1(B_353, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_5923])).
% 6.04/2.18  tff(c_5949, plain, (![B_356]: (r2_hidden(B_356, '#skF_3') | ~m1_subset_1(B_356, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_5637, c_5939])).
% 6.04/2.18  tff(c_5956, plain, (![B_356]: (m1_subset_1(B_356, '#skF_3') | v1_xboole_0('#skF_3') | ~m1_subset_1(B_356, '#skF_4'))), inference(resolution, [status(thm)], [c_5949, c_16])).
% 6.04/2.18  tff(c_5971, plain, (![B_357]: (m1_subset_1(B_357, '#skF_3') | ~m1_subset_1(B_357, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_5602, c_5956])).
% 6.04/2.18  tff(c_5618, plain, (![B_15]: (~m1_subset_1(B_15, '#skF_3') | ~m1_subset_1(B_15, '#skF_4'))), inference(splitLeft, [status(thm)], [c_5595])).
% 6.04/2.18  tff(c_6007, plain, (![B_358]: (~m1_subset_1(B_358, '#skF_4'))), inference(resolution, [status(thm)], [c_5971, c_5618])).
% 6.04/2.18  tff(c_6019, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_177, c_6007])).
% 6.04/2.18  tff(c_6033, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5637, c_6019])).
% 6.04/2.18  tff(c_6035, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_5636])).
% 6.04/2.18  tff(c_6040, plain, (![B_359]: (k3_xboole_0('#skF_4', B_359)='#skF_4')), inference(resolution, [status(thm)], [c_6035, c_145])).
% 6.04/2.18  tff(c_5486, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_159])).
% 6.04/2.18  tff(c_5490, plain, (![B_311]: (k3_xboole_0('#skF_5', B_311)='#skF_5')), inference(resolution, [status(thm)], [c_5486, c_145])).
% 6.04/2.18  tff(c_5499, plain, (![B_311]: (k3_xboole_0(B_311, '#skF_5')='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5490, c_2])).
% 6.04/2.18  tff(c_6045, plain, ('#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_6040, c_5499])).
% 6.04/2.18  tff(c_6075, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_6045])).
% 6.04/2.18  tff(c_6076, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_5595])).
% 6.04/2.18  tff(c_6080, plain, (![B_360]: (k3_xboole_0('#skF_4', B_360)='#skF_4')), inference(resolution, [status(thm)], [c_6076, c_145])).
% 6.04/2.18  tff(c_6085, plain, ('#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_6080, c_5499])).
% 6.04/2.18  tff(c_6115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_6085])).
% 6.04/2.18  tff(c_6117, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_5601])).
% 6.04/2.18  tff(c_6131, plain, (![B_364]: (k3_xboole_0('#skF_3', B_364)='#skF_3')), inference(resolution, [status(thm)], [c_6117, c_145])).
% 6.04/2.18  tff(c_6136, plain, ('#skF_5'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_6131, c_5499])).
% 6.04/2.18  tff(c_6174, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6136, c_26])).
% 6.04/2.18  tff(c_6320, plain, (![B_375]: (~m1_subset_1(B_375, '#skF_3') | ~m1_subset_1(B_375, '#skF_4'))), inference(splitLeft, [status(thm)], [c_5595])).
% 6.04/2.18  tff(c_6328, plain, (![B_15]: (~m1_subset_1(B_15, '#skF_4') | ~v1_xboole_0(B_15) | ~v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_6320])).
% 6.04/2.18  tff(c_6334, plain, (![B_376]: (~m1_subset_1(B_376, '#skF_4') | ~v1_xboole_0(B_376))), inference(demodulation, [status(thm), theory('equality')], [c_6117, c_6328])).
% 6.04/2.18  tff(c_6344, plain, (![B_15]: (~v1_xboole_0(B_15) | ~v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_20, c_6334])).
% 6.04/2.18  tff(c_6345, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_6344])).
% 6.04/2.18  tff(c_6118, plain, (![C_361, A_362, B_363]: (r2_hidden(C_361, A_362) | ~r2_hidden(C_361, B_363) | ~m1_subset_1(B_363, k1_zfmisc_1(A_362)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.04/2.18  tff(c_6295, plain, (![A_373, A_374]: (r2_hidden('#skF_1'(A_373), A_374) | ~m1_subset_1(A_373, k1_zfmisc_1(A_374)) | v1_xboole_0(A_373))), inference(resolution, [status(thm)], [c_6, c_6118])).
% 6.04/2.18  tff(c_6347, plain, (![A_377, A_378]: (~v1_xboole_0(A_377) | ~m1_subset_1(A_378, k1_zfmisc_1(A_377)) | v1_xboole_0(A_378))), inference(resolution, [status(thm)], [c_6295, c_4])).
% 6.04/2.18  tff(c_6361, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_30, c_6347])).
% 6.04/2.18  tff(c_6369, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6117, c_6361])).
% 6.04/2.18  tff(c_6371, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6345, c_6369])).
% 6.04/2.18  tff(c_6372, plain, (![B_15]: (~v1_xboole_0(B_15))), inference(splitRight, [status(thm)], [c_6344])).
% 6.04/2.18  tff(c_6373, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_6344])).
% 6.04/2.18  tff(c_6387, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6372, c_6373])).
% 6.04/2.18  tff(c_6388, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_5595])).
% 6.04/2.18  tff(c_6417, plain, (![B_381]: (k3_xboole_0('#skF_4', B_381)='#skF_4')), inference(resolution, [status(thm)], [c_6388, c_145])).
% 6.04/2.18  tff(c_6146, plain, (![B_364]: (k3_xboole_0(B_364, '#skF_3')='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6131, c_2])).
% 6.04/2.18  tff(c_6422, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_6417, c_6146])).
% 6.04/2.18  tff(c_6452, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6174, c_6422])).
% 6.04/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.04/2.18  
% 6.04/2.18  Inference rules
% 6.04/2.18  ----------------------
% 6.04/2.18  #Ref     : 0
% 6.04/2.18  #Sup     : 1388
% 6.04/2.18  #Fact    : 0
% 6.04/2.18  #Define  : 0
% 6.04/2.18  #Split   : 20
% 6.04/2.18  #Chain   : 0
% 6.04/2.18  #Close   : 0
% 6.04/2.18  
% 6.04/2.18  Ordering : KBO
% 6.04/2.18  
% 6.04/2.18  Simplification rules
% 6.04/2.18  ----------------------
% 6.04/2.18  #Subsume      : 296
% 6.04/2.18  #Demod        : 378
% 6.04/2.18  #Tautology    : 357
% 6.04/2.18  #SimpNegUnit  : 222
% 6.04/2.18  #BackRed      : 22
% 6.04/2.18  
% 6.04/2.18  #Partial instantiations: 0
% 6.04/2.18  #Strategies tried      : 1
% 6.04/2.18  
% 6.04/2.18  Timing (in seconds)
% 6.04/2.18  ----------------------
% 6.04/2.18  Preprocessing        : 0.30
% 6.04/2.18  Parsing              : 0.16
% 6.04/2.18  CNF conversion       : 0.02
% 6.04/2.18  Main loop            : 1.04
% 6.04/2.18  Inferencing          : 0.36
% 6.04/2.18  Reduction            : 0.31
% 6.04/2.18  Demodulation         : 0.20
% 6.04/2.18  BG Simplification    : 0.04
% 6.04/2.18  Subsumption          : 0.25
% 6.04/2.18  Abstraction          : 0.04
% 6.04/2.18  MUC search           : 0.00
% 6.04/2.18  Cooper               : 0.00
% 6.04/2.18  Total                : 1.41
% 6.04/2.18  Index Insertion      : 0.00
% 6.04/2.18  Index Deletion       : 0.00
% 6.04/2.18  Index Matching       : 0.00
% 6.04/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
