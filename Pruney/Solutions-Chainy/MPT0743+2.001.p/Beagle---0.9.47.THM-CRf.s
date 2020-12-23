%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:08 EST 2020

% Result     : Theorem 38.17s
% Output     : CNFRefutation 38.29s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 193 expanded)
%              Number of leaves         :   31 (  75 expanded)
%              Depth                    :   11
%              Number of atoms          :  167 ( 428 expanded)
%              Number of equality atoms :   13 (  21 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_52,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_126,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_111,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_65,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_98,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).

tff(f_107,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_116,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(c_32,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_72,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_68,plain,(
    ! [A_32] :
      ( v3_ordinal1(k1_ordinal1(A_32))
      | ~ v3_ordinal1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_74,plain,(
    v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_56,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ r1_ordinal1(A_22,B_23)
      | ~ v3_ordinal1(B_23)
      | ~ v3_ordinal1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_86,plain,(
    ! [A_38] :
      ( v1_ordinal1(A_38)
      | ~ v3_ordinal1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_94,plain,(
    v1_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_86])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( r2_xboole_0(A_9,B_10)
      | B_10 = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_921,plain,(
    ! [A_134,B_135] :
      ( r2_hidden(A_134,B_135)
      | ~ r2_xboole_0(A_134,B_135)
      | ~ v3_ordinal1(B_135)
      | ~ v1_ordinal1(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_7205,plain,(
    ! [A_3448,B_3449] :
      ( r2_hidden(A_3448,B_3449)
      | ~ v3_ordinal1(B_3449)
      | ~ v1_ordinal1(A_3448)
      | B_3449 = A_3448
      | ~ r1_tarski(A_3448,B_3449) ) ),
    inference(resolution,[status(thm)],[c_22,c_921])).

tff(c_82,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | r1_ordinal1(k1_ordinal1('#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_104,plain,(
    r1_ordinal1(k1_ordinal1('#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_76,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_5'),'#skF_6')
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_126,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_76])).

tff(c_7802,plain,
    ( ~ v3_ordinal1('#skF_6')
    | ~ v1_ordinal1('#skF_5')
    | '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_7205,c_126])).

tff(c_7968,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_72,c_7802])).

tff(c_7970,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_7968])).

tff(c_7973,plain,
    ( ~ r1_ordinal1('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_7970])).

tff(c_7976,plain,(
    ~ r1_ordinal1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_7973])).

tff(c_66,plain,(
    ! [B_31,A_29] :
      ( r2_hidden(B_31,A_29)
      | r1_ordinal1(A_29,B_31)
      | ~ v3_ordinal1(B_31)
      | ~ v3_ordinal1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_490,plain,(
    ! [A_96,B_97] :
      ( r1_tarski(A_96,B_97)
      | ~ r1_ordinal1(A_96,B_97)
      | ~ v3_ordinal1(B_97)
      | ~ v3_ordinal1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_154,plain,(
    ! [A_56,B_57] :
      ( ~ r2_hidden(A_56,B_57)
      | r2_hidden(A_56,k1_ordinal1(B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_70,plain,(
    ! [B_34,A_33] :
      ( ~ r1_tarski(B_34,A_33)
      | ~ r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_161,plain,(
    ! [B_57,A_56] :
      ( ~ r1_tarski(k1_ordinal1(B_57),A_56)
      | ~ r2_hidden(A_56,B_57) ) ),
    inference(resolution,[status(thm)],[c_154,c_70])).

tff(c_76076,plain,(
    ! [B_18937,B_18938] :
      ( ~ r2_hidden(B_18937,B_18938)
      | ~ r1_ordinal1(k1_ordinal1(B_18938),B_18937)
      | ~ v3_ordinal1(B_18937)
      | ~ v3_ordinal1(k1_ordinal1(B_18938)) ) ),
    inference(resolution,[status(thm)],[c_490,c_161])).

tff(c_76134,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1(k1_ordinal1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_104,c_76076])).

tff(c_76151,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | ~ v3_ordinal1(k1_ordinal1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76134])).

tff(c_76152,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_76151])).

tff(c_76155,plain,(
    ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_76152])).

tff(c_76159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_76155])).

tff(c_76160,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_76151])).

tff(c_76178,plain,
    ( r1_ordinal1('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_76160])).

tff(c_76185,plain,(
    r1_ordinal1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_76178])).

tff(c_76187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7976,c_76185])).

tff(c_76188,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_7968])).

tff(c_76194,plain,(
    r1_ordinal1(k1_ordinal1('#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76188,c_104])).

tff(c_60,plain,(
    ! [B_25] : r2_hidden(B_25,k1_ordinal1(B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_136,plain,(
    ! [B_50,A_51] :
      ( ~ r1_tarski(B_50,A_51)
      | ~ r2_hidden(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_143,plain,(
    ! [B_25] : ~ r1_tarski(k1_ordinal1(B_25),B_25) ),
    inference(resolution,[status(thm)],[c_60,c_136])).

tff(c_508,plain,(
    ! [B_97] :
      ( ~ r1_ordinal1(k1_ordinal1(B_97),B_97)
      | ~ v3_ordinal1(B_97)
      | ~ v3_ordinal1(k1_ordinal1(B_97)) ) ),
    inference(resolution,[status(thm)],[c_490,c_143])).

tff(c_76277,plain,
    ( ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1(k1_ordinal1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_76194,c_508])).

tff(c_76280,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76277])).

tff(c_76284,plain,(
    ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_76280])).

tff(c_76288,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76284])).

tff(c_76289,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_76306,plain,(
    ! [B_19087,A_19088] :
      ( ~ r2_hidden(B_19087,A_19088)
      | ~ r2_hidden(A_19088,B_19087) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_76315,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_76289,c_76306])).

tff(c_76777,plain,(
    ! [B_19150,A_19151] :
      ( r1_ordinal1(B_19150,A_19151)
      | r1_ordinal1(A_19151,B_19150)
      | ~ v3_ordinal1(B_19150)
      | ~ v3_ordinal1(A_19151) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_76290,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_76780,plain,
    ( r1_ordinal1('#skF_6',k1_ordinal1('#skF_5'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_5'))
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76777,c_76290])).

tff(c_76786,plain,
    ( r1_ordinal1('#skF_6',k1_ordinal1('#skF_5'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76780])).

tff(c_76791,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_76786])).

tff(c_76794,plain,(
    ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_76791])).

tff(c_76798,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_76794])).

tff(c_76800,plain,(
    v3_ordinal1(k1_ordinal1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_76786])).

tff(c_76877,plain,(
    ! [B_19163,A_19164] :
      ( r2_hidden(B_19163,A_19164)
      | r1_ordinal1(A_19164,B_19163)
      | ~ v3_ordinal1(B_19163)
      | ~ v3_ordinal1(A_19164) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_58,plain,(
    ! [B_25,A_24] :
      ( B_25 = A_24
      | r2_hidden(A_24,B_25)
      | ~ r2_hidden(A_24,k1_ordinal1(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_87473,plain,(
    ! [B_23408,B_23407] :
      ( B_23408 = B_23407
      | r2_hidden(B_23408,B_23407)
      | r1_ordinal1(k1_ordinal1(B_23407),B_23408)
      | ~ v3_ordinal1(B_23408)
      | ~ v3_ordinal1(k1_ordinal1(B_23407)) ) ),
    inference(resolution,[status(thm)],[c_76877,c_58])).

tff(c_87480,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1(k1_ordinal1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_87473,c_76290])).

tff(c_87486,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76800,c_72,c_87480])).

tff(c_87487,plain,(
    '#skF_5' = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_76315,c_87486])).

tff(c_76324,plain,(
    ! [B_19093,A_19094] :
      ( ~ r1_tarski(B_19093,A_19094)
      | ~ r2_hidden(A_19094,B_19093) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_76336,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_76289,c_76324])).

tff(c_87499,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87487,c_76336])).

tff(c_87508,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_87499])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 38.17/26.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 38.29/26.76  
% 38.29/26.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 38.29/26.76  %$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 38.29/26.76  
% 38.29/26.76  %Foreground sorts:
% 38.29/26.76  
% 38.29/26.76  
% 38.29/26.76  %Background operators:
% 38.29/26.76  
% 38.29/26.76  
% 38.29/26.76  %Foreground operators:
% 38.29/26.76  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 38.29/26.76  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 38.29/26.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 38.29/26.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 38.29/26.76  tff(k1_tarski, type, k1_tarski: $i > $i).
% 38.29/26.76  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 38.29/26.76  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 38.29/26.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 38.29/26.76  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 38.29/26.76  tff('#skF_5', type, '#skF_5': $i).
% 38.29/26.76  tff('#skF_6', type, '#skF_6': $i).
% 38.29/26.76  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 38.29/26.76  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 38.29/26.76  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 38.29/26.76  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 38.29/26.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 38.29/26.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 38.29/26.76  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 38.29/26.76  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 38.29/26.76  
% 38.29/26.78  tff(f_52, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 38.29/26.78  tff(f_126, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_ordinal1)).
% 38.29/26.78  tff(f_111, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 38.29/26.78  tff(f_83, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 38.29/26.78  tff(f_65, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 38.29/26.78  tff(f_46, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 38.29/26.78  tff(f_98, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_ordinal1)).
% 38.29/26.78  tff(f_107, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 38.29/26.78  tff(f_89, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 38.29/26.78  tff(f_116, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 38.29/26.78  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 38.29/26.78  tff(f_73, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 38.29/26.78  tff(c_32, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 38.29/26.78  tff(c_72, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_126])).
% 38.29/26.78  tff(c_68, plain, (![A_32]: (v3_ordinal1(k1_ordinal1(A_32)) | ~v3_ordinal1(A_32))), inference(cnfTransformation, [status(thm)], [f_111])).
% 38.29/26.78  tff(c_74, plain, (v3_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_126])).
% 38.29/26.78  tff(c_56, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | ~r1_ordinal1(A_22, B_23) | ~v3_ordinal1(B_23) | ~v3_ordinal1(A_22))), inference(cnfTransformation, [status(thm)], [f_83])).
% 38.29/26.78  tff(c_86, plain, (![A_38]: (v1_ordinal1(A_38) | ~v3_ordinal1(A_38))), inference(cnfTransformation, [status(thm)], [f_65])).
% 38.29/26.78  tff(c_94, plain, (v1_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_86])).
% 38.29/26.78  tff(c_22, plain, (![A_9, B_10]: (r2_xboole_0(A_9, B_10) | B_10=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 38.29/26.78  tff(c_921, plain, (![A_134, B_135]: (r2_hidden(A_134, B_135) | ~r2_xboole_0(A_134, B_135) | ~v3_ordinal1(B_135) | ~v1_ordinal1(A_134))), inference(cnfTransformation, [status(thm)], [f_98])).
% 38.29/26.78  tff(c_7205, plain, (![A_3448, B_3449]: (r2_hidden(A_3448, B_3449) | ~v3_ordinal1(B_3449) | ~v1_ordinal1(A_3448) | B_3449=A_3448 | ~r1_tarski(A_3448, B_3449))), inference(resolution, [status(thm)], [c_22, c_921])).
% 38.29/26.78  tff(c_82, plain, (r2_hidden('#skF_5', '#skF_6') | r1_ordinal1(k1_ordinal1('#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_126])).
% 38.29/26.78  tff(c_104, plain, (r1_ordinal1(k1_ordinal1('#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_82])).
% 38.29/26.78  tff(c_76, plain, (~r1_ordinal1(k1_ordinal1('#skF_5'), '#skF_6') | ~r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_126])).
% 38.29/26.78  tff(c_126, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_76])).
% 38.29/26.78  tff(c_7802, plain, (~v3_ordinal1('#skF_6') | ~v1_ordinal1('#skF_5') | '#skF_5'='#skF_6' | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_7205, c_126])).
% 38.29/26.78  tff(c_7968, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_72, c_7802])).
% 38.29/26.78  tff(c_7970, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_7968])).
% 38.29/26.78  tff(c_7973, plain, (~r1_ordinal1('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_7970])).
% 38.29/26.78  tff(c_7976, plain, (~r1_ordinal1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_7973])).
% 38.29/26.78  tff(c_66, plain, (![B_31, A_29]: (r2_hidden(B_31, A_29) | r1_ordinal1(A_29, B_31) | ~v3_ordinal1(B_31) | ~v3_ordinal1(A_29))), inference(cnfTransformation, [status(thm)], [f_107])).
% 38.29/26.78  tff(c_490, plain, (![A_96, B_97]: (r1_tarski(A_96, B_97) | ~r1_ordinal1(A_96, B_97) | ~v3_ordinal1(B_97) | ~v3_ordinal1(A_96))), inference(cnfTransformation, [status(thm)], [f_83])).
% 38.29/26.78  tff(c_154, plain, (![A_56, B_57]: (~r2_hidden(A_56, B_57) | r2_hidden(A_56, k1_ordinal1(B_57)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 38.29/26.78  tff(c_70, plain, (![B_34, A_33]: (~r1_tarski(B_34, A_33) | ~r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_116])).
% 38.29/26.78  tff(c_161, plain, (![B_57, A_56]: (~r1_tarski(k1_ordinal1(B_57), A_56) | ~r2_hidden(A_56, B_57))), inference(resolution, [status(thm)], [c_154, c_70])).
% 38.29/26.78  tff(c_76076, plain, (![B_18937, B_18938]: (~r2_hidden(B_18937, B_18938) | ~r1_ordinal1(k1_ordinal1(B_18938), B_18937) | ~v3_ordinal1(B_18937) | ~v3_ordinal1(k1_ordinal1(B_18938)))), inference(resolution, [status(thm)], [c_490, c_161])).
% 38.29/26.78  tff(c_76134, plain, (~r2_hidden('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1(k1_ordinal1('#skF_5'))), inference(resolution, [status(thm)], [c_104, c_76076])).
% 38.29/26.78  tff(c_76151, plain, (~r2_hidden('#skF_6', '#skF_5') | ~v3_ordinal1(k1_ordinal1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_76134])).
% 38.29/26.78  tff(c_76152, plain, (~v3_ordinal1(k1_ordinal1('#skF_5'))), inference(splitLeft, [status(thm)], [c_76151])).
% 38.29/26.78  tff(c_76155, plain, (~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_68, c_76152])).
% 38.29/26.78  tff(c_76159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_76155])).
% 38.29/26.78  tff(c_76160, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_76151])).
% 38.29/26.78  tff(c_76178, plain, (r1_ordinal1('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_76160])).
% 38.29/26.78  tff(c_76185, plain, (r1_ordinal1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_76178])).
% 38.29/26.78  tff(c_76187, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7976, c_76185])).
% 38.29/26.78  tff(c_76188, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_7968])).
% 38.29/26.78  tff(c_76194, plain, (r1_ordinal1(k1_ordinal1('#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_76188, c_104])).
% 38.29/26.78  tff(c_60, plain, (![B_25]: (r2_hidden(B_25, k1_ordinal1(B_25)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 38.29/26.78  tff(c_136, plain, (![B_50, A_51]: (~r1_tarski(B_50, A_51) | ~r2_hidden(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_116])).
% 38.29/26.78  tff(c_143, plain, (![B_25]: (~r1_tarski(k1_ordinal1(B_25), B_25))), inference(resolution, [status(thm)], [c_60, c_136])).
% 38.29/26.78  tff(c_508, plain, (![B_97]: (~r1_ordinal1(k1_ordinal1(B_97), B_97) | ~v3_ordinal1(B_97) | ~v3_ordinal1(k1_ordinal1(B_97)))), inference(resolution, [status(thm)], [c_490, c_143])).
% 38.29/26.78  tff(c_76277, plain, (~v3_ordinal1('#skF_6') | ~v3_ordinal1(k1_ordinal1('#skF_6'))), inference(resolution, [status(thm)], [c_76194, c_508])).
% 38.29/26.78  tff(c_76280, plain, (~v3_ordinal1(k1_ordinal1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_76277])).
% 38.29/26.78  tff(c_76284, plain, (~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_68, c_76280])).
% 38.29/26.78  tff(c_76288, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_76284])).
% 38.29/26.78  tff(c_76289, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_82])).
% 38.29/26.78  tff(c_76306, plain, (![B_19087, A_19088]: (~r2_hidden(B_19087, A_19088) | ~r2_hidden(A_19088, B_19087))), inference(cnfTransformation, [status(thm)], [f_30])).
% 38.29/26.78  tff(c_76315, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_76289, c_76306])).
% 38.29/26.78  tff(c_76777, plain, (![B_19150, A_19151]: (r1_ordinal1(B_19150, A_19151) | r1_ordinal1(A_19151, B_19150) | ~v3_ordinal1(B_19150) | ~v3_ordinal1(A_19151))), inference(cnfTransformation, [status(thm)], [f_73])).
% 38.29/26.78  tff(c_76290, plain, (~r1_ordinal1(k1_ordinal1('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_82])).
% 38.29/26.78  tff(c_76780, plain, (r1_ordinal1('#skF_6', k1_ordinal1('#skF_5')) | ~v3_ordinal1(k1_ordinal1('#skF_5')) | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_76777, c_76290])).
% 38.29/26.78  tff(c_76786, plain, (r1_ordinal1('#skF_6', k1_ordinal1('#skF_5')) | ~v3_ordinal1(k1_ordinal1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_76780])).
% 38.29/26.78  tff(c_76791, plain, (~v3_ordinal1(k1_ordinal1('#skF_5'))), inference(splitLeft, [status(thm)], [c_76786])).
% 38.29/26.78  tff(c_76794, plain, (~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_68, c_76791])).
% 38.29/26.78  tff(c_76798, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_76794])).
% 38.29/26.78  tff(c_76800, plain, (v3_ordinal1(k1_ordinal1('#skF_5'))), inference(splitRight, [status(thm)], [c_76786])).
% 38.29/26.78  tff(c_76877, plain, (![B_19163, A_19164]: (r2_hidden(B_19163, A_19164) | r1_ordinal1(A_19164, B_19163) | ~v3_ordinal1(B_19163) | ~v3_ordinal1(A_19164))), inference(cnfTransformation, [status(thm)], [f_107])).
% 38.29/26.78  tff(c_58, plain, (![B_25, A_24]: (B_25=A_24 | r2_hidden(A_24, B_25) | ~r2_hidden(A_24, k1_ordinal1(B_25)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 38.29/26.78  tff(c_87473, plain, (![B_23408, B_23407]: (B_23408=B_23407 | r2_hidden(B_23408, B_23407) | r1_ordinal1(k1_ordinal1(B_23407), B_23408) | ~v3_ordinal1(B_23408) | ~v3_ordinal1(k1_ordinal1(B_23407)))), inference(resolution, [status(thm)], [c_76877, c_58])).
% 38.29/26.78  tff(c_87480, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1(k1_ordinal1('#skF_5'))), inference(resolution, [status(thm)], [c_87473, c_76290])).
% 38.29/26.78  tff(c_87486, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76800, c_72, c_87480])).
% 38.29/26.78  tff(c_87487, plain, ('#skF_5'='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_76315, c_87486])).
% 38.29/26.78  tff(c_76324, plain, (![B_19093, A_19094]: (~r1_tarski(B_19093, A_19094) | ~r2_hidden(A_19094, B_19093))), inference(cnfTransformation, [status(thm)], [f_116])).
% 38.29/26.78  tff(c_76336, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_76289, c_76324])).
% 38.29/26.78  tff(c_87499, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_87487, c_76336])).
% 38.29/26.78  tff(c_87508, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_87499])).
% 38.29/26.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 38.29/26.78  
% 38.29/26.78  Inference rules
% 38.29/26.78  ----------------------
% 38.29/26.78  #Ref     : 0
% 38.29/26.78  #Sup     : 17763
% 38.29/26.78  #Fact    : 62
% 38.29/26.78  #Define  : 0
% 38.29/26.78  #Split   : 13
% 38.29/26.78  #Chain   : 0
% 38.29/26.78  #Close   : 0
% 38.29/26.78  
% 38.29/26.78  Ordering : KBO
% 38.29/26.78  
% 38.29/26.78  Simplification rules
% 38.29/26.78  ----------------------
% 38.29/26.78  #Subsume      : 5889
% 38.29/26.78  #Demod        : 898
% 38.29/26.78  #Tautology    : 444
% 38.29/26.78  #SimpNegUnit  : 309
% 38.29/26.78  #BackRed      : 28
% 38.29/26.78  
% 38.29/26.78  #Partial instantiations: 12672
% 38.29/26.78  #Strategies tried      : 1
% 38.29/26.78  
% 38.29/26.78  Timing (in seconds)
% 38.29/26.78  ----------------------
% 38.29/26.78  Preprocessing        : 0.32
% 38.29/26.78  Parsing              : 0.17
% 38.29/26.78  CNF conversion       : 0.03
% 38.29/26.78  Main loop            : 25.70
% 38.29/26.78  Inferencing          : 2.82
% 38.29/26.78  Reduction            : 9.10
% 38.29/26.78  Demodulation         : 2.34
% 38.29/26.78  BG Simplification    : 0.32
% 38.29/26.78  Subsumption          : 12.09
% 38.29/26.78  Abstraction          : 0.60
% 38.29/26.78  MUC search           : 0.00
% 38.29/26.78  Cooper               : 0.00
% 38.29/26.78  Total                : 26.05
% 38.29/26.78  Index Insertion      : 0.00
% 38.29/26.78  Index Deletion       : 0.00
% 38.29/26.78  Index Matching       : 0.00
% 38.29/26.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
