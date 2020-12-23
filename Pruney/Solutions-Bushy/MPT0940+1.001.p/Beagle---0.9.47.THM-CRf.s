%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0940+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:07 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   52 (  87 expanded)
%              Number of leaves         :   22 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :  110 ( 202 expanded)
%              Number of equality atoms :   17 (  29 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_relat_2 > r2_hidden > r1_tarski > v4_relat_2 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r4_relat_2,type,(
    r4_relat_2: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_69,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r4_relat_2(A,B)
        <=> ! [C,D] :
              ( ( r2_hidden(C,B)
                & r2_hidden(D,B)
                & r2_hidden(k4_tarski(C,D),A)
                & r2_hidden(k4_tarski(D,C),A) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_2)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_30,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v4_relat_2(A)
      <=> r4_relat_2(A,k3_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_2)).

tff(f_72,negated_conjecture,(
    ~ ! [A] : v4_relat_2(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_wellord2)).

tff(c_42,plain,(
    ! [A_29] : v1_relat_1(k1_wellord2(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_38,plain,(
    ! [A_12,B_22] :
      ( r2_hidden('#skF_4'(A_12,B_22),B_22)
      | r4_relat_2(A_12,B_22)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_40,plain,(
    ! [A_12,B_22] :
      ( r2_hidden('#skF_3'(A_12,B_22),B_22)
      | r4_relat_2(A_12,B_22)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_36,plain,(
    ! [A_12,B_22] :
      ( r2_hidden(k4_tarski('#skF_3'(A_12,B_22),'#skF_4'(A_12,B_22)),A_12)
      | r4_relat_2(A_12,B_22)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_28,plain,(
    ! [C_10,D_11,A_4] :
      ( r1_tarski(C_10,D_11)
      | ~ r2_hidden(k4_tarski(C_10,D_11),k1_wellord2(A_4))
      | ~ r2_hidden(D_11,A_4)
      | ~ r2_hidden(C_10,A_4)
      | ~ v1_relat_1(k1_wellord2(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_151,plain,(
    ! [C_60,D_61,A_62] :
      ( r1_tarski(C_60,D_61)
      | ~ r2_hidden(k4_tarski(C_60,D_61),k1_wellord2(A_62))
      | ~ r2_hidden(D_61,A_62)
      | ~ r2_hidden(C_60,A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_28])).

tff(c_158,plain,(
    ! [A_62,B_22] :
      ( r1_tarski('#skF_3'(k1_wellord2(A_62),B_22),'#skF_4'(k1_wellord2(A_62),B_22))
      | ~ r2_hidden('#skF_4'(k1_wellord2(A_62),B_22),A_62)
      | ~ r2_hidden('#skF_3'(k1_wellord2(A_62),B_22),A_62)
      | r4_relat_2(k1_wellord2(A_62),B_22)
      | ~ v1_relat_1(k1_wellord2(A_62)) ) ),
    inference(resolution,[status(thm)],[c_36,c_151])).

tff(c_166,plain,(
    ! [A_62,B_22] :
      ( r1_tarski('#skF_3'(k1_wellord2(A_62),B_22),'#skF_4'(k1_wellord2(A_62),B_22))
      | ~ r2_hidden('#skF_4'(k1_wellord2(A_62),B_22),A_62)
      | ~ r2_hidden('#skF_3'(k1_wellord2(A_62),B_22),A_62)
      | r4_relat_2(k1_wellord2(A_62),B_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_158])).

tff(c_34,plain,(
    ! [A_12,B_22] :
      ( r2_hidden(k4_tarski('#skF_4'(A_12,B_22),'#skF_3'(A_12,B_22)),A_12)
      | r4_relat_2(A_12,B_22)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_162,plain,(
    ! [A_62,B_22] :
      ( r1_tarski('#skF_4'(k1_wellord2(A_62),B_22),'#skF_3'(k1_wellord2(A_62),B_22))
      | ~ r2_hidden('#skF_3'(k1_wellord2(A_62),B_22),A_62)
      | ~ r2_hidden('#skF_4'(k1_wellord2(A_62),B_22),A_62)
      | r4_relat_2(k1_wellord2(A_62),B_22)
      | ~ v1_relat_1(k1_wellord2(A_62)) ) ),
    inference(resolution,[status(thm)],[c_34,c_151])).

tff(c_174,plain,(
    ! [A_65,B_66] :
      ( r1_tarski('#skF_4'(k1_wellord2(A_65),B_66),'#skF_3'(k1_wellord2(A_65),B_66))
      | ~ r2_hidden('#skF_3'(k1_wellord2(A_65),B_66),A_65)
      | ~ r2_hidden('#skF_4'(k1_wellord2(A_65),B_66),A_65)
      | r4_relat_2(k1_wellord2(A_65),B_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_162])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_258,plain,(
    ! [A_79,B_80] :
      ( '#skF_3'(k1_wellord2(A_79),B_80) = '#skF_4'(k1_wellord2(A_79),B_80)
      | ~ r1_tarski('#skF_3'(k1_wellord2(A_79),B_80),'#skF_4'(k1_wellord2(A_79),B_80))
      | ~ r2_hidden('#skF_3'(k1_wellord2(A_79),B_80),A_79)
      | ~ r2_hidden('#skF_4'(k1_wellord2(A_79),B_80),A_79)
      | r4_relat_2(k1_wellord2(A_79),B_80) ) ),
    inference(resolution,[status(thm)],[c_174,c_2])).

tff(c_263,plain,(
    ! [A_81,B_82] :
      ( '#skF_3'(k1_wellord2(A_81),B_82) = '#skF_4'(k1_wellord2(A_81),B_82)
      | ~ r2_hidden('#skF_4'(k1_wellord2(A_81),B_82),A_81)
      | ~ r2_hidden('#skF_3'(k1_wellord2(A_81),B_82),A_81)
      | r4_relat_2(k1_wellord2(A_81),B_82) ) ),
    inference(resolution,[status(thm)],[c_166,c_258])).

tff(c_267,plain,(
    ! [B_22] :
      ( '#skF_3'(k1_wellord2(B_22),B_22) = '#skF_4'(k1_wellord2(B_22),B_22)
      | ~ r2_hidden('#skF_4'(k1_wellord2(B_22),B_22),B_22)
      | r4_relat_2(k1_wellord2(B_22),B_22)
      | ~ v1_relat_1(k1_wellord2(B_22)) ) ),
    inference(resolution,[status(thm)],[c_40,c_263])).

tff(c_271,plain,(
    ! [B_83] :
      ( '#skF_3'(k1_wellord2(B_83),B_83) = '#skF_4'(k1_wellord2(B_83),B_83)
      | ~ r2_hidden('#skF_4'(k1_wellord2(B_83),B_83),B_83)
      | r4_relat_2(k1_wellord2(B_83),B_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_267])).

tff(c_275,plain,(
    ! [B_22] :
      ( '#skF_3'(k1_wellord2(B_22),B_22) = '#skF_4'(k1_wellord2(B_22),B_22)
      | r4_relat_2(k1_wellord2(B_22),B_22)
      | ~ v1_relat_1(k1_wellord2(B_22)) ) ),
    inference(resolution,[status(thm)],[c_38,c_271])).

tff(c_279,plain,(
    ! [B_84] :
      ( '#skF_3'(k1_wellord2(B_84),B_84) = '#skF_4'(k1_wellord2(B_84),B_84)
      | r4_relat_2(k1_wellord2(B_84),B_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_275])).

tff(c_24,plain,(
    ! [A_4] :
      ( k3_relat_1(k1_wellord2(A_4)) = A_4
      | ~ v1_relat_1(k1_wellord2(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_50,plain,(
    ! [A_4] : k3_relat_1(k1_wellord2(A_4)) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_24])).

tff(c_70,plain,(
    ! [A_35] :
      ( v4_relat_2(A_35)
      | ~ r4_relat_2(A_35,k3_relat_1(A_35))
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_73,plain,(
    ! [A_4] :
      ( v4_relat_2(k1_wellord2(A_4))
      | ~ r4_relat_2(k1_wellord2(A_4),A_4)
      | ~ v1_relat_1(k1_wellord2(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_70])).

tff(c_75,plain,(
    ! [A_4] :
      ( v4_relat_2(k1_wellord2(A_4))
      | ~ r4_relat_2(k1_wellord2(A_4),A_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_73])).

tff(c_284,plain,(
    ! [B_85] :
      ( v4_relat_2(k1_wellord2(B_85))
      | '#skF_3'(k1_wellord2(B_85),B_85) = '#skF_4'(k1_wellord2(B_85),B_85) ) ),
    inference(resolution,[status(thm)],[c_279,c_75])).

tff(c_94,plain,(
    ! [A_43,B_44] :
      ( '#skF_3'(A_43,B_44) != '#skF_4'(A_43,B_44)
      | r4_relat_2(A_43,B_44)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_98,plain,(
    ! [B_44] :
      ( v4_relat_2(k1_wellord2(B_44))
      | '#skF_3'(k1_wellord2(B_44),B_44) != '#skF_4'(k1_wellord2(B_44),B_44)
      | ~ v1_relat_1(k1_wellord2(B_44)) ) ),
    inference(resolution,[status(thm)],[c_94,c_75])).

tff(c_105,plain,(
    ! [B_44] :
      ( v4_relat_2(k1_wellord2(B_44))
      | '#skF_3'(k1_wellord2(B_44),B_44) != '#skF_4'(k1_wellord2(B_44),B_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_98])).

tff(c_327,plain,(
    ! [B_85] : v4_relat_2(k1_wellord2(B_85)) ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_105])).

tff(c_44,plain,(
    ~ v4_relat_2(k1_wellord2('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_338,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_44])).

%------------------------------------------------------------------------------
