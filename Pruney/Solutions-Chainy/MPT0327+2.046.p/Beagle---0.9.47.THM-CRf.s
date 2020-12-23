%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:36 EST 2020

% Result     : Theorem 39.84s
% Output     : CNFRefutation 40.39s
% Verified   : 
% Statistics : Number of formulae       :  161 (2226 expanded)
%              Number of leaves         :   37 ( 756 expanded)
%              Depth                    :   21
%              Number of atoms          :  203 (2762 expanded)
%              Number of equality atoms :  140 (1817 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_65,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_46,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_84,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_52,plain,(
    ! [A_26] : k2_tarski(A_26,A_26) = k1_tarski(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_91,plain,(
    ! [D_45,B_46] : r2_hidden(D_45,k2_tarski(D_45,B_46)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_94,plain,(
    ! [A_26] : r2_hidden(A_26,k1_tarski(A_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_91])).

tff(c_24,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_68,plain,(
    ! [A_42] : r1_tarski(A_42,k1_zfmisc_1(k3_tarski(A_42))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_136,plain,(
    ! [A_55,B_56] :
      ( k4_xboole_0(A_55,B_56) = k1_xboole_0
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_144,plain,(
    ! [A_42] : k4_xboole_0(A_42,k1_zfmisc_1(k3_tarski(A_42))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_68,c_136])).

tff(c_164,plain,(
    ! [A_61,B_62] :
      ( k3_xboole_0(A_61,B_62) = A_61
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_172,plain,(
    ! [A_42] : k3_xboole_0(A_42,k1_zfmisc_1(k3_tarski(A_42))) = A_42 ),
    inference(resolution,[status(thm)],[c_68,c_164])).

tff(c_288,plain,(
    ! [A_79,B_80] : k5_xboole_0(A_79,k3_xboole_0(A_79,B_80)) = k4_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_297,plain,(
    ! [A_42] : k4_xboole_0(A_42,k1_zfmisc_1(k3_tarski(A_42))) = k5_xboole_0(A_42,A_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_288])).

tff(c_306,plain,(
    ! [A_42] : k5_xboole_0(A_42,A_42) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_297])).

tff(c_523,plain,(
    ! [A_103,B_104,C_105] : k5_xboole_0(k5_xboole_0(A_103,B_104),C_105) = k5_xboole_0(A_103,k5_xboole_0(B_104,C_105)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_124962,plain,(
    ! [A_40587,C_40588] : k5_xboole_0(A_40587,k5_xboole_0(A_40587,C_40588)) = k5_xboole_0(k1_xboole_0,C_40588) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_523])).

tff(c_125082,plain,(
    ! [A_42] : k5_xboole_0(k1_xboole_0,A_42) = k5_xboole_0(A_42,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_124962])).

tff(c_125115,plain,(
    ! [A_42] : k5_xboole_0(k1_xboole_0,A_42) = A_42 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_125082])).

tff(c_537,plain,(
    ! [A_103,B_104] : k5_xboole_0(A_103,k5_xboole_0(B_104,k5_xboole_0(A_103,B_104))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_306])).

tff(c_561,plain,(
    ! [A_42,C_105] : k5_xboole_0(A_42,k5_xboole_0(A_42,C_105)) = k5_xboole_0(k1_xboole_0,C_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_523])).

tff(c_125237,plain,(
    ! [A_40590,C_40591] : k5_xboole_0(A_40590,k5_xboole_0(A_40590,C_40591)) = C_40591 ),
    inference(demodulation,[status(thm),theory(equality)],[c_125115,c_561])).

tff(c_125311,plain,(
    ! [B_104,A_103] : k5_xboole_0(B_104,k5_xboole_0(A_103,B_104)) = k5_xboole_0(A_103,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_537,c_125237])).

tff(c_125411,plain,(
    ! [B_40596,A_40597] : k5_xboole_0(B_40596,k5_xboole_0(A_40597,B_40596)) = A_40597 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_125311])).

tff(c_125117,plain,(
    ! [A_42,C_105] : k5_xboole_0(A_42,k5_xboole_0(A_42,C_105)) = C_105 ),
    inference(demodulation,[status(thm),theory(equality)],[c_125115,c_561])).

tff(c_125420,plain,(
    ! [B_40596,A_40597] : k5_xboole_0(B_40596,A_40597) = k5_xboole_0(A_40597,B_40596) ),
    inference(superposition,[status(thm),theory(equality)],[c_125411,c_125117])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_72,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_248,plain,(
    ! [A_74,B_75] :
      ( r1_tarski(k1_tarski(A_74),B_75)
      | ~ r2_hidden(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = k1_xboole_0
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_260,plain,(
    ! [A_74,B_75] :
      ( k4_xboole_0(k1_tarski(A_74),B_75) = k1_xboole_0
      | ~ r2_hidden(A_74,B_75) ) ),
    inference(resolution,[status(thm)],[c_248,c_18])).

tff(c_303,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_288])).

tff(c_876,plain,(
    ! [A_112,B_113] : k5_xboole_0(k5_xboole_0(A_112,B_113),k3_xboole_0(A_112,B_113)) = k2_xboole_0(A_112,B_113) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_30,plain,(
    ! [A_15,B_16,C_17] : k5_xboole_0(k5_xboole_0(A_15,B_16),C_17) = k5_xboole_0(A_15,k5_xboole_0(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_891,plain,(
    ! [A_112,B_113] : k5_xboole_0(A_112,k5_xboole_0(B_113,k3_xboole_0(A_112,B_113))) = k2_xboole_0(A_112,B_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_876,c_30])).

tff(c_949,plain,(
    ! [A_114,B_115] : k5_xboole_0(A_114,k4_xboole_0(B_115,A_114)) = k2_xboole_0(A_114,B_115) ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_891])).

tff(c_990,plain,(
    ! [B_75,A_74] :
      ( k2_xboole_0(B_75,k1_tarski(A_74)) = k5_xboole_0(B_75,k1_xboole_0)
      | ~ r2_hidden(A_74,B_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_949])).

tff(c_997,plain,(
    ! [B_75,A_74] :
      ( k2_xboole_0(B_75,k1_tarski(A_74)) = B_75
      | ~ r2_hidden(A_74,B_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_990])).

tff(c_233,plain,(
    ! [A_69,B_70] :
      ( r1_xboole_0(k1_tarski(A_69),B_70)
      | r2_hidden(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = A_13
      | ~ r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_237,plain,(
    ! [A_69,B_70] :
      ( k4_xboole_0(k1_tarski(A_69),B_70) = k1_tarski(A_69)
      | r2_hidden(A_69,B_70) ) ),
    inference(resolution,[status(thm)],[c_233,c_26])).

tff(c_20,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_129228,plain,(
    ! [A_46663,B_46664,C_46665] : k5_xboole_0(A_46663,k5_xboole_0(k3_xboole_0(A_46663,B_46664),C_46665)) = k5_xboole_0(k4_xboole_0(A_46663,B_46664),C_46665) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_523])).

tff(c_129386,plain,(
    ! [A_46663,B_46664] : k5_xboole_0(k4_xboole_0(A_46663,B_46664),k3_xboole_0(A_46663,B_46664)) = k5_xboole_0(A_46663,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_129228])).

tff(c_129424,plain,(
    ! [A_46728,B_46729] : k5_xboole_0(k4_xboole_0(A_46728,B_46729),k3_xboole_0(A_46728,B_46729)) = A_46728 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_129386])).

tff(c_129638,plain,(
    ! [A_46855,B_46856] : k5_xboole_0(k4_xboole_0(A_46855,B_46856),k3_xboole_0(B_46856,A_46855)) = A_46855 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_129424])).

tff(c_131481,plain,(
    ! [A_50429,B_50430] : k5_xboole_0(k4_xboole_0(A_50429,B_50430),A_50429) = k3_xboole_0(B_50430,A_50429) ),
    inference(superposition,[status(thm),theory(equality)],[c_129638,c_125117])).

tff(c_131535,plain,(
    ! [A_69,B_70] :
      ( k5_xboole_0(k1_tarski(A_69),k1_tarski(A_69)) = k3_xboole_0(B_70,k1_tarski(A_69))
      | r2_hidden(A_69,B_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_131481])).

tff(c_132470,plain,(
    ! [B_51372,A_51373] :
      ( k3_xboole_0(B_51372,k1_tarski(A_51373)) = k1_xboole_0
      | r2_hidden(A_51373,B_51372) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_131535])).

tff(c_132538,plain,(
    ! [B_51372,A_51373] :
      ( k4_xboole_0(B_51372,k1_tarski(A_51373)) = k5_xboole_0(B_51372,k1_xboole_0)
      | r2_hidden(A_51373,B_51372) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132470,c_20])).

tff(c_139083,plain,(
    ! [B_56280,A_56281] :
      ( k4_xboole_0(B_56280,k1_tarski(A_56281)) = B_56280
      | r2_hidden(A_56281,B_56280) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_132538])).

tff(c_42,plain,(
    ! [A_20,B_21,C_22] :
      ( '#skF_1'(A_20,B_21,C_22) = B_21
      | '#skF_1'(A_20,B_21,C_22) = A_20
      | '#skF_2'(A_20,B_21,C_22) != B_21
      | k2_tarski(A_20,B_21) = C_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_125679,plain,(
    ! [B_21,C_22] :
      ( '#skF_2'(B_21,B_21,C_22) != B_21
      | k2_tarski(B_21,B_21) = C_22
      | '#skF_1'(B_21,B_21,C_22) = B_21 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_42])).

tff(c_130107,plain,(
    ! [B_47109,C_47110] :
      ( '#skF_2'(B_47109,B_47109,C_47110) != B_47109
      | k1_tarski(B_47109) = C_47110
      | '#skF_1'(B_47109,B_47109,C_47110) = B_47109 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_125679])).

tff(c_70,plain,(
    k2_xboole_0(k4_xboole_0('#skF_4',k1_tarski('#skF_3')),k1_tarski('#skF_3')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_131212,plain,(
    ! [C_47110] :
      ( k2_xboole_0(k4_xboole_0('#skF_4',C_47110),k1_tarski('#skF_3')) != '#skF_4'
      | '#skF_2'('#skF_3','#skF_3',C_47110) != '#skF_3'
      | '#skF_1'('#skF_3','#skF_3',C_47110) = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130107,c_70])).

tff(c_139139,plain,(
    ! [A_56281] :
      ( k2_xboole_0('#skF_4',k1_tarski('#skF_3')) != '#skF_4'
      | '#skF_2'('#skF_3','#skF_3',k1_tarski(A_56281)) != '#skF_3'
      | '#skF_1'('#skF_3','#skF_3',k1_tarski(A_56281)) = '#skF_3'
      | r2_hidden(A_56281,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139083,c_131212])).

tff(c_139557,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_139139])).

tff(c_139567,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_997,c_139557])).

tff(c_139571,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_139567])).

tff(c_139573,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_139139])).

tff(c_943,plain,(
    ! [A_112,B_113] : k5_xboole_0(A_112,k4_xboole_0(B_113,A_112)) = k2_xboole_0(A_112,B_113) ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_891])).

tff(c_125305,plain,(
    ! [A_112,B_113] : k5_xboole_0(A_112,k2_xboole_0(A_112,B_113)) = k4_xboole_0(B_113,A_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_943,c_125237])).

tff(c_139583,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k5_xboole_0('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_139573,c_125305])).

tff(c_139630,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_139583])).

tff(c_125498,plain,(
    ! [A_8,B_9] : k5_xboole_0(k3_xboole_0(A_8,B_9),k4_xboole_0(A_8,B_9)) = A_8 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_125411])).

tff(c_139665,plain,(
    k5_xboole_0(k3_xboole_0(k1_tarski('#skF_3'),'#skF_4'),k1_xboole_0) = k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_139630,c_125498])).

tff(c_139749,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125115,c_125420,c_2,c_139665])).

tff(c_1350,plain,(
    ! [B_130,A_131] :
      ( k2_xboole_0(B_130,k1_tarski(A_131)) = B_130
      | ~ r2_hidden(A_131,B_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_990])).

tff(c_1379,plain,
    ( k4_xboole_0('#skF_4',k1_tarski('#skF_3')) != '#skF_4'
    | ~ r2_hidden('#skF_3',k4_xboole_0('#skF_4',k1_tarski('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1350,c_70])).

tff(c_1628,plain,(
    ~ r2_hidden('#skF_3',k4_xboole_0('#skF_4',k1_tarski('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1379])).

tff(c_6212,plain,(
    ! [A_6271,B_6272,C_6273] : k5_xboole_0(A_6271,k5_xboole_0(k3_xboole_0(A_6271,B_6272),C_6273)) = k5_xboole_0(k4_xboole_0(A_6271,B_6272),C_6273) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_523])).

tff(c_6374,plain,(
    ! [A_6271,B_6272] : k5_xboole_0(k4_xboole_0(A_6271,B_6272),k3_xboole_0(A_6271,B_6272)) = k5_xboole_0(A_6271,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_6212])).

tff(c_6411,plain,(
    ! [A_6336,B_6337] : k5_xboole_0(k4_xboole_0(A_6336,B_6337),k3_xboole_0(A_6336,B_6337)) = A_6336 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_6374])).

tff(c_6625,plain,(
    ! [A_6463,B_6464] : k5_xboole_0(k4_xboole_0(A_6463,B_6464),k3_xboole_0(B_6464,A_6463)) = A_6463 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_6411])).

tff(c_1634,plain,(
    ! [A_141,C_142] : k5_xboole_0(A_141,k5_xboole_0(A_141,C_142)) = k5_xboole_0(k1_xboole_0,C_142) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_523])).

tff(c_1754,plain,(
    ! [A_42] : k5_xboole_0(k1_xboole_0,A_42) = k5_xboole_0(A_42,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_1634])).

tff(c_1787,plain,(
    ! [A_42] : k5_xboole_0(k1_xboole_0,A_42) = A_42 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1754])).

tff(c_1909,plain,(
    ! [A_144,C_145] : k5_xboole_0(A_144,k5_xboole_0(A_144,C_145)) = C_145 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1787,c_561])).

tff(c_1983,plain,(
    ! [B_104,A_103] : k5_xboole_0(B_104,k5_xboole_0(A_103,B_104)) = k5_xboole_0(A_103,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_537,c_1909])).

tff(c_2020,plain,(
    ! [B_104,A_103] : k5_xboole_0(B_104,k5_xboole_0(A_103,B_104)) = A_103 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1983])).

tff(c_12153,plain,(
    ! [B_13403,A_13404] : k5_xboole_0(k3_xboole_0(B_13403,A_13404),A_13404) = k4_xboole_0(A_13404,B_13403) ),
    inference(superposition,[status(thm),theory(equality)],[c_6625,c_2020])).

tff(c_568,plain,(
    ! [A_8,B_9,C_105] : k5_xboole_0(A_8,k5_xboole_0(k3_xboole_0(A_8,B_9),C_105)) = k5_xboole_0(k4_xboole_0(A_8,B_9),C_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_523])).

tff(c_12171,plain,(
    ! [B_13403,A_13404] : k5_xboole_0(k4_xboole_0(B_13403,A_13404),A_13404) = k5_xboole_0(B_13403,k4_xboole_0(A_13404,B_13403)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12153,c_568])).

tff(c_22852,plain,(
    ! [B_19445,A_19446] : k5_xboole_0(k4_xboole_0(B_19445,A_19446),A_19446) = k2_xboole_0(B_19445,A_19446) ),
    inference(demodulation,[status(thm),theory(equality)],[c_943,c_12171])).

tff(c_5540,plain,(
    ! [A_5891,B_5892] : k5_xboole_0(A_5891,k2_xboole_0(A_5891,B_5892)) = k4_xboole_0(B_5892,A_5891) ),
    inference(superposition,[status(thm),theory(equality)],[c_943,c_1909])).

tff(c_2070,plain,(
    ! [B_151,A_152] : k5_xboole_0(B_151,k5_xboole_0(A_152,B_151)) = A_152 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1983])).

tff(c_2073,plain,(
    ! [A_152,B_151] : k5_xboole_0(k5_xboole_0(A_152,B_151),A_152) = B_151 ),
    inference(superposition,[status(thm),theory(equality)],[c_2070,c_2020])).

tff(c_5561,plain,(
    ! [B_5892,A_5891] : k5_xboole_0(k4_xboole_0(B_5892,A_5891),A_5891) = k2_xboole_0(A_5891,B_5892) ),
    inference(superposition,[status(thm),theory(equality)],[c_5540,c_2073])).

tff(c_22858,plain,(
    ! [B_19445,A_19446] : k2_xboole_0(B_19445,A_19446) = k2_xboole_0(A_19446,B_19445) ),
    inference(superposition,[status(thm),theory(equality)],[c_22852,c_5561])).

tff(c_23074,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k4_xboole_0('#skF_4',k1_tarski('#skF_3'))) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22858,c_70])).

tff(c_4207,plain,(
    ! [A_4816,B_4817] :
      ( k4_xboole_0(k1_tarski(A_4816),B_4817) = k1_tarski(A_4816)
      | r2_hidden(A_4816,B_4817) ) ),
    inference(resolution,[status(thm)],[c_233,c_26])).

tff(c_124240,plain,(
    ! [B_40487,A_40488] :
      ( k5_xboole_0(B_40487,k1_tarski(A_40488)) = k2_xboole_0(B_40487,k1_tarski(A_40488))
      | r2_hidden(A_40488,B_40487) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4207,c_943])).

tff(c_1789,plain,(
    ! [A_42,C_105] : k5_xboole_0(A_42,k5_xboole_0(A_42,C_105)) = C_105 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1787,c_561])).

tff(c_6861,plain,(
    ! [A_6590,B_6591] : k5_xboole_0(k4_xboole_0(A_6590,B_6591),A_6590) = k3_xboole_0(B_6591,A_6590) ),
    inference(superposition,[status(thm),theory(equality)],[c_6625,c_1789])).

tff(c_6916,plain,(
    ! [A_69,B_70] :
      ( k5_xboole_0(k1_tarski(A_69),k1_tarski(A_69)) = k3_xboole_0(B_70,k1_tarski(A_69))
      | r2_hidden(A_69,B_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_6861])).

tff(c_6963,plain,(
    ! [B_70,A_69] :
      ( k3_xboole_0(B_70,k1_tarski(A_69)) = k1_xboole_0
      | r2_hidden(A_69,B_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_6916])).

tff(c_11977,plain,(
    ! [A_13214,B_13215] : k5_xboole_0(k3_xboole_0(A_13214,B_13215),A_13214) = k4_xboole_0(A_13214,B_13215) ),
    inference(superposition,[status(thm),theory(equality)],[c_6411,c_2020])).

tff(c_12040,plain,(
    ! [B_70,A_69] :
      ( k4_xboole_0(B_70,k1_tarski(A_69)) = k5_xboole_0(k1_xboole_0,B_70)
      | r2_hidden(A_69,B_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6963,c_11977])).

tff(c_14610,plain,(
    ! [B_14723,A_14724] :
      ( k4_xboole_0(B_14723,k1_tarski(A_14724)) = B_14723
      | r2_hidden(A_14724,B_14723) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1787,c_12040])).

tff(c_46,plain,(
    ! [A_20,B_21,C_22] :
      ( '#skF_1'(A_20,B_21,C_22) = B_21
      | '#skF_1'(A_20,B_21,C_22) = A_20
      | '#skF_2'(A_20,B_21,C_22) != A_20
      | k2_tarski(A_20,B_21) = C_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3080,plain,(
    ! [B_21,C_22] :
      ( '#skF_2'(B_21,B_21,C_22) != B_21
      | k2_tarski(B_21,B_21) = C_22
      | '#skF_1'(B_21,B_21,C_22) = B_21 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_46])).

tff(c_8377,plain,(
    ! [B_7606,C_7607] :
      ( '#skF_2'(B_7606,B_7606,C_7607) != B_7606
      | k1_tarski(B_7606) = C_7607
      | '#skF_1'(B_7606,B_7606,C_7607) = B_7606 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3080])).

tff(c_9847,plain,(
    ! [C_7607] :
      ( k2_xboole_0(k4_xboole_0('#skF_4',C_7607),k1_tarski('#skF_3')) != '#skF_4'
      | '#skF_2'('#skF_3','#skF_3',C_7607) != '#skF_3'
      | '#skF_1'('#skF_3','#skF_3',C_7607) = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8377,c_70])).

tff(c_14642,plain,(
    ! [A_14724] :
      ( k2_xboole_0('#skF_4',k1_tarski('#skF_3')) != '#skF_4'
      | '#skF_2'('#skF_3','#skF_3',k1_tarski(A_14724)) != '#skF_3'
      | '#skF_1'('#skF_3','#skF_3',k1_tarski(A_14724)) = '#skF_3'
      | r2_hidden(A_14724,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14610,c_9847])).

tff(c_14811,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_14642])).

tff(c_14821,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_997,c_14811])).

tff(c_14825,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_14821])).

tff(c_14827,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_14642])).

tff(c_2160,plain,(
    ! [A_8,B_9] : k5_xboole_0(k3_xboole_0(A_8,B_9),k4_xboole_0(A_8,B_9)) = A_8 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2070])).

tff(c_13913,plain,(
    ! [A_14439,B_14440,C_14441] : k5_xboole_0(k5_xboole_0(A_14439,B_14440),k5_xboole_0(k3_xboole_0(A_14439,B_14440),C_14441)) = k5_xboole_0(k2_xboole_0(A_14439,B_14440),C_14441) ),
    inference(superposition,[status(thm),theory(equality)],[c_876,c_30])).

tff(c_14088,plain,(
    ! [A_8,B_9] : k5_xboole_0(k2_xboole_0(A_8,B_9),k4_xboole_0(A_8,B_9)) = k5_xboole_0(k5_xboole_0(A_8,B_9),A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_2160,c_13913])).

tff(c_24546,plain,(
    ! [A_20390,B_20391] : k5_xboole_0(k2_xboole_0(A_20390,B_20391),k4_xboole_0(A_20390,B_20391)) = B_20391 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2020,c_30,c_14088])).

tff(c_26355,plain,(
    ! [A_21149,B_21150] : k5_xboole_0(k2_xboole_0(A_21149,B_21150),B_21150) = k4_xboole_0(A_21149,B_21150) ),
    inference(superposition,[status(thm),theory(equality)],[c_24546,c_1789])).

tff(c_26510,plain,(
    k5_xboole_0('#skF_4',k1_tarski('#skF_3')) = k4_xboole_0('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14827,c_26355])).

tff(c_2118,plain,(
    ! [A_42,C_105] : k5_xboole_0(k5_xboole_0(A_42,C_105),C_105) = A_42 ),
    inference(superposition,[status(thm),theory(equality)],[c_1789,c_2070])).

tff(c_27202,plain,(
    k5_xboole_0(k4_xboole_0('#skF_4',k1_tarski('#skF_3')),k1_tarski('#skF_3')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_26510,c_2118])).

tff(c_124472,plain,
    ( k2_xboole_0(k4_xboole_0('#skF_4',k1_tarski('#skF_3')),k1_tarski('#skF_3')) = '#skF_4'
    | r2_hidden('#skF_3',k4_xboole_0('#skF_4',k1_tarski('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_124240,c_27202])).

tff(c_124943,plain,
    ( k2_xboole_0(k1_tarski('#skF_3'),k4_xboole_0('#skF_4',k1_tarski('#skF_3'))) = '#skF_4'
    | r2_hidden('#skF_3',k4_xboole_0('#skF_4',k1_tarski('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22858,c_124472])).

tff(c_124945,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1628,c_23074,c_124943])).

tff(c_124947,plain,(
    r2_hidden('#skF_3',k4_xboole_0('#skF_4',k1_tarski('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1379])).

tff(c_1451,plain,(
    ! [A_135,C_136,B_137] :
      ( ~ r2_hidden(A_135,C_136)
      | ~ r2_hidden(A_135,B_137)
      | ~ r2_hidden(A_135,k5_xboole_0(B_137,C_136)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_133703,plain,(
    ! [A_52315,A_52316,B_52317] :
      ( ~ r2_hidden(A_52315,k3_xboole_0(A_52316,B_52317))
      | ~ r2_hidden(A_52315,A_52316)
      | ~ r2_hidden(A_52315,k4_xboole_0(A_52316,B_52317)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1451])).

tff(c_133728,plain,
    ( ~ r2_hidden('#skF_3',k3_xboole_0('#skF_4',k1_tarski('#skF_3')))
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_124947,c_133703])).

tff(c_133744,plain,(
    ~ r2_hidden('#skF_3',k3_xboole_0('#skF_4',k1_tarski('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_133728])).

tff(c_139769,plain,(
    ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139749,c_133744])).

tff(c_139772,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_139769])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:20:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 39.84/28.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.94/28.64  
% 39.94/28.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.94/28.64  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 39.94/28.64  
% 39.94/28.64  %Foreground sorts:
% 39.94/28.64  
% 39.94/28.64  
% 39.94/28.64  %Background operators:
% 39.94/28.64  
% 39.94/28.64  
% 39.94/28.64  %Foreground operators:
% 39.94/28.64  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 39.94/28.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 39.94/28.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 39.94/28.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 39.94/28.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 39.94/28.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 39.94/28.64  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 39.94/28.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 39.94/28.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 39.94/28.64  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 39.94/28.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 39.94/28.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 39.94/28.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 39.94/28.64  tff('#skF_3', type, '#skF_3': $i).
% 39.94/28.64  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 39.94/28.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 39.94/28.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 39.94/28.64  tff(k3_tarski, type, k3_tarski: $i > $i).
% 39.94/28.64  tff('#skF_4', type, '#skF_4': $i).
% 39.94/28.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 39.94/28.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 39.94/28.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 39.94/28.64  
% 40.39/28.69  tff(f_65, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 40.39/28.69  tff(f_63, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 40.39/28.69  tff(f_46, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 40.39/28.69  tff(f_84, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 40.39/28.69  tff(f_38, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 40.39/28.69  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 40.39/28.69  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 40.39/28.69  tff(f_52, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 40.39/28.69  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 40.39/28.69  tff(f_89, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 40.39/28.69  tff(f_75, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 40.39/28.69  tff(f_54, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 40.39/28.69  tff(f_80, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 40.39/28.69  tff(f_50, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 40.39/28.69  tff(f_34, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 40.39/28.69  tff(c_52, plain, (![A_26]: (k2_tarski(A_26, A_26)=k1_tarski(A_26))), inference(cnfTransformation, [status(thm)], [f_65])).
% 40.39/28.69  tff(c_91, plain, (![D_45, B_46]: (r2_hidden(D_45, k2_tarski(D_45, B_46)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 40.39/28.69  tff(c_94, plain, (![A_26]: (r2_hidden(A_26, k1_tarski(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_91])).
% 40.39/28.69  tff(c_24, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_46])).
% 40.39/28.69  tff(c_68, plain, (![A_42]: (r1_tarski(A_42, k1_zfmisc_1(k3_tarski(A_42))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 40.39/28.69  tff(c_136, plain, (![A_55, B_56]: (k4_xboole_0(A_55, B_56)=k1_xboole_0 | ~r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_38])).
% 40.39/28.69  tff(c_144, plain, (![A_42]: (k4_xboole_0(A_42, k1_zfmisc_1(k3_tarski(A_42)))=k1_xboole_0)), inference(resolution, [status(thm)], [c_68, c_136])).
% 40.39/28.69  tff(c_164, plain, (![A_61, B_62]: (k3_xboole_0(A_61, B_62)=A_61 | ~r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_44])).
% 40.39/28.69  tff(c_172, plain, (![A_42]: (k3_xboole_0(A_42, k1_zfmisc_1(k3_tarski(A_42)))=A_42)), inference(resolution, [status(thm)], [c_68, c_164])).
% 40.39/28.69  tff(c_288, plain, (![A_79, B_80]: (k5_xboole_0(A_79, k3_xboole_0(A_79, B_80))=k4_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_40])).
% 40.39/28.69  tff(c_297, plain, (![A_42]: (k4_xboole_0(A_42, k1_zfmisc_1(k3_tarski(A_42)))=k5_xboole_0(A_42, A_42))), inference(superposition, [status(thm), theory('equality')], [c_172, c_288])).
% 40.39/28.69  tff(c_306, plain, (![A_42]: (k5_xboole_0(A_42, A_42)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_144, c_297])).
% 40.39/28.69  tff(c_523, plain, (![A_103, B_104, C_105]: (k5_xboole_0(k5_xboole_0(A_103, B_104), C_105)=k5_xboole_0(A_103, k5_xboole_0(B_104, C_105)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 40.39/28.69  tff(c_124962, plain, (![A_40587, C_40588]: (k5_xboole_0(A_40587, k5_xboole_0(A_40587, C_40588))=k5_xboole_0(k1_xboole_0, C_40588))), inference(superposition, [status(thm), theory('equality')], [c_306, c_523])).
% 40.39/28.69  tff(c_125082, plain, (![A_42]: (k5_xboole_0(k1_xboole_0, A_42)=k5_xboole_0(A_42, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_306, c_124962])).
% 40.39/28.69  tff(c_125115, plain, (![A_42]: (k5_xboole_0(k1_xboole_0, A_42)=A_42)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_125082])).
% 40.39/28.69  tff(c_537, plain, (![A_103, B_104]: (k5_xboole_0(A_103, k5_xboole_0(B_104, k5_xboole_0(A_103, B_104)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_523, c_306])).
% 40.39/28.69  tff(c_561, plain, (![A_42, C_105]: (k5_xboole_0(A_42, k5_xboole_0(A_42, C_105))=k5_xboole_0(k1_xboole_0, C_105))), inference(superposition, [status(thm), theory('equality')], [c_306, c_523])).
% 40.39/28.69  tff(c_125237, plain, (![A_40590, C_40591]: (k5_xboole_0(A_40590, k5_xboole_0(A_40590, C_40591))=C_40591)), inference(demodulation, [status(thm), theory('equality')], [c_125115, c_561])).
% 40.39/28.69  tff(c_125311, plain, (![B_104, A_103]: (k5_xboole_0(B_104, k5_xboole_0(A_103, B_104))=k5_xboole_0(A_103, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_537, c_125237])).
% 40.39/28.69  tff(c_125411, plain, (![B_40596, A_40597]: (k5_xboole_0(B_40596, k5_xboole_0(A_40597, B_40596))=A_40597)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_125311])).
% 40.39/28.69  tff(c_125117, plain, (![A_42, C_105]: (k5_xboole_0(A_42, k5_xboole_0(A_42, C_105))=C_105)), inference(demodulation, [status(thm), theory('equality')], [c_125115, c_561])).
% 40.39/28.69  tff(c_125420, plain, (![B_40596, A_40597]: (k5_xboole_0(B_40596, A_40597)=k5_xboole_0(A_40597, B_40596))), inference(superposition, [status(thm), theory('equality')], [c_125411, c_125117])).
% 40.39/28.69  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 40.39/28.69  tff(c_72, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 40.39/28.69  tff(c_248, plain, (![A_74, B_75]: (r1_tarski(k1_tarski(A_74), B_75) | ~r2_hidden(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_75])).
% 40.39/28.69  tff(c_18, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=k1_xboole_0 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 40.39/28.69  tff(c_260, plain, (![A_74, B_75]: (k4_xboole_0(k1_tarski(A_74), B_75)=k1_xboole_0 | ~r2_hidden(A_74, B_75))), inference(resolution, [status(thm)], [c_248, c_18])).
% 40.39/28.69  tff(c_303, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_288])).
% 40.39/28.69  tff(c_876, plain, (![A_112, B_113]: (k5_xboole_0(k5_xboole_0(A_112, B_113), k3_xboole_0(A_112, B_113))=k2_xboole_0(A_112, B_113))), inference(cnfTransformation, [status(thm)], [f_54])).
% 40.39/28.69  tff(c_30, plain, (![A_15, B_16, C_17]: (k5_xboole_0(k5_xboole_0(A_15, B_16), C_17)=k5_xboole_0(A_15, k5_xboole_0(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 40.39/28.69  tff(c_891, plain, (![A_112, B_113]: (k5_xboole_0(A_112, k5_xboole_0(B_113, k3_xboole_0(A_112, B_113)))=k2_xboole_0(A_112, B_113))), inference(superposition, [status(thm), theory('equality')], [c_876, c_30])).
% 40.39/28.69  tff(c_949, plain, (![A_114, B_115]: (k5_xboole_0(A_114, k4_xboole_0(B_115, A_114))=k2_xboole_0(A_114, B_115))), inference(demodulation, [status(thm), theory('equality')], [c_303, c_891])).
% 40.39/28.69  tff(c_990, plain, (![B_75, A_74]: (k2_xboole_0(B_75, k1_tarski(A_74))=k5_xboole_0(B_75, k1_xboole_0) | ~r2_hidden(A_74, B_75))), inference(superposition, [status(thm), theory('equality')], [c_260, c_949])).
% 40.39/28.69  tff(c_997, plain, (![B_75, A_74]: (k2_xboole_0(B_75, k1_tarski(A_74))=B_75 | ~r2_hidden(A_74, B_75))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_990])).
% 40.39/28.69  tff(c_233, plain, (![A_69, B_70]: (r1_xboole_0(k1_tarski(A_69), B_70) | r2_hidden(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_80])).
% 40.39/28.69  tff(c_26, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=A_13 | ~r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 40.39/28.69  tff(c_237, plain, (![A_69, B_70]: (k4_xboole_0(k1_tarski(A_69), B_70)=k1_tarski(A_69) | r2_hidden(A_69, B_70))), inference(resolution, [status(thm)], [c_233, c_26])).
% 40.39/28.69  tff(c_20, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 40.39/28.69  tff(c_129228, plain, (![A_46663, B_46664, C_46665]: (k5_xboole_0(A_46663, k5_xboole_0(k3_xboole_0(A_46663, B_46664), C_46665))=k5_xboole_0(k4_xboole_0(A_46663, B_46664), C_46665))), inference(superposition, [status(thm), theory('equality')], [c_20, c_523])).
% 40.39/28.69  tff(c_129386, plain, (![A_46663, B_46664]: (k5_xboole_0(k4_xboole_0(A_46663, B_46664), k3_xboole_0(A_46663, B_46664))=k5_xboole_0(A_46663, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_306, c_129228])).
% 40.39/28.69  tff(c_129424, plain, (![A_46728, B_46729]: (k5_xboole_0(k4_xboole_0(A_46728, B_46729), k3_xboole_0(A_46728, B_46729))=A_46728)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_129386])).
% 40.39/28.69  tff(c_129638, plain, (![A_46855, B_46856]: (k5_xboole_0(k4_xboole_0(A_46855, B_46856), k3_xboole_0(B_46856, A_46855))=A_46855)), inference(superposition, [status(thm), theory('equality')], [c_2, c_129424])).
% 40.39/28.69  tff(c_131481, plain, (![A_50429, B_50430]: (k5_xboole_0(k4_xboole_0(A_50429, B_50430), A_50429)=k3_xboole_0(B_50430, A_50429))), inference(superposition, [status(thm), theory('equality')], [c_129638, c_125117])).
% 40.39/28.69  tff(c_131535, plain, (![A_69, B_70]: (k5_xboole_0(k1_tarski(A_69), k1_tarski(A_69))=k3_xboole_0(B_70, k1_tarski(A_69)) | r2_hidden(A_69, B_70))), inference(superposition, [status(thm), theory('equality')], [c_237, c_131481])).
% 40.39/28.69  tff(c_132470, plain, (![B_51372, A_51373]: (k3_xboole_0(B_51372, k1_tarski(A_51373))=k1_xboole_0 | r2_hidden(A_51373, B_51372))), inference(demodulation, [status(thm), theory('equality')], [c_306, c_131535])).
% 40.39/28.69  tff(c_132538, plain, (![B_51372, A_51373]: (k4_xboole_0(B_51372, k1_tarski(A_51373))=k5_xboole_0(B_51372, k1_xboole_0) | r2_hidden(A_51373, B_51372))), inference(superposition, [status(thm), theory('equality')], [c_132470, c_20])).
% 40.39/28.69  tff(c_139083, plain, (![B_56280, A_56281]: (k4_xboole_0(B_56280, k1_tarski(A_56281))=B_56280 | r2_hidden(A_56281, B_56280))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_132538])).
% 40.39/28.69  tff(c_42, plain, (![A_20, B_21, C_22]: ('#skF_1'(A_20, B_21, C_22)=B_21 | '#skF_1'(A_20, B_21, C_22)=A_20 | '#skF_2'(A_20, B_21, C_22)!=B_21 | k2_tarski(A_20, B_21)=C_22)), inference(cnfTransformation, [status(thm)], [f_63])).
% 40.39/28.69  tff(c_125679, plain, (![B_21, C_22]: ('#skF_2'(B_21, B_21, C_22)!=B_21 | k2_tarski(B_21, B_21)=C_22 | '#skF_1'(B_21, B_21, C_22)=B_21)), inference(factorization, [status(thm), theory('equality')], [c_42])).
% 40.39/28.69  tff(c_130107, plain, (![B_47109, C_47110]: ('#skF_2'(B_47109, B_47109, C_47110)!=B_47109 | k1_tarski(B_47109)=C_47110 | '#skF_1'(B_47109, B_47109, C_47110)=B_47109)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_125679])).
% 40.39/28.69  tff(c_70, plain, (k2_xboole_0(k4_xboole_0('#skF_4', k1_tarski('#skF_3')), k1_tarski('#skF_3'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_89])).
% 40.39/28.69  tff(c_131212, plain, (![C_47110]: (k2_xboole_0(k4_xboole_0('#skF_4', C_47110), k1_tarski('#skF_3'))!='#skF_4' | '#skF_2'('#skF_3', '#skF_3', C_47110)!='#skF_3' | '#skF_1'('#skF_3', '#skF_3', C_47110)='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_130107, c_70])).
% 40.39/28.69  tff(c_139139, plain, (![A_56281]: (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))!='#skF_4' | '#skF_2'('#skF_3', '#skF_3', k1_tarski(A_56281))!='#skF_3' | '#skF_1'('#skF_3', '#skF_3', k1_tarski(A_56281))='#skF_3' | r2_hidden(A_56281, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_139083, c_131212])).
% 40.39/28.69  tff(c_139557, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_139139])).
% 40.39/28.69  tff(c_139567, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_997, c_139557])).
% 40.39/28.69  tff(c_139571, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_139567])).
% 40.39/28.69  tff(c_139573, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(splitRight, [status(thm)], [c_139139])).
% 40.39/28.69  tff(c_943, plain, (![A_112, B_113]: (k5_xboole_0(A_112, k4_xboole_0(B_113, A_112))=k2_xboole_0(A_112, B_113))), inference(demodulation, [status(thm), theory('equality')], [c_303, c_891])).
% 40.39/28.69  tff(c_125305, plain, (![A_112, B_113]: (k5_xboole_0(A_112, k2_xboole_0(A_112, B_113))=k4_xboole_0(B_113, A_112))), inference(superposition, [status(thm), theory('equality')], [c_943, c_125237])).
% 40.39/28.69  tff(c_139583, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k5_xboole_0('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_139573, c_125305])).
% 40.39/28.69  tff(c_139630, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_306, c_139583])).
% 40.39/28.69  tff(c_125498, plain, (![A_8, B_9]: (k5_xboole_0(k3_xboole_0(A_8, B_9), k4_xboole_0(A_8, B_9))=A_8)), inference(superposition, [status(thm), theory('equality')], [c_20, c_125411])).
% 40.39/28.69  tff(c_139665, plain, (k5_xboole_0(k3_xboole_0(k1_tarski('#skF_3'), '#skF_4'), k1_xboole_0)=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_139630, c_125498])).
% 40.39/28.69  tff(c_139749, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_125115, c_125420, c_2, c_139665])).
% 40.39/28.69  tff(c_1350, plain, (![B_130, A_131]: (k2_xboole_0(B_130, k1_tarski(A_131))=B_130 | ~r2_hidden(A_131, B_130))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_990])).
% 40.39/28.69  tff(c_1379, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))!='#skF_4' | ~r2_hidden('#skF_3', k4_xboole_0('#skF_4', k1_tarski('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1350, c_70])).
% 40.39/28.69  tff(c_1628, plain, (~r2_hidden('#skF_3', k4_xboole_0('#skF_4', k1_tarski('#skF_3')))), inference(splitLeft, [status(thm)], [c_1379])).
% 40.39/28.69  tff(c_6212, plain, (![A_6271, B_6272, C_6273]: (k5_xboole_0(A_6271, k5_xboole_0(k3_xboole_0(A_6271, B_6272), C_6273))=k5_xboole_0(k4_xboole_0(A_6271, B_6272), C_6273))), inference(superposition, [status(thm), theory('equality')], [c_20, c_523])).
% 40.39/28.69  tff(c_6374, plain, (![A_6271, B_6272]: (k5_xboole_0(k4_xboole_0(A_6271, B_6272), k3_xboole_0(A_6271, B_6272))=k5_xboole_0(A_6271, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_306, c_6212])).
% 40.39/28.69  tff(c_6411, plain, (![A_6336, B_6337]: (k5_xboole_0(k4_xboole_0(A_6336, B_6337), k3_xboole_0(A_6336, B_6337))=A_6336)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_6374])).
% 40.39/28.69  tff(c_6625, plain, (![A_6463, B_6464]: (k5_xboole_0(k4_xboole_0(A_6463, B_6464), k3_xboole_0(B_6464, A_6463))=A_6463)), inference(superposition, [status(thm), theory('equality')], [c_2, c_6411])).
% 40.39/28.69  tff(c_1634, plain, (![A_141, C_142]: (k5_xboole_0(A_141, k5_xboole_0(A_141, C_142))=k5_xboole_0(k1_xboole_0, C_142))), inference(superposition, [status(thm), theory('equality')], [c_306, c_523])).
% 40.39/28.69  tff(c_1754, plain, (![A_42]: (k5_xboole_0(k1_xboole_0, A_42)=k5_xboole_0(A_42, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_306, c_1634])).
% 40.39/28.69  tff(c_1787, plain, (![A_42]: (k5_xboole_0(k1_xboole_0, A_42)=A_42)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1754])).
% 40.39/28.69  tff(c_1909, plain, (![A_144, C_145]: (k5_xboole_0(A_144, k5_xboole_0(A_144, C_145))=C_145)), inference(demodulation, [status(thm), theory('equality')], [c_1787, c_561])).
% 40.39/28.69  tff(c_1983, plain, (![B_104, A_103]: (k5_xboole_0(B_104, k5_xboole_0(A_103, B_104))=k5_xboole_0(A_103, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_537, c_1909])).
% 40.39/28.69  tff(c_2020, plain, (![B_104, A_103]: (k5_xboole_0(B_104, k5_xboole_0(A_103, B_104))=A_103)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1983])).
% 40.39/28.69  tff(c_12153, plain, (![B_13403, A_13404]: (k5_xboole_0(k3_xboole_0(B_13403, A_13404), A_13404)=k4_xboole_0(A_13404, B_13403))), inference(superposition, [status(thm), theory('equality')], [c_6625, c_2020])).
% 40.39/28.69  tff(c_568, plain, (![A_8, B_9, C_105]: (k5_xboole_0(A_8, k5_xboole_0(k3_xboole_0(A_8, B_9), C_105))=k5_xboole_0(k4_xboole_0(A_8, B_9), C_105))), inference(superposition, [status(thm), theory('equality')], [c_20, c_523])).
% 40.39/28.69  tff(c_12171, plain, (![B_13403, A_13404]: (k5_xboole_0(k4_xboole_0(B_13403, A_13404), A_13404)=k5_xboole_0(B_13403, k4_xboole_0(A_13404, B_13403)))), inference(superposition, [status(thm), theory('equality')], [c_12153, c_568])).
% 40.39/28.69  tff(c_22852, plain, (![B_19445, A_19446]: (k5_xboole_0(k4_xboole_0(B_19445, A_19446), A_19446)=k2_xboole_0(B_19445, A_19446))), inference(demodulation, [status(thm), theory('equality')], [c_943, c_12171])).
% 40.39/28.69  tff(c_5540, plain, (![A_5891, B_5892]: (k5_xboole_0(A_5891, k2_xboole_0(A_5891, B_5892))=k4_xboole_0(B_5892, A_5891))), inference(superposition, [status(thm), theory('equality')], [c_943, c_1909])).
% 40.39/28.69  tff(c_2070, plain, (![B_151, A_152]: (k5_xboole_0(B_151, k5_xboole_0(A_152, B_151))=A_152)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1983])).
% 40.39/28.69  tff(c_2073, plain, (![A_152, B_151]: (k5_xboole_0(k5_xboole_0(A_152, B_151), A_152)=B_151)), inference(superposition, [status(thm), theory('equality')], [c_2070, c_2020])).
% 40.39/28.69  tff(c_5561, plain, (![B_5892, A_5891]: (k5_xboole_0(k4_xboole_0(B_5892, A_5891), A_5891)=k2_xboole_0(A_5891, B_5892))), inference(superposition, [status(thm), theory('equality')], [c_5540, c_2073])).
% 40.39/28.69  tff(c_22858, plain, (![B_19445, A_19446]: (k2_xboole_0(B_19445, A_19446)=k2_xboole_0(A_19446, B_19445))), inference(superposition, [status(thm), theory('equality')], [c_22852, c_5561])).
% 40.39/28.69  tff(c_23074, plain, (k2_xboole_0(k1_tarski('#skF_3'), k4_xboole_0('#skF_4', k1_tarski('#skF_3')))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_22858, c_70])).
% 40.39/28.69  tff(c_4207, plain, (![A_4816, B_4817]: (k4_xboole_0(k1_tarski(A_4816), B_4817)=k1_tarski(A_4816) | r2_hidden(A_4816, B_4817))), inference(resolution, [status(thm)], [c_233, c_26])).
% 40.39/28.69  tff(c_124240, plain, (![B_40487, A_40488]: (k5_xboole_0(B_40487, k1_tarski(A_40488))=k2_xboole_0(B_40487, k1_tarski(A_40488)) | r2_hidden(A_40488, B_40487))), inference(superposition, [status(thm), theory('equality')], [c_4207, c_943])).
% 40.39/28.69  tff(c_1789, plain, (![A_42, C_105]: (k5_xboole_0(A_42, k5_xboole_0(A_42, C_105))=C_105)), inference(demodulation, [status(thm), theory('equality')], [c_1787, c_561])).
% 40.39/28.69  tff(c_6861, plain, (![A_6590, B_6591]: (k5_xboole_0(k4_xboole_0(A_6590, B_6591), A_6590)=k3_xboole_0(B_6591, A_6590))), inference(superposition, [status(thm), theory('equality')], [c_6625, c_1789])).
% 40.39/28.69  tff(c_6916, plain, (![A_69, B_70]: (k5_xboole_0(k1_tarski(A_69), k1_tarski(A_69))=k3_xboole_0(B_70, k1_tarski(A_69)) | r2_hidden(A_69, B_70))), inference(superposition, [status(thm), theory('equality')], [c_237, c_6861])).
% 40.39/28.69  tff(c_6963, plain, (![B_70, A_69]: (k3_xboole_0(B_70, k1_tarski(A_69))=k1_xboole_0 | r2_hidden(A_69, B_70))), inference(demodulation, [status(thm), theory('equality')], [c_306, c_6916])).
% 40.39/28.69  tff(c_11977, plain, (![A_13214, B_13215]: (k5_xboole_0(k3_xboole_0(A_13214, B_13215), A_13214)=k4_xboole_0(A_13214, B_13215))), inference(superposition, [status(thm), theory('equality')], [c_6411, c_2020])).
% 40.39/28.69  tff(c_12040, plain, (![B_70, A_69]: (k4_xboole_0(B_70, k1_tarski(A_69))=k5_xboole_0(k1_xboole_0, B_70) | r2_hidden(A_69, B_70))), inference(superposition, [status(thm), theory('equality')], [c_6963, c_11977])).
% 40.39/28.69  tff(c_14610, plain, (![B_14723, A_14724]: (k4_xboole_0(B_14723, k1_tarski(A_14724))=B_14723 | r2_hidden(A_14724, B_14723))), inference(demodulation, [status(thm), theory('equality')], [c_1787, c_12040])).
% 40.39/28.69  tff(c_46, plain, (![A_20, B_21, C_22]: ('#skF_1'(A_20, B_21, C_22)=B_21 | '#skF_1'(A_20, B_21, C_22)=A_20 | '#skF_2'(A_20, B_21, C_22)!=A_20 | k2_tarski(A_20, B_21)=C_22)), inference(cnfTransformation, [status(thm)], [f_63])).
% 40.39/28.69  tff(c_3080, plain, (![B_21, C_22]: ('#skF_2'(B_21, B_21, C_22)!=B_21 | k2_tarski(B_21, B_21)=C_22 | '#skF_1'(B_21, B_21, C_22)=B_21)), inference(factorization, [status(thm), theory('equality')], [c_46])).
% 40.39/28.69  tff(c_8377, plain, (![B_7606, C_7607]: ('#skF_2'(B_7606, B_7606, C_7607)!=B_7606 | k1_tarski(B_7606)=C_7607 | '#skF_1'(B_7606, B_7606, C_7607)=B_7606)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_3080])).
% 40.39/28.69  tff(c_9847, plain, (![C_7607]: (k2_xboole_0(k4_xboole_0('#skF_4', C_7607), k1_tarski('#skF_3'))!='#skF_4' | '#skF_2'('#skF_3', '#skF_3', C_7607)!='#skF_3' | '#skF_1'('#skF_3', '#skF_3', C_7607)='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8377, c_70])).
% 40.39/28.69  tff(c_14642, plain, (![A_14724]: (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))!='#skF_4' | '#skF_2'('#skF_3', '#skF_3', k1_tarski(A_14724))!='#skF_3' | '#skF_1'('#skF_3', '#skF_3', k1_tarski(A_14724))='#skF_3' | r2_hidden(A_14724, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_14610, c_9847])).
% 40.39/28.69  tff(c_14811, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_14642])).
% 40.39/28.69  tff(c_14821, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_997, c_14811])).
% 40.39/28.69  tff(c_14825, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_14821])).
% 40.39/28.69  tff(c_14827, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(splitRight, [status(thm)], [c_14642])).
% 40.39/28.69  tff(c_2160, plain, (![A_8, B_9]: (k5_xboole_0(k3_xboole_0(A_8, B_9), k4_xboole_0(A_8, B_9))=A_8)), inference(superposition, [status(thm), theory('equality')], [c_20, c_2070])).
% 40.39/28.69  tff(c_13913, plain, (![A_14439, B_14440, C_14441]: (k5_xboole_0(k5_xboole_0(A_14439, B_14440), k5_xboole_0(k3_xboole_0(A_14439, B_14440), C_14441))=k5_xboole_0(k2_xboole_0(A_14439, B_14440), C_14441))), inference(superposition, [status(thm), theory('equality')], [c_876, c_30])).
% 40.39/28.69  tff(c_14088, plain, (![A_8, B_9]: (k5_xboole_0(k2_xboole_0(A_8, B_9), k4_xboole_0(A_8, B_9))=k5_xboole_0(k5_xboole_0(A_8, B_9), A_8))), inference(superposition, [status(thm), theory('equality')], [c_2160, c_13913])).
% 40.39/28.69  tff(c_24546, plain, (![A_20390, B_20391]: (k5_xboole_0(k2_xboole_0(A_20390, B_20391), k4_xboole_0(A_20390, B_20391))=B_20391)), inference(demodulation, [status(thm), theory('equality')], [c_2020, c_30, c_14088])).
% 40.39/28.69  tff(c_26355, plain, (![A_21149, B_21150]: (k5_xboole_0(k2_xboole_0(A_21149, B_21150), B_21150)=k4_xboole_0(A_21149, B_21150))), inference(superposition, [status(thm), theory('equality')], [c_24546, c_1789])).
% 40.39/28.69  tff(c_26510, plain, (k5_xboole_0('#skF_4', k1_tarski('#skF_3'))=k4_xboole_0('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_14827, c_26355])).
% 40.39/28.69  tff(c_2118, plain, (![A_42, C_105]: (k5_xboole_0(k5_xboole_0(A_42, C_105), C_105)=A_42)), inference(superposition, [status(thm), theory('equality')], [c_1789, c_2070])).
% 40.39/28.69  tff(c_27202, plain, (k5_xboole_0(k4_xboole_0('#skF_4', k1_tarski('#skF_3')), k1_tarski('#skF_3'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_26510, c_2118])).
% 40.39/28.69  tff(c_124472, plain, (k2_xboole_0(k4_xboole_0('#skF_4', k1_tarski('#skF_3')), k1_tarski('#skF_3'))='#skF_4' | r2_hidden('#skF_3', k4_xboole_0('#skF_4', k1_tarski('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_124240, c_27202])).
% 40.39/28.69  tff(c_124943, plain, (k2_xboole_0(k1_tarski('#skF_3'), k4_xboole_0('#skF_4', k1_tarski('#skF_3')))='#skF_4' | r2_hidden('#skF_3', k4_xboole_0('#skF_4', k1_tarski('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_22858, c_124472])).
% 40.39/28.69  tff(c_124945, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1628, c_23074, c_124943])).
% 40.39/28.69  tff(c_124947, plain, (r2_hidden('#skF_3', k4_xboole_0('#skF_4', k1_tarski('#skF_3')))), inference(splitRight, [status(thm)], [c_1379])).
% 40.39/28.69  tff(c_1451, plain, (![A_135, C_136, B_137]: (~r2_hidden(A_135, C_136) | ~r2_hidden(A_135, B_137) | ~r2_hidden(A_135, k5_xboole_0(B_137, C_136)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 40.39/28.69  tff(c_133703, plain, (![A_52315, A_52316, B_52317]: (~r2_hidden(A_52315, k3_xboole_0(A_52316, B_52317)) | ~r2_hidden(A_52315, A_52316) | ~r2_hidden(A_52315, k4_xboole_0(A_52316, B_52317)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1451])).
% 40.39/28.69  tff(c_133728, plain, (~r2_hidden('#skF_3', k3_xboole_0('#skF_4', k1_tarski('#skF_3'))) | ~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_124947, c_133703])).
% 40.39/28.69  tff(c_133744, plain, (~r2_hidden('#skF_3', k3_xboole_0('#skF_4', k1_tarski('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_133728])).
% 40.39/28.69  tff(c_139769, plain, (~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_139749, c_133744])).
% 40.39/28.69  tff(c_139772, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_139769])).
% 40.39/28.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 40.39/28.69  
% 40.39/28.69  Inference rules
% 40.39/28.69  ----------------------
% 40.39/28.69  #Ref     : 0
% 40.39/28.69  #Sup     : 31785
% 40.39/28.69  #Fact    : 186
% 40.39/28.69  #Define  : 0
% 40.39/28.69  #Split   : 26
% 40.39/28.69  #Chain   : 0
% 40.39/28.69  #Close   : 0
% 40.39/28.69  
% 40.39/28.69  Ordering : KBO
% 40.39/28.69  
% 40.39/28.69  Simplification rules
% 40.39/28.69  ----------------------
% 40.39/28.69  #Subsume      : 4811
% 40.39/28.69  #Demod        : 28761
% 40.39/28.69  #Tautology    : 8707
% 40.39/28.69  #SimpNegUnit  : 97
% 40.39/28.69  #BackRed      : 19
% 40.39/28.69  
% 40.39/28.69  #Partial instantiations: 28784
% 40.39/28.69  #Strategies tried      : 1
% 40.39/28.69  
% 40.39/28.69  Timing (in seconds)
% 40.39/28.69  ----------------------
% 40.39/28.69  Preprocessing        : 0.33
% 40.39/28.69  Parsing              : 0.17
% 40.39/28.69  CNF conversion       : 0.02
% 40.39/28.70  Main loop            : 27.50
% 40.39/28.70  Inferencing          : 3.64
% 40.39/28.70  Reduction            : 16.87
% 40.39/28.70  Demodulation         : 15.59
% 40.39/28.70  BG Simplification    : 0.51
% 40.39/28.70  Subsumption          : 5.63
% 40.39/28.70  Abstraction          : 0.79
% 40.39/28.70  MUC search           : 0.00
% 40.39/28.70  Cooper               : 0.00
% 40.39/28.70  Total                : 27.93
% 40.39/28.70  Index Insertion      : 0.00
% 40.39/28.70  Index Deletion       : 0.00
% 40.39/28.70  Index Matching       : 0.00
% 40.39/28.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
