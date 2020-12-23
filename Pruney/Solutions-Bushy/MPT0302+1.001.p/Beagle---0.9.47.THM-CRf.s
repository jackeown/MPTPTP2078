%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0302+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:04 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 125 expanded)
%              Number of leaves         :   16 (  49 expanded)
%              Depth                    :   14
%              Number of atoms          :   74 ( 269 expanded)
%              Number of equality atoms :   22 ( 100 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(B,A)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_45,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_30,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_18,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),B_6)
      | r2_hidden('#skF_2'(A_5,B_6),A_5)
      | B_6 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_3'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_57,plain,(
    ! [A_31,B_32,C_33,D_34] :
      ( r2_hidden(k4_tarski(A_31,B_32),k2_zfmisc_1(C_33,D_34))
      | ~ r2_hidden(B_32,D_34)
      | ~ r2_hidden(A_31,C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_24,plain,(
    k2_zfmisc_1('#skF_5','#skF_4') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_30,plain,(
    ! [A_11,C_12,B_13,D_14] :
      ( r2_hidden(A_11,C_12)
      | ~ r2_hidden(k4_tarski(A_11,B_13),k2_zfmisc_1(C_12,D_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_33,plain,(
    ! [A_11,B_13] :
      ( r2_hidden(A_11,'#skF_5')
      | ~ r2_hidden(k4_tarski(A_11,B_13),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_30])).

tff(c_76,plain,(
    ! [A_31,B_32] :
      ( r2_hidden(A_31,'#skF_5')
      | ~ r2_hidden(B_32,'#skF_5')
      | ~ r2_hidden(A_31,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_57,c_33])).

tff(c_159,plain,(
    ! [B_41] : ~ r2_hidden(B_41,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_173,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_16,c_159])).

tff(c_179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_173])).

tff(c_181,plain,(
    ! [A_42] :
      ( r2_hidden(A_42,'#skF_5')
      | ~ r2_hidden(A_42,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),B_6)
      | ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | B_6 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_195,plain,(
    ! [A_43] :
      ( r2_hidden('#skF_1'(A_43,'#skF_5'),'#skF_5')
      | A_43 = '#skF_5'
      | ~ r2_hidden('#skF_2'(A_43,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_181,c_10])).

tff(c_199,plain,
    ( r2_hidden('#skF_1'('#skF_4','#skF_5'),'#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_14,c_195])).

tff(c_206,plain,(
    r2_hidden('#skF_1'('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_18,c_199])).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_34,plain,(
    ! [B_15,D_16,A_17,C_18] :
      ( r2_hidden(B_15,D_16)
      | ~ r2_hidden(k4_tarski(A_17,B_15),k2_zfmisc_1(C_18,D_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_37,plain,(
    ! [B_15,A_17] :
      ( r2_hidden(B_15,'#skF_4')
      | ~ r2_hidden(k4_tarski(A_17,B_15),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_34])).

tff(c_75,plain,(
    ! [B_32,A_31] :
      ( r2_hidden(B_32,'#skF_4')
      | ~ r2_hidden(B_32,'#skF_5')
      | ~ r2_hidden(A_31,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_57,c_37])).

tff(c_98,plain,(
    ! [A_37] : ~ r2_hidden(A_37,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_112,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_16,c_98])).

tff(c_118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_112])).

tff(c_119,plain,(
    ! [B_32] :
      ( r2_hidden(B_32,'#skF_4')
      | ~ r2_hidden(B_32,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_229,plain,(
    r2_hidden('#skF_1'('#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_206,c_119])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_1'(A_5,B_6),A_5)
      | r2_hidden('#skF_2'(A_5,B_6),A_5)
      | B_6 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_180,plain,(
    ! [A_31] :
      ( r2_hidden(A_31,'#skF_5')
      | ~ r2_hidden(A_31,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_1'(A_5,B_6),A_5)
      | ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | B_6 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_231,plain,
    ( ~ r2_hidden('#skF_2'('#skF_4','#skF_5'),'#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_229,c_8])).

tff(c_234,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_231])).

tff(c_238,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_180,c_234])).

tff(c_244,plain,
    ( ~ r2_hidden('#skF_1'('#skF_4','#skF_5'),'#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_12,c_238])).

tff(c_250,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_244])).

tff(c_252,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_250])).

%------------------------------------------------------------------------------
