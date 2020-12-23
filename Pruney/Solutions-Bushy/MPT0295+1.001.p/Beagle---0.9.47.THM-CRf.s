%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0295+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:04 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   40 (  47 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   52 (  81 expanded)
%              Number of equality atoms :    7 (  13 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_1 > #skF_11 > #skF_4 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3 > #skF_7

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_57,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(A,k2_zfmisc_1(B,C))
          & r2_hidden(D,A)
          & ! [E,F] :
              ~ ( r2_hidden(E,B)
                & r2_hidden(F,C)
                & D = k4_tarski(E,F) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_8,plain,(
    ! [A_1,B_2,D_28] :
      ( r2_hidden('#skF_5'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28),A_1)
      | ~ r2_hidden(D_28,k2_zfmisc_1(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_6,plain,(
    ! [A_1,B_2,D_28] :
      ( r2_hidden('#skF_6'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28),B_2)
      | ~ r2_hidden(D_28,k2_zfmisc_1(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_179,plain,(
    ! [A_100,B_101,D_102] :
      ( k4_tarski('#skF_5'(A_100,B_101,k2_zfmisc_1(A_100,B_101),D_102),'#skF_6'(A_100,B_101,k2_zfmisc_1(A_100,B_101),D_102)) = D_102
      | ~ r2_hidden(D_102,k2_zfmisc_1(A_100,B_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_32,plain,(
    ! [E_42,F_43] :
      ( k4_tarski(E_42,F_43) != '#skF_11'
      | ~ r2_hidden(F_43,'#skF_10')
      | ~ r2_hidden(E_42,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_199,plain,(
    ! [D_107,A_108,B_109] :
      ( D_107 != '#skF_11'
      | ~ r2_hidden('#skF_6'(A_108,B_109,k2_zfmisc_1(A_108,B_109),D_107),'#skF_10')
      | ~ r2_hidden('#skF_5'(A_108,B_109,k2_zfmisc_1(A_108,B_109),D_107),'#skF_9')
      | ~ r2_hidden(D_107,k2_zfmisc_1(A_108,B_109)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_32])).

tff(c_206,plain,(
    ! [D_110,A_111] :
      ( D_110 != '#skF_11'
      | ~ r2_hidden('#skF_5'(A_111,'#skF_10',k2_zfmisc_1(A_111,'#skF_10'),D_110),'#skF_9')
      | ~ r2_hidden(D_110,k2_zfmisc_1(A_111,'#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_6,c_199])).

tff(c_217,plain,(
    ~ r2_hidden('#skF_11',k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_8,c_206])).

tff(c_30,plain,(
    ! [A_35,B_36] :
      ( r2_hidden('#skF_7'(A_35,B_36),A_35)
      | r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_38,plain,(
    ! [A_46,B_47] :
      ( ~ r2_hidden('#skF_7'(A_46,B_47),B_47)
      | r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_43,plain,(
    ! [A_35] : r1_tarski(A_35,A_35) ),
    inference(resolution,[status(thm)],[c_30,c_38])).

tff(c_36,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_34,plain,(
    r2_hidden('#skF_11','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_45,plain,(
    ! [C_49,B_50,A_51] :
      ( r2_hidden(C_49,B_50)
      | ~ r2_hidden(C_49,A_51)
      | ~ r1_tarski(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_52,plain,(
    ! [B_52] :
      ( r2_hidden('#skF_11',B_52)
      | ~ r1_tarski('#skF_8',B_52) ) ),
    inference(resolution,[status(thm)],[c_34,c_45])).

tff(c_26,plain,(
    ! [C_39,B_36,A_35] :
      ( r2_hidden(C_39,B_36)
      | ~ r2_hidden(C_39,A_35)
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_56,plain,(
    ! [B_53,B_54] :
      ( r2_hidden('#skF_11',B_53)
      | ~ r1_tarski(B_54,B_53)
      | ~ r1_tarski('#skF_8',B_54) ) ),
    inference(resolution,[status(thm)],[c_52,c_26])).

tff(c_60,plain,
    ( r2_hidden('#skF_11',k2_zfmisc_1('#skF_9','#skF_10'))
    | ~ r1_tarski('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_56])).

tff(c_64,plain,(
    r2_hidden('#skF_11',k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_60])).

tff(c_219,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_217,c_64])).

%------------------------------------------------------------------------------
