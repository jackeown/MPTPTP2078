%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0291+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:03 EST 2020

% Result     : Theorem 4.73s
% Output     : CNFRefutation 5.04s
% Verified   : 
% Statistics : Number of formulae       :   38 (  47 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 (  80 expanded)
%              Number of equality atoms :    2 (   5 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_xboole_0 > #nlpp > k3_tarski > #skF_6 > #skF_4 > #skF_3 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_7 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( ! [C] :
            ( r2_hidden(C,A)
           => r1_xboole_0(C,B) )
       => r1_xboole_0(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(c_44,plain,(
    ~ r1_xboole_0(k3_tarski('#skF_8'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_53,plain,(
    ! [A_50,B_51] :
      ( r2_hidden('#skF_7'(A_50,B_51),k3_xboole_0(A_50,B_51))
      | r1_xboole_0(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    ! [D_25,B_21,A_20] :
      ( r2_hidden(D_25,B_21)
      | ~ r2_hidden(D_25,k3_xboole_0(A_20,B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_66,plain,(
    ! [A_50,B_51] :
      ( r2_hidden('#skF_7'(A_50,B_51),B_51)
      | r1_xboole_0(A_50,B_51) ) ),
    inference(resolution,[status(thm)],[c_53,c_22])).

tff(c_24,plain,(
    ! [D_25,A_20,B_21] :
      ( r2_hidden(D_25,A_20)
      | ~ r2_hidden(D_25,k3_xboole_0(A_20,B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_67,plain,(
    ! [A_50,B_51] :
      ( r2_hidden('#skF_7'(A_50,B_51),A_50)
      | r1_xboole_0(A_50,B_51) ) ),
    inference(resolution,[status(thm)],[c_53,c_24])).

tff(c_6,plain,(
    ! [C_16,A_1] :
      ( r2_hidden(C_16,'#skF_4'(A_1,k3_tarski(A_1),C_16))
      | ~ r2_hidden(C_16,k3_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_191,plain,(
    ! [A_76,C_77] :
      ( r2_hidden('#skF_4'(A_76,k3_tarski(A_76),C_77),A_76)
      | ~ r2_hidden(C_77,k3_tarski(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_46,plain,(
    ! [C_34] :
      ( r1_xboole_0(C_34,'#skF_9')
      | ~ r2_hidden(C_34,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_347,plain,(
    ! [C_95] :
      ( r1_xboole_0('#skF_4'('#skF_8',k3_tarski('#skF_8'),C_95),'#skF_9')
      | ~ r2_hidden(C_95,k3_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_191,c_46])).

tff(c_137,plain,(
    ! [D_65,A_66,B_67] :
      ( r2_hidden(D_65,k3_xboole_0(A_66,B_67))
      | ~ r2_hidden(D_65,B_67)
      | ~ r2_hidden(D_65,A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_42,plain,(
    ! [A_28,B_29,C_32] :
      ( ~ r1_xboole_0(A_28,B_29)
      | ~ r2_hidden(C_32,k3_xboole_0(A_28,B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_152,plain,(
    ! [A_66,B_67,D_65] :
      ( ~ r1_xboole_0(A_66,B_67)
      | ~ r2_hidden(D_65,B_67)
      | ~ r2_hidden(D_65,A_66) ) ),
    inference(resolution,[status(thm)],[c_137,c_42])).

tff(c_3127,plain,(
    ! [D_303,C_304] :
      ( ~ r2_hidden(D_303,'#skF_9')
      | ~ r2_hidden(D_303,'#skF_4'('#skF_8',k3_tarski('#skF_8'),C_304))
      | ~ r2_hidden(C_304,k3_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_347,c_152])).

tff(c_3228,plain,(
    ! [C_305] :
      ( ~ r2_hidden(C_305,'#skF_9')
      | ~ r2_hidden(C_305,k3_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_6,c_3127])).

tff(c_3324,plain,(
    ! [B_306] :
      ( ~ r2_hidden('#skF_7'(k3_tarski('#skF_8'),B_306),'#skF_9')
      | r1_xboole_0(k3_tarski('#skF_8'),B_306) ) ),
    inference(resolution,[status(thm)],[c_67,c_3228])).

tff(c_3336,plain,(
    r1_xboole_0(k3_tarski('#skF_8'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_66,c_3324])).

tff(c_3342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_44,c_3336])).

%------------------------------------------------------------------------------
