%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0215+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:55 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   23 (  24 expanded)
%              Number of leaves         :   16 (  17 expanded)
%              Depth                    :    4
%              Number of atoms          :   17 (  19 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_45,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k1_tarski(A) = k2_tarski(B,C)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_31,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_32,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_34,plain,(
    k2_tarski('#skF_6','#skF_7') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_40,plain,(
    ! [D_13,B_14] : r2_hidden(D_13,k2_tarski(D_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_43,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_40])).

tff(c_48,plain,(
    ! [C_17,A_18] :
      ( C_17 = A_18
      | ~ r2_hidden(C_17,k1_tarski(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_43,c_48])).

tff(c_62,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_54])).

%------------------------------------------------------------------------------
