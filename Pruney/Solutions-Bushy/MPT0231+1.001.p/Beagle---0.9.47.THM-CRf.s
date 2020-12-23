%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0231+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:57 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   33 (  41 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   31 (  51 expanded)
%              Number of equality atoms :   10 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1 > #skF_5

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_38,plain,(
    '#skF_6' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_40,plain,(
    r1_tarski(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    ! [D_11,A_6] : r2_hidden(D_11,k2_tarski(A_6,D_11)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_63,plain,(
    ! [C_29,B_30,A_31] :
      ( r2_hidden(C_29,B_30)
      | ~ r2_hidden(C_29,A_31)
      | ~ r1_tarski(A_31,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_83,plain,(
    ! [D_34,B_35,A_36] :
      ( r2_hidden(D_34,B_35)
      | ~ r1_tarski(k2_tarski(A_36,D_34),B_35) ) ),
    inference(resolution,[status(thm)],[c_16,c_63])).

tff(c_93,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_40,c_83])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_100,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_93,c_2])).

tff(c_102,plain,(
    r1_tarski(k2_tarski('#skF_6','#skF_8'),k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_40])).

tff(c_18,plain,(
    ! [D_11,B_7] : r2_hidden(D_11,k2_tarski(D_11,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_130,plain,(
    ! [D_40,B_41,B_42] :
      ( r2_hidden(D_40,B_41)
      | ~ r1_tarski(k2_tarski(D_40,B_42),B_41) ) ),
    inference(resolution,[status(thm)],[c_18,c_63])).

tff(c_138,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_102,c_130])).

tff(c_145,plain,(
    '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_138,c_2])).

tff(c_150,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_145])).

%------------------------------------------------------------------------------
