%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0729+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:46 EST 2020

% Result     : Theorem 4.41s
% Output     : CNFRefutation 4.50s
% Verified   : 
% Statistics : Number of formulae       :   36 (  50 expanded)
%              Number of leaves         :   19 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   42 (  71 expanded)
%              Number of equality atoms :   14 (  29 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( k1_ordinal1(A) = k1_ordinal1(B)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_ordinal1)).

tff(f_49,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_31,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_38,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_40,plain,(
    k1_ordinal1('#skF_5') = k1_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_46,plain,(
    ! [A_17] : r2_hidden(A_17,k1_ordinal1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_49,plain,(
    r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_46])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_tarski(A_3)) = k1_ordinal1(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_170,plain,(
    ! [D_38,B_39,A_40] :
      ( r2_hidden(D_38,B_39)
      | r2_hidden(D_38,A_40)
      | ~ r2_hidden(D_38,k2_xboole_0(A_40,B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1804,plain,(
    ! [D_195,A_196] :
      ( r2_hidden(D_195,k1_tarski(A_196))
      | r2_hidden(D_195,A_196)
      | ~ r2_hidden(D_195,k1_ordinal1(A_196)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_170])).

tff(c_6,plain,(
    ! [C_8,A_4] :
      ( C_8 = A_4
      | ~ r2_hidden(C_8,k1_tarski(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2293,plain,(
    ! [D_202,A_203] :
      ( D_202 = A_203
      | r2_hidden(D_202,A_203)
      | ~ r2_hidden(D_202,k1_ordinal1(A_203)) ) ),
    inference(resolution,[status(thm)],[c_1804,c_6])).

tff(c_2326,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_49,c_2293])).

tff(c_2343,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_2326])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2348,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_2343,c_2])).

tff(c_36,plain,(
    ! [A_15] : r2_hidden(A_15,k1_ordinal1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2349,plain,(
    ! [D_204] :
      ( D_204 = '#skF_5'
      | r2_hidden(D_204,'#skF_5')
      | ~ r2_hidden(D_204,k1_ordinal1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_2293])).

tff(c_2387,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_2349])).

tff(c_2401,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2348,c_38,c_2387])).

%------------------------------------------------------------------------------
