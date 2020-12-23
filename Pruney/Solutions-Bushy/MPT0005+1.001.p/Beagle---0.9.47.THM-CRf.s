%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0005+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:33 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   30 (  40 expanded)
%              Number of leaves         :   15 (  21 expanded)
%              Depth                    :    4
%              Number of atoms          :   39 (  82 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_xboole_0(A,B)
          & r2_hidden(C,k2_xboole_0(A,B))
          & ~ ( r2_hidden(C,A)
              & ~ r2_hidden(C,B) )
          & ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_26,plain,
    ( r2_hidden('#skF_6','#skF_4')
    | ~ r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_33,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_28,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | ~ r2_hidden('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_34,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_28])).

tff(c_30,plain,(
    r2_hidden('#skF_6',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_70,plain,(
    ! [D_28,B_29,A_30] :
      ( r2_hidden(D_28,B_29)
      | r2_hidden(D_28,A_30)
      | ~ r2_hidden(D_28,k2_xboole_0(A_30,B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_87,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_70])).

tff(c_95,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_33,c_87])).

tff(c_96,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_97,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_32,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_104,plain,(
    ! [A_41,B_42,C_43] :
      ( ~ r1_xboole_0(A_41,B_42)
      | ~ r2_hidden(C_43,B_42)
      | ~ r2_hidden(C_43,A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_108,plain,(
    ! [C_44] :
      ( ~ r2_hidden(C_44,'#skF_5')
      | ~ r2_hidden(C_44,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_104])).

tff(c_119,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_97,c_108])).

tff(c_125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_119])).

%------------------------------------------------------------------------------
