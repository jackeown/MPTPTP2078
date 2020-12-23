%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0005+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:09 EST 2020

% Result     : Theorem 4.15s
% Output     : CNFRefutation 4.15s
% Verified   : 
% Statistics : Number of formulae       :   50 (  65 expanded)
%              Number of leaves         :   33 (  41 expanded)
%              Depth                    :    4
%              Number of atoms          :   41 ( 101 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_18 > #skF_17 > #skF_6 > #skF_1 > #skF_12 > #skF_4 > #skF_16 > #skF_14 > #skF_5 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_15

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_18',type,(
    '#skF_18': $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_17',type,(
    '#skF_17': $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * ( $i * $i ) ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * ( $i * $i ) ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_16',type,(
    '#skF_16': $i )).

tff('#skF_14',type,(
    '#skF_14': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * ( $i * $i ) ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * ( $i * $i ) ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_15',type,(
    '#skF_15': ( $i * $i ) > $i )).

tff(f_171,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_xboole_0(A,B)
          & r2_hidden(C,k2_xboole_0(A,B))
          & ~ ( r2_hidden(C,A)
              & ~ r2_hidden(C,B) )
          & ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_0)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_139,axiom,(
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

tff(c_164,plain,
    ( r2_hidden('#skF_18','#skF_17')
    | ~ r2_hidden('#skF_18','#skF_16') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_238,plain,(
    ~ r2_hidden('#skF_18','#skF_16') ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_162,plain,
    ( r2_hidden('#skF_18','#skF_16')
    | ~ r2_hidden('#skF_18','#skF_17') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_239,plain,(
    ~ r2_hidden('#skF_18','#skF_17') ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_166,plain,(
    r2_hidden('#skF_18',k2_xboole_0('#skF_16','#skF_17')) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_1929,plain,(
    ! [D_212,B_213,A_214] :
      ( r2_hidden(D_212,B_213)
      | r2_hidden(D_212,A_214)
      | ~ r2_hidden(D_212,k2_xboole_0(A_214,B_213)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1967,plain,
    ( r2_hidden('#skF_18','#skF_17')
    | r2_hidden('#skF_18','#skF_16') ),
    inference(resolution,[status(thm)],[c_166,c_1929])).

tff(c_1981,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_238,c_239,c_1967])).

tff(c_1982,plain,(
    r2_hidden('#skF_18','#skF_16') ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_1984,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_238,c_1982])).

tff(c_1985,plain,(
    r2_hidden('#skF_18','#skF_17') ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_1995,plain,(
    r2_hidden('#skF_18','#skF_16') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1985,c_162])).

tff(c_168,plain,(
    r1_xboole_0('#skF_16','#skF_17') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_2759,plain,(
    ! [A_286,B_287,C_288] :
      ( ~ r1_xboole_0(A_286,B_287)
      | ~ r2_hidden(C_288,B_287)
      | ~ r2_hidden(C_288,A_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2784,plain,(
    ! [C_289] :
      ( ~ r2_hidden(C_289,'#skF_17')
      | ~ r2_hidden(C_289,'#skF_16') ) ),
    inference(resolution,[status(thm)],[c_168,c_2759])).

tff(c_2799,plain,(
    ~ r2_hidden('#skF_18','#skF_16') ),
    inference(resolution,[status(thm)],[c_1985,c_2784])).

tff(c_2808,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1995,c_2799])).
%------------------------------------------------------------------------------
