%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0442+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:19 EST 2020

% Result     : Theorem 5.56s
% Output     : CNFRefutation 5.56s
% Verified   : 
% Statistics : Number of formulae       :   47 (  68 expanded)
%              Number of leaves         :   24 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   58 ( 120 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_11 > #skF_3 > #skF_10 > #skF_5 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
                & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_32,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_10'),k2_relat_1('#skF_11'))
    | ~ r1_tarski(k1_relat_1('#skF_10'),k1_relat_1('#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_53,plain,(
    ~ r1_tarski(k1_relat_1('#skF_10'),k1_relat_1('#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    r1_tarski('#skF_10','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_63,plain,(
    ! [C_62,A_63] :
      ( r2_hidden(k4_tarski(C_62,'#skF_5'(A_63,k1_relat_1(A_63),C_62)),A_63)
      | ~ r2_hidden(C_62,k1_relat_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1272,plain,(
    ! [C_176,A_177,B_178] :
      ( r2_hidden(k4_tarski(C_176,'#skF_5'(A_177,k1_relat_1(A_177),C_176)),B_178)
      | ~ r1_tarski(A_177,B_178)
      | ~ r2_hidden(C_176,k1_relat_1(A_177)) ) ),
    inference(resolution,[status(thm)],[c_63,c_2])).

tff(c_10,plain,(
    ! [C_21,A_6,D_24] :
      ( r2_hidden(C_21,k1_relat_1(A_6))
      | ~ r2_hidden(k4_tarski(C_21,D_24),A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1292,plain,(
    ! [C_179,B_180,A_181] :
      ( r2_hidden(C_179,k1_relat_1(B_180))
      | ~ r1_tarski(A_181,B_180)
      | ~ r2_hidden(C_179,k1_relat_1(A_181)) ) ),
    inference(resolution,[status(thm)],[c_1272,c_10])).

tff(c_1305,plain,(
    ! [C_182] :
      ( r2_hidden(C_182,k1_relat_1('#skF_11'))
      | ~ r2_hidden(C_182,k1_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_34,c_1292])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1511,plain,(
    ! [A_191] :
      ( r1_tarski(A_191,k1_relat_1('#skF_11'))
      | ~ r2_hidden('#skF_1'(A_191,k1_relat_1('#skF_11')),k1_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_1305,c_4])).

tff(c_1523,plain,(
    r1_tarski(k1_relat_1('#skF_10'),k1_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_6,c_1511])).

tff(c_1529,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_53,c_1523])).

tff(c_1530,plain,(
    ~ r1_tarski(k2_relat_1('#skF_10'),k2_relat_1('#skF_11')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1557,plain,(
    ! [A_199,C_200] :
      ( r2_hidden(k4_tarski('#skF_9'(A_199,k2_relat_1(A_199),C_200),C_200),A_199)
      | ~ r2_hidden(C_200,k2_relat_1(A_199)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2747,plain,(
    ! [A_310,C_311,B_312] :
      ( r2_hidden(k4_tarski('#skF_9'(A_310,k2_relat_1(A_310),C_311),C_311),B_312)
      | ~ r1_tarski(A_310,B_312)
      | ~ r2_hidden(C_311,k2_relat_1(A_310)) ) ),
    inference(resolution,[status(thm)],[c_1557,c_2])).

tff(c_22,plain,(
    ! [C_40,A_25,D_43] :
      ( r2_hidden(C_40,k2_relat_1(A_25))
      | ~ r2_hidden(k4_tarski(D_43,C_40),A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2767,plain,(
    ! [C_313,B_314,A_315] :
      ( r2_hidden(C_313,k2_relat_1(B_314))
      | ~ r1_tarski(A_315,B_314)
      | ~ r2_hidden(C_313,k2_relat_1(A_315)) ) ),
    inference(resolution,[status(thm)],[c_2747,c_22])).

tff(c_2780,plain,(
    ! [C_316] :
      ( r2_hidden(C_316,k2_relat_1('#skF_11'))
      | ~ r2_hidden(C_316,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_34,c_2767])).

tff(c_2977,plain,(
    ! [A_323] :
      ( r1_tarski(A_323,k2_relat_1('#skF_11'))
      | ~ r2_hidden('#skF_1'(A_323,k2_relat_1('#skF_11')),k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_2780,c_4])).

tff(c_2989,plain,(
    r1_tarski(k2_relat_1('#skF_10'),k2_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_6,c_2977])).

tff(c_2995,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1530,c_1530,c_2989])).

%------------------------------------------------------------------------------
