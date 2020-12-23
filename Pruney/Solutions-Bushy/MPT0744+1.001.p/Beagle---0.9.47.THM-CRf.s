%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0744+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:48 EST 2020

% Result     : Theorem 8.51s
% Output     : CNFRefutation 8.90s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 201 expanded)
%              Number of leaves         :   29 (  79 expanded)
%              Depth                    :   10
%              Number of atoms          :  140 ( 447 expanded)
%              Number of equality atoms :   21 (  53 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_3 > #skF_2 > #skF_1

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

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => r1_ordinal1(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r1_ordinal1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_43,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_95,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_62,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_56,plain,(
    ! [A_24,B_25] :
      ( r1_ordinal1(A_24,A_24)
      | ~ v3_ordinal1(B_25)
      | ~ v3_ordinal1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6827,plain,(
    ! [B_25] : ~ v3_ordinal1(B_25) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_60,plain,(
    v3_ordinal1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_6830,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6827,c_60])).

tff(c_6831,plain,(
    ! [A_24] :
      ( r1_ordinal1(A_24,A_24)
      | ~ v3_ordinal1(A_24) ) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_18,plain,(
    ! [C_11] : r2_hidden(C_11,k1_tarski(C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_tarski(A_6)) = k1_ordinal1(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_253,plain,(
    ! [D_63,B_64,A_65] :
      ( ~ r2_hidden(D_63,B_64)
      | r2_hidden(D_63,k2_xboole_0(A_65,B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_431,plain,(
    ! [D_84,A_85] :
      ( ~ r2_hidden(D_84,k1_tarski(A_85))
      | r2_hidden(D_84,k1_ordinal1(A_85)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_253])).

tff(c_440,plain,(
    ! [C_11] : r2_hidden(C_11,k1_ordinal1(C_11)) ),
    inference(resolution,[status(thm)],[c_18,c_431])).

tff(c_83,plain,(
    ! [A_33] :
      ( v1_ordinal1(A_33)
      | ~ v3_ordinal1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_91,plain,(
    v1_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_83])).

tff(c_679,plain,(
    ! [B_112,A_113] :
      ( r2_hidden(B_112,A_113)
      | B_112 = A_113
      | r2_hidden(A_113,B_112)
      | ~ v3_ordinal1(B_112)
      | ~ v3_ordinal1(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_28,plain,(
    ! [B_15,A_12] :
      ( r1_tarski(B_15,A_12)
      | ~ r2_hidden(B_15,A_12)
      | ~ v1_ordinal1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_5968,plain,(
    ! [B_442,A_443] :
      ( r1_tarski(B_442,A_443)
      | ~ v1_ordinal1(A_443)
      | B_442 = A_443
      | r2_hidden(A_443,B_442)
      | ~ v3_ordinal1(B_442)
      | ~ v3_ordinal1(A_443) ) ),
    inference(resolution,[status(thm)],[c_679,c_28])).

tff(c_142,plain,(
    ! [D_47,A_48,B_49] :
      ( ~ r2_hidden(D_47,A_48)
      | r2_hidden(D_47,k2_xboole_0(A_48,B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_184,plain,(
    ! [D_56,A_57] :
      ( ~ r2_hidden(D_56,A_57)
      | r2_hidden(D_56,k1_ordinal1(A_57)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_142])).

tff(c_70,plain,
    ( r2_hidden('#skF_6',k1_ordinal1('#skF_7'))
    | r1_ordinal1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_92,plain,(
    r1_ordinal1('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_64,plain,
    ( ~ r1_ordinal1('#skF_6','#skF_7')
    | ~ r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_125,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_64])).

tff(c_208,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_184,c_125])).

tff(c_6564,plain,
    ( r1_tarski('#skF_7','#skF_6')
    | ~ v1_ordinal1('#skF_6')
    | '#skF_7' = '#skF_6'
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_5968,c_208])).

tff(c_6752,plain,
    ( r1_tarski('#skF_7','#skF_6')
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_91,c_6564])).

tff(c_6763,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_6752])).

tff(c_6765,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6763,c_125])).

tff(c_6772,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_6765])).

tff(c_6774,plain,(
    '#skF_7' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_6752])).

tff(c_6773,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_6752])).

tff(c_330,plain,(
    ! [A_71,B_72] :
      ( r1_tarski(A_71,B_72)
      | ~ r1_ordinal1(A_71,B_72)
      | ~ v3_ordinal1(B_72)
      | ~ v3_ordinal1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8,plain,(
    ! [B_5,A_4] :
      ( B_5 = A_4
      | ~ r1_tarski(B_5,A_4)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_337,plain,(
    ! [B_72,A_71] :
      ( B_72 = A_71
      | ~ r1_tarski(B_72,A_71)
      | ~ r1_ordinal1(A_71,B_72)
      | ~ v3_ordinal1(B_72)
      | ~ v3_ordinal1(A_71) ) ),
    inference(resolution,[status(thm)],[c_330,c_8])).

tff(c_6778,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r1_ordinal1('#skF_6','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_6773,c_337])).

tff(c_6786,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_92,c_6778])).

tff(c_6788,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6774,c_6786])).

tff(c_6790,plain,(
    ~ r1_ordinal1('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_90,plain,(
    v1_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_83])).

tff(c_6789,plain,(
    r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_7242,plain,(
    ! [D_506,B_507,A_508] :
      ( r2_hidden(D_506,B_507)
      | r2_hidden(D_506,A_508)
      | ~ r2_hidden(D_506,k2_xboole_0(A_508,B_507)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8998,plain,(
    ! [D_619,A_620] :
      ( r2_hidden(D_619,k1_tarski(A_620))
      | r2_hidden(D_619,A_620)
      | ~ r2_hidden(D_619,k1_ordinal1(A_620)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_7242])).

tff(c_16,plain,(
    ! [C_11,A_7] :
      ( C_11 = A_7
      | ~ r2_hidden(C_11,k1_tarski(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_9425,plain,(
    ! [D_625,A_626] :
      ( D_625 = A_626
      | r2_hidden(D_625,A_626)
      | ~ r2_hidden(D_625,k1_ordinal1(A_626)) ) ),
    inference(resolution,[status(thm)],[c_8998,c_16])).

tff(c_9502,plain,
    ( '#skF_7' = '#skF_6'
    | r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_6789,c_9425])).

tff(c_9503,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_9502])).

tff(c_9506,plain,
    ( r1_tarski('#skF_6','#skF_7')
    | ~ v1_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_9503,c_28])).

tff(c_9511,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_9506])).

tff(c_52,plain,(
    ! [A_22,B_23] :
      ( r1_ordinal1(A_22,B_23)
      | ~ r1_tarski(A_22,B_23)
      | ~ v3_ordinal1(B_23)
      | ~ v3_ordinal1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_9515,plain,
    ( r1_ordinal1('#skF_6','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_9511,c_52])).

tff(c_9520,plain,(
    r1_ordinal1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_9515])).

tff(c_9522,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6790,c_9520])).

tff(c_9523,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_9502])).

tff(c_9528,plain,(
    ~ r1_ordinal1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9523,c_6790])).

tff(c_9562,plain,(
    ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_6831,c_9528])).

tff(c_9566,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_9562])).

%------------------------------------------------------------------------------
