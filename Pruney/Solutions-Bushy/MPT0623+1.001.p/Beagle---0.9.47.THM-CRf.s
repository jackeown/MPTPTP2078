%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0623+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:36 EST 2020

% Result     : Theorem 11.06s
% Output     : CNFRefutation 11.06s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 275 expanded)
%              Number of leaves         :   35 ( 111 expanded)
%              Depth                    :   16
%              Number of atoms          :  156 ( 727 expanded)
%              Number of equality atoms :   42 ( 244 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > o_1_0_funct_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_1_0_funct_1,type,(
    o_1_0_funct_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_56,axiom,(
    ! [A] : m1_subset_1(o_1_0_funct_1(A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_1_0_funct_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_77,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = B
      & ! [D] :
          ( r2_hidden(D,B)
         => k1_funct_1(C,D) = o_1_0_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e1_27_1__funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_65,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_28,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_85,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(c_54,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_61,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_30,plain,(
    ! [A_48] : m1_subset_1(o_1_0_funct_1(A_48),A_48) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_46,plain,(
    ! [A_58,B_59] :
      ( r2_hidden(A_58,B_59)
      | v1_xboole_0(B_59)
      | ~ m1_subset_1(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_44,plain,(
    ! [A_51,B_52] : v1_relat_1('#skF_6'(A_51,B_52)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_42,plain,(
    ! [A_51,B_52] : v1_funct_1('#skF_6'(A_51,B_52)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_40,plain,(
    ! [A_51,B_52] : k1_relat_1('#skF_6'(A_51,B_52)) = B_52 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_176,plain,(
    ! [A_86,B_87] :
      ( r2_hidden('#skF_1'(A_86,B_87),A_86)
      | r1_tarski(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_181,plain,(
    ! [A_86] : r1_tarski(A_86,A_86) ),
    inference(resolution,[status(thm)],[c_176,c_8])).

tff(c_743,plain,(
    ! [A_170,C_171] :
      ( r2_hidden('#skF_5'(A_170,k2_relat_1(A_170),C_171),k1_relat_1(A_170))
      | ~ r2_hidden(C_171,k2_relat_1(A_170))
      | ~ v1_funct_1(A_170)
      | ~ v1_relat_1(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_770,plain,(
    ! [A_170,C_171,B_4] :
      ( r2_hidden('#skF_5'(A_170,k2_relat_1(A_170),C_171),B_4)
      | ~ r1_tarski(k1_relat_1(A_170),B_4)
      | ~ r2_hidden(C_171,k2_relat_1(A_170))
      | ~ v1_funct_1(A_170)
      | ~ v1_relat_1(A_170) ) ),
    inference(resolution,[status(thm)],[c_743,c_6])).

tff(c_38,plain,(
    ! [A_51,B_52,D_57] :
      ( k1_funct_1('#skF_6'(A_51,B_52),D_57) = o_1_0_funct_1(A_51)
      | ~ r2_hidden(D_57,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_622,plain,(
    ! [A_141,C_142] :
      ( k1_funct_1(A_141,'#skF_5'(A_141,k2_relat_1(A_141),C_142)) = C_142
      | ~ r2_hidden(C_142,k2_relat_1(A_141))
      | ~ v1_funct_1(A_141)
      | ~ v1_relat_1(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_639,plain,(
    ! [A_51,C_142,B_52] :
      ( o_1_0_funct_1(A_51) = C_142
      | ~ r2_hidden(C_142,k2_relat_1('#skF_6'(A_51,B_52)))
      | ~ v1_funct_1('#skF_6'(A_51,B_52))
      | ~ v1_relat_1('#skF_6'(A_51,B_52))
      | ~ r2_hidden('#skF_5'('#skF_6'(A_51,B_52),k2_relat_1('#skF_6'(A_51,B_52)),C_142),B_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_622])).

tff(c_4367,plain,(
    ! [A_417,C_418,B_419] :
      ( o_1_0_funct_1(A_417) = C_418
      | ~ r2_hidden(C_418,k2_relat_1('#skF_6'(A_417,B_419)))
      | ~ r2_hidden('#skF_5'('#skF_6'(A_417,B_419),k2_relat_1('#skF_6'(A_417,B_419)),C_418),B_419) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_639])).

tff(c_4374,plain,(
    ! [A_417,C_171,B_4] :
      ( o_1_0_funct_1(A_417) = C_171
      | ~ r1_tarski(k1_relat_1('#skF_6'(A_417,B_4)),B_4)
      | ~ r2_hidden(C_171,k2_relat_1('#skF_6'(A_417,B_4)))
      | ~ v1_funct_1('#skF_6'(A_417,B_4))
      | ~ v1_relat_1('#skF_6'(A_417,B_4)) ) ),
    inference(resolution,[status(thm)],[c_770,c_4367])).

tff(c_4394,plain,(
    ! [A_420,C_421,B_422] :
      ( o_1_0_funct_1(A_420) = C_421
      | ~ r2_hidden(C_421,k2_relat_1('#skF_6'(A_420,B_422))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_181,c_40,c_4374])).

tff(c_18570,plain,(
    ! [A_5353,B_5354,B_5355] :
      ( '#skF_1'(k2_relat_1('#skF_6'(A_5353,B_5354)),B_5355) = o_1_0_funct_1(A_5353)
      | r1_tarski(k2_relat_1('#skF_6'(A_5353,B_5354)),B_5355) ) ),
    inference(resolution,[status(thm)],[c_10,c_4394])).

tff(c_52,plain,(
    ! [C_63] :
      ( ~ r1_tarski(k2_relat_1(C_63),'#skF_7')
      | k1_relat_1(C_63) != '#skF_8'
      | ~ v1_funct_1(C_63)
      | ~ v1_relat_1(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_18717,plain,(
    ! [A_5353,B_5354] :
      ( k1_relat_1('#skF_6'(A_5353,B_5354)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(A_5353,B_5354))
      | ~ v1_relat_1('#skF_6'(A_5353,B_5354))
      | '#skF_1'(k2_relat_1('#skF_6'(A_5353,B_5354)),'#skF_7') = o_1_0_funct_1(A_5353) ) ),
    inference(resolution,[status(thm)],[c_18570,c_52])).

tff(c_18837,plain,(
    ! [B_5374,A_5375] :
      ( B_5374 != '#skF_8'
      | '#skF_1'(k2_relat_1('#skF_6'(A_5375,B_5374)),'#skF_7') = o_1_0_funct_1(A_5375) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_18717])).

tff(c_19791,plain,(
    ! [A_5538,B_5539] :
      ( ~ r2_hidden(o_1_0_funct_1(A_5538),'#skF_7')
      | r1_tarski(k2_relat_1('#skF_6'(A_5538,B_5539)),'#skF_7')
      | B_5539 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18837,c_8])).

tff(c_19825,plain,(
    ! [A_5538,B_5539] :
      ( k1_relat_1('#skF_6'(A_5538,B_5539)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(A_5538,B_5539))
      | ~ v1_relat_1('#skF_6'(A_5538,B_5539))
      | ~ r2_hidden(o_1_0_funct_1(A_5538),'#skF_7')
      | B_5539 != '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_19791,c_52])).

tff(c_19889,plain,(
    ! [A_5538,B_5539] :
      ( ~ r2_hidden(o_1_0_funct_1(A_5538),'#skF_7')
      | B_5539 != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_19825])).

tff(c_20192,plain,(
    ! [B_5539] : B_5539 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_19889])).

tff(c_20196,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_20192])).

tff(c_20199,plain,(
    ! [A_5578] : ~ r2_hidden(o_1_0_funct_1(A_5578),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_19889])).

tff(c_20210,plain,(
    ! [A_5578] :
      ( v1_xboole_0('#skF_7')
      | ~ m1_subset_1(o_1_0_funct_1(A_5578),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_46,c_20199])).

tff(c_20375,plain,(
    ! [A_5618] : ~ m1_subset_1(o_1_0_funct_1(A_5618),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_20210])).

tff(c_20387,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_30,c_20375])).

tff(c_20388,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_20210])).

tff(c_50,plain,(
    ! [A_61] :
      ( k1_xboole_0 = A_61
      | ~ v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_20397,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_20388,c_50])).

tff(c_20409,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_20397])).

tff(c_20410,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_36,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_56,plain,(
    ! [A_65] :
      ( v1_relat_1(A_65)
      | ~ v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_60,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_36,c_56])).

tff(c_20412,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20410,c_60])).

tff(c_20414,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20410,c_36])).

tff(c_20442,plain,(
    ! [A_5663] :
      ( v1_funct_1(A_5663)
      | ~ v1_xboole_0(A_5663) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_20446,plain,(
    v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_20414,c_20442])).

tff(c_48,plain,(
    ! [A_60] : r1_tarski(k1_xboole_0,A_60) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_20413,plain,(
    ! [A_60] : r1_tarski('#skF_8',A_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20410,c_48])).

tff(c_20472,plain,(
    ! [A_5667] :
      ( v1_xboole_0(k2_relat_1(A_5667))
      | ~ v1_xboole_0(A_5667) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20434,plain,(
    ! [A_61] :
      ( A_61 = '#skF_8'
      | ~ v1_xboole_0(A_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20410,c_50])).

tff(c_20491,plain,(
    ! [A_5672] :
      ( k2_relat_1(A_5672) = '#skF_8'
      | ~ v1_xboole_0(A_5672) ) ),
    inference(resolution,[status(thm)],[c_20472,c_20434])).

tff(c_20503,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_20414,c_20491])).

tff(c_20411,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_20419,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20410,c_20411])).

tff(c_20430,plain,(
    ! [C_63] :
      ( ~ r1_tarski(k2_relat_1(C_63),'#skF_8')
      | k1_relat_1(C_63) != '#skF_8'
      | ~ v1_funct_1(C_63)
      | ~ v1_relat_1(C_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20419,c_52])).

tff(c_20513,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | k1_relat_1('#skF_8') != '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_20503,c_20430])).

tff(c_20521,plain,(
    k1_relat_1('#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20412,c_20446,c_20413,c_20513])).

tff(c_20456,plain,(
    ! [A_5666] :
      ( v1_xboole_0(k1_relat_1(A_5666))
      | ~ v1_xboole_0(A_5666) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_20535,plain,(
    ! [A_5676] :
      ( k1_relat_1(A_5676) = '#skF_8'
      | ~ v1_xboole_0(A_5676) ) ),
    inference(resolution,[status(thm)],[c_20456,c_20434])).

tff(c_20544,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_20414,c_20535])).

tff(c_20550,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20521,c_20544])).

%------------------------------------------------------------------------------
