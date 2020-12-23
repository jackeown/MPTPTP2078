%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0574+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:31 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   39 (  50 expanded)
%              Number of leaves         :   19 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :   67 ( 103 expanded)
%              Number of equality atoms :    1 (   3 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_51,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_24,plain,(
    ! [A_43,B_44] :
      ( r2_hidden('#skF_5'(A_43,B_44),A_43)
      | r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_32,plain,(
    ! [A_50,B_51] :
      ( ~ r2_hidden('#skF_5'(A_50,B_51),B_51)
      | r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_37,plain,(
    ! [A_43] : r1_tarski(A_43,A_43) ),
    inference(resolution,[status(thm)],[c_24,c_32])).

tff(c_6,plain,(
    ! [D_39,A_1,B_24] :
      ( r2_hidden(k4_tarski(D_39,'#skF_4'(A_1,B_24,k10_relat_1(A_1,B_24),D_39)),A_1)
      | ~ r2_hidden(D_39,k10_relat_1(A_1,B_24))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_114,plain,(
    ! [A_78,B_79,D_80] :
      ( r2_hidden('#skF_4'(A_78,B_79,k10_relat_1(A_78,B_79),D_80),B_79)
      | ~ r2_hidden(D_80,k10_relat_1(A_78,B_79))
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [C_47,B_44,A_43] :
      ( r2_hidden(C_47,B_44)
      | ~ r2_hidden(C_47,A_43)
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_154,plain,(
    ! [A_102,B_103,D_104,B_105] :
      ( r2_hidden('#skF_4'(A_102,B_103,k10_relat_1(A_102,B_103),D_104),B_105)
      | ~ r1_tarski(B_103,B_105)
      | ~ r2_hidden(D_104,k10_relat_1(A_102,B_103))
      | ~ v1_relat_1(A_102) ) ),
    inference(resolution,[status(thm)],[c_114,c_20])).

tff(c_197,plain,(
    ! [B_133,B_132,D_134,B_135,A_136] :
      ( r2_hidden('#skF_4'(A_136,B_133,k10_relat_1(A_136,B_133),D_134),B_135)
      | ~ r1_tarski(B_132,B_135)
      | ~ r1_tarski(B_133,B_132)
      | ~ r2_hidden(D_134,k10_relat_1(A_136,B_133))
      | ~ v1_relat_1(A_136) ) ),
    inference(resolution,[status(thm)],[c_154,c_20])).

tff(c_207,plain,(
    ! [A_137,B_138,D_139] :
      ( r2_hidden('#skF_4'(A_137,B_138,k10_relat_1(A_137,B_138),D_139),'#skF_7')
      | ~ r1_tarski(B_138,'#skF_6')
      | ~ r2_hidden(D_139,k10_relat_1(A_137,B_138))
      | ~ v1_relat_1(A_137) ) ),
    inference(resolution,[status(thm)],[c_28,c_197])).

tff(c_2,plain,(
    ! [D_39,A_1,B_24,E_42] :
      ( r2_hidden(D_39,k10_relat_1(A_1,B_24))
      | ~ r2_hidden(E_42,B_24)
      | ~ r2_hidden(k4_tarski(D_39,E_42),A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_448,plain,(
    ! [A_233,B_232,D_229,D_230,A_231] :
      ( r2_hidden(D_230,k10_relat_1(A_231,'#skF_7'))
      | ~ r2_hidden(k4_tarski(D_230,'#skF_4'(A_233,B_232,k10_relat_1(A_233,B_232),D_229)),A_231)
      | ~ v1_relat_1(A_231)
      | ~ r1_tarski(B_232,'#skF_6')
      | ~ r2_hidden(D_229,k10_relat_1(A_233,B_232))
      | ~ v1_relat_1(A_233) ) ),
    inference(resolution,[status(thm)],[c_207,c_2])).

tff(c_465,plain,(
    ! [D_234,A_235,B_236] :
      ( r2_hidden(D_234,k10_relat_1(A_235,'#skF_7'))
      | ~ r1_tarski(B_236,'#skF_6')
      | ~ r2_hidden(D_234,k10_relat_1(A_235,B_236))
      | ~ v1_relat_1(A_235) ) ),
    inference(resolution,[status(thm)],[c_6,c_448])).

tff(c_566,plain,(
    ! [A_237,B_238,B_239] :
      ( r2_hidden('#skF_5'(k10_relat_1(A_237,B_238),B_239),k10_relat_1(A_237,'#skF_7'))
      | ~ r1_tarski(B_238,'#skF_6')
      | ~ v1_relat_1(A_237)
      | r1_tarski(k10_relat_1(A_237,B_238),B_239) ) ),
    inference(resolution,[status(thm)],[c_24,c_465])).

tff(c_22,plain,(
    ! [A_43,B_44] :
      ( ~ r2_hidden('#skF_5'(A_43,B_44),B_44)
      | r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_581,plain,(
    ! [B_240,A_241] :
      ( ~ r1_tarski(B_240,'#skF_6')
      | ~ v1_relat_1(A_241)
      | r1_tarski(k10_relat_1(A_241,B_240),k10_relat_1(A_241,'#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_566,c_22])).

tff(c_26,plain,(
    ~ r1_tarski(k10_relat_1('#skF_8','#skF_6'),k10_relat_1('#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_608,plain,
    ( ~ r1_tarski('#skF_6','#skF_6')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_581,c_26])).

tff(c_624,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_37,c_608])).

%------------------------------------------------------------------------------
