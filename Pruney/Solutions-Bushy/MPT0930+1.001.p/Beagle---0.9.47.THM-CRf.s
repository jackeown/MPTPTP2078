%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0930+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:06 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   43 (  56 expanded)
%              Number of leaves         :   24 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   43 (  80 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > #skF_6 > #skF_4 > #skF_3 > #skF_10 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( r2_hidden(B,A)
           => ( r2_hidden(k1_mcart_1(B),k1_relat_1(A))
              & r2_hidden(k2_mcart_1(B),k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_mcart_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_30,plain,(
    r2_hidden('#skF_10','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_32,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_65,plain,(
    ! [A_51,B_52] :
      ( k4_tarski(k1_mcart_1(A_51),k2_mcart_1(A_51)) = A_51
      | ~ r2_hidden(A_51,B_52)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_69,plain,
    ( k4_tarski(k1_mcart_1('#skF_10'),k2_mcart_1('#skF_10')) = '#skF_10'
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_30,c_65])).

tff(c_73,plain,(
    k4_tarski(k1_mcart_1('#skF_10'),k2_mcart_1('#skF_10')) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_69])).

tff(c_16,plain,(
    ! [C_35,A_20,D_38] :
      ( r2_hidden(C_35,k2_relat_1(A_20))
      | ~ r2_hidden(k4_tarski(D_38,C_35),A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_88,plain,(
    ! [A_54] :
      ( r2_hidden(k2_mcart_1('#skF_10'),k2_relat_1(A_54))
      | ~ r2_hidden('#skF_10',A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_16])).

tff(c_36,plain,(
    ! [A_48,B_49] :
      ( k4_tarski(k1_mcart_1(A_48),k2_mcart_1(A_48)) = A_48
      | ~ r2_hidden(A_48,B_49)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_38,plain,
    ( k4_tarski(k1_mcart_1('#skF_10'),k2_mcart_1('#skF_10')) = '#skF_10'
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_30,c_36])).

tff(c_41,plain,(
    k4_tarski(k1_mcart_1('#skF_10'),k2_mcart_1('#skF_10')) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_38])).

tff(c_4,plain,(
    ! [C_16,A_1,D_19] :
      ( r2_hidden(C_16,k1_relat_1(A_1))
      | ~ r2_hidden(k4_tarski(C_16,D_19),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    ! [A_50] :
      ( r2_hidden(k1_mcart_1('#skF_10'),k1_relat_1(A_50))
      | ~ r2_hidden('#skF_10',A_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_4])).

tff(c_28,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_10'),k2_relat_1('#skF_9'))
    | ~ r2_hidden(k1_mcart_1('#skF_10'),k1_relat_1('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_35,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_10'),k1_relat_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_57,plain,(
    ~ r2_hidden('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_52,c_35])).

tff(c_62,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_57])).

tff(c_63,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_10'),k2_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_93,plain,(
    ~ r2_hidden('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_88,c_63])).

tff(c_98,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_93])).

%------------------------------------------------------------------------------
