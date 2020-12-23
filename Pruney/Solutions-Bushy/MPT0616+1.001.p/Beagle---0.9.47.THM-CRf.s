%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0616+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:35 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   45 (  72 expanded)
%              Number of leaves         :   20 (  35 expanded)
%              Depth                    :    5
%              Number of atoms          :   60 ( 155 expanded)
%              Number of equality atoms :   12 (  34 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(k4_tarski(A,B),C)
        <=> ( r2_hidden(A,k1_relat_1(C))
            & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_42,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_36,plain,
    ( r2_hidden(k4_tarski('#skF_5','#skF_6'),'#skF_7')
    | r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_43,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_32,plain,
    ( r2_hidden(k4_tarski('#skF_5','#skF_6'),'#skF_7')
    | k1_funct_1('#skF_7','#skF_5') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_37,plain,(
    k1_funct_1('#skF_7','#skF_5') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_26,plain,
    ( k1_funct_1('#skF_7','#skF_5') != '#skF_6'
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_7'))
    | ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_51,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_37,c_26])).

tff(c_24,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_63,plain,(
    ! [B_37,A_38] :
      ( r2_hidden(k4_tarski(B_37,k1_funct_1(A_38,B_37)),A_38)
      | ~ r2_hidden(B_37,k1_relat_1(A_38))
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_69,plain,
    ( r2_hidden(k4_tarski('#skF_5','#skF_6'),'#skF_7')
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_63])).

tff(c_72,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_43,c_69])).

tff(c_74,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_72])).

tff(c_76,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_75,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_12,plain,(
    ! [C_21,A_6,D_24] :
      ( r2_hidden(C_21,k1_relat_1(A_6))
      | ~ r2_hidden(k4_tarski(C_21,D_24),A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_79,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_75,c_12])).

tff(c_83,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_79])).

tff(c_85,plain,(
    k1_funct_1('#skF_7','#skF_5') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_84,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_86,plain,(
    ! [C_39,A_40,D_41] :
      ( r2_hidden(C_39,k1_relat_1(A_40))
      | ~ r2_hidden(k4_tarski(C_39,D_41),A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_90,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_84,c_86])).

tff(c_137,plain,(
    ! [A_56,B_57,C_58] :
      ( k1_funct_1(A_56,B_57) = C_58
      | ~ r2_hidden(k4_tarski(B_57,C_58),A_56)
      | ~ r2_hidden(B_57,k1_relat_1(A_56))
      | ~ v1_funct_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_154,plain,
    ( k1_funct_1('#skF_7','#skF_5') = '#skF_6'
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_84,c_137])).

tff(c_162,plain,(
    k1_funct_1('#skF_7','#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_90,c_154])).

tff(c_164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_162])).

%------------------------------------------------------------------------------
