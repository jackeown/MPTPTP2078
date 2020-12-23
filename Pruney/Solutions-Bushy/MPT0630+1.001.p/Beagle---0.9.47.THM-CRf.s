%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0630+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:37 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   45 (  66 expanded)
%              Number of leaves         :   22 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   89 ( 174 expanded)
%              Number of equality atoms :    5 (  17 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
             => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
          <=> ( r2_hidden(A,k1_relat_1(C))
              & r2_hidden(k1_funct_1(C,A),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).

tff(c_32,plain,(
    ~ r1_tarski(k2_relat_1('#skF_7'),k1_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_36,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_48,plain,(
    ! [A_53,B_54] :
      ( r2_hidden('#skF_1'(A_53,B_54),A_53)
      | r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53,plain,(
    ! [A_53] : r1_tarski(A_53,A_53) ),
    inference(resolution,[status(thm)],[c_48,c_4])).

tff(c_76,plain,(
    ! [A_68,C_69] :
      ( r2_hidden('#skF_5'(A_68,k2_relat_1(A_68),C_69),k1_relat_1(A_68))
      | ~ r2_hidden(C_69,k2_relat_1(A_68))
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_82,plain,(
    ! [A_68,C_69,B_2] :
      ( r2_hidden('#skF_5'(A_68,k2_relat_1(A_68),C_69),B_2)
      | ~ r1_tarski(k1_relat_1(A_68),B_2)
      | ~ r2_hidden(C_69,k2_relat_1(A_68))
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(resolution,[status(thm)],[c_76,c_2])).

tff(c_42,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_40,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_34,plain,(
    k1_relat_1(k5_relat_1('#skF_7','#skF_6')) = k1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_10,plain,(
    ! [A_6,C_42] :
      ( k1_funct_1(A_6,'#skF_5'(A_6,k2_relat_1(A_6),C_42)) = C_42
      | ~ r2_hidden(C_42,k2_relat_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_182,plain,(
    ! [C_87,A_88,B_89] :
      ( r2_hidden(k1_funct_1(C_87,A_88),k1_relat_1(B_89))
      | ~ r2_hidden(A_88,k1_relat_1(k5_relat_1(C_87,B_89)))
      | ~ v1_funct_1(C_87)
      | ~ v1_relat_1(C_87)
      | ~ v1_funct_1(B_89)
      | ~ v1_relat_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_604,plain,(
    ! [C_178,B_179,A_180] :
      ( r2_hidden(C_178,k1_relat_1(B_179))
      | ~ r2_hidden('#skF_5'(A_180,k2_relat_1(A_180),C_178),k1_relat_1(k5_relat_1(A_180,B_179)))
      | ~ v1_funct_1(A_180)
      | ~ v1_relat_1(A_180)
      | ~ v1_funct_1(B_179)
      | ~ v1_relat_1(B_179)
      | ~ r2_hidden(C_178,k2_relat_1(A_180))
      | ~ v1_funct_1(A_180)
      | ~ v1_relat_1(A_180) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_182])).

tff(c_615,plain,(
    ! [C_178] :
      ( r2_hidden(C_178,k1_relat_1('#skF_6'))
      | ~ r2_hidden('#skF_5'('#skF_7',k2_relat_1('#skF_7'),C_178),k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(C_178,k2_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_604])).

tff(c_620,plain,(
    ! [C_181] :
      ( r2_hidden(C_181,k1_relat_1('#skF_6'))
      | ~ r2_hidden('#skF_5'('#skF_7',k2_relat_1('#skF_7'),C_181),k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_181,k2_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_42,c_40,c_38,c_36,c_615])).

tff(c_624,plain,(
    ! [C_69] :
      ( r2_hidden(C_69,k1_relat_1('#skF_6'))
      | ~ r1_tarski(k1_relat_1('#skF_7'),k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_69,k2_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_82,c_620])).

tff(c_635,plain,(
    ! [C_182] :
      ( r2_hidden(C_182,k1_relat_1('#skF_6'))
      | ~ r2_hidden(C_182,k2_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_53,c_624])).

tff(c_745,plain,(
    ! [B_183] :
      ( r2_hidden('#skF_1'(k2_relat_1('#skF_7'),B_183),k1_relat_1('#skF_6'))
      | r1_tarski(k2_relat_1('#skF_7'),B_183) ) ),
    inference(resolution,[status(thm)],[c_6,c_635])).

tff(c_751,plain,(
    r1_tarski(k2_relat_1('#skF_7'),k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_745,c_4])).

tff(c_756,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_32,c_751])).

%------------------------------------------------------------------------------
