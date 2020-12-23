%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1052+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:20 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   35 (  47 expanded)
%              Number of leaves         :   19 (  27 expanded)
%              Depth                    :    5
%              Number of atoms          :   35 (  86 expanded)
%              Number of equality atoms :   13 (  28 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_51,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(C,k1_funct_2(A,B))
         => ( k1_relat_1(C) = A
            & r1_tarski(k2_relat_1(C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_funct_2)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k1_funct_2(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E] :
              ( v1_relat_1(E)
              & v1_funct_1(E)
              & D = E
              & k1_relat_1(E) = A
              & r1_tarski(k2_relat_1(E),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).

tff(c_38,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_7'),'#skF_6')
    | k1_relat_1('#skF_7') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_45,plain,(
    k1_relat_1('#skF_7') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_40,plain,(
    r2_hidden('#skF_7',k1_funct_2('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_47,plain,(
    ! [A_24,B_25,D_26] :
      ( '#skF_4'(A_24,B_25,k1_funct_2(A_24,B_25),D_26) = D_26
      | ~ r2_hidden(D_26,k1_funct_2(A_24,B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_50,plain,(
    '#skF_4'('#skF_5','#skF_6',k1_funct_2('#skF_5','#skF_6'),'#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_40,c_47])).

tff(c_70,plain,(
    ! [A_32,B_33,D_34] :
      ( k1_relat_1('#skF_4'(A_32,B_33,k1_funct_2(A_32,B_33),D_34)) = A_32
      | ~ r2_hidden(D_34,k1_funct_2(A_32,B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_82,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ r2_hidden('#skF_7',k1_funct_2('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_70])).

tff(c_86,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_82])).

tff(c_88,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_86])).

tff(c_89,plain,(
    ~ r1_tarski(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_96,plain,(
    ! [A_38,B_39,D_40] :
      ( '#skF_4'(A_38,B_39,k1_funct_2(A_38,B_39),D_40) = D_40
      | ~ r2_hidden(D_40,k1_funct_2(A_38,B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_99,plain,(
    '#skF_4'('#skF_5','#skF_6',k1_funct_2('#skF_5','#skF_6'),'#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_40,c_96])).

tff(c_146,plain,(
    ! [A_51,B_52,D_53] :
      ( r1_tarski(k2_relat_1('#skF_4'(A_51,B_52,k1_funct_2(A_51,B_52),D_53)),B_52)
      | ~ r2_hidden(D_53,k1_funct_2(A_51,B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_149,plain,
    ( r1_tarski(k2_relat_1('#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_7',k1_funct_2('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_146])).

tff(c_151,plain,(
    r1_tarski(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_149])).

tff(c_153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_151])).

%------------------------------------------------------------------------------
