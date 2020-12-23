%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0600+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:33 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :   46 (  64 expanded)
%              Number of leaves         :   22 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   72 ( 119 expanded)
%              Number of equality atoms :    7 (  15 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k9_relat_1 > k4_tarski > k11_relat_1 > #nlpp > k1_tarski > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r2_hidden(k4_tarski(A,B),C)
        <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_34,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_36,plain,
    ( ~ r2_hidden('#skF_8',k11_relat_1('#skF_9','#skF_7'))
    | ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_59,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_42,plain,
    ( r2_hidden(k4_tarski('#skF_7','#skF_8'),'#skF_9')
    | r2_hidden('#skF_8',k11_relat_1('#skF_9','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_60,plain,(
    r2_hidden('#skF_8',k11_relat_1('#skF_9','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_42])).

tff(c_20,plain,(
    ! [A_43,B_45] :
      ( k9_relat_1(A_43,k1_tarski(B_45)) = k11_relat_1(A_43,B_45)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_132,plain,(
    ! [A_75,B_76,D_77] :
      ( r2_hidden('#skF_4'(A_75,B_76,k9_relat_1(A_75,B_76),D_77),B_76)
      | ~ r2_hidden(D_77,k9_relat_1(A_75,B_76))
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [C_50,A_46] :
      ( C_50 = A_46
      | ~ r2_hidden(C_50,k1_tarski(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_234,plain,(
    ! [A_98,A_99,D_100] :
      ( '#skF_4'(A_98,k1_tarski(A_99),k9_relat_1(A_98,k1_tarski(A_99)),D_100) = A_99
      | ~ r2_hidden(D_100,k9_relat_1(A_98,k1_tarski(A_99)))
      | ~ v1_relat_1(A_98) ) ),
    inference(resolution,[status(thm)],[c_132,c_22])).

tff(c_6,plain,(
    ! [A_1,B_24,D_39] :
      ( r2_hidden(k4_tarski('#skF_4'(A_1,B_24,k9_relat_1(A_1,B_24),D_39),D_39),A_1)
      | ~ r2_hidden(D_39,k9_relat_1(A_1,B_24))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_489,plain,(
    ! [A_139,D_140,A_141] :
      ( r2_hidden(k4_tarski(A_139,D_140),A_141)
      | ~ r2_hidden(D_140,k9_relat_1(A_141,k1_tarski(A_139)))
      | ~ v1_relat_1(A_141)
      | ~ r2_hidden(D_140,k9_relat_1(A_141,k1_tarski(A_139)))
      | ~ v1_relat_1(A_141) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_6])).

tff(c_764,plain,(
    ! [B_169,D_170,A_171] :
      ( r2_hidden(k4_tarski(B_169,D_170),A_171)
      | ~ r2_hidden(D_170,k11_relat_1(A_171,B_169))
      | ~ v1_relat_1(A_171)
      | ~ r2_hidden(D_170,k9_relat_1(A_171,k1_tarski(B_169)))
      | ~ v1_relat_1(A_171)
      | ~ v1_relat_1(A_171) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_489])).

tff(c_1169,plain,(
    ! [B_202,D_203,A_204] :
      ( r2_hidden(k4_tarski(B_202,D_203),A_204)
      | ~ r2_hidden(D_203,k11_relat_1(A_204,B_202))
      | ~ v1_relat_1(A_204)
      | ~ r2_hidden(D_203,k11_relat_1(A_204,B_202))
      | ~ v1_relat_1(A_204)
      | ~ v1_relat_1(A_204)
      | ~ v1_relat_1(A_204) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_764])).

tff(c_1219,plain,
    ( ~ r2_hidden('#skF_8',k11_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_1169,c_59])).

tff(c_1248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_60,c_1219])).

tff(c_1249,plain,(
    ~ r2_hidden('#skF_8',k11_relat_1('#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1250,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_24,plain,(
    ! [C_50] : r2_hidden(C_50,k1_tarski(C_50)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1290,plain,(
    ! [D_215,A_216,B_217,E_218] :
      ( r2_hidden(D_215,k9_relat_1(A_216,B_217))
      | ~ r2_hidden(E_218,B_217)
      | ~ r2_hidden(k4_tarski(E_218,D_215),A_216)
      | ~ v1_relat_1(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1303,plain,(
    ! [D_219,A_220,C_221] :
      ( r2_hidden(D_219,k9_relat_1(A_220,k1_tarski(C_221)))
      | ~ r2_hidden(k4_tarski(C_221,D_219),A_220)
      | ~ v1_relat_1(A_220) ) ),
    inference(resolution,[status(thm)],[c_24,c_1290])).

tff(c_1326,plain,(
    ! [D_224,A_225,B_226] :
      ( r2_hidden(D_224,k11_relat_1(A_225,B_226))
      | ~ r2_hidden(k4_tarski(B_226,D_224),A_225)
      | ~ v1_relat_1(A_225)
      | ~ v1_relat_1(A_225) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1303])).

tff(c_1333,plain,
    ( r2_hidden('#skF_8',k11_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_1250,c_1326])).

tff(c_1341,plain,(
    r2_hidden('#skF_8',k11_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1333])).

tff(c_1343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1249,c_1341])).

%------------------------------------------------------------------------------
