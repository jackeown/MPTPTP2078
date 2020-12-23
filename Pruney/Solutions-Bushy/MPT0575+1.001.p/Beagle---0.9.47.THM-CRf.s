%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0575+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:31 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   37 (  44 expanded)
%              Number of leaves         :   19 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   57 (  85 expanded)
%              Number of equality atoms :    1 (   3 expanded)
%              Maximal formula depth    :   11 (   5 average)
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

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => ( r1_tarski(B,C)
             => r1_tarski(k10_relat_1(B,A),k10_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t179_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

tff(c_24,plain,(
    ! [A_43,B_44] :
      ( r2_hidden('#skF_5'(A_43,B_44),A_43)
      | r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_32,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_30,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_28,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_119,plain,(
    ! [D_87,A_88,B_89] :
      ( r2_hidden(k4_tarski(D_87,'#skF_4'(A_88,B_89,k10_relat_1(A_88,B_89),D_87)),A_88)
      | ~ r2_hidden(D_87,k10_relat_1(A_88,B_89))
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [C_47,B_44,A_43] :
      ( r2_hidden(C_47,B_44)
      | ~ r2_hidden(C_47,A_43)
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_125,plain,(
    ! [D_87,A_88,B_89,B_44] :
      ( r2_hidden(k4_tarski(D_87,'#skF_4'(A_88,B_89,k10_relat_1(A_88,B_89),D_87)),B_44)
      | ~ r1_tarski(A_88,B_44)
      | ~ r2_hidden(D_87,k10_relat_1(A_88,B_89))
      | ~ v1_relat_1(A_88) ) ),
    inference(resolution,[status(thm)],[c_119,c_20])).

tff(c_104,plain,(
    ! [A_76,B_77,D_78] :
      ( r2_hidden('#skF_4'(A_76,B_77,k10_relat_1(A_76,B_77),D_78),B_77)
      | ~ r2_hidden(D_78,k10_relat_1(A_76,B_77))
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [D_39,A_1,B_24,E_42] :
      ( r2_hidden(D_39,k10_relat_1(A_1,B_24))
      | ~ r2_hidden(E_42,B_24)
      | ~ r2_hidden(k4_tarski(D_39,E_42),A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_329,plain,(
    ! [D_192,A_194,A_193,B_190,D_191] :
      ( r2_hidden(D_192,k10_relat_1(A_194,B_190))
      | ~ r2_hidden(k4_tarski(D_192,'#skF_4'(A_193,B_190,k10_relat_1(A_193,B_190),D_191)),A_194)
      | ~ v1_relat_1(A_194)
      | ~ r2_hidden(D_191,k10_relat_1(A_193,B_190))
      | ~ v1_relat_1(A_193) ) ),
    inference(resolution,[status(thm)],[c_104,c_2])).

tff(c_433,plain,(
    ! [D_198,B_199,B_200,A_201] :
      ( r2_hidden(D_198,k10_relat_1(B_199,B_200))
      | ~ v1_relat_1(B_199)
      | ~ r1_tarski(A_201,B_199)
      | ~ r2_hidden(D_198,k10_relat_1(A_201,B_200))
      | ~ v1_relat_1(A_201) ) ),
    inference(resolution,[status(thm)],[c_125,c_329])).

tff(c_437,plain,(
    ! [D_198,B_200] :
      ( r2_hidden(D_198,k10_relat_1('#skF_8',B_200))
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_198,k10_relat_1('#skF_7',B_200))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_28,c_433])).

tff(c_442,plain,(
    ! [D_202,B_203] :
      ( r2_hidden(D_202,k10_relat_1('#skF_8',B_203))
      | ~ r2_hidden(D_202,k10_relat_1('#skF_7',B_203)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_437])).

tff(c_569,plain,(
    ! [B_208,B_209] :
      ( r2_hidden('#skF_5'(k10_relat_1('#skF_7',B_208),B_209),k10_relat_1('#skF_8',B_208))
      | r1_tarski(k10_relat_1('#skF_7',B_208),B_209) ) ),
    inference(resolution,[status(thm)],[c_24,c_442])).

tff(c_22,plain,(
    ! [A_43,B_44] :
      ( ~ r2_hidden('#skF_5'(A_43,B_44),B_44)
      | r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_585,plain,(
    ! [B_208] : r1_tarski(k10_relat_1('#skF_7',B_208),k10_relat_1('#skF_8',B_208)) ),
    inference(resolution,[status(thm)],[c_569,c_22])).

tff(c_26,plain,(
    ~ r1_tarski(k10_relat_1('#skF_7','#skF_6'),k10_relat_1('#skF_8','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_588,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_585,c_26])).

%------------------------------------------------------------------------------
