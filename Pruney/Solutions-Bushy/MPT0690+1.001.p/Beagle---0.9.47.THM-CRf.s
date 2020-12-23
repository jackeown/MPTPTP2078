%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0690+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:43 EST 2020

% Result     : Theorem 4.14s
% Output     : CNFRefutation 4.14s
% Verified   : 
% Statistics : Number of formulae       :   38 (  42 expanded)
%              Number of leaves         :   24 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   59 (  75 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k1_funct_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_1 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_7

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

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( r2_hidden(D,k1_relat_1(A))
                & r2_hidden(k1_funct_1(A,D),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

tff(c_54,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_52,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_48,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_7'(A_55,B_56),A_55)
      | r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [A_1,B_24,D_39] :
      ( r2_hidden('#skF_4'(A_1,B_24,k9_relat_1(A_1,B_24),D_39),B_24)
      | ~ r2_hidden(D_39,k9_relat_1(A_1,B_24))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_165,plain,(
    ! [A_106,B_107,D_108] :
      ( k1_funct_1(A_106,'#skF_4'(A_106,B_107,k9_relat_1(A_106,B_107),D_108)) = D_108
      | ~ r2_hidden(D_108,k9_relat_1(A_106,B_107))
      | ~ v1_funct_1(A_106)
      | ~ v1_relat_1(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28,plain,(
    ! [A_43,D_54,B_50] :
      ( r2_hidden(k1_funct_1(A_43,D_54),B_50)
      | ~ r2_hidden(D_54,k10_relat_1(A_43,B_50))
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_919,plain,(
    ! [D_263,B_264,A_265,B_266] :
      ( r2_hidden(D_263,B_264)
      | ~ r2_hidden('#skF_4'(A_265,B_266,k9_relat_1(A_265,B_266),D_263),k10_relat_1(A_265,B_264))
      | ~ v1_funct_1(A_265)
      | ~ v1_relat_1(A_265)
      | ~ r2_hidden(D_263,k9_relat_1(A_265,B_266))
      | ~ v1_funct_1(A_265)
      | ~ v1_relat_1(A_265) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_28])).

tff(c_940,plain,(
    ! [D_267,B_268,A_269] :
      ( r2_hidden(D_267,B_268)
      | ~ r2_hidden(D_267,k9_relat_1(A_269,k10_relat_1(A_269,B_268)))
      | ~ v1_funct_1(A_269)
      | ~ v1_relat_1(A_269) ) ),
    inference(resolution,[status(thm)],[c_6,c_919])).

tff(c_1141,plain,(
    ! [A_285,B_286,B_287] :
      ( r2_hidden('#skF_7'(k9_relat_1(A_285,k10_relat_1(A_285,B_286)),B_287),B_286)
      | ~ v1_funct_1(A_285)
      | ~ v1_relat_1(A_285)
      | r1_tarski(k9_relat_1(A_285,k10_relat_1(A_285,B_286)),B_287) ) ),
    inference(resolution,[status(thm)],[c_48,c_940])).

tff(c_46,plain,(
    ! [A_55,B_56] :
      ( ~ r2_hidden('#skF_7'(A_55,B_56),B_56)
      | r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1175,plain,(
    ! [A_292,B_293] :
      ( ~ v1_funct_1(A_292)
      | ~ v1_relat_1(A_292)
      | r1_tarski(k9_relat_1(A_292,k10_relat_1(A_292,B_293)),B_293) ) ),
    inference(resolution,[status(thm)],[c_1141,c_46])).

tff(c_50,plain,(
    ~ r1_tarski(k9_relat_1('#skF_9',k10_relat_1('#skF_9','#skF_8')),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1209,plain,
    ( ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_1175,c_50])).

tff(c_1226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1209])).

%------------------------------------------------------------------------------
