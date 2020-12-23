%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0671+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:40 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   39 (  64 expanded)
%              Number of leaves         :   21 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   64 ( 140 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k8_relat_1 > k1_funct_1 > #nlpp > k1_relat_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => r1_tarski(k1_relat_1(k8_relat_1(A,B)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k8_relat_1(A,B))
        & v1_funct_1(k8_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( B = k8_relat_1(A,C)
          <=> ( ! [D] :
                  ( r2_hidden(D,k1_relat_1(B))
                <=> ( r2_hidden(D,k1_relat_1(C))
                    & r2_hidden(k1_funct_1(C,D),A) ) )
              & ! [D] :
                  ( r2_hidden(D,k1_relat_1(B))
                 => k1_funct_1(B,D) = k1_funct_1(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_1)).

tff(c_50,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_48,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( v1_funct_1(k8_relat_1(A_8,B_9))
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k8_relat_1(A_6,B_7))
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_65,plain,(
    ! [D_40,C_41,A_42] :
      ( r2_hidden(D_40,k1_relat_1(C_41))
      | ~ r2_hidden(D_40,k1_relat_1(k8_relat_1(A_42,C_41)))
      | ~ v1_funct_1(C_41)
      | ~ v1_relat_1(C_41)
      | ~ v1_funct_1(k8_relat_1(A_42,C_41))
      | ~ v1_relat_1(k8_relat_1(A_42,C_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_151,plain,(
    ! [A_62,C_63,B_64] :
      ( r2_hidden('#skF_1'(k1_relat_1(k8_relat_1(A_62,C_63)),B_64),k1_relat_1(C_63))
      | ~ v1_funct_1(C_63)
      | ~ v1_relat_1(C_63)
      | ~ v1_funct_1(k8_relat_1(A_62,C_63))
      | ~ v1_relat_1(k8_relat_1(A_62,C_63))
      | r1_tarski(k1_relat_1(k8_relat_1(A_62,C_63)),B_64) ) ),
    inference(resolution,[status(thm)],[c_6,c_65])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_175,plain,(
    ! [C_65,A_66] :
      ( ~ v1_funct_1(C_65)
      | ~ v1_relat_1(C_65)
      | ~ v1_funct_1(k8_relat_1(A_66,C_65))
      | ~ v1_relat_1(k8_relat_1(A_66,C_65))
      | r1_tarski(k1_relat_1(k8_relat_1(A_66,C_65)),k1_relat_1(C_65)) ) ),
    inference(resolution,[status(thm)],[c_151,c_4])).

tff(c_46,plain,(
    ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_5','#skF_6')),k1_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_180,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_175,c_46])).

tff(c_184,plain,
    ( ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_180])).

tff(c_185,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_188,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_8,c_185])).

tff(c_192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_188])).

tff(c_193,plain,(
    ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_197,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_10,c_193])).

tff(c_201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_197])).

%------------------------------------------------------------------------------
