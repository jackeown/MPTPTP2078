%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0808+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:52 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :   49 (  88 expanded)
%              Number of leaves         :   24 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :  116 ( 366 expanded)
%              Number of equality atoms :    4 (   9 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_wellord1 > r4_wellord1 > r2_hidden > r1_tarski > v2_wellord1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(r4_wellord1,type,(
    r4_wellord1: ( $i * $i ) > $o )).

tff(r3_wellord1,type,(
    r3_wellord1: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v1_funct_1(C) )
               => ( ( v2_wellord1(A)
                    & r3_wellord1(A,B,C) )
                 => ! [D] :
                      ~ ( r2_hidden(D,k3_relat_1(A))
                        & ! [E] :
                            ~ ( r2_hidden(E,k3_relat_1(B))
                              & r4_wellord1(k2_wellord1(A,k1_wellord1(A,D)),k2_wellord1(B,k1_wellord1(B,E))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_wellord1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ( r3_wellord1(A,B,C)
               => ! [D] :
                    ~ ( r2_hidden(D,k3_relat_1(A))
                      & ! [E] :
                          ~ ( r2_hidden(E,k3_relat_1(B))
                            & k9_relat_1(C,k1_wellord1(A,D)) = k1_wellord1(B,E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_wellord1)).

tff(f_28,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_wellord1(B,A),k3_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_wellord1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ! [D] :
              ( ( v1_relat_1(D)
                & v1_funct_1(D) )
             => ( ( v2_wellord1(B)
                  & r1_tarski(A,k3_relat_1(B))
                  & r3_wellord1(B,C,D) )
               => ( r3_wellord1(k2_wellord1(B,A),k2_wellord1(C,k9_relat_1(D,A)),k7_relat_1(D,A))
                  & r4_wellord1(k2_wellord1(B,A),k2_wellord1(C,k9_relat_1(D,A))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_wellord1)).

tff(c_22,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_20,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_16,plain,(
    r3_wellord1('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_14,plain,(
    r2_hidden('#skF_5',k3_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_10,plain,(
    ! [A_11,B_27,C_35,D_39] :
      ( r2_hidden('#skF_1'(A_11,B_27,C_35,D_39),k3_relat_1(B_27))
      | ~ r2_hidden(D_39,k3_relat_1(A_11))
      | ~ r3_wellord1(A_11,B_27,C_35)
      | ~ v1_funct_1(C_35)
      | ~ v1_relat_1(C_35)
      | ~ v1_relat_1(B_27)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_wellord1(B_2,A_1),k3_relat_1(B_2))
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_18,plain,(
    v2_wellord1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_31,plain,(
    ! [C_79,A_80,D_81,B_82] :
      ( k9_relat_1(C_79,k1_wellord1(A_80,D_81)) = k1_wellord1(B_82,'#skF_1'(A_80,B_82,C_79,D_81))
      | ~ r2_hidden(D_81,k3_relat_1(A_80))
      | ~ r3_wellord1(A_80,B_82,C_79)
      | ~ v1_funct_1(C_79)
      | ~ v1_relat_1(C_79)
      | ~ v1_relat_1(B_82)
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_35,plain,(
    ! [C_79,B_82] :
      ( k9_relat_1(C_79,k1_wellord1('#skF_2','#skF_5')) = k1_wellord1(B_82,'#skF_1'('#skF_2',B_82,C_79,'#skF_5'))
      | ~ r3_wellord1('#skF_2',B_82,C_79)
      | ~ v1_funct_1(C_79)
      | ~ v1_relat_1(C_79)
      | ~ v1_relat_1(B_82)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_14,c_31])).

tff(c_40,plain,(
    ! [C_83,B_84] :
      ( k9_relat_1(C_83,k1_wellord1('#skF_2','#skF_5')) = k1_wellord1(B_84,'#skF_1'('#skF_2',B_84,C_83,'#skF_5'))
      | ~ r3_wellord1('#skF_2',B_84,C_83)
      | ~ v1_funct_1(C_83)
      | ~ v1_relat_1(C_83)
      | ~ v1_relat_1(B_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_35])).

tff(c_4,plain,(
    ! [B_4,A_3,C_8,D_10] :
      ( r4_wellord1(k2_wellord1(B_4,A_3),k2_wellord1(C_8,k9_relat_1(D_10,A_3)))
      | ~ r3_wellord1(B_4,C_8,D_10)
      | ~ r1_tarski(A_3,k3_relat_1(B_4))
      | ~ v2_wellord1(B_4)
      | ~ v1_funct_1(D_10)
      | ~ v1_relat_1(D_10)
      | ~ v1_relat_1(C_8)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_381,plain,(
    ! [B_141,C_142,B_143,C_144] :
      ( r4_wellord1(k2_wellord1(B_141,k1_wellord1('#skF_2','#skF_5')),k2_wellord1(C_142,k1_wellord1(B_143,'#skF_1'('#skF_2',B_143,C_144,'#skF_5'))))
      | ~ r3_wellord1(B_141,C_142,C_144)
      | ~ r1_tarski(k1_wellord1('#skF_2','#skF_5'),k3_relat_1(B_141))
      | ~ v2_wellord1(B_141)
      | ~ v1_funct_1(C_144)
      | ~ v1_relat_1(C_144)
      | ~ v1_relat_1(C_142)
      | ~ v1_relat_1(B_141)
      | ~ r3_wellord1('#skF_2',B_143,C_144)
      | ~ v1_funct_1(C_144)
      | ~ v1_relat_1(C_144)
      | ~ v1_relat_1(B_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_4])).

tff(c_12,plain,(
    ! [E_67] :
      ( ~ r4_wellord1(k2_wellord1('#skF_2',k1_wellord1('#skF_2','#skF_5')),k2_wellord1('#skF_3',k1_wellord1('#skF_3',E_67)))
      | ~ r2_hidden(E_67,k3_relat_1('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_389,plain,(
    ! [C_144] :
      ( ~ r2_hidden('#skF_1'('#skF_2','#skF_3',C_144,'#skF_5'),k3_relat_1('#skF_3'))
      | ~ r1_tarski(k1_wellord1('#skF_2','#skF_5'),k3_relat_1('#skF_2'))
      | ~ v2_wellord1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ r3_wellord1('#skF_2','#skF_3',C_144)
      | ~ v1_funct_1(C_144)
      | ~ v1_relat_1(C_144)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_381,c_12])).

tff(c_404,plain,(
    ! [C_144] :
      ( ~ r2_hidden('#skF_1'('#skF_2','#skF_3',C_144,'#skF_5'),k3_relat_1('#skF_3'))
      | ~ r1_tarski(k1_wellord1('#skF_2','#skF_5'),k3_relat_1('#skF_2'))
      | ~ r3_wellord1('#skF_2','#skF_3',C_144)
      | ~ v1_funct_1(C_144)
      | ~ v1_relat_1(C_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26,c_18,c_389])).

tff(c_405,plain,(
    ~ r1_tarski(k1_wellord1('#skF_2','#skF_5'),k3_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_404])).

tff(c_408,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_405])).

tff(c_412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_408])).

tff(c_451,plain,(
    ! [C_146] :
      ( ~ r2_hidden('#skF_1'('#skF_2','#skF_3',C_146,'#skF_5'),k3_relat_1('#skF_3'))
      | ~ r3_wellord1('#skF_2','#skF_3',C_146)
      | ~ v1_funct_1(C_146)
      | ~ v1_relat_1(C_146) ) ),
    inference(splitRight,[status(thm)],[c_404])).

tff(c_455,plain,(
    ! [C_35] :
      ( ~ r2_hidden('#skF_5',k3_relat_1('#skF_2'))
      | ~ r3_wellord1('#skF_2','#skF_3',C_35)
      | ~ v1_funct_1(C_35)
      | ~ v1_relat_1(C_35)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_10,c_451])).

tff(c_459,plain,(
    ! [C_147] :
      ( ~ r3_wellord1('#skF_2','#skF_3',C_147)
      | ~ v1_funct_1(C_147)
      | ~ v1_relat_1(C_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_14,c_455])).

tff(c_462,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_459])).

tff(c_466,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_462])).

%------------------------------------------------------------------------------
