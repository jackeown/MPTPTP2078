%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0720+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:45 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   47 (  55 expanded)
%              Number of leaves         :   25 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   97 ( 132 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B)
              & v5_funct_1(B,A) )
           => r1_tarski(k1_relat_1(B),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_66,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_65,axiom,(
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

tff(f_40,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( v5_funct_1(B,A)
          <=> ! [C] :
                ( r2_hidden(C,k1_relat_1(B))
               => r2_hidden(k1_funct_1(B,C),k1_funct_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(c_38,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_34,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_32,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_30,plain,(
    v5_funct_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_2'(A_11,B_12),A_11)
      | r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_39,plain,(
    ! [A_25] :
      ( k1_xboole_0 = A_25
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_43,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_39])).

tff(c_44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_22])).

tff(c_96,plain,(
    ! [A_44,B_45] :
      ( k1_funct_1(A_44,B_45) = k1_xboole_0
      | r2_hidden(B_45,k1_relat_1(A_44))
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10,plain,(
    ! [A_11,B_12] :
      ( ~ r2_hidden('#skF_2'(A_11,B_12),B_12)
      | r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_107,plain,(
    ! [A_11,A_44] :
      ( r1_tarski(A_11,k1_relat_1(A_44))
      | k1_funct_1(A_44,'#skF_2'(A_11,k1_relat_1(A_44))) = k1_xboole_0
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(resolution,[status(thm)],[c_96,c_10])).

tff(c_340,plain,(
    ! [B_97,C_98,A_99] :
      ( r2_hidden(k1_funct_1(B_97,C_98),k1_funct_1(A_99,C_98))
      | ~ r2_hidden(C_98,k1_relat_1(B_97))
      | ~ v5_funct_1(B_97,A_99)
      | ~ v1_funct_1(B_97)
      | ~ v1_relat_1(B_97)
      | ~ v1_funct_1(A_99)
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_26,plain,(
    ! [B_23,A_22] :
      ( ~ v1_xboole_0(B_23)
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_374,plain,(
    ! [A_103,C_104,B_105] :
      ( ~ v1_xboole_0(k1_funct_1(A_103,C_104))
      | ~ r2_hidden(C_104,k1_relat_1(B_105))
      | ~ v5_funct_1(B_105,A_103)
      | ~ v1_funct_1(B_105)
      | ~ v1_relat_1(B_105)
      | ~ v1_funct_1(A_103)
      | ~ v1_relat_1(A_103) ) ),
    inference(resolution,[status(thm)],[c_340,c_26])).

tff(c_376,plain,(
    ! [A_11,A_44,B_105] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden('#skF_2'(A_11,k1_relat_1(A_44)),k1_relat_1(B_105))
      | ~ v5_funct_1(B_105,A_44)
      | ~ v1_funct_1(B_105)
      | ~ v1_relat_1(B_105)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44)
      | r1_tarski(A_11,k1_relat_1(A_44))
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_374])).

tff(c_410,plain,(
    ! [A_115,A_116,B_117] :
      ( ~ r2_hidden('#skF_2'(A_115,k1_relat_1(A_116)),k1_relat_1(B_117))
      | ~ v5_funct_1(B_117,A_116)
      | ~ v1_funct_1(B_117)
      | ~ v1_relat_1(B_117)
      | r1_tarski(A_115,k1_relat_1(A_116))
      | ~ v1_funct_1(A_116)
      | ~ v1_relat_1(A_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_376])).

tff(c_426,plain,(
    ! [B_118,A_119] :
      ( ~ v5_funct_1(B_118,A_119)
      | ~ v1_funct_1(B_118)
      | ~ v1_relat_1(B_118)
      | ~ v1_funct_1(A_119)
      | ~ v1_relat_1(A_119)
      | r1_tarski(k1_relat_1(B_118),k1_relat_1(A_119)) ) ),
    inference(resolution,[status(thm)],[c_12,c_410])).

tff(c_28,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_448,plain,
    ( ~ v5_funct_1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_426,c_28])).

tff(c_461,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_448])).

%------------------------------------------------------------------------------
