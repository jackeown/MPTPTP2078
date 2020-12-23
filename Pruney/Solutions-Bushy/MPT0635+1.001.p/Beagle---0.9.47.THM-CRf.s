%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0635+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:37 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   46 (  67 expanded)
%              Number of leaves         :   23 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 ( 119 expanded)
%              Number of equality atoms :   20 (  30 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_26,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(C,A) = k1_funct_1(k5_relat_1(k6_relat_1(B),C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_38,plain,(
    r2_hidden('#skF_4',k3_xboole_0(k1_relat_1('#skF_6'),'#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_51,plain,(
    r2_hidden('#skF_4',k3_xboole_0('#skF_5',k1_relat_1('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_38])).

tff(c_116,plain,(
    ! [D_29,A_30,B_31] :
      ( r2_hidden(D_29,A_30)
      | ~ r2_hidden(D_29,k3_xboole_0(A_30,B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_126,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_51,c_116])).

tff(c_22,plain,(
    ! [A_9] : v1_relat_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ! [A_9] : v1_funct_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_32,plain,(
    ! [A_14,C_18] :
      ( k1_funct_1(k6_relat_1(A_14),C_18) = C_18
      | ~ r2_hidden(C_18,A_14)
      | ~ v1_funct_1(k6_relat_1(A_14))
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_46,plain,(
    ! [A_14,C_18] :
      ( k1_funct_1(k6_relat_1(A_14),C_18) = C_18
      | ~ r2_hidden(C_18,A_14)
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_32])).

tff(c_48,plain,(
    ! [A_14,C_18] :
      ( k1_funct_1(k6_relat_1(A_14),C_18) = C_18
      | ~ r2_hidden(C_18,A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_46])).

tff(c_42,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_40,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_34,plain,(
    ! [A_14] :
      ( k1_relat_1(k6_relat_1(A_14)) = A_14
      | ~ v1_funct_1(k6_relat_1(A_14))
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_44,plain,(
    ! [A_14] :
      ( k1_relat_1(k6_relat_1(A_14)) = A_14
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_34])).

tff(c_50,plain,(
    ! [A_14] : k1_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_44])).

tff(c_374,plain,(
    ! [B_68,C_69,A_70] :
      ( k1_funct_1(k5_relat_1(B_68,C_69),A_70) = k1_funct_1(C_69,k1_funct_1(B_68,A_70))
      | ~ r2_hidden(A_70,k1_relat_1(B_68))
      | ~ v1_funct_1(C_69)
      | ~ v1_relat_1(C_69)
      | ~ v1_funct_1(B_68)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_413,plain,(
    ! [A_14,C_69,A_70] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_14),C_69),A_70) = k1_funct_1(C_69,k1_funct_1(k6_relat_1(A_14),A_70))
      | ~ r2_hidden(A_70,A_14)
      | ~ v1_funct_1(C_69)
      | ~ v1_relat_1(C_69)
      | ~ v1_funct_1(k6_relat_1(A_14))
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_374])).

tff(c_746,plain,(
    ! [A_93,C_94,A_95] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_93),C_94),A_95) = k1_funct_1(C_94,k1_funct_1(k6_relat_1(A_93),A_95))
      | ~ r2_hidden(A_95,A_93)
      | ~ v1_funct_1(C_94)
      | ~ v1_relat_1(C_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_413])).

tff(c_36,plain,(
    k1_funct_1(k5_relat_1(k6_relat_1('#skF_5'),'#skF_6'),'#skF_4') != k1_funct_1('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_756,plain,
    ( k1_funct_1('#skF_6',k1_funct_1(k6_relat_1('#skF_5'),'#skF_4')) != k1_funct_1('#skF_6','#skF_4')
    | ~ r2_hidden('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_746,c_36])).

tff(c_762,plain,(
    k1_funct_1('#skF_6',k1_funct_1(k6_relat_1('#skF_5'),'#skF_4')) != k1_funct_1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_126,c_756])).

tff(c_766,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_762])).

tff(c_770,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_766])).

%------------------------------------------------------------------------------
