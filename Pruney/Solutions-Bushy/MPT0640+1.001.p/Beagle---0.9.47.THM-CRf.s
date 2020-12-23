%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0640+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:38 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 300 expanded)
%              Number of leaves         :   22 ( 120 expanded)
%              Depth                    :   12
%              Number of atoms          :  207 (1181 expanded)
%              Number of equality atoms :   28 ( 137 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v2_funct_1(k5_relat_1(B,A))
                & r1_tarski(k2_relat_1(B),k1_relat_1(A)) )
             => v2_funct_1(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_22,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_30,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_28,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_10,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),k1_relat_1(A_1))
      | v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_2'(A_1),k1_relat_1(A_1))
      | v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_36,plain,(
    ! [A_22] :
      ( '#skF_2'(A_22) != '#skF_1'(A_22)
      | v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_39,plain,
    ( '#skF_2'('#skF_4') != '#skF_1'('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_22])).

tff(c_42,plain,(
    '#skF_2'('#skF_4') != '#skF_1'('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_39])).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(k5_relat_1(A_8,B_9))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    r1_tarski(k2_relat_1('#skF_4'),k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_55,plain,(
    ! [A_28,B_29] :
      ( k1_relat_1(k5_relat_1(A_28,B_29)) = k1_relat_1(A_28)
      | ~ r1_tarski(k2_relat_1(A_28),k1_relat_1(B_29))
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_58,plain,
    ( k1_relat_1(k5_relat_1('#skF_4','#skF_3')) = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_55])).

tff(c_61,plain,(
    k1_relat_1(k5_relat_1('#skF_4','#skF_3')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34,c_58])).

tff(c_20,plain,(
    ! [A_16,B_18] :
      ( k1_relat_1(k5_relat_1(A_16,B_18)) = k1_relat_1(A_16)
      | ~ r1_tarski(k2_relat_1(A_16),k1_relat_1(B_18))
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_74,plain,(
    ! [A_16] :
      ( k1_relat_1(k5_relat_1(A_16,k5_relat_1('#skF_4','#skF_3'))) = k1_relat_1(A_16)
      | ~ r1_tarski(k2_relat_1(A_16),k1_relat_1('#skF_4'))
      | ~ v1_relat_1(k5_relat_1('#skF_4','#skF_3'))
      | ~ v1_relat_1(A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_20])).

tff(c_86,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_89,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_86])).

tff(c_93,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34,c_89])).

tff(c_95,plain,(
    v1_relat_1(k5_relat_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( v1_funct_1(k5_relat_1(A_10,B_11))
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    ! [B_13,C_15,A_12] :
      ( k1_funct_1(k5_relat_1(B_13,C_15),A_12) = k1_funct_1(C_15,k1_funct_1(B_13,A_12))
      | ~ r2_hidden(A_12,k1_relat_1(B_13))
      | ~ v1_funct_1(C_15)
      | ~ v1_relat_1(C_15)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_71,plain,(
    ! [C_15,A_12] :
      ( k1_funct_1(k5_relat_1(k5_relat_1('#skF_4','#skF_3'),C_15),A_12) = k1_funct_1(C_15,k1_funct_1(k5_relat_1('#skF_4','#skF_3'),A_12))
      | ~ r2_hidden(A_12,k1_relat_1('#skF_4'))
      | ~ v1_funct_1(C_15)
      | ~ v1_relat_1(C_15)
      | ~ v1_funct_1(k5_relat_1('#skF_4','#skF_3'))
      | ~ v1_relat_1(k5_relat_1('#skF_4','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_18])).

tff(c_96,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_98,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_96])).

tff(c_99,plain,(
    ! [C_15,A_12] :
      ( ~ v1_funct_1(k5_relat_1('#skF_4','#skF_3'))
      | k1_funct_1(k5_relat_1(k5_relat_1('#skF_4','#skF_3'),C_15),A_12) = k1_funct_1(C_15,k1_funct_1(k5_relat_1('#skF_4','#skF_3'),A_12))
      | ~ r2_hidden(A_12,k1_relat_1('#skF_4'))
      | ~ v1_funct_1(C_15)
      | ~ v1_relat_1(C_15) ) ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_138,plain,(
    ~ v1_funct_1(k5_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_141,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_138])).

tff(c_145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_34,c_32,c_141])).

tff(c_147,plain,(
    v1_funct_1(k5_relat_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_26,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_62,plain,(
    ! [B_30,C_31,A_32] :
      ( k1_funct_1(k5_relat_1(B_30,C_31),A_32) = k1_funct_1(C_31,k1_funct_1(B_30,A_32))
      | ~ r2_hidden(A_32,k1_relat_1(B_30))
      | ~ v1_funct_1(C_31)
      | ~ v1_relat_1(C_31)
      | ~ v1_funct_1(B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_68,plain,(
    ! [A_1,C_31] :
      ( k1_funct_1(k5_relat_1(A_1,C_31),'#skF_1'(A_1)) = k1_funct_1(C_31,k1_funct_1(A_1,'#skF_1'(A_1)))
      | ~ v1_funct_1(C_31)
      | ~ v1_relat_1(C_31)
      | v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(resolution,[status(thm)],[c_10,c_62])).

tff(c_6,plain,(
    ! [A_1] :
      ( k1_funct_1(A_1,'#skF_2'(A_1)) = k1_funct_1(A_1,'#skF_1'(A_1))
      | v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_125,plain,(
    ! [A_39,C_40] :
      ( k1_funct_1(k5_relat_1(A_39,C_40),'#skF_2'(A_39)) = k1_funct_1(C_40,k1_funct_1(A_39,'#skF_2'(A_39)))
      | ~ v1_funct_1(C_40)
      | ~ v1_relat_1(C_40)
      | v2_funct_1(A_39)
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(resolution,[status(thm)],[c_8,c_62])).

tff(c_2,plain,(
    ! [C_7,B_6,A_1] :
      ( C_7 = B_6
      | k1_funct_1(A_1,C_7) != k1_funct_1(A_1,B_6)
      | ~ r2_hidden(C_7,k1_relat_1(A_1))
      | ~ r2_hidden(B_6,k1_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_217,plain,(
    ! [C_46,A_47,C_48] :
      ( C_46 = '#skF_2'(A_47)
      | k1_funct_1(k5_relat_1(A_47,C_48),C_46) != k1_funct_1(C_48,k1_funct_1(A_47,'#skF_2'(A_47)))
      | ~ r2_hidden(C_46,k1_relat_1(k5_relat_1(A_47,C_48)))
      | ~ r2_hidden('#skF_2'(A_47),k1_relat_1(k5_relat_1(A_47,C_48)))
      | ~ v2_funct_1(k5_relat_1(A_47,C_48))
      | ~ v1_funct_1(k5_relat_1(A_47,C_48))
      | ~ v1_relat_1(k5_relat_1(A_47,C_48))
      | ~ v1_funct_1(C_48)
      | ~ v1_relat_1(C_48)
      | v2_funct_1(A_47)
      | ~ v1_funct_1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_2])).

tff(c_269,plain,(
    ! [C_50,A_51,C_52] :
      ( C_50 = '#skF_2'(A_51)
      | k1_funct_1(k5_relat_1(A_51,C_52),C_50) != k1_funct_1(C_52,k1_funct_1(A_51,'#skF_1'(A_51)))
      | ~ r2_hidden(C_50,k1_relat_1(k5_relat_1(A_51,C_52)))
      | ~ r2_hidden('#skF_2'(A_51),k1_relat_1(k5_relat_1(A_51,C_52)))
      | ~ v2_funct_1(k5_relat_1(A_51,C_52))
      | ~ v1_funct_1(k5_relat_1(A_51,C_52))
      | ~ v1_relat_1(k5_relat_1(A_51,C_52))
      | ~ v1_funct_1(C_52)
      | ~ v1_relat_1(C_52)
      | v2_funct_1(A_51)
      | ~ v1_funct_1(A_51)
      | ~ v1_relat_1(A_51)
      | v2_funct_1(A_51)
      | ~ v1_funct_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_217])).

tff(c_295,plain,(
    ! [A_53,C_54] :
      ( '#skF_2'(A_53) = '#skF_1'(A_53)
      | ~ r2_hidden('#skF_1'(A_53),k1_relat_1(k5_relat_1(A_53,C_54)))
      | ~ r2_hidden('#skF_2'(A_53),k1_relat_1(k5_relat_1(A_53,C_54)))
      | ~ v2_funct_1(k5_relat_1(A_53,C_54))
      | ~ v1_funct_1(k5_relat_1(A_53,C_54))
      | ~ v1_relat_1(k5_relat_1(A_53,C_54))
      | ~ v1_funct_1(C_54)
      | ~ v1_relat_1(C_54)
      | v2_funct_1(A_53)
      | ~ v1_funct_1(A_53)
      | ~ v1_relat_1(A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_269])).

tff(c_298,plain,
    ( '#skF_2'('#skF_4') = '#skF_1'('#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_4'),k1_relat_1(k5_relat_1('#skF_4','#skF_3')))
    | ~ r2_hidden('#skF_2'('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v2_funct_1(k5_relat_1('#skF_4','#skF_3'))
    | ~ v1_funct_1(k5_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1(k5_relat_1('#skF_4','#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_295])).

tff(c_300,plain,
    ( '#skF_2'('#skF_4') = '#skF_1'('#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_4'),k1_relat_1('#skF_4'))
    | ~ r2_hidden('#skF_2'('#skF_4'),k1_relat_1('#skF_4'))
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_34,c_32,c_95,c_147,c_26,c_61,c_298])).

tff(c_301,plain,
    ( ~ r2_hidden('#skF_1'('#skF_4'),k1_relat_1('#skF_4'))
    | ~ r2_hidden('#skF_2'('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_42,c_300])).

tff(c_302,plain,(
    ~ r2_hidden('#skF_2'('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_301])).

tff(c_305,plain,
    ( v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_302])).

tff(c_308,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_305])).

tff(c_310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_308])).

tff(c_311,plain,(
    ~ r2_hidden('#skF_1'('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_301])).

tff(c_315,plain,
    ( v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_311])).

tff(c_318,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_315])).

tff(c_320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_318])).

%------------------------------------------------------------------------------
