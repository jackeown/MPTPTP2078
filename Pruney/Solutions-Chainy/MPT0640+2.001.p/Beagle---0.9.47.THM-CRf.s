%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:38 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 696 expanded)
%              Number of leaves         :   22 ( 271 expanded)
%              Depth                    :   19
%              Number of atoms          :  185 (2610 expanded)
%              Number of equality atoms :   40 ( 319 expanded)
%              Maximal formula depth    :   11 (   4 average)
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

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v2_funct_1(k5_relat_1(B,A))
                & r1_tarski(k2_relat_1(B),k1_relat_1(A)) )
             => v2_funct_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(c_22,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_30,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_28,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_funct_1(A_6,'#skF_2'(A_6)) = k1_funct_1(A_6,'#skF_1'(A_6))
      | v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),k1_relat_1(A_6))
      | v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_36,plain,(
    ! [A_22] :
      ( '#skF_2'(A_22) != '#skF_1'(A_22)
      | v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

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
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_24,plain,(
    r1_tarski(k2_relat_1('#skF_4'),k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_55,plain,(
    ! [A_28,B_29] :
      ( k1_relat_1(k5_relat_1(A_28,B_29)) = k1_relat_1(A_28)
      | ~ r1_tarski(k2_relat_1(A_28),k1_relat_1(B_29))
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_58,plain,
    ( k1_relat_1(k5_relat_1('#skF_4','#skF_3')) = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_55])).

tff(c_61,plain,(
    k1_relat_1(k5_relat_1('#skF_4','#skF_3')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34,c_58])).

tff(c_97,plain,(
    ! [C_34,B_35,A_36] :
      ( k1_funct_1(k5_relat_1(C_34,B_35),A_36) = k1_funct_1(B_35,k1_funct_1(C_34,A_36))
      | ~ r2_hidden(A_36,k1_relat_1(k5_relat_1(C_34,B_35)))
      | ~ v1_funct_1(C_34)
      | ~ v1_relat_1(C_34)
      | ~ v1_funct_1(B_35)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_100,plain,(
    ! [A_36] :
      ( k1_funct_1(k5_relat_1('#skF_4','#skF_3'),A_36) = k1_funct_1('#skF_3',k1_funct_1('#skF_4',A_36))
      | ~ r2_hidden(A_36,k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_97])).

tff(c_113,plain,(
    ! [A_37] :
      ( k1_funct_1(k5_relat_1('#skF_4','#skF_3'),A_37) = k1_funct_1('#skF_3',k1_funct_1('#skF_4',A_37))
      | ~ r2_hidden(A_37,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_100])).

tff(c_117,plain,
    ( k1_funct_1(k5_relat_1('#skF_4','#skF_3'),'#skF_2'('#skF_4')) = k1_funct_1('#skF_3',k1_funct_1('#skF_4','#skF_2'('#skF_4')))
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_113])).

tff(c_124,plain,
    ( k1_funct_1(k5_relat_1('#skF_4','#skF_3'),'#skF_2'('#skF_4')) = k1_funct_1('#skF_3',k1_funct_1('#skF_4','#skF_2'('#skF_4')))
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_117])).

tff(c_125,plain,(
    k1_funct_1(k5_relat_1('#skF_4','#skF_3'),'#skF_2'('#skF_4')) = k1_funct_1('#skF_3',k1_funct_1('#skF_4','#skF_2'('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_124])).

tff(c_14,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_1'(A_6),k1_relat_1(A_6))
      | v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( v1_funct_1(k5_relat_1(A_13,B_14))
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k5_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3,B_5] :
      ( k1_relat_1(k5_relat_1(A_3,B_5)) = k1_relat_1(A_3)
      | ~ r1_tarski(k2_relat_1(A_3),k1_relat_1(B_5))
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_74,plain,(
    ! [A_3] :
      ( k1_relat_1(k5_relat_1(A_3,k5_relat_1('#skF_4','#skF_3'))) = k1_relat_1(A_3)
      | ~ r1_tarski(k2_relat_1(A_3),k1_relat_1('#skF_4'))
      | ~ v1_relat_1(k5_relat_1('#skF_4','#skF_3'))
      | ~ v1_relat_1(A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_4])).

tff(c_86,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_89,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2,c_86])).

tff(c_93,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34,c_89])).

tff(c_95,plain,(
    v1_relat_1(k5_relat_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_26,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_6,plain,(
    ! [C_12,B_11,A_6] :
      ( C_12 = B_11
      | k1_funct_1(A_6,C_12) != k1_funct_1(A_6,B_11)
      | ~ r2_hidden(C_12,k1_relat_1(A_6))
      | ~ r2_hidden(B_11,k1_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_134,plain,(
    ! [C_12] :
      ( C_12 = '#skF_2'('#skF_4')
      | k1_funct_1(k5_relat_1('#skF_4','#skF_3'),C_12) != k1_funct_1('#skF_3',k1_funct_1('#skF_4','#skF_2'('#skF_4')))
      | ~ r2_hidden(C_12,k1_relat_1(k5_relat_1('#skF_4','#skF_3')))
      | ~ r2_hidden('#skF_2'('#skF_4'),k1_relat_1(k5_relat_1('#skF_4','#skF_3')))
      | ~ v2_funct_1(k5_relat_1('#skF_4','#skF_3'))
      | ~ v1_funct_1(k5_relat_1('#skF_4','#skF_3'))
      | ~ v1_relat_1(k5_relat_1('#skF_4','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_6])).

tff(c_140,plain,(
    ! [C_12] :
      ( C_12 = '#skF_2'('#skF_4')
      | k1_funct_1(k5_relat_1('#skF_4','#skF_3'),C_12) != k1_funct_1('#skF_3',k1_funct_1('#skF_4','#skF_2'('#skF_4')))
      | ~ r2_hidden(C_12,k1_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),k1_relat_1('#skF_4'))
      | ~ v1_funct_1(k5_relat_1('#skF_4','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_26,c_61,c_61,c_134])).

tff(c_173,plain,(
    ~ v1_funct_1(k5_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_176,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_173])).

tff(c_180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_34,c_32,c_176])).

tff(c_182,plain,(
    v1_funct_1(k5_relat_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_121,plain,
    ( k1_funct_1(k5_relat_1('#skF_4','#skF_3'),'#skF_1'('#skF_4')) = k1_funct_1('#skF_3',k1_funct_1('#skF_4','#skF_1'('#skF_4')))
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_113])).

tff(c_128,plain,
    ( k1_funct_1(k5_relat_1('#skF_4','#skF_3'),'#skF_1'('#skF_4')) = k1_funct_1('#skF_3',k1_funct_1('#skF_4','#skF_1'('#skF_4')))
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_121])).

tff(c_129,plain,(
    k1_funct_1(k5_relat_1('#skF_4','#skF_3'),'#skF_1'('#skF_4')) = k1_funct_1('#skF_3',k1_funct_1('#skF_4','#skF_1'('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_128])).

tff(c_146,plain,(
    ! [C_12] :
      ( C_12 = '#skF_1'('#skF_4')
      | k1_funct_1(k5_relat_1('#skF_4','#skF_3'),C_12) != k1_funct_1('#skF_3',k1_funct_1('#skF_4','#skF_1'('#skF_4')))
      | ~ r2_hidden(C_12,k1_relat_1(k5_relat_1('#skF_4','#skF_3')))
      | ~ r2_hidden('#skF_1'('#skF_4'),k1_relat_1(k5_relat_1('#skF_4','#skF_3')))
      | ~ v2_funct_1(k5_relat_1('#skF_4','#skF_3'))
      | ~ v1_funct_1(k5_relat_1('#skF_4','#skF_3'))
      | ~ v1_relat_1(k5_relat_1('#skF_4','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_6])).

tff(c_152,plain,(
    ! [C_12] :
      ( C_12 = '#skF_1'('#skF_4')
      | k1_funct_1(k5_relat_1('#skF_4','#skF_3'),C_12) != k1_funct_1('#skF_3',k1_funct_1('#skF_4','#skF_1'('#skF_4')))
      | ~ r2_hidden(C_12,k1_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_1'('#skF_4'),k1_relat_1('#skF_4'))
      | ~ v1_funct_1(k5_relat_1('#skF_4','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_26,c_61,c_61,c_146])).

tff(c_184,plain,(
    ! [C_12] :
      ( C_12 = '#skF_1'('#skF_4')
      | k1_funct_1(k5_relat_1('#skF_4','#skF_3'),C_12) != k1_funct_1('#skF_3',k1_funct_1('#skF_4','#skF_1'('#skF_4')))
      | ~ r2_hidden(C_12,k1_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_1'('#skF_4'),k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_152])).

tff(c_185,plain,(
    ~ r2_hidden('#skF_1'('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_188,plain,
    ( v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_185])).

tff(c_191,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_188])).

tff(c_193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_191])).

tff(c_201,plain,(
    ! [C_40] :
      ( C_40 = '#skF_1'('#skF_4')
      | k1_funct_1(k5_relat_1('#skF_4','#skF_3'),C_40) != k1_funct_1('#skF_3',k1_funct_1('#skF_4','#skF_1'('#skF_4')))
      | ~ r2_hidden(C_40,k1_relat_1('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_208,plain,
    ( '#skF_2'('#skF_4') = '#skF_1'('#skF_4')
    | k1_funct_1('#skF_3',k1_funct_1('#skF_4','#skF_2'('#skF_4'))) != k1_funct_1('#skF_3',k1_funct_1('#skF_4','#skF_1'('#skF_4')))
    | ~ r2_hidden('#skF_2'('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_201])).

tff(c_218,plain,
    ( k1_funct_1('#skF_3',k1_funct_1('#skF_4','#skF_2'('#skF_4'))) != k1_funct_1('#skF_3',k1_funct_1('#skF_4','#skF_1'('#skF_4')))
    | ~ r2_hidden('#skF_2'('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_208])).

tff(c_221,plain,(
    ~ r2_hidden('#skF_2'('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_224,plain,
    ( v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_221])).

tff(c_227,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_224])).

tff(c_229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_227])).

tff(c_230,plain,(
    k1_funct_1('#skF_3',k1_funct_1('#skF_4','#skF_2'('#skF_4'))) != k1_funct_1('#skF_3',k1_funct_1('#skF_4','#skF_1'('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_257,plain,
    ( v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_230])).

tff(c_260,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_257])).

tff(c_262,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_260])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:21:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.30  
% 2.18/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.30  %$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 2.18/1.30  
% 2.18/1.30  %Foreground sorts:
% 2.18/1.30  
% 2.18/1.30  
% 2.18/1.30  %Background operators:
% 2.18/1.30  
% 2.18/1.30  
% 2.18/1.30  %Foreground operators:
% 2.18/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.18/1.30  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.18/1.30  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.18/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.18/1.30  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.18/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.18/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.18/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.18/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.18/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.18/1.30  
% 2.18/1.32  tff(f_96, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & r1_tarski(k2_relat_1(B), k1_relat_1(A))) => v2_funct_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_funct_1)).
% 2.18/1.32  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 2.18/1.32  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 2.18/1.32  tff(f_80, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 2.18/1.32  tff(f_67, axiom, (![A, B]: ((((v1_relat_1(A) & v1_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v1_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funct_1)).
% 2.18/1.32  tff(f_31, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.18/1.32  tff(c_22, plain, (~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.18/1.32  tff(c_30, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.18/1.32  tff(c_28, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.18/1.32  tff(c_10, plain, (![A_6]: (k1_funct_1(A_6, '#skF_2'(A_6))=k1_funct_1(A_6, '#skF_1'(A_6)) | v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.18/1.32  tff(c_12, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), k1_relat_1(A_6)) | v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.18/1.32  tff(c_36, plain, (![A_22]: ('#skF_2'(A_22)!='#skF_1'(A_22) | v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.18/1.32  tff(c_39, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_22])).
% 2.18/1.32  tff(c_42, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_39])).
% 2.18/1.32  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.18/1.32  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.18/1.32  tff(c_24, plain, (r1_tarski(k2_relat_1('#skF_4'), k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.18/1.32  tff(c_55, plain, (![A_28, B_29]: (k1_relat_1(k5_relat_1(A_28, B_29))=k1_relat_1(A_28) | ~r1_tarski(k2_relat_1(A_28), k1_relat_1(B_29)) | ~v1_relat_1(B_29) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.18/1.32  tff(c_58, plain, (k1_relat_1(k5_relat_1('#skF_4', '#skF_3'))=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_55])).
% 2.18/1.32  tff(c_61, plain, (k1_relat_1(k5_relat_1('#skF_4', '#skF_3'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_34, c_58])).
% 2.18/1.32  tff(c_97, plain, (![C_34, B_35, A_36]: (k1_funct_1(k5_relat_1(C_34, B_35), A_36)=k1_funct_1(B_35, k1_funct_1(C_34, A_36)) | ~r2_hidden(A_36, k1_relat_1(k5_relat_1(C_34, B_35))) | ~v1_funct_1(C_34) | ~v1_relat_1(C_34) | ~v1_funct_1(B_35) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.18/1.32  tff(c_100, plain, (![A_36]: (k1_funct_1(k5_relat_1('#skF_4', '#skF_3'), A_36)=k1_funct_1('#skF_3', k1_funct_1('#skF_4', A_36)) | ~r2_hidden(A_36, k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_97])).
% 2.18/1.32  tff(c_113, plain, (![A_37]: (k1_funct_1(k5_relat_1('#skF_4', '#skF_3'), A_37)=k1_funct_1('#skF_3', k1_funct_1('#skF_4', A_37)) | ~r2_hidden(A_37, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_100])).
% 2.18/1.32  tff(c_117, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_3'), '#skF_2'('#skF_4'))=k1_funct_1('#skF_3', k1_funct_1('#skF_4', '#skF_2'('#skF_4'))) | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_113])).
% 2.18/1.32  tff(c_124, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_3'), '#skF_2'('#skF_4'))=k1_funct_1('#skF_3', k1_funct_1('#skF_4', '#skF_2'('#skF_4'))) | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_117])).
% 2.18/1.32  tff(c_125, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_3'), '#skF_2'('#skF_4'))=k1_funct_1('#skF_3', k1_funct_1('#skF_4', '#skF_2'('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_22, c_124])).
% 2.18/1.32  tff(c_14, plain, (![A_6]: (r2_hidden('#skF_1'(A_6), k1_relat_1(A_6)) | v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.18/1.32  tff(c_16, plain, (![A_13, B_14]: (v1_funct_1(k5_relat_1(A_13, B_14)) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.18/1.32  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k5_relat_1(A_1, B_2)) | ~v1_relat_1(B_2) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.18/1.32  tff(c_4, plain, (![A_3, B_5]: (k1_relat_1(k5_relat_1(A_3, B_5))=k1_relat_1(A_3) | ~r1_tarski(k2_relat_1(A_3), k1_relat_1(B_5)) | ~v1_relat_1(B_5) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.18/1.32  tff(c_74, plain, (![A_3]: (k1_relat_1(k5_relat_1(A_3, k5_relat_1('#skF_4', '#skF_3')))=k1_relat_1(A_3) | ~r1_tarski(k2_relat_1(A_3), k1_relat_1('#skF_4')) | ~v1_relat_1(k5_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1(A_3))), inference(superposition, [status(thm), theory('equality')], [c_61, c_4])).
% 2.18/1.32  tff(c_86, plain, (~v1_relat_1(k5_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_74])).
% 2.18/1.32  tff(c_89, plain, (~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2, c_86])).
% 2.18/1.32  tff(c_93, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_34, c_89])).
% 2.18/1.32  tff(c_95, plain, (v1_relat_1(k5_relat_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_74])).
% 2.18/1.32  tff(c_26, plain, (v2_funct_1(k5_relat_1('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.18/1.32  tff(c_6, plain, (![C_12, B_11, A_6]: (C_12=B_11 | k1_funct_1(A_6, C_12)!=k1_funct_1(A_6, B_11) | ~r2_hidden(C_12, k1_relat_1(A_6)) | ~r2_hidden(B_11, k1_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.18/1.32  tff(c_134, plain, (![C_12]: (C_12='#skF_2'('#skF_4') | k1_funct_1(k5_relat_1('#skF_4', '#skF_3'), C_12)!=k1_funct_1('#skF_3', k1_funct_1('#skF_4', '#skF_2'('#skF_4'))) | ~r2_hidden(C_12, k1_relat_1(k5_relat_1('#skF_4', '#skF_3'))) | ~r2_hidden('#skF_2'('#skF_4'), k1_relat_1(k5_relat_1('#skF_4', '#skF_3'))) | ~v2_funct_1(k5_relat_1('#skF_4', '#skF_3')) | ~v1_funct_1(k5_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1(k5_relat_1('#skF_4', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_125, c_6])).
% 2.18/1.32  tff(c_140, plain, (![C_12]: (C_12='#skF_2'('#skF_4') | k1_funct_1(k5_relat_1('#skF_4', '#skF_3'), C_12)!=k1_funct_1('#skF_3', k1_funct_1('#skF_4', '#skF_2'('#skF_4'))) | ~r2_hidden(C_12, k1_relat_1('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), k1_relat_1('#skF_4')) | ~v1_funct_1(k5_relat_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_26, c_61, c_61, c_134])).
% 2.18/1.32  tff(c_173, plain, (~v1_funct_1(k5_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_140])).
% 2.18/1.32  tff(c_176, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_173])).
% 2.18/1.32  tff(c_180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_34, c_32, c_176])).
% 2.18/1.32  tff(c_182, plain, (v1_funct_1(k5_relat_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_140])).
% 2.18/1.32  tff(c_121, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_3'), '#skF_1'('#skF_4'))=k1_funct_1('#skF_3', k1_funct_1('#skF_4', '#skF_1'('#skF_4'))) | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_113])).
% 2.18/1.32  tff(c_128, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_3'), '#skF_1'('#skF_4'))=k1_funct_1('#skF_3', k1_funct_1('#skF_4', '#skF_1'('#skF_4'))) | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_121])).
% 2.18/1.32  tff(c_129, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_3'), '#skF_1'('#skF_4'))=k1_funct_1('#skF_3', k1_funct_1('#skF_4', '#skF_1'('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_22, c_128])).
% 2.18/1.32  tff(c_146, plain, (![C_12]: (C_12='#skF_1'('#skF_4') | k1_funct_1(k5_relat_1('#skF_4', '#skF_3'), C_12)!=k1_funct_1('#skF_3', k1_funct_1('#skF_4', '#skF_1'('#skF_4'))) | ~r2_hidden(C_12, k1_relat_1(k5_relat_1('#skF_4', '#skF_3'))) | ~r2_hidden('#skF_1'('#skF_4'), k1_relat_1(k5_relat_1('#skF_4', '#skF_3'))) | ~v2_funct_1(k5_relat_1('#skF_4', '#skF_3')) | ~v1_funct_1(k5_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1(k5_relat_1('#skF_4', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_129, c_6])).
% 2.18/1.32  tff(c_152, plain, (![C_12]: (C_12='#skF_1'('#skF_4') | k1_funct_1(k5_relat_1('#skF_4', '#skF_3'), C_12)!=k1_funct_1('#skF_3', k1_funct_1('#skF_4', '#skF_1'('#skF_4'))) | ~r2_hidden(C_12, k1_relat_1('#skF_4')) | ~r2_hidden('#skF_1'('#skF_4'), k1_relat_1('#skF_4')) | ~v1_funct_1(k5_relat_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_26, c_61, c_61, c_146])).
% 2.18/1.32  tff(c_184, plain, (![C_12]: (C_12='#skF_1'('#skF_4') | k1_funct_1(k5_relat_1('#skF_4', '#skF_3'), C_12)!=k1_funct_1('#skF_3', k1_funct_1('#skF_4', '#skF_1'('#skF_4'))) | ~r2_hidden(C_12, k1_relat_1('#skF_4')) | ~r2_hidden('#skF_1'('#skF_4'), k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_152])).
% 2.18/1.32  tff(c_185, plain, (~r2_hidden('#skF_1'('#skF_4'), k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_184])).
% 2.18/1.32  tff(c_188, plain, (v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_185])).
% 2.18/1.32  tff(c_191, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_188])).
% 2.18/1.32  tff(c_193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_191])).
% 2.18/1.32  tff(c_201, plain, (![C_40]: (C_40='#skF_1'('#skF_4') | k1_funct_1(k5_relat_1('#skF_4', '#skF_3'), C_40)!=k1_funct_1('#skF_3', k1_funct_1('#skF_4', '#skF_1'('#skF_4'))) | ~r2_hidden(C_40, k1_relat_1('#skF_4')))), inference(splitRight, [status(thm)], [c_184])).
% 2.18/1.32  tff(c_208, plain, ('#skF_2'('#skF_4')='#skF_1'('#skF_4') | k1_funct_1('#skF_3', k1_funct_1('#skF_4', '#skF_2'('#skF_4')))!=k1_funct_1('#skF_3', k1_funct_1('#skF_4', '#skF_1'('#skF_4'))) | ~r2_hidden('#skF_2'('#skF_4'), k1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_125, c_201])).
% 2.18/1.32  tff(c_218, plain, (k1_funct_1('#skF_3', k1_funct_1('#skF_4', '#skF_2'('#skF_4')))!=k1_funct_1('#skF_3', k1_funct_1('#skF_4', '#skF_1'('#skF_4'))) | ~r2_hidden('#skF_2'('#skF_4'), k1_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_42, c_208])).
% 2.18/1.32  tff(c_221, plain, (~r2_hidden('#skF_2'('#skF_4'), k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_218])).
% 2.18/1.32  tff(c_224, plain, (v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_221])).
% 2.18/1.32  tff(c_227, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_224])).
% 2.18/1.32  tff(c_229, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_227])).
% 2.18/1.32  tff(c_230, plain, (k1_funct_1('#skF_3', k1_funct_1('#skF_4', '#skF_2'('#skF_4')))!=k1_funct_1('#skF_3', k1_funct_1('#skF_4', '#skF_1'('#skF_4')))), inference(splitRight, [status(thm)], [c_218])).
% 2.18/1.32  tff(c_257, plain, (v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10, c_230])).
% 2.18/1.32  tff(c_260, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_257])).
% 2.18/1.32  tff(c_262, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_260])).
% 2.18/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.32  
% 2.18/1.32  Inference rules
% 2.18/1.32  ----------------------
% 2.18/1.32  #Ref     : 1
% 2.18/1.32  #Sup     : 46
% 2.18/1.32  #Fact    : 0
% 2.18/1.32  #Define  : 0
% 2.18/1.32  #Split   : 4
% 2.18/1.32  #Chain   : 0
% 2.18/1.32  #Close   : 0
% 2.18/1.32  
% 2.18/1.32  Ordering : KBO
% 2.18/1.32  
% 2.18/1.32  Simplification rules
% 2.18/1.32  ----------------------
% 2.18/1.32  #Subsume      : 1
% 2.18/1.32  #Demod        : 63
% 2.18/1.32  #Tautology    : 27
% 2.18/1.32  #SimpNegUnit  : 6
% 2.18/1.32  #BackRed      : 0
% 2.18/1.32  
% 2.18/1.32  #Partial instantiations: 0
% 2.18/1.32  #Strategies tried      : 1
% 2.18/1.32  
% 2.18/1.32  Timing (in seconds)
% 2.18/1.32  ----------------------
% 2.18/1.32  Preprocessing        : 0.30
% 2.18/1.32  Parsing              : 0.16
% 2.18/1.32  CNF conversion       : 0.02
% 2.18/1.32  Main loop            : 0.25
% 2.18/1.32  Inferencing          : 0.09
% 2.18/1.32  Reduction            : 0.08
% 2.18/1.32  Demodulation         : 0.05
% 2.18/1.32  BG Simplification    : 0.02
% 2.18/1.32  Subsumption          : 0.05
% 2.18/1.32  Abstraction          : 0.02
% 2.18/1.32  MUC search           : 0.00
% 2.18/1.32  Cooper               : 0.00
% 2.18/1.32  Total                : 0.58
% 2.18/1.32  Index Insertion      : 0.00
% 2.18/1.32  Index Deletion       : 0.00
% 2.18/1.32  Index Matching       : 0.00
% 2.18/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
