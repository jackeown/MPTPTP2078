%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0800+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:52 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   44 (  58 expanded)
%              Number of leaves         :   17 (  28 expanded)
%              Depth                    :   15
%              Number of atoms          :  168 ( 246 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_wellord1 > r4_wellord1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => ( ( r4_wellord1(A,B)
                    & r4_wellord1(B,C) )
                 => r4_wellord1(A,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_wellord1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
          <=> ? [C] :
                ( v1_relat_1(C)
                & v1_funct_1(C)
                & r3_wellord1(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_wellord1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ! [D] :
                  ( ( v1_relat_1(D)
                    & v1_funct_1(D) )
                 => ! [E] :
                      ( ( v1_relat_1(E)
                        & v1_funct_1(E) )
                     => ( ( r3_wellord1(A,B,D)
                          & r3_wellord1(B,C,E) )
                       => r3_wellord1(A,C,k5_relat_1(D,E)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_wellord1)).

tff(c_18,plain,(
    ~ r4_wellord1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_22,plain,(
    r4_wellord1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_26,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_24,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_20,plain,(
    r4_wellord1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_6,plain,(
    ! [A_1,B_7] :
      ( v1_funct_1('#skF_1'(A_1,B_7))
      | ~ r4_wellord1(A_1,B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_1,B_7] :
      ( v1_relat_1('#skF_1'(A_1,B_7))
      | ~ r4_wellord1(A_1,B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4,plain,(
    ! [A_1,B_7] :
      ( r3_wellord1(A_1,B_7,'#skF_1'(A_1,B_7))
      | ~ r4_wellord1(A_1,B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12,plain,(
    ! [A_13,B_14] :
      ( v1_funct_1(k5_relat_1(A_13,B_14))
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    ! [A_11,B_12] :
      ( v1_relat_1(k5_relat_1(A_11,B_12))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_39,plain,(
    ! [D_64,A_67,E_63,C_66,B_65] :
      ( r3_wellord1(A_67,C_66,k5_relat_1(D_64,E_63))
      | ~ r3_wellord1(B_65,C_66,E_63)
      | ~ r3_wellord1(A_67,B_65,D_64)
      | ~ v1_funct_1(E_63)
      | ~ v1_relat_1(E_63)
      | ~ v1_funct_1(D_64)
      | ~ v1_relat_1(D_64)
      | ~ v1_relat_1(C_66)
      | ~ v1_relat_1(B_65)
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_43,plain,(
    ! [A_68,B_69,D_70,A_71] :
      ( r3_wellord1(A_68,B_69,k5_relat_1(D_70,'#skF_1'(A_71,B_69)))
      | ~ r3_wellord1(A_68,A_71,D_70)
      | ~ v1_funct_1('#skF_1'(A_71,B_69))
      | ~ v1_relat_1('#skF_1'(A_71,B_69))
      | ~ v1_funct_1(D_70)
      | ~ v1_relat_1(D_70)
      | ~ v1_relat_1(A_68)
      | ~ r4_wellord1(A_71,B_69)
      | ~ v1_relat_1(B_69)
      | ~ v1_relat_1(A_71) ) ),
    inference(resolution,[status(thm)],[c_4,c_39])).

tff(c_2,plain,(
    ! [A_1,B_7,C_10] :
      ( r4_wellord1(A_1,B_7)
      | ~ r3_wellord1(A_1,B_7,C_10)
      | ~ v1_funct_1(C_10)
      | ~ v1_relat_1(C_10)
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_51,plain,(
    ! [A_72,B_73,D_74,A_75] :
      ( r4_wellord1(A_72,B_73)
      | ~ v1_funct_1(k5_relat_1(D_74,'#skF_1'(A_75,B_73)))
      | ~ v1_relat_1(k5_relat_1(D_74,'#skF_1'(A_75,B_73)))
      | ~ r3_wellord1(A_72,A_75,D_74)
      | ~ v1_funct_1('#skF_1'(A_75,B_73))
      | ~ v1_relat_1('#skF_1'(A_75,B_73))
      | ~ v1_funct_1(D_74)
      | ~ v1_relat_1(D_74)
      | ~ v1_relat_1(A_72)
      | ~ r4_wellord1(A_75,B_73)
      | ~ v1_relat_1(B_73)
      | ~ v1_relat_1(A_75) ) ),
    inference(resolution,[status(thm)],[c_43,c_2])).

tff(c_63,plain,(
    ! [A_82,B_83,A_84,A_85] :
      ( r4_wellord1(A_82,B_83)
      | ~ v1_funct_1(k5_relat_1(A_84,'#skF_1'(A_85,B_83)))
      | ~ r3_wellord1(A_82,A_85,A_84)
      | ~ v1_funct_1('#skF_1'(A_85,B_83))
      | ~ v1_funct_1(A_84)
      | ~ v1_relat_1(A_82)
      | ~ r4_wellord1(A_85,B_83)
      | ~ v1_relat_1(B_83)
      | ~ v1_relat_1(A_85)
      | ~ v1_relat_1('#skF_1'(A_85,B_83))
      | ~ v1_relat_1(A_84) ) ),
    inference(resolution,[status(thm)],[c_10,c_51])).

tff(c_68,plain,(
    ! [A_86,B_87,A_88,A_89] :
      ( r4_wellord1(A_86,B_87)
      | ~ r3_wellord1(A_86,A_88,A_89)
      | ~ v1_relat_1(A_86)
      | ~ r4_wellord1(A_88,B_87)
      | ~ v1_relat_1(B_87)
      | ~ v1_relat_1(A_88)
      | ~ v1_funct_1('#skF_1'(A_88,B_87))
      | ~ v1_relat_1('#skF_1'(A_88,B_87))
      | ~ v1_funct_1(A_89)
      | ~ v1_relat_1(A_89) ) ),
    inference(resolution,[status(thm)],[c_12,c_63])).

tff(c_75,plain,(
    ! [A_90,B_91,B_92] :
      ( r4_wellord1(A_90,B_91)
      | ~ r4_wellord1(B_92,B_91)
      | ~ v1_relat_1(B_91)
      | ~ v1_funct_1('#skF_1'(B_92,B_91))
      | ~ v1_relat_1('#skF_1'(B_92,B_91))
      | ~ v1_funct_1('#skF_1'(A_90,B_92))
      | ~ v1_relat_1('#skF_1'(A_90,B_92))
      | ~ r4_wellord1(A_90,B_92)
      | ~ v1_relat_1(B_92)
      | ~ v1_relat_1(A_90) ) ),
    inference(resolution,[status(thm)],[c_4,c_68])).

tff(c_79,plain,(
    ! [A_93,B_94,A_95] :
      ( r4_wellord1(A_93,B_94)
      | ~ v1_funct_1('#skF_1'(A_95,B_94))
      | ~ v1_funct_1('#skF_1'(A_93,A_95))
      | ~ v1_relat_1('#skF_1'(A_93,A_95))
      | ~ r4_wellord1(A_93,A_95)
      | ~ v1_relat_1(A_93)
      | ~ r4_wellord1(A_95,B_94)
      | ~ v1_relat_1(B_94)
      | ~ v1_relat_1(A_95) ) ),
    inference(resolution,[status(thm)],[c_8,c_75])).

tff(c_83,plain,(
    ! [A_96,B_97,A_98] :
      ( r4_wellord1(A_96,B_97)
      | ~ v1_funct_1('#skF_1'(A_96,A_98))
      | ~ v1_relat_1('#skF_1'(A_96,A_98))
      | ~ r4_wellord1(A_96,A_98)
      | ~ v1_relat_1(A_96)
      | ~ r4_wellord1(A_98,B_97)
      | ~ v1_relat_1(B_97)
      | ~ v1_relat_1(A_98) ) ),
    inference(resolution,[status(thm)],[c_6,c_79])).

tff(c_87,plain,(
    ! [A_99,B_100,B_101] :
      ( r4_wellord1(A_99,B_100)
      | ~ v1_funct_1('#skF_1'(A_99,B_101))
      | ~ r4_wellord1(B_101,B_100)
      | ~ v1_relat_1(B_100)
      | ~ r4_wellord1(A_99,B_101)
      | ~ v1_relat_1(B_101)
      | ~ v1_relat_1(A_99) ) ),
    inference(resolution,[status(thm)],[c_8,c_83])).

tff(c_91,plain,(
    ! [A_102,B_103,B_104] :
      ( r4_wellord1(A_102,B_103)
      | ~ r4_wellord1(B_104,B_103)
      | ~ v1_relat_1(B_103)
      | ~ r4_wellord1(A_102,B_104)
      | ~ v1_relat_1(B_104)
      | ~ v1_relat_1(A_102) ) ),
    inference(resolution,[status(thm)],[c_6,c_87])).

tff(c_93,plain,(
    ! [A_102] :
      ( r4_wellord1(A_102,'#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ r4_wellord1(A_102,'#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(A_102) ) ),
    inference(resolution,[status(thm)],[c_20,c_91])).

tff(c_102,plain,(
    ! [A_105] :
      ( r4_wellord1(A_105,'#skF_4')
      | ~ r4_wellord1(A_105,'#skF_3')
      | ~ v1_relat_1(A_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_93])).

tff(c_105,plain,
    ( r4_wellord1('#skF_2','#skF_4')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_102])).

tff(c_108,plain,(
    r4_wellord1('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_105])).

tff(c_110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_108])).

%------------------------------------------------------------------------------
