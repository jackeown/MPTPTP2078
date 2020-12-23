%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:38 EST 2020

% Result     : Theorem 13.81s
% Output     : CNFRefutation 13.81s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 135 expanded)
%              Number of leaves         :   20 (  57 expanded)
%              Depth                    :   19
%              Number of atoms          :  325 ( 665 expanded)
%              Number of equality atoms :   29 (  64 expanded)
%              Maximal formula depth    :   28 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_1 > #skF_3 > #skF_4

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

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v2_funct_1(A)
                & v2_funct_1(B) )
             => v2_funct_1(k5_relat_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_funct_1)).

tff(f_58,axiom,(
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

tff(f_46,axiom,(
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

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
          <=> ( r2_hidden(A,k1_relat_1(C))
              & r2_hidden(k1_funct_1(C,A),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_34,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_32,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( v1_funct_1(k5_relat_1(A_10,B_11))
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k5_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    ! [A_23] :
      ( '#skF_2'(A_23) != '#skF_1'(A_23)
      | v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_44,plain,
    ( '#skF_2'(k5_relat_1('#skF_3','#skF_4')) != '#skF_1'(k5_relat_1('#skF_3','#skF_4'))
    | ~ v1_funct_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ v1_relat_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_26])).

tff(c_45,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_48,plain,
    ( ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_45])).

tff(c_52,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_48])).

tff(c_53,plain,
    ( ~ v1_funct_1(k5_relat_1('#skF_3','#skF_4'))
    | '#skF_2'(k5_relat_1('#skF_3','#skF_4')) != '#skF_1'(k5_relat_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_67,plain,(
    '#skF_2'(k5_relat_1('#skF_3','#skF_4')) != '#skF_1'(k5_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_53])).

tff(c_54,plain,(
    v1_relat_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_28,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_30,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_12,plain,(
    ! [A_3] :
      ( r2_hidden('#skF_1'(A_3),k1_relat_1(A_3))
      | v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_68,plain,(
    ! [A_29,C_30,B_31] :
      ( r2_hidden(A_29,k1_relat_1(C_30))
      | ~ r2_hidden(A_29,k1_relat_1(k5_relat_1(C_30,B_31)))
      | ~ v1_funct_1(C_30)
      | ~ v1_relat_1(C_30)
      | ~ v1_funct_1(B_31)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_78,plain,(
    ! [C_30,B_31] :
      ( r2_hidden('#skF_1'(k5_relat_1(C_30,B_31)),k1_relat_1(C_30))
      | ~ v1_funct_1(C_30)
      | ~ v1_relat_1(C_30)
      | ~ v1_funct_1(B_31)
      | ~ v1_relat_1(B_31)
      | v2_funct_1(k5_relat_1(C_30,B_31))
      | ~ v1_funct_1(k5_relat_1(C_30,B_31))
      | ~ v1_relat_1(k5_relat_1(C_30,B_31)) ) ),
    inference(resolution,[status(thm)],[c_12,c_68])).

tff(c_10,plain,(
    ! [A_3] :
      ( r2_hidden('#skF_2'(A_3),k1_relat_1(A_3))
      | v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_77,plain,(
    ! [C_30,B_31] :
      ( r2_hidden('#skF_2'(k5_relat_1(C_30,B_31)),k1_relat_1(C_30))
      | ~ v1_funct_1(C_30)
      | ~ v1_relat_1(C_30)
      | ~ v1_funct_1(B_31)
      | ~ v1_relat_1(B_31)
      | v2_funct_1(k5_relat_1(C_30,B_31))
      | ~ v1_funct_1(k5_relat_1(C_30,B_31))
      | ~ v1_relat_1(k5_relat_1(C_30,B_31)) ) ),
    inference(resolution,[status(thm)],[c_10,c_68])).

tff(c_20,plain,(
    ! [C_15,A_12,B_13] :
      ( r2_hidden(k1_funct_1(C_15,A_12),k1_relat_1(B_13))
      | ~ r2_hidden(A_12,k1_relat_1(k5_relat_1(C_15,B_13)))
      | ~ v1_funct_1(C_15)
      | ~ v1_relat_1(C_15)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_105,plain,(
    ! [C_41,B_42,A_43] :
      ( k1_funct_1(k5_relat_1(C_41,B_42),A_43) = k1_funct_1(B_42,k1_funct_1(C_41,A_43))
      | ~ r2_hidden(A_43,k1_relat_1(k5_relat_1(C_41,B_42)))
      | ~ v1_funct_1(C_41)
      | ~ v1_relat_1(C_41)
      | ~ v1_funct_1(B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_244,plain,(
    ! [C_64,B_65] :
      ( k1_funct_1(k5_relat_1(C_64,B_65),'#skF_2'(k5_relat_1(C_64,B_65))) = k1_funct_1(B_65,k1_funct_1(C_64,'#skF_2'(k5_relat_1(C_64,B_65))))
      | ~ v1_funct_1(C_64)
      | ~ v1_relat_1(C_64)
      | ~ v1_funct_1(B_65)
      | ~ v1_relat_1(B_65)
      | v2_funct_1(k5_relat_1(C_64,B_65))
      | ~ v1_funct_1(k5_relat_1(C_64,B_65))
      | ~ v1_relat_1(k5_relat_1(C_64,B_65)) ) ),
    inference(resolution,[status(thm)],[c_10,c_105])).

tff(c_8,plain,(
    ! [A_3] :
      ( k1_funct_1(A_3,'#skF_2'(A_3)) = k1_funct_1(A_3,'#skF_1'(A_3))
      | v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_360,plain,(
    ! [C_85,B_86] :
      ( k1_funct_1(k5_relat_1(C_85,B_86),'#skF_1'(k5_relat_1(C_85,B_86))) = k1_funct_1(B_86,k1_funct_1(C_85,'#skF_2'(k5_relat_1(C_85,B_86))))
      | v2_funct_1(k5_relat_1(C_85,B_86))
      | ~ v1_funct_1(k5_relat_1(C_85,B_86))
      | ~ v1_relat_1(k5_relat_1(C_85,B_86))
      | ~ v1_funct_1(C_85)
      | ~ v1_relat_1(C_85)
      | ~ v1_funct_1(B_86)
      | ~ v1_relat_1(B_86)
      | v2_funct_1(k5_relat_1(C_85,B_86))
      | ~ v1_funct_1(k5_relat_1(C_85,B_86))
      | ~ v1_relat_1(k5_relat_1(C_85,B_86)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_8])).

tff(c_120,plain,(
    ! [C_41,B_42] :
      ( k1_funct_1(k5_relat_1(C_41,B_42),'#skF_1'(k5_relat_1(C_41,B_42))) = k1_funct_1(B_42,k1_funct_1(C_41,'#skF_1'(k5_relat_1(C_41,B_42))))
      | ~ v1_funct_1(C_41)
      | ~ v1_relat_1(C_41)
      | ~ v1_funct_1(B_42)
      | ~ v1_relat_1(B_42)
      | v2_funct_1(k5_relat_1(C_41,B_42))
      | ~ v1_funct_1(k5_relat_1(C_41,B_42))
      | ~ v1_relat_1(k5_relat_1(C_41,B_42)) ) ),
    inference(resolution,[status(thm)],[c_12,c_105])).

tff(c_1310,plain,(
    ! [B_218,C_219] :
      ( k1_funct_1(B_218,k1_funct_1(C_219,'#skF_2'(k5_relat_1(C_219,B_218)))) = k1_funct_1(B_218,k1_funct_1(C_219,'#skF_1'(k5_relat_1(C_219,B_218))))
      | ~ v1_funct_1(C_219)
      | ~ v1_relat_1(C_219)
      | ~ v1_funct_1(B_218)
      | ~ v1_relat_1(B_218)
      | v2_funct_1(k5_relat_1(C_219,B_218))
      | ~ v1_funct_1(k5_relat_1(C_219,B_218))
      | ~ v1_relat_1(k5_relat_1(C_219,B_218))
      | v2_funct_1(k5_relat_1(C_219,B_218))
      | ~ v1_funct_1(k5_relat_1(C_219,B_218))
      | ~ v1_relat_1(k5_relat_1(C_219,B_218))
      | ~ v1_funct_1(C_219)
      | ~ v1_relat_1(C_219)
      | ~ v1_funct_1(B_218)
      | ~ v1_relat_1(B_218)
      | v2_funct_1(k5_relat_1(C_219,B_218))
      | ~ v1_funct_1(k5_relat_1(C_219,B_218))
      | ~ v1_relat_1(k5_relat_1(C_219,B_218)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_120])).

tff(c_4,plain,(
    ! [C_9,B_8,A_3] :
      ( C_9 = B_8
      | k1_funct_1(A_3,C_9) != k1_funct_1(A_3,B_8)
      | ~ r2_hidden(C_9,k1_relat_1(A_3))
      | ~ r2_hidden(B_8,k1_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1333,plain,(
    ! [C_219,B_218,C_9] :
      ( k1_funct_1(C_219,'#skF_2'(k5_relat_1(C_219,B_218))) = C_9
      | k1_funct_1(B_218,k1_funct_1(C_219,'#skF_1'(k5_relat_1(C_219,B_218)))) != k1_funct_1(B_218,C_9)
      | ~ r2_hidden(C_9,k1_relat_1(B_218))
      | ~ r2_hidden(k1_funct_1(C_219,'#skF_2'(k5_relat_1(C_219,B_218))),k1_relat_1(B_218))
      | ~ v2_funct_1(B_218)
      | ~ v1_funct_1(B_218)
      | ~ v1_relat_1(B_218)
      | ~ v1_funct_1(C_219)
      | ~ v1_relat_1(C_219)
      | ~ v1_funct_1(B_218)
      | ~ v1_relat_1(B_218)
      | v2_funct_1(k5_relat_1(C_219,B_218))
      | ~ v1_funct_1(k5_relat_1(C_219,B_218))
      | ~ v1_relat_1(k5_relat_1(C_219,B_218))
      | v2_funct_1(k5_relat_1(C_219,B_218))
      | ~ v1_funct_1(k5_relat_1(C_219,B_218))
      | ~ v1_relat_1(k5_relat_1(C_219,B_218))
      | ~ v1_funct_1(C_219)
      | ~ v1_relat_1(C_219)
      | ~ v1_funct_1(B_218)
      | ~ v1_relat_1(B_218)
      | v2_funct_1(k5_relat_1(C_219,B_218))
      | ~ v1_funct_1(k5_relat_1(C_219,B_218))
      | ~ v1_relat_1(k5_relat_1(C_219,B_218)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1310,c_4])).

tff(c_4061,plain,(
    ! [C_625,B_626] :
      ( k1_funct_1(C_625,'#skF_2'(k5_relat_1(C_625,B_626))) = k1_funct_1(C_625,'#skF_1'(k5_relat_1(C_625,B_626)))
      | ~ r2_hidden(k1_funct_1(C_625,'#skF_1'(k5_relat_1(C_625,B_626))),k1_relat_1(B_626))
      | ~ r2_hidden(k1_funct_1(C_625,'#skF_2'(k5_relat_1(C_625,B_626))),k1_relat_1(B_626))
      | ~ v2_funct_1(B_626)
      | ~ v1_funct_1(B_626)
      | ~ v1_relat_1(B_626)
      | ~ v1_funct_1(C_625)
      | ~ v1_relat_1(C_625)
      | ~ v1_funct_1(B_626)
      | ~ v1_relat_1(B_626)
      | v2_funct_1(k5_relat_1(C_625,B_626))
      | ~ v1_funct_1(k5_relat_1(C_625,B_626))
      | ~ v1_relat_1(k5_relat_1(C_625,B_626))
      | v2_funct_1(k5_relat_1(C_625,B_626))
      | ~ v1_funct_1(k5_relat_1(C_625,B_626))
      | ~ v1_relat_1(k5_relat_1(C_625,B_626))
      | ~ v1_funct_1(C_625)
      | ~ v1_relat_1(C_625)
      | ~ v1_funct_1(B_626)
      | ~ v1_relat_1(B_626)
      | v2_funct_1(k5_relat_1(C_625,B_626))
      | ~ v1_funct_1(k5_relat_1(C_625,B_626))
      | ~ v1_relat_1(k5_relat_1(C_625,B_626)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1333])).

tff(c_4075,plain,(
    ! [C_627,B_628] :
      ( k1_funct_1(C_627,'#skF_2'(k5_relat_1(C_627,B_628))) = k1_funct_1(C_627,'#skF_1'(k5_relat_1(C_627,B_628)))
      | ~ r2_hidden(k1_funct_1(C_627,'#skF_1'(k5_relat_1(C_627,B_628))),k1_relat_1(B_628))
      | ~ v2_funct_1(B_628)
      | v2_funct_1(k5_relat_1(C_627,B_628))
      | ~ v1_funct_1(k5_relat_1(C_627,B_628))
      | ~ v1_relat_1(k5_relat_1(C_627,B_628))
      | ~ r2_hidden('#skF_2'(k5_relat_1(C_627,B_628)),k1_relat_1(k5_relat_1(C_627,B_628)))
      | ~ v1_funct_1(C_627)
      | ~ v1_relat_1(C_627)
      | ~ v1_funct_1(B_628)
      | ~ v1_relat_1(B_628) ) ),
    inference(resolution,[status(thm)],[c_20,c_4061])).

tff(c_4089,plain,(
    ! [C_629,B_630] :
      ( k1_funct_1(C_629,'#skF_2'(k5_relat_1(C_629,B_630))) = k1_funct_1(C_629,'#skF_1'(k5_relat_1(C_629,B_630)))
      | ~ v2_funct_1(B_630)
      | v2_funct_1(k5_relat_1(C_629,B_630))
      | ~ v1_funct_1(k5_relat_1(C_629,B_630))
      | ~ v1_relat_1(k5_relat_1(C_629,B_630))
      | ~ r2_hidden('#skF_2'(k5_relat_1(C_629,B_630)),k1_relat_1(k5_relat_1(C_629,B_630)))
      | ~ r2_hidden('#skF_1'(k5_relat_1(C_629,B_630)),k1_relat_1(k5_relat_1(C_629,B_630)))
      | ~ v1_funct_1(C_629)
      | ~ v1_relat_1(C_629)
      | ~ v1_funct_1(B_630)
      | ~ v1_relat_1(B_630) ) ),
    inference(resolution,[status(thm)],[c_20,c_4075])).

tff(c_4099,plain,(
    ! [C_631,B_632] :
      ( k1_funct_1(C_631,'#skF_2'(k5_relat_1(C_631,B_632))) = k1_funct_1(C_631,'#skF_1'(k5_relat_1(C_631,B_632)))
      | ~ v2_funct_1(B_632)
      | ~ r2_hidden('#skF_1'(k5_relat_1(C_631,B_632)),k1_relat_1(k5_relat_1(C_631,B_632)))
      | ~ v1_funct_1(C_631)
      | ~ v1_relat_1(C_631)
      | ~ v1_funct_1(B_632)
      | ~ v1_relat_1(B_632)
      | v2_funct_1(k5_relat_1(C_631,B_632))
      | ~ v1_funct_1(k5_relat_1(C_631,B_632))
      | ~ v1_relat_1(k5_relat_1(C_631,B_632)) ) ),
    inference(resolution,[status(thm)],[c_10,c_4089])).

tff(c_4109,plain,(
    ! [C_633,B_634] :
      ( k1_funct_1(C_633,'#skF_2'(k5_relat_1(C_633,B_634))) = k1_funct_1(C_633,'#skF_1'(k5_relat_1(C_633,B_634)))
      | ~ v2_funct_1(B_634)
      | ~ v1_funct_1(C_633)
      | ~ v1_relat_1(C_633)
      | ~ v1_funct_1(B_634)
      | ~ v1_relat_1(B_634)
      | v2_funct_1(k5_relat_1(C_633,B_634))
      | ~ v1_funct_1(k5_relat_1(C_633,B_634))
      | ~ v1_relat_1(k5_relat_1(C_633,B_634)) ) ),
    inference(resolution,[status(thm)],[c_12,c_4099])).

tff(c_4222,plain,(
    ! [C_9,C_633,B_634] :
      ( C_9 = '#skF_2'(k5_relat_1(C_633,B_634))
      | k1_funct_1(C_633,C_9) != k1_funct_1(C_633,'#skF_1'(k5_relat_1(C_633,B_634)))
      | ~ r2_hidden(C_9,k1_relat_1(C_633))
      | ~ r2_hidden('#skF_2'(k5_relat_1(C_633,B_634)),k1_relat_1(C_633))
      | ~ v2_funct_1(C_633)
      | ~ v1_funct_1(C_633)
      | ~ v1_relat_1(C_633)
      | ~ v2_funct_1(B_634)
      | ~ v1_funct_1(C_633)
      | ~ v1_relat_1(C_633)
      | ~ v1_funct_1(B_634)
      | ~ v1_relat_1(B_634)
      | v2_funct_1(k5_relat_1(C_633,B_634))
      | ~ v1_funct_1(k5_relat_1(C_633,B_634))
      | ~ v1_relat_1(k5_relat_1(C_633,B_634)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4109,c_4])).

tff(c_4664,plain,(
    ! [C_650,B_651] :
      ( '#skF_2'(k5_relat_1(C_650,B_651)) = '#skF_1'(k5_relat_1(C_650,B_651))
      | ~ r2_hidden('#skF_1'(k5_relat_1(C_650,B_651)),k1_relat_1(C_650))
      | ~ r2_hidden('#skF_2'(k5_relat_1(C_650,B_651)),k1_relat_1(C_650))
      | ~ v2_funct_1(C_650)
      | ~ v1_funct_1(C_650)
      | ~ v1_relat_1(C_650)
      | ~ v2_funct_1(B_651)
      | ~ v1_funct_1(C_650)
      | ~ v1_relat_1(C_650)
      | ~ v1_funct_1(B_651)
      | ~ v1_relat_1(B_651)
      | v2_funct_1(k5_relat_1(C_650,B_651))
      | ~ v1_funct_1(k5_relat_1(C_650,B_651))
      | ~ v1_relat_1(k5_relat_1(C_650,B_651)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_4222])).

tff(c_4669,plain,(
    ! [C_652,B_653] :
      ( '#skF_2'(k5_relat_1(C_652,B_653)) = '#skF_1'(k5_relat_1(C_652,B_653))
      | ~ r2_hidden('#skF_1'(k5_relat_1(C_652,B_653)),k1_relat_1(C_652))
      | ~ v2_funct_1(C_652)
      | ~ v2_funct_1(B_653)
      | ~ v1_funct_1(C_652)
      | ~ v1_relat_1(C_652)
      | ~ v1_funct_1(B_653)
      | ~ v1_relat_1(B_653)
      | v2_funct_1(k5_relat_1(C_652,B_653))
      | ~ v1_funct_1(k5_relat_1(C_652,B_653))
      | ~ v1_relat_1(k5_relat_1(C_652,B_653)) ) ),
    inference(resolution,[status(thm)],[c_77,c_4664])).

tff(c_4674,plain,(
    ! [C_654,B_655] :
      ( '#skF_2'(k5_relat_1(C_654,B_655)) = '#skF_1'(k5_relat_1(C_654,B_655))
      | ~ v2_funct_1(C_654)
      | ~ v2_funct_1(B_655)
      | ~ v1_funct_1(C_654)
      | ~ v1_relat_1(C_654)
      | ~ v1_funct_1(B_655)
      | ~ v1_relat_1(B_655)
      | v2_funct_1(k5_relat_1(C_654,B_655))
      | ~ v1_funct_1(k5_relat_1(C_654,B_655))
      | ~ v1_relat_1(k5_relat_1(C_654,B_655)) ) ),
    inference(resolution,[status(thm)],[c_78,c_4669])).

tff(c_4677,plain,
    ( '#skF_2'(k5_relat_1('#skF_3','#skF_4')) = '#skF_1'(k5_relat_1('#skF_3','#skF_4'))
    | ~ v2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ v1_relat_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_4674,c_26])).

tff(c_4680,plain,
    ( '#skF_2'(k5_relat_1('#skF_3','#skF_4')) = '#skF_1'(k5_relat_1('#skF_3','#skF_4'))
    | ~ v1_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_34,c_32,c_38,c_36,c_28,c_30,c_4677])).

tff(c_4681,plain,(
    ~ v1_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_4680])).

tff(c_4684,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_4681])).

tff(c_4688,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_4684])).

tff(c_4689,plain,(
    ~ v1_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_4693,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_4689])).

tff(c_4697,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_4693])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:44:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.81/6.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.81/6.76  
% 13.81/6.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.81/6.76  %$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 13.81/6.76  
% 13.81/6.76  %Foreground sorts:
% 13.81/6.76  
% 13.81/6.76  
% 13.81/6.76  %Background operators:
% 13.81/6.76  
% 13.81/6.76  
% 13.81/6.76  %Foreground operators:
% 13.81/6.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.81/6.76  tff('#skF_2', type, '#skF_2': $i > $i).
% 13.81/6.76  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 13.81/6.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.81/6.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.81/6.76  tff('#skF_1', type, '#skF_1': $i > $i).
% 13.81/6.76  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 13.81/6.76  tff('#skF_3', type, '#skF_3': $i).
% 13.81/6.76  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 13.81/6.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.81/6.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.81/6.76  tff('#skF_4', type, '#skF_4': $i).
% 13.81/6.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.81/6.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.81/6.76  
% 13.81/6.78  tff(f_102, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(A) & v2_funct_1(B)) => v2_funct_1(k5_relat_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_funct_1)).
% 13.81/6.78  tff(f_58, axiom, (![A, B]: ((((v1_relat_1(A) & v1_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v1_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funct_1)).
% 13.81/6.78  tff(f_31, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 13.81/6.78  tff(f_46, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 13.81/6.78  tff(f_73, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), k1_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_funct_1)).
% 13.81/6.78  tff(f_86, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 13.81/6.78  tff(c_38, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 13.81/6.78  tff(c_36, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 13.81/6.78  tff(c_34, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 13.81/6.78  tff(c_32, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 13.81/6.78  tff(c_14, plain, (![A_10, B_11]: (v1_funct_1(k5_relat_1(A_10, B_11)) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_58])).
% 13.81/6.78  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k5_relat_1(A_1, B_2)) | ~v1_relat_1(B_2) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.81/6.78  tff(c_40, plain, (![A_23]: ('#skF_2'(A_23)!='#skF_1'(A_23) | v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_46])).
% 13.81/6.78  tff(c_26, plain, (~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 13.81/6.78  tff(c_44, plain, ('#skF_2'(k5_relat_1('#skF_3', '#skF_4'))!='#skF_1'(k5_relat_1('#skF_3', '#skF_4')) | ~v1_funct_1(k5_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k5_relat_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_40, c_26])).
% 13.81/6.78  tff(c_45, plain, (~v1_relat_1(k5_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_44])).
% 13.81/6.78  tff(c_48, plain, (~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2, c_45])).
% 13.81/6.78  tff(c_52, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_48])).
% 13.81/6.78  tff(c_53, plain, (~v1_funct_1(k5_relat_1('#skF_3', '#skF_4')) | '#skF_2'(k5_relat_1('#skF_3', '#skF_4'))!='#skF_1'(k5_relat_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_44])).
% 13.81/6.78  tff(c_67, plain, ('#skF_2'(k5_relat_1('#skF_3', '#skF_4'))!='#skF_1'(k5_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_53])).
% 13.81/6.78  tff(c_54, plain, (v1_relat_1(k5_relat_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_44])).
% 13.81/6.78  tff(c_28, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 13.81/6.78  tff(c_30, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 13.81/6.78  tff(c_12, plain, (![A_3]: (r2_hidden('#skF_1'(A_3), k1_relat_1(A_3)) | v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_46])).
% 13.81/6.78  tff(c_68, plain, (![A_29, C_30, B_31]: (r2_hidden(A_29, k1_relat_1(C_30)) | ~r2_hidden(A_29, k1_relat_1(k5_relat_1(C_30, B_31))) | ~v1_funct_1(C_30) | ~v1_relat_1(C_30) | ~v1_funct_1(B_31) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.81/6.78  tff(c_78, plain, (![C_30, B_31]: (r2_hidden('#skF_1'(k5_relat_1(C_30, B_31)), k1_relat_1(C_30)) | ~v1_funct_1(C_30) | ~v1_relat_1(C_30) | ~v1_funct_1(B_31) | ~v1_relat_1(B_31) | v2_funct_1(k5_relat_1(C_30, B_31)) | ~v1_funct_1(k5_relat_1(C_30, B_31)) | ~v1_relat_1(k5_relat_1(C_30, B_31)))), inference(resolution, [status(thm)], [c_12, c_68])).
% 13.81/6.78  tff(c_10, plain, (![A_3]: (r2_hidden('#skF_2'(A_3), k1_relat_1(A_3)) | v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_46])).
% 13.81/6.78  tff(c_77, plain, (![C_30, B_31]: (r2_hidden('#skF_2'(k5_relat_1(C_30, B_31)), k1_relat_1(C_30)) | ~v1_funct_1(C_30) | ~v1_relat_1(C_30) | ~v1_funct_1(B_31) | ~v1_relat_1(B_31) | v2_funct_1(k5_relat_1(C_30, B_31)) | ~v1_funct_1(k5_relat_1(C_30, B_31)) | ~v1_relat_1(k5_relat_1(C_30, B_31)))), inference(resolution, [status(thm)], [c_10, c_68])).
% 13.81/6.78  tff(c_20, plain, (![C_15, A_12, B_13]: (r2_hidden(k1_funct_1(C_15, A_12), k1_relat_1(B_13)) | ~r2_hidden(A_12, k1_relat_1(k5_relat_1(C_15, B_13))) | ~v1_funct_1(C_15) | ~v1_relat_1(C_15) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.81/6.78  tff(c_105, plain, (![C_41, B_42, A_43]: (k1_funct_1(k5_relat_1(C_41, B_42), A_43)=k1_funct_1(B_42, k1_funct_1(C_41, A_43)) | ~r2_hidden(A_43, k1_relat_1(k5_relat_1(C_41, B_42))) | ~v1_funct_1(C_41) | ~v1_relat_1(C_41) | ~v1_funct_1(B_42) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.81/6.78  tff(c_244, plain, (![C_64, B_65]: (k1_funct_1(k5_relat_1(C_64, B_65), '#skF_2'(k5_relat_1(C_64, B_65)))=k1_funct_1(B_65, k1_funct_1(C_64, '#skF_2'(k5_relat_1(C_64, B_65)))) | ~v1_funct_1(C_64) | ~v1_relat_1(C_64) | ~v1_funct_1(B_65) | ~v1_relat_1(B_65) | v2_funct_1(k5_relat_1(C_64, B_65)) | ~v1_funct_1(k5_relat_1(C_64, B_65)) | ~v1_relat_1(k5_relat_1(C_64, B_65)))), inference(resolution, [status(thm)], [c_10, c_105])).
% 13.81/6.78  tff(c_8, plain, (![A_3]: (k1_funct_1(A_3, '#skF_2'(A_3))=k1_funct_1(A_3, '#skF_1'(A_3)) | v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_46])).
% 13.81/6.78  tff(c_360, plain, (![C_85, B_86]: (k1_funct_1(k5_relat_1(C_85, B_86), '#skF_1'(k5_relat_1(C_85, B_86)))=k1_funct_1(B_86, k1_funct_1(C_85, '#skF_2'(k5_relat_1(C_85, B_86)))) | v2_funct_1(k5_relat_1(C_85, B_86)) | ~v1_funct_1(k5_relat_1(C_85, B_86)) | ~v1_relat_1(k5_relat_1(C_85, B_86)) | ~v1_funct_1(C_85) | ~v1_relat_1(C_85) | ~v1_funct_1(B_86) | ~v1_relat_1(B_86) | v2_funct_1(k5_relat_1(C_85, B_86)) | ~v1_funct_1(k5_relat_1(C_85, B_86)) | ~v1_relat_1(k5_relat_1(C_85, B_86)))), inference(superposition, [status(thm), theory('equality')], [c_244, c_8])).
% 13.81/6.78  tff(c_120, plain, (![C_41, B_42]: (k1_funct_1(k5_relat_1(C_41, B_42), '#skF_1'(k5_relat_1(C_41, B_42)))=k1_funct_1(B_42, k1_funct_1(C_41, '#skF_1'(k5_relat_1(C_41, B_42)))) | ~v1_funct_1(C_41) | ~v1_relat_1(C_41) | ~v1_funct_1(B_42) | ~v1_relat_1(B_42) | v2_funct_1(k5_relat_1(C_41, B_42)) | ~v1_funct_1(k5_relat_1(C_41, B_42)) | ~v1_relat_1(k5_relat_1(C_41, B_42)))), inference(resolution, [status(thm)], [c_12, c_105])).
% 13.81/6.78  tff(c_1310, plain, (![B_218, C_219]: (k1_funct_1(B_218, k1_funct_1(C_219, '#skF_2'(k5_relat_1(C_219, B_218))))=k1_funct_1(B_218, k1_funct_1(C_219, '#skF_1'(k5_relat_1(C_219, B_218)))) | ~v1_funct_1(C_219) | ~v1_relat_1(C_219) | ~v1_funct_1(B_218) | ~v1_relat_1(B_218) | v2_funct_1(k5_relat_1(C_219, B_218)) | ~v1_funct_1(k5_relat_1(C_219, B_218)) | ~v1_relat_1(k5_relat_1(C_219, B_218)) | v2_funct_1(k5_relat_1(C_219, B_218)) | ~v1_funct_1(k5_relat_1(C_219, B_218)) | ~v1_relat_1(k5_relat_1(C_219, B_218)) | ~v1_funct_1(C_219) | ~v1_relat_1(C_219) | ~v1_funct_1(B_218) | ~v1_relat_1(B_218) | v2_funct_1(k5_relat_1(C_219, B_218)) | ~v1_funct_1(k5_relat_1(C_219, B_218)) | ~v1_relat_1(k5_relat_1(C_219, B_218)))), inference(superposition, [status(thm), theory('equality')], [c_360, c_120])).
% 13.81/6.78  tff(c_4, plain, (![C_9, B_8, A_3]: (C_9=B_8 | k1_funct_1(A_3, C_9)!=k1_funct_1(A_3, B_8) | ~r2_hidden(C_9, k1_relat_1(A_3)) | ~r2_hidden(B_8, k1_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_46])).
% 13.81/6.78  tff(c_1333, plain, (![C_219, B_218, C_9]: (k1_funct_1(C_219, '#skF_2'(k5_relat_1(C_219, B_218)))=C_9 | k1_funct_1(B_218, k1_funct_1(C_219, '#skF_1'(k5_relat_1(C_219, B_218))))!=k1_funct_1(B_218, C_9) | ~r2_hidden(C_9, k1_relat_1(B_218)) | ~r2_hidden(k1_funct_1(C_219, '#skF_2'(k5_relat_1(C_219, B_218))), k1_relat_1(B_218)) | ~v2_funct_1(B_218) | ~v1_funct_1(B_218) | ~v1_relat_1(B_218) | ~v1_funct_1(C_219) | ~v1_relat_1(C_219) | ~v1_funct_1(B_218) | ~v1_relat_1(B_218) | v2_funct_1(k5_relat_1(C_219, B_218)) | ~v1_funct_1(k5_relat_1(C_219, B_218)) | ~v1_relat_1(k5_relat_1(C_219, B_218)) | v2_funct_1(k5_relat_1(C_219, B_218)) | ~v1_funct_1(k5_relat_1(C_219, B_218)) | ~v1_relat_1(k5_relat_1(C_219, B_218)) | ~v1_funct_1(C_219) | ~v1_relat_1(C_219) | ~v1_funct_1(B_218) | ~v1_relat_1(B_218) | v2_funct_1(k5_relat_1(C_219, B_218)) | ~v1_funct_1(k5_relat_1(C_219, B_218)) | ~v1_relat_1(k5_relat_1(C_219, B_218)))), inference(superposition, [status(thm), theory('equality')], [c_1310, c_4])).
% 13.81/6.78  tff(c_4061, plain, (![C_625, B_626]: (k1_funct_1(C_625, '#skF_2'(k5_relat_1(C_625, B_626)))=k1_funct_1(C_625, '#skF_1'(k5_relat_1(C_625, B_626))) | ~r2_hidden(k1_funct_1(C_625, '#skF_1'(k5_relat_1(C_625, B_626))), k1_relat_1(B_626)) | ~r2_hidden(k1_funct_1(C_625, '#skF_2'(k5_relat_1(C_625, B_626))), k1_relat_1(B_626)) | ~v2_funct_1(B_626) | ~v1_funct_1(B_626) | ~v1_relat_1(B_626) | ~v1_funct_1(C_625) | ~v1_relat_1(C_625) | ~v1_funct_1(B_626) | ~v1_relat_1(B_626) | v2_funct_1(k5_relat_1(C_625, B_626)) | ~v1_funct_1(k5_relat_1(C_625, B_626)) | ~v1_relat_1(k5_relat_1(C_625, B_626)) | v2_funct_1(k5_relat_1(C_625, B_626)) | ~v1_funct_1(k5_relat_1(C_625, B_626)) | ~v1_relat_1(k5_relat_1(C_625, B_626)) | ~v1_funct_1(C_625) | ~v1_relat_1(C_625) | ~v1_funct_1(B_626) | ~v1_relat_1(B_626) | v2_funct_1(k5_relat_1(C_625, B_626)) | ~v1_funct_1(k5_relat_1(C_625, B_626)) | ~v1_relat_1(k5_relat_1(C_625, B_626)))), inference(reflexivity, [status(thm), theory('equality')], [c_1333])).
% 13.81/6.78  tff(c_4075, plain, (![C_627, B_628]: (k1_funct_1(C_627, '#skF_2'(k5_relat_1(C_627, B_628)))=k1_funct_1(C_627, '#skF_1'(k5_relat_1(C_627, B_628))) | ~r2_hidden(k1_funct_1(C_627, '#skF_1'(k5_relat_1(C_627, B_628))), k1_relat_1(B_628)) | ~v2_funct_1(B_628) | v2_funct_1(k5_relat_1(C_627, B_628)) | ~v1_funct_1(k5_relat_1(C_627, B_628)) | ~v1_relat_1(k5_relat_1(C_627, B_628)) | ~r2_hidden('#skF_2'(k5_relat_1(C_627, B_628)), k1_relat_1(k5_relat_1(C_627, B_628))) | ~v1_funct_1(C_627) | ~v1_relat_1(C_627) | ~v1_funct_1(B_628) | ~v1_relat_1(B_628))), inference(resolution, [status(thm)], [c_20, c_4061])).
% 13.81/6.78  tff(c_4089, plain, (![C_629, B_630]: (k1_funct_1(C_629, '#skF_2'(k5_relat_1(C_629, B_630)))=k1_funct_1(C_629, '#skF_1'(k5_relat_1(C_629, B_630))) | ~v2_funct_1(B_630) | v2_funct_1(k5_relat_1(C_629, B_630)) | ~v1_funct_1(k5_relat_1(C_629, B_630)) | ~v1_relat_1(k5_relat_1(C_629, B_630)) | ~r2_hidden('#skF_2'(k5_relat_1(C_629, B_630)), k1_relat_1(k5_relat_1(C_629, B_630))) | ~r2_hidden('#skF_1'(k5_relat_1(C_629, B_630)), k1_relat_1(k5_relat_1(C_629, B_630))) | ~v1_funct_1(C_629) | ~v1_relat_1(C_629) | ~v1_funct_1(B_630) | ~v1_relat_1(B_630))), inference(resolution, [status(thm)], [c_20, c_4075])).
% 13.81/6.78  tff(c_4099, plain, (![C_631, B_632]: (k1_funct_1(C_631, '#skF_2'(k5_relat_1(C_631, B_632)))=k1_funct_1(C_631, '#skF_1'(k5_relat_1(C_631, B_632))) | ~v2_funct_1(B_632) | ~r2_hidden('#skF_1'(k5_relat_1(C_631, B_632)), k1_relat_1(k5_relat_1(C_631, B_632))) | ~v1_funct_1(C_631) | ~v1_relat_1(C_631) | ~v1_funct_1(B_632) | ~v1_relat_1(B_632) | v2_funct_1(k5_relat_1(C_631, B_632)) | ~v1_funct_1(k5_relat_1(C_631, B_632)) | ~v1_relat_1(k5_relat_1(C_631, B_632)))), inference(resolution, [status(thm)], [c_10, c_4089])).
% 13.81/6.78  tff(c_4109, plain, (![C_633, B_634]: (k1_funct_1(C_633, '#skF_2'(k5_relat_1(C_633, B_634)))=k1_funct_1(C_633, '#skF_1'(k5_relat_1(C_633, B_634))) | ~v2_funct_1(B_634) | ~v1_funct_1(C_633) | ~v1_relat_1(C_633) | ~v1_funct_1(B_634) | ~v1_relat_1(B_634) | v2_funct_1(k5_relat_1(C_633, B_634)) | ~v1_funct_1(k5_relat_1(C_633, B_634)) | ~v1_relat_1(k5_relat_1(C_633, B_634)))), inference(resolution, [status(thm)], [c_12, c_4099])).
% 13.81/6.78  tff(c_4222, plain, (![C_9, C_633, B_634]: (C_9='#skF_2'(k5_relat_1(C_633, B_634)) | k1_funct_1(C_633, C_9)!=k1_funct_1(C_633, '#skF_1'(k5_relat_1(C_633, B_634))) | ~r2_hidden(C_9, k1_relat_1(C_633)) | ~r2_hidden('#skF_2'(k5_relat_1(C_633, B_634)), k1_relat_1(C_633)) | ~v2_funct_1(C_633) | ~v1_funct_1(C_633) | ~v1_relat_1(C_633) | ~v2_funct_1(B_634) | ~v1_funct_1(C_633) | ~v1_relat_1(C_633) | ~v1_funct_1(B_634) | ~v1_relat_1(B_634) | v2_funct_1(k5_relat_1(C_633, B_634)) | ~v1_funct_1(k5_relat_1(C_633, B_634)) | ~v1_relat_1(k5_relat_1(C_633, B_634)))), inference(superposition, [status(thm), theory('equality')], [c_4109, c_4])).
% 13.81/6.78  tff(c_4664, plain, (![C_650, B_651]: ('#skF_2'(k5_relat_1(C_650, B_651))='#skF_1'(k5_relat_1(C_650, B_651)) | ~r2_hidden('#skF_1'(k5_relat_1(C_650, B_651)), k1_relat_1(C_650)) | ~r2_hidden('#skF_2'(k5_relat_1(C_650, B_651)), k1_relat_1(C_650)) | ~v2_funct_1(C_650) | ~v1_funct_1(C_650) | ~v1_relat_1(C_650) | ~v2_funct_1(B_651) | ~v1_funct_1(C_650) | ~v1_relat_1(C_650) | ~v1_funct_1(B_651) | ~v1_relat_1(B_651) | v2_funct_1(k5_relat_1(C_650, B_651)) | ~v1_funct_1(k5_relat_1(C_650, B_651)) | ~v1_relat_1(k5_relat_1(C_650, B_651)))), inference(reflexivity, [status(thm), theory('equality')], [c_4222])).
% 13.81/6.78  tff(c_4669, plain, (![C_652, B_653]: ('#skF_2'(k5_relat_1(C_652, B_653))='#skF_1'(k5_relat_1(C_652, B_653)) | ~r2_hidden('#skF_1'(k5_relat_1(C_652, B_653)), k1_relat_1(C_652)) | ~v2_funct_1(C_652) | ~v2_funct_1(B_653) | ~v1_funct_1(C_652) | ~v1_relat_1(C_652) | ~v1_funct_1(B_653) | ~v1_relat_1(B_653) | v2_funct_1(k5_relat_1(C_652, B_653)) | ~v1_funct_1(k5_relat_1(C_652, B_653)) | ~v1_relat_1(k5_relat_1(C_652, B_653)))), inference(resolution, [status(thm)], [c_77, c_4664])).
% 13.81/6.78  tff(c_4674, plain, (![C_654, B_655]: ('#skF_2'(k5_relat_1(C_654, B_655))='#skF_1'(k5_relat_1(C_654, B_655)) | ~v2_funct_1(C_654) | ~v2_funct_1(B_655) | ~v1_funct_1(C_654) | ~v1_relat_1(C_654) | ~v1_funct_1(B_655) | ~v1_relat_1(B_655) | v2_funct_1(k5_relat_1(C_654, B_655)) | ~v1_funct_1(k5_relat_1(C_654, B_655)) | ~v1_relat_1(k5_relat_1(C_654, B_655)))), inference(resolution, [status(thm)], [c_78, c_4669])).
% 13.81/6.78  tff(c_4677, plain, ('#skF_2'(k5_relat_1('#skF_3', '#skF_4'))='#skF_1'(k5_relat_1('#skF_3', '#skF_4')) | ~v2_funct_1('#skF_3') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1(k5_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k5_relat_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_4674, c_26])).
% 13.81/6.78  tff(c_4680, plain, ('#skF_2'(k5_relat_1('#skF_3', '#skF_4'))='#skF_1'(k5_relat_1('#skF_3', '#skF_4')) | ~v1_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_34, c_32, c_38, c_36, c_28, c_30, c_4677])).
% 13.81/6.78  tff(c_4681, plain, (~v1_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_67, c_4680])).
% 13.81/6.78  tff(c_4684, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_4681])).
% 13.81/6.78  tff(c_4688, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_4684])).
% 13.81/6.78  tff(c_4689, plain, (~v1_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_53])).
% 13.81/6.78  tff(c_4693, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_4689])).
% 13.81/6.78  tff(c_4697, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_4693])).
% 13.81/6.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.81/6.78  
% 13.81/6.78  Inference rules
% 13.81/6.78  ----------------------
% 13.81/6.78  #Ref     : 3
% 13.81/6.78  #Sup     : 1051
% 13.81/6.78  #Fact    : 0
% 13.81/6.78  #Define  : 0
% 13.81/6.78  #Split   : 2
% 13.81/6.78  #Chain   : 0
% 13.81/6.78  #Close   : 0
% 13.81/6.78  
% 13.81/6.78  Ordering : KBO
% 13.81/6.78  
% 13.81/6.78  Simplification rules
% 13.81/6.78  ----------------------
% 13.81/6.78  #Subsume      : 146
% 13.81/6.78  #Demod        : 17
% 13.81/6.78  #Tautology    : 86
% 13.81/6.78  #SimpNegUnit  : 1
% 13.81/6.78  #BackRed      : 0
% 13.81/6.78  
% 13.81/6.78  #Partial instantiations: 0
% 13.81/6.78  #Strategies tried      : 1
% 13.81/6.78  
% 13.81/6.78  Timing (in seconds)
% 13.81/6.78  ----------------------
% 13.81/6.79  Preprocessing        : 0.32
% 13.81/6.79  Parsing              : 0.16
% 13.81/6.79  CNF conversion       : 0.02
% 13.81/6.79  Main loop            : 5.70
% 13.81/6.79  Inferencing          : 0.87
% 13.81/6.79  Reduction            : 0.42
% 13.81/6.79  Demodulation         : 0.28
% 13.81/6.79  BG Simplification    : 0.10
% 13.81/6.79  Subsumption          : 4.16
% 13.81/6.79  Abstraction          : 0.15
% 13.81/6.79  MUC search           : 0.00
% 13.81/6.79  Cooper               : 0.00
% 13.81/6.79  Total                : 6.05
% 13.81/6.79  Index Insertion      : 0.00
% 13.81/6.79  Index Deletion       : 0.00
% 13.81/6.79  Index Matching       : 0.00
% 13.81/6.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
