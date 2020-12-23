%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0639+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:38 EST 2020

% Result     : Theorem 14.22s
% Output     : CNFRefutation 14.43s
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

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v2_funct_1(A)
                & v2_funct_1(B) )
             => v2_funct_1(k5_relat_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_funct_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

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

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
          <=> ( r2_hidden(A,k1_relat_1(C))
              & r2_hidden(k1_funct_1(C,A),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_34,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_32,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( v1_funct_1(k5_relat_1(A_10,B_11))
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(k5_relat_1(A_8,B_9))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_40,plain,(
    ! [A_23] :
      ( '#skF_2'(A_23) != '#skF_1'(A_23)
      | v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

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
    inference(resolution,[status(thm)],[c_12,c_45])).

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
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_30,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_10,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),k1_relat_1(A_1))
      | v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_68,plain,(
    ! [A_29,C_30,B_31] :
      ( r2_hidden(A_29,k1_relat_1(C_30))
      | ~ r2_hidden(A_29,k1_relat_1(k5_relat_1(C_30,B_31)))
      | ~ v1_funct_1(C_30)
      | ~ v1_relat_1(C_30)
      | ~ v1_funct_1(B_31)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_77,plain,(
    ! [C_30,B_31] :
      ( r2_hidden('#skF_1'(k5_relat_1(C_30,B_31)),k1_relat_1(C_30))
      | ~ v1_funct_1(C_30)
      | ~ v1_relat_1(C_30)
      | ~ v1_funct_1(B_31)
      | ~ v1_relat_1(B_31)
      | v2_funct_1(k5_relat_1(C_30,B_31))
      | ~ v1_funct_1(k5_relat_1(C_30,B_31))
      | ~ v1_relat_1(k5_relat_1(C_30,B_31)) ) ),
    inference(resolution,[status(thm)],[c_10,c_68])).

tff(c_8,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_2'(A_1),k1_relat_1(A_1))
      | v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_78,plain,(
    ! [C_30,B_31] :
      ( r2_hidden('#skF_2'(k5_relat_1(C_30,B_31)),k1_relat_1(C_30))
      | ~ v1_funct_1(C_30)
      | ~ v1_relat_1(C_30)
      | ~ v1_funct_1(B_31)
      | ~ v1_relat_1(B_31)
      | v2_funct_1(k5_relat_1(C_30,B_31))
      | ~ v1_funct_1(k5_relat_1(C_30,B_31))
      | ~ v1_relat_1(k5_relat_1(C_30,B_31)) ) ),
    inference(resolution,[status(thm)],[c_8,c_68])).

tff(c_20,plain,(
    ! [C_15,A_12,B_13] :
      ( r2_hidden(k1_funct_1(C_15,A_12),k1_relat_1(B_13))
      | ~ r2_hidden(A_12,k1_relat_1(k5_relat_1(C_15,B_13)))
      | ~ v1_funct_1(C_15)
      | ~ v1_relat_1(C_15)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_105,plain,(
    ! [C_41,B_42,A_43] :
      ( k1_funct_1(k5_relat_1(C_41,B_42),A_43) = k1_funct_1(B_42,k1_funct_1(C_41,A_43))
      | ~ r2_hidden(A_43,k1_relat_1(k5_relat_1(C_41,B_42)))
      | ~ v1_funct_1(C_41)
      | ~ v1_relat_1(C_41)
      | ~ v1_funct_1(B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_219,plain,(
    ! [C_62,B_63] :
      ( k1_funct_1(k5_relat_1(C_62,B_63),'#skF_2'(k5_relat_1(C_62,B_63))) = k1_funct_1(B_63,k1_funct_1(C_62,'#skF_2'(k5_relat_1(C_62,B_63))))
      | ~ v1_funct_1(C_62)
      | ~ v1_relat_1(C_62)
      | ~ v1_funct_1(B_63)
      | ~ v1_relat_1(B_63)
      | v2_funct_1(k5_relat_1(C_62,B_63))
      | ~ v1_funct_1(k5_relat_1(C_62,B_63))
      | ~ v1_relat_1(k5_relat_1(C_62,B_63)) ) ),
    inference(resolution,[status(thm)],[c_8,c_105])).

tff(c_6,plain,(
    ! [A_1] :
      ( k1_funct_1(A_1,'#skF_2'(A_1)) = k1_funct_1(A_1,'#skF_1'(A_1))
      | v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

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
    inference(superposition,[status(thm),theory(equality)],[c_219,c_6])).

tff(c_119,plain,(
    ! [C_41,B_42] :
      ( k1_funct_1(k5_relat_1(C_41,B_42),'#skF_1'(k5_relat_1(C_41,B_42))) = k1_funct_1(B_42,k1_funct_1(C_41,'#skF_1'(k5_relat_1(C_41,B_42))))
      | ~ v1_funct_1(C_41)
      | ~ v1_relat_1(C_41)
      | ~ v1_funct_1(B_42)
      | ~ v1_relat_1(B_42)
      | v2_funct_1(k5_relat_1(C_41,B_42))
      | ~ v1_funct_1(k5_relat_1(C_41,B_42))
      | ~ v1_relat_1(k5_relat_1(C_41,B_42)) ) ),
    inference(resolution,[status(thm)],[c_10,c_105])).

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
    inference(superposition,[status(thm),theory(equality)],[c_360,c_119])).

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

tff(c_1333,plain,(
    ! [C_219,B_218,C_7] :
      ( k1_funct_1(C_219,'#skF_2'(k5_relat_1(C_219,B_218))) = C_7
      | k1_funct_1(B_218,k1_funct_1(C_219,'#skF_1'(k5_relat_1(C_219,B_218)))) != k1_funct_1(B_218,C_7)
      | ~ r2_hidden(C_7,k1_relat_1(B_218))
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
    inference(superposition,[status(thm),theory(equality)],[c_1310,c_2])).

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
    inference(resolution,[status(thm)],[c_8,c_4089])).

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
    inference(resolution,[status(thm)],[c_10,c_4099])).

tff(c_4222,plain,(
    ! [C_7,C_633,B_634] :
      ( C_7 = '#skF_2'(k5_relat_1(C_633,B_634))
      | k1_funct_1(C_633,C_7) != k1_funct_1(C_633,'#skF_1'(k5_relat_1(C_633,B_634)))
      | ~ r2_hidden(C_7,k1_relat_1(C_633))
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
    inference(superposition,[status(thm),theory(equality)],[c_4109,c_2])).

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
    inference(resolution,[status(thm)],[c_78,c_4664])).

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
    inference(resolution,[status(thm)],[c_77,c_4669])).

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
