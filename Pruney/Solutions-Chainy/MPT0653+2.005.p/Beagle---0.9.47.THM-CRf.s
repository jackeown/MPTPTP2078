%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:58 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 214 expanded)
%              Number of leaves         :   21 (  89 expanded)
%              Depth                    :   16
%              Number of atoms          :  205 (1087 expanded)
%              Number of equality atoms :   59 ( 354 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v2_funct_1(A)
                & k1_relat_1(A) = k2_relat_1(B)
                & k2_relat_1(A) = k1_relat_1(B)
                & ! [C,D] :
                    ( ( r2_hidden(C,k1_relat_1(A))
                      & r2_hidden(D,k1_relat_1(B)) )
                   => ( k1_funct_1(A,C) = D
                    <=> k1_funct_1(B,D) = C ) ) )
             => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_1)).

tff(f_51,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k1_relat_1(B)) )
       => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
          & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_32,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_26,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_22,plain,(
    k2_relat_1('#skF_2') = k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_10,plain,(
    ! [A_4] :
      ( k1_relat_1(k2_funct_1(A_4)) = k2_relat_1(A_4)
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    k2_funct_1('#skF_2') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_relat_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_4] :
      ( k2_relat_1(k2_funct_1(A_4)) = k1_relat_1(A_4)
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_68,plain,(
    ! [B_27,A_28] :
      ( r2_hidden(k1_funct_1(B_27,A_28),k2_relat_1(B_27))
      | ~ r2_hidden(A_28,k1_relat_1(B_27))
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_356,plain,(
    ! [A_49,A_50] :
      ( r2_hidden(k1_funct_1(k2_funct_1(A_49),A_50),k1_relat_1(A_49))
      | ~ r2_hidden(A_50,k1_relat_1(k2_funct_1(A_49)))
      | ~ v1_funct_1(k2_funct_1(A_49))
      | ~ v1_relat_1(k2_funct_1(A_49))
      | ~ v2_funct_1(A_49)
      | ~ v1_funct_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_68])).

tff(c_77,plain,(
    ! [A_28] :
      ( r2_hidden(k1_funct_1('#skF_2',A_28),k1_relat_1('#skF_3'))
      | ~ r2_hidden(A_28,k1_relat_1('#skF_2'))
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_68])).

tff(c_88,plain,(
    ! [A_31] :
      ( r2_hidden(k1_funct_1('#skF_2',A_31),k1_relat_1('#skF_3'))
      | ~ r2_hidden(A_31,k1_relat_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_77])).

tff(c_38,plain,(
    ! [C_20] :
      ( k1_funct_1('#skF_3',k1_funct_1('#skF_2',C_20)) = C_20
      | ~ r2_hidden(k1_funct_1('#skF_2',C_20),k1_relat_1('#skF_3'))
      | ~ r2_hidden(C_20,k1_relat_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_92,plain,(
    ! [A_31] :
      ( k1_funct_1('#skF_3',k1_funct_1('#skF_2',A_31)) = A_31
      | ~ r2_hidden(A_31,k1_relat_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_88,c_38])).

tff(c_360,plain,(
    ! [A_50] :
      ( k1_funct_1('#skF_3',k1_funct_1('#skF_2',k1_funct_1(k2_funct_1('#skF_2'),A_50))) = k1_funct_1(k2_funct_1('#skF_2'),A_50)
      | ~ r2_hidden(A_50,k1_relat_1(k2_funct_1('#skF_2')))
      | ~ v1_funct_1(k2_funct_1('#skF_2'))
      | ~ v1_relat_1(k2_funct_1('#skF_2'))
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_356,c_92])).

tff(c_376,plain,(
    ! [A_50] :
      ( k1_funct_1('#skF_3',k1_funct_1('#skF_2',k1_funct_1(k2_funct_1('#skF_2'),A_50))) = k1_funct_1(k2_funct_1('#skF_2'),A_50)
      | ~ r2_hidden(A_50,k1_relat_1(k2_funct_1('#skF_2')))
      | ~ v1_funct_1(k2_funct_1('#skF_2'))
      | ~ v1_relat_1(k2_funct_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_360])).

tff(c_382,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_376])).

tff(c_385,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_382])).

tff(c_389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_385])).

tff(c_391,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_376])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_funct_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_390,plain,(
    ! [A_50] :
      ( ~ v1_funct_1(k2_funct_1('#skF_2'))
      | k1_funct_1('#skF_3',k1_funct_1('#skF_2',k1_funct_1(k2_funct_1('#skF_2'),A_50))) = k1_funct_1(k2_funct_1('#skF_2'),A_50)
      | ~ r2_hidden(A_50,k1_relat_1(k2_funct_1('#skF_2'))) ) ),
    inference(splitRight,[status(thm)],[c_376])).

tff(c_392,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_390])).

tff(c_430,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_392])).

tff(c_434,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_430])).

tff(c_436,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_390])).

tff(c_30,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_28,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_18,plain,(
    ! [A_7,B_11] :
      ( r2_hidden('#skF_1'(A_7,B_11),k1_relat_1(A_7))
      | B_11 = A_7
      | k1_relat_1(B_11) != k1_relat_1(A_7)
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_24,plain,(
    k2_relat_1('#skF_3') = k1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_74,plain,(
    ! [A_28] :
      ( r2_hidden(k1_funct_1('#skF_3',A_28),k1_relat_1('#skF_2'))
      | ~ r2_hidden(A_28,k1_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_68])).

tff(c_79,plain,(
    ! [A_28] :
      ( r2_hidden(k1_funct_1('#skF_3',A_28),k1_relat_1('#skF_2'))
      | ~ r2_hidden(A_28,k1_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_74])).

tff(c_204,plain,(
    ! [A_40,B_41] :
      ( r2_hidden('#skF_1'(A_40,B_41),k1_relat_1(A_40))
      | B_41 = A_40
      | k1_relat_1(B_41) != k1_relat_1(A_40)
      | ~ v1_funct_1(B_41)
      | ~ v1_relat_1(B_41)
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_82,plain,(
    ! [A_29] :
      ( r2_hidden(k1_funct_1('#skF_3',A_29),k1_relat_1('#skF_2'))
      | ~ r2_hidden(A_29,k1_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_74])).

tff(c_36,plain,(
    ! [D_21] :
      ( k1_funct_1('#skF_2',k1_funct_1('#skF_3',D_21)) = D_21
      | ~ r2_hidden(D_21,k1_relat_1('#skF_3'))
      | ~ r2_hidden(k1_funct_1('#skF_3',D_21),k1_relat_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_86,plain,(
    ! [A_29] :
      ( k1_funct_1('#skF_2',k1_funct_1('#skF_3',A_29)) = A_29
      | ~ r2_hidden(A_29,k1_relat_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_82,c_36])).

tff(c_212,plain,(
    ! [B_41] :
      ( k1_funct_1('#skF_2',k1_funct_1('#skF_3','#skF_1'('#skF_3',B_41))) = '#skF_1'('#skF_3',B_41)
      | B_41 = '#skF_3'
      | k1_relat_1(B_41) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_41)
      | ~ v1_relat_1(B_41)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_204,c_86])).

tff(c_266,plain,(
    ! [B_45] :
      ( k1_funct_1('#skF_2',k1_funct_1('#skF_3','#skF_1'('#skF_3',B_45))) = '#skF_1'('#skF_3',B_45)
      | B_45 = '#skF_3'
      | k1_relat_1(B_45) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_45)
      | ~ v1_relat_1(B_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_212])).

tff(c_14,plain,(
    ! [B_6,A_5] :
      ( k1_funct_1(k2_funct_1(B_6),k1_funct_1(B_6,A_5)) = A_5
      | ~ r2_hidden(A_5,k1_relat_1(B_6))
      | ~ v2_funct_1(B_6)
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_272,plain,(
    ! [B_45] :
      ( k1_funct_1(k2_funct_1('#skF_2'),'#skF_1'('#skF_3',B_45)) = k1_funct_1('#skF_3','#skF_1'('#skF_3',B_45))
      | ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'('#skF_3',B_45)),k1_relat_1('#skF_2'))
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | B_45 = '#skF_3'
      | k1_relat_1(B_45) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_45)
      | ~ v1_relat_1(B_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_14])).

tff(c_876,plain,(
    ! [B_75] :
      ( k1_funct_1(k2_funct_1('#skF_2'),'#skF_1'('#skF_3',B_75)) = k1_funct_1('#skF_3','#skF_1'('#skF_3',B_75))
      | ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'('#skF_3',B_75)),k1_relat_1('#skF_2'))
      | B_75 = '#skF_3'
      | k1_relat_1(B_75) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_75)
      | ~ v1_relat_1(B_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_272])).

tff(c_881,plain,(
    ! [B_76] :
      ( k1_funct_1(k2_funct_1('#skF_2'),'#skF_1'('#skF_3',B_76)) = k1_funct_1('#skF_3','#skF_1'('#skF_3',B_76))
      | B_76 = '#skF_3'
      | k1_relat_1(B_76) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_76)
      | ~ v1_relat_1(B_76)
      | ~ r2_hidden('#skF_1'('#skF_3',B_76),k1_relat_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_79,c_876])).

tff(c_885,plain,(
    ! [B_11] :
      ( k1_funct_1(k2_funct_1('#skF_2'),'#skF_1'('#skF_3',B_11)) = k1_funct_1('#skF_3','#skF_1'('#skF_3',B_11))
      | B_11 = '#skF_3'
      | k1_relat_1(B_11) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_18,c_881])).

tff(c_889,plain,(
    ! [B_77] :
      ( k1_funct_1(k2_funct_1('#skF_2'),'#skF_1'('#skF_3',B_77)) = k1_funct_1('#skF_3','#skF_1'('#skF_3',B_77))
      | B_77 = '#skF_3'
      | k1_relat_1(B_77) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_77)
      | ~ v1_relat_1(B_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_885])).

tff(c_16,plain,(
    ! [B_11,A_7] :
      ( k1_funct_1(B_11,'#skF_1'(A_7,B_11)) != k1_funct_1(A_7,'#skF_1'(A_7,B_11))
      | B_11 = A_7
      | k1_relat_1(B_11) != k1_relat_1(A_7)
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_908,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | k2_funct_1('#skF_2') = '#skF_3'
    | k1_relat_1(k2_funct_1('#skF_2')) != k1_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_889,c_16])).

tff(c_925,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_relat_1(k2_funct_1('#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_436,c_30,c_28,c_908])).

tff(c_926,plain,(
    k1_relat_1(k2_funct_1('#skF_2')) != k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_925])).

tff(c_934,plain,
    ( k2_relat_1('#skF_2') != k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_926])).

tff(c_937,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_22,c_934])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:41:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.50/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.63  
% 3.50/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.63  %$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.50/1.63  
% 3.50/1.63  %Foreground sorts:
% 3.50/1.63  
% 3.50/1.63  
% 3.50/1.63  %Background operators:
% 3.50/1.63  
% 3.50/1.63  
% 3.50/1.63  %Foreground operators:
% 3.50/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.50/1.63  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.50/1.63  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.50/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.50/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.50/1.63  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.50/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.50/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.50/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.50/1.63  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.50/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.50/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.50/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.50/1.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.50/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.50/1.63  
% 3.50/1.64  tff(f_108, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((((v2_funct_1(A) & (k1_relat_1(A) = k2_relat_1(B))) & (k2_relat_1(A) = k1_relat_1(B))) & (![C, D]: ((r2_hidden(C, k1_relat_1(A)) & r2_hidden(D, k1_relat_1(B))) => ((k1_funct_1(A, C) = D) <=> (k1_funct_1(B, D) = C))))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_funct_1)).
% 3.50/1.64  tff(f_51, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.50/1.64  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.50/1.64  tff(f_41, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 3.50/1.64  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 3.50/1.64  tff(f_63, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_funct_1)).
% 3.50/1.64  tff(c_34, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.50/1.64  tff(c_32, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.50/1.64  tff(c_26, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.50/1.64  tff(c_22, plain, (k2_relat_1('#skF_2')=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.50/1.64  tff(c_10, plain, (![A_4]: (k1_relat_1(k2_funct_1(A_4))=k2_relat_1(A_4) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.50/1.64  tff(c_20, plain, (k2_funct_1('#skF_2')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.50/1.64  tff(c_4, plain, (![A_1]: (v1_relat_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.50/1.64  tff(c_8, plain, (![A_4]: (k2_relat_1(k2_funct_1(A_4))=k1_relat_1(A_4) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.50/1.64  tff(c_68, plain, (![B_27, A_28]: (r2_hidden(k1_funct_1(B_27, A_28), k2_relat_1(B_27)) | ~r2_hidden(A_28, k1_relat_1(B_27)) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.50/1.64  tff(c_356, plain, (![A_49, A_50]: (r2_hidden(k1_funct_1(k2_funct_1(A_49), A_50), k1_relat_1(A_49)) | ~r2_hidden(A_50, k1_relat_1(k2_funct_1(A_49))) | ~v1_funct_1(k2_funct_1(A_49)) | ~v1_relat_1(k2_funct_1(A_49)) | ~v2_funct_1(A_49) | ~v1_funct_1(A_49) | ~v1_relat_1(A_49))), inference(superposition, [status(thm), theory('equality')], [c_8, c_68])).
% 3.50/1.64  tff(c_77, plain, (![A_28]: (r2_hidden(k1_funct_1('#skF_2', A_28), k1_relat_1('#skF_3')) | ~r2_hidden(A_28, k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_22, c_68])).
% 3.50/1.64  tff(c_88, plain, (![A_31]: (r2_hidden(k1_funct_1('#skF_2', A_31), k1_relat_1('#skF_3')) | ~r2_hidden(A_31, k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_77])).
% 3.50/1.64  tff(c_38, plain, (![C_20]: (k1_funct_1('#skF_3', k1_funct_1('#skF_2', C_20))=C_20 | ~r2_hidden(k1_funct_1('#skF_2', C_20), k1_relat_1('#skF_3')) | ~r2_hidden(C_20, k1_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.50/1.64  tff(c_92, plain, (![A_31]: (k1_funct_1('#skF_3', k1_funct_1('#skF_2', A_31))=A_31 | ~r2_hidden(A_31, k1_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_88, c_38])).
% 3.50/1.64  tff(c_360, plain, (![A_50]: (k1_funct_1('#skF_3', k1_funct_1('#skF_2', k1_funct_1(k2_funct_1('#skF_2'), A_50)))=k1_funct_1(k2_funct_1('#skF_2'), A_50) | ~r2_hidden(A_50, k1_relat_1(k2_funct_1('#skF_2'))) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_356, c_92])).
% 3.50/1.64  tff(c_376, plain, (![A_50]: (k1_funct_1('#skF_3', k1_funct_1('#skF_2', k1_funct_1(k2_funct_1('#skF_2'), A_50)))=k1_funct_1(k2_funct_1('#skF_2'), A_50) | ~r2_hidden(A_50, k1_relat_1(k2_funct_1('#skF_2'))) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_360])).
% 3.50/1.64  tff(c_382, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_376])).
% 3.50/1.64  tff(c_385, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_4, c_382])).
% 3.50/1.64  tff(c_389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_385])).
% 3.50/1.64  tff(c_391, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_376])).
% 3.50/1.64  tff(c_2, plain, (![A_1]: (v1_funct_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.50/1.64  tff(c_390, plain, (![A_50]: (~v1_funct_1(k2_funct_1('#skF_2')) | k1_funct_1('#skF_3', k1_funct_1('#skF_2', k1_funct_1(k2_funct_1('#skF_2'), A_50)))=k1_funct_1(k2_funct_1('#skF_2'), A_50) | ~r2_hidden(A_50, k1_relat_1(k2_funct_1('#skF_2'))))), inference(splitRight, [status(thm)], [c_376])).
% 3.50/1.64  tff(c_392, plain, (~v1_funct_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_390])).
% 3.50/1.64  tff(c_430, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2, c_392])).
% 3.50/1.64  tff(c_434, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_430])).
% 3.50/1.64  tff(c_436, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_390])).
% 3.50/1.64  tff(c_30, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.50/1.64  tff(c_28, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.50/1.64  tff(c_18, plain, (![A_7, B_11]: (r2_hidden('#skF_1'(A_7, B_11), k1_relat_1(A_7)) | B_11=A_7 | k1_relat_1(B_11)!=k1_relat_1(A_7) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.50/1.64  tff(c_24, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.50/1.64  tff(c_74, plain, (![A_28]: (r2_hidden(k1_funct_1('#skF_3', A_28), k1_relat_1('#skF_2')) | ~r2_hidden(A_28, k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_68])).
% 3.50/1.64  tff(c_79, plain, (![A_28]: (r2_hidden(k1_funct_1('#skF_3', A_28), k1_relat_1('#skF_2')) | ~r2_hidden(A_28, k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_74])).
% 3.50/1.64  tff(c_204, plain, (![A_40, B_41]: (r2_hidden('#skF_1'(A_40, B_41), k1_relat_1(A_40)) | B_41=A_40 | k1_relat_1(B_41)!=k1_relat_1(A_40) | ~v1_funct_1(B_41) | ~v1_relat_1(B_41) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.50/1.64  tff(c_82, plain, (![A_29]: (r2_hidden(k1_funct_1('#skF_3', A_29), k1_relat_1('#skF_2')) | ~r2_hidden(A_29, k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_74])).
% 3.50/1.64  tff(c_36, plain, (![D_21]: (k1_funct_1('#skF_2', k1_funct_1('#skF_3', D_21))=D_21 | ~r2_hidden(D_21, k1_relat_1('#skF_3')) | ~r2_hidden(k1_funct_1('#skF_3', D_21), k1_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.50/1.64  tff(c_86, plain, (![A_29]: (k1_funct_1('#skF_2', k1_funct_1('#skF_3', A_29))=A_29 | ~r2_hidden(A_29, k1_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_82, c_36])).
% 3.50/1.64  tff(c_212, plain, (![B_41]: (k1_funct_1('#skF_2', k1_funct_1('#skF_3', '#skF_1'('#skF_3', B_41)))='#skF_1'('#skF_3', B_41) | B_41='#skF_3' | k1_relat_1(B_41)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_41) | ~v1_relat_1(B_41) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_204, c_86])).
% 3.50/1.64  tff(c_266, plain, (![B_45]: (k1_funct_1('#skF_2', k1_funct_1('#skF_3', '#skF_1'('#skF_3', B_45)))='#skF_1'('#skF_3', B_45) | B_45='#skF_3' | k1_relat_1(B_45)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_45) | ~v1_relat_1(B_45))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_212])).
% 3.50/1.64  tff(c_14, plain, (![B_6, A_5]: (k1_funct_1(k2_funct_1(B_6), k1_funct_1(B_6, A_5))=A_5 | ~r2_hidden(A_5, k1_relat_1(B_6)) | ~v2_funct_1(B_6) | ~v1_funct_1(B_6) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.50/1.64  tff(c_272, plain, (![B_45]: (k1_funct_1(k2_funct_1('#skF_2'), '#skF_1'('#skF_3', B_45))=k1_funct_1('#skF_3', '#skF_1'('#skF_3', B_45)) | ~r2_hidden(k1_funct_1('#skF_3', '#skF_1'('#skF_3', B_45)), k1_relat_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | B_45='#skF_3' | k1_relat_1(B_45)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_45) | ~v1_relat_1(B_45))), inference(superposition, [status(thm), theory('equality')], [c_266, c_14])).
% 3.50/1.64  tff(c_876, plain, (![B_75]: (k1_funct_1(k2_funct_1('#skF_2'), '#skF_1'('#skF_3', B_75))=k1_funct_1('#skF_3', '#skF_1'('#skF_3', B_75)) | ~r2_hidden(k1_funct_1('#skF_3', '#skF_1'('#skF_3', B_75)), k1_relat_1('#skF_2')) | B_75='#skF_3' | k1_relat_1(B_75)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_75) | ~v1_relat_1(B_75))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_272])).
% 3.50/1.64  tff(c_881, plain, (![B_76]: (k1_funct_1(k2_funct_1('#skF_2'), '#skF_1'('#skF_3', B_76))=k1_funct_1('#skF_3', '#skF_1'('#skF_3', B_76)) | B_76='#skF_3' | k1_relat_1(B_76)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_76) | ~v1_relat_1(B_76) | ~r2_hidden('#skF_1'('#skF_3', B_76), k1_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_79, c_876])).
% 3.50/1.64  tff(c_885, plain, (![B_11]: (k1_funct_1(k2_funct_1('#skF_2'), '#skF_1'('#skF_3', B_11))=k1_funct_1('#skF_3', '#skF_1'('#skF_3', B_11)) | B_11='#skF_3' | k1_relat_1(B_11)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_11) | ~v1_relat_1(B_11) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_18, c_881])).
% 3.50/1.64  tff(c_889, plain, (![B_77]: (k1_funct_1(k2_funct_1('#skF_2'), '#skF_1'('#skF_3', B_77))=k1_funct_1('#skF_3', '#skF_1'('#skF_3', B_77)) | B_77='#skF_3' | k1_relat_1(B_77)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_77) | ~v1_relat_1(B_77))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_885])).
% 3.50/1.64  tff(c_16, plain, (![B_11, A_7]: (k1_funct_1(B_11, '#skF_1'(A_7, B_11))!=k1_funct_1(A_7, '#skF_1'(A_7, B_11)) | B_11=A_7 | k1_relat_1(B_11)!=k1_relat_1(A_7) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.50/1.64  tff(c_908, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | k2_funct_1('#skF_2')='#skF_3' | k1_relat_1(k2_funct_1('#skF_2'))!=k1_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_889, c_16])).
% 3.50/1.64  tff(c_925, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_relat_1(k2_funct_1('#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_391, c_436, c_30, c_28, c_908])).
% 3.50/1.64  tff(c_926, plain, (k1_relat_1(k2_funct_1('#skF_2'))!=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_20, c_925])).
% 3.50/1.64  tff(c_934, plain, (k2_relat_1('#skF_2')!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10, c_926])).
% 3.50/1.64  tff(c_937, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_22, c_934])).
% 3.50/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.64  
% 3.50/1.64  Inference rules
% 3.50/1.64  ----------------------
% 3.50/1.64  #Ref     : 1
% 3.50/1.64  #Sup     : 217
% 3.50/1.64  #Fact    : 0
% 3.50/1.64  #Define  : 0
% 3.50/1.64  #Split   : 3
% 3.50/1.64  #Chain   : 0
% 3.50/1.64  #Close   : 0
% 3.50/1.64  
% 3.50/1.64  Ordering : KBO
% 3.50/1.64  
% 3.50/1.64  Simplification rules
% 3.50/1.64  ----------------------
% 3.50/1.64  #Subsume      : 44
% 3.50/1.64  #Demod        : 161
% 3.50/1.64  #Tautology    : 55
% 3.50/1.64  #SimpNegUnit  : 1
% 3.50/1.64  #BackRed      : 0
% 3.50/1.64  
% 3.50/1.64  #Partial instantiations: 0
% 3.50/1.64  #Strategies tried      : 1
% 3.50/1.64  
% 3.50/1.64  Timing (in seconds)
% 3.50/1.64  ----------------------
% 3.50/1.65  Preprocessing        : 0.33
% 3.50/1.65  Parsing              : 0.15
% 3.50/1.65  CNF conversion       : 0.02
% 3.50/1.65  Main loop            : 0.48
% 3.50/1.65  Inferencing          : 0.18
% 3.50/1.65  Reduction            : 0.14
% 3.50/1.65  Demodulation         : 0.10
% 3.50/1.65  BG Simplification    : 0.03
% 3.50/1.65  Subsumption          : 0.11
% 3.50/1.65  Abstraction          : 0.03
% 3.50/1.65  MUC search           : 0.00
% 3.50/1.65  Cooper               : 0.00
% 3.50/1.65  Total                : 0.84
% 3.50/1.65  Index Insertion      : 0.00
% 3.50/1.65  Index Deletion       : 0.00
% 3.50/1.65  Index Matching       : 0.00
% 3.50/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
