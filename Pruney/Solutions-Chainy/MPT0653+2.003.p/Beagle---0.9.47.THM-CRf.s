%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:58 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 269 expanded)
%              Number of leaves         :   23 ( 108 expanded)
%              Depth                    :   14
%              Number of atoms          :  192 (1221 expanded)
%              Number of equality atoms :   59 ( 444 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_112,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_85,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k1_relat_1(B)) )
       => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
          & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

tff(c_22,plain,(
    k2_funct_1('#skF_2') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_34,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_10,plain,(
    ! [A_3] :
      ( v1_relat_1(k2_funct_1(A_3))
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    k2_relat_1('#skF_2') = k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_28,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_70,plain,(
    ! [A_28] :
      ( k4_relat_1(A_28) = k2_funct_1(A_28)
      | ~ v2_funct_1(A_28)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_73,plain,
    ( k4_relat_1('#skF_2') = k2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_70])).

tff(c_76,plain,(
    k4_relat_1('#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_73])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_relat_1(k4_relat_1(A_1)) = k2_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_80,plain,
    ( k1_relat_1(k2_funct_1('#skF_2')) = k2_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_4])).

tff(c_87,plain,(
    k1_relat_1(k2_funct_1('#skF_2')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_24,c_80])).

tff(c_2,plain,(
    ! [A_1] :
      ( k2_relat_1(k4_relat_1(A_1)) = k1_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_83,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_2])).

tff(c_89,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_83])).

tff(c_12,plain,(
    ! [B_5,A_4] :
      ( r2_hidden(k1_funct_1(B_5,A_4),k2_relat_1(B_5))
      | ~ r2_hidden(A_4,k1_relat_1(B_5))
      | ~ v1_funct_1(B_5)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_112,plain,(
    ! [A_4] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_2'),A_4),k1_relat_1('#skF_2'))
      | ~ r2_hidden(A_4,k1_relat_1(k2_funct_1('#skF_2')))
      | ~ v1_funct_1(k2_funct_1('#skF_2'))
      | ~ v1_relat_1(k2_funct_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_12])).

tff(c_115,plain,(
    ! [A_4] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_2'),A_4),k1_relat_1('#skF_2'))
      | ~ r2_hidden(A_4,k1_relat_1('#skF_3'))
      | ~ v1_funct_1(k2_funct_1('#skF_2'))
      | ~ v1_relat_1(k2_funct_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_112])).

tff(c_239,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_242,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_239])).

tff(c_246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_242])).

tff(c_248,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_8,plain,(
    ! [A_3] :
      ( v1_funct_1(k2_funct_1(A_3))
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_247,plain,(
    ! [A_4] :
      ( ~ v1_funct_1(k2_funct_1('#skF_2'))
      | r2_hidden(k1_funct_1(k2_funct_1('#skF_2'),A_4),k1_relat_1('#skF_2'))
      | ~ r2_hidden(A_4,k1_relat_1('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_260,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_247])).

tff(c_263,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_260])).

tff(c_267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_263])).

tff(c_269,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_247])).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_20,plain,(
    ! [A_8,B_12] :
      ( r2_hidden('#skF_1'(A_8,B_12),k1_relat_1(A_8))
      | B_12 = A_8
      | k1_relat_1(B_12) != k1_relat_1(A_8)
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_26,plain,(
    k2_relat_1('#skF_3') = k1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_91,plain,(
    ! [B_29,A_30] :
      ( r2_hidden(k1_funct_1(B_29,A_30),k2_relat_1(B_29))
      | ~ r2_hidden(A_30,k1_relat_1(B_29))
      | ~ v1_funct_1(B_29)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_97,plain,(
    ! [A_30] :
      ( r2_hidden(k1_funct_1('#skF_3',A_30),k1_relat_1('#skF_2'))
      | ~ r2_hidden(A_30,k1_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_91])).

tff(c_102,plain,(
    ! [A_30] :
      ( r2_hidden(k1_funct_1('#skF_3',A_30),k1_relat_1('#skF_2'))
      | ~ r2_hidden(A_30,k1_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_97])).

tff(c_281,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_1'(A_44,B_45),k1_relat_1(A_44))
      | B_45 = A_44
      | k1_relat_1(B_45) != k1_relat_1(A_44)
      | ~ v1_funct_1(B_45)
      | ~ v1_relat_1(B_45)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_118,plain,(
    ! [D_32] :
      ( k1_funct_1('#skF_2',k1_funct_1('#skF_3',D_32)) = D_32
      | ~ r2_hidden(D_32,k1_relat_1('#skF_3'))
      | ~ r2_hidden(k1_funct_1('#skF_3',D_32),k1_relat_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_122,plain,(
    ! [A_30] :
      ( k1_funct_1('#skF_2',k1_funct_1('#skF_3',A_30)) = A_30
      | ~ r2_hidden(A_30,k1_relat_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_102,c_118])).

tff(c_289,plain,(
    ! [B_45] :
      ( k1_funct_1('#skF_2',k1_funct_1('#skF_3','#skF_1'('#skF_3',B_45))) = '#skF_1'('#skF_3',B_45)
      | B_45 = '#skF_3'
      | k1_relat_1(B_45) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_45)
      | ~ v1_relat_1(B_45)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_281,c_122])).

tff(c_442,plain,(
    ! [B_52] :
      ( k1_funct_1('#skF_2',k1_funct_1('#skF_3','#skF_1'('#skF_3',B_52))) = '#skF_1'('#skF_3',B_52)
      | B_52 = '#skF_3'
      | k1_relat_1(B_52) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_52)
      | ~ v1_relat_1(B_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_289])).

tff(c_16,plain,(
    ! [B_7,A_6] :
      ( k1_funct_1(k2_funct_1(B_7),k1_funct_1(B_7,A_6)) = A_6
      | ~ r2_hidden(A_6,k1_relat_1(B_7))
      | ~ v2_funct_1(B_7)
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_451,plain,(
    ! [B_52] :
      ( k1_funct_1(k2_funct_1('#skF_2'),'#skF_1'('#skF_3',B_52)) = k1_funct_1('#skF_3','#skF_1'('#skF_3',B_52))
      | ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'('#skF_3',B_52)),k1_relat_1('#skF_2'))
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | B_52 = '#skF_3'
      | k1_relat_1(B_52) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_52)
      | ~ v1_relat_1(B_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_16])).

tff(c_749,plain,(
    ! [B_67] :
      ( k1_funct_1(k2_funct_1('#skF_2'),'#skF_1'('#skF_3',B_67)) = k1_funct_1('#skF_3','#skF_1'('#skF_3',B_67))
      | ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'('#skF_3',B_67)),k1_relat_1('#skF_2'))
      | B_67 = '#skF_3'
      | k1_relat_1(B_67) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_67)
      | ~ v1_relat_1(B_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_28,c_451])).

tff(c_806,plain,(
    ! [B_70] :
      ( k1_funct_1(k2_funct_1('#skF_2'),'#skF_1'('#skF_3',B_70)) = k1_funct_1('#skF_3','#skF_1'('#skF_3',B_70))
      | B_70 = '#skF_3'
      | k1_relat_1(B_70) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_70)
      | ~ v1_relat_1(B_70)
      | ~ r2_hidden('#skF_1'('#skF_3',B_70),k1_relat_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_102,c_749])).

tff(c_810,plain,(
    ! [B_12] :
      ( k1_funct_1(k2_funct_1('#skF_2'),'#skF_1'('#skF_3',B_12)) = k1_funct_1('#skF_3','#skF_1'('#skF_3',B_12))
      | B_12 = '#skF_3'
      | k1_relat_1(B_12) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_806])).

tff(c_814,plain,(
    ! [B_71] :
      ( k1_funct_1(k2_funct_1('#skF_2'),'#skF_1'('#skF_3',B_71)) = k1_funct_1('#skF_3','#skF_1'('#skF_3',B_71))
      | B_71 = '#skF_3'
      | k1_relat_1(B_71) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_71)
      | ~ v1_relat_1(B_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_810])).

tff(c_18,plain,(
    ! [B_12,A_8] :
      ( k1_funct_1(B_12,'#skF_1'(A_8,B_12)) != k1_funct_1(A_8,'#skF_1'(A_8,B_12))
      | B_12 = A_8
      | k1_relat_1(B_12) != k1_relat_1(A_8)
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_827,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | k2_funct_1('#skF_2') = '#skF_3'
    | k1_relat_1(k2_funct_1('#skF_2')) != k1_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_814,c_18])).

tff(c_850,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_269,c_87,c_32,c_30,c_827])).

tff(c_852,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_850])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:49:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.65  
% 3.27/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.65  %$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.27/1.65  
% 3.27/1.65  %Foreground sorts:
% 3.27/1.65  
% 3.27/1.65  
% 3.27/1.65  %Background operators:
% 3.27/1.65  
% 3.27/1.65  
% 3.27/1.65  %Foreground operators:
% 3.27/1.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.27/1.65  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.27/1.65  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.27/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.27/1.65  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.27/1.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.27/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.27/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.27/1.65  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.27/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.27/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.65  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.27/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.27/1.65  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.27/1.65  
% 3.27/1.66  tff(f_112, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((((v2_funct_1(A) & (k1_relat_1(A) = k2_relat_1(B))) & (k2_relat_1(A) = k1_relat_1(B))) & (![C, D]: ((r2_hidden(C, k1_relat_1(A)) & r2_hidden(D, k1_relat_1(B))) => ((k1_funct_1(A, C) = D) <=> (k1_funct_1(B, D) = C))))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_1)).
% 3.27/1.66  tff(f_47, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.27/1.66  tff(f_39, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 3.27/1.66  tff(f_31, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 3.27/1.66  tff(f_55, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 3.27/1.66  tff(f_85, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 3.27/1.66  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_funct_1)).
% 3.27/1.66  tff(c_22, plain, (k2_funct_1('#skF_2')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.27/1.66  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.27/1.66  tff(c_34, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.27/1.66  tff(c_10, plain, (![A_3]: (v1_relat_1(k2_funct_1(A_3)) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.27/1.66  tff(c_24, plain, (k2_relat_1('#skF_2')=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.27/1.66  tff(c_28, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.27/1.66  tff(c_70, plain, (![A_28]: (k4_relat_1(A_28)=k2_funct_1(A_28) | ~v2_funct_1(A_28) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.27/1.66  tff(c_73, plain, (k4_relat_1('#skF_2')=k2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_28, c_70])).
% 3.27/1.66  tff(c_76, plain, (k4_relat_1('#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_73])).
% 3.27/1.66  tff(c_4, plain, (![A_1]: (k1_relat_1(k4_relat_1(A_1))=k2_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.27/1.66  tff(c_80, plain, (k1_relat_1(k2_funct_1('#skF_2'))=k2_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_76, c_4])).
% 3.27/1.66  tff(c_87, plain, (k1_relat_1(k2_funct_1('#skF_2'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_24, c_80])).
% 3.27/1.66  tff(c_2, plain, (![A_1]: (k2_relat_1(k4_relat_1(A_1))=k1_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.27/1.66  tff(c_83, plain, (k2_relat_1(k2_funct_1('#skF_2'))=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_76, c_2])).
% 3.27/1.66  tff(c_89, plain, (k2_relat_1(k2_funct_1('#skF_2'))=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_83])).
% 3.27/1.66  tff(c_12, plain, (![B_5, A_4]: (r2_hidden(k1_funct_1(B_5, A_4), k2_relat_1(B_5)) | ~r2_hidden(A_4, k1_relat_1(B_5)) | ~v1_funct_1(B_5) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.27/1.66  tff(c_112, plain, (![A_4]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_2'), A_4), k1_relat_1('#skF_2')) | ~r2_hidden(A_4, k1_relat_1(k2_funct_1('#skF_2'))) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_89, c_12])).
% 3.27/1.66  tff(c_115, plain, (![A_4]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_2'), A_4), k1_relat_1('#skF_2')) | ~r2_hidden(A_4, k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_112])).
% 3.27/1.66  tff(c_239, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_115])).
% 3.27/1.66  tff(c_242, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10, c_239])).
% 3.27/1.66  tff(c_246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_242])).
% 3.27/1.66  tff(c_248, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_115])).
% 3.27/1.66  tff(c_8, plain, (![A_3]: (v1_funct_1(k2_funct_1(A_3)) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.27/1.66  tff(c_247, plain, (![A_4]: (~v1_funct_1(k2_funct_1('#skF_2')) | r2_hidden(k1_funct_1(k2_funct_1('#skF_2'), A_4), k1_relat_1('#skF_2')) | ~r2_hidden(A_4, k1_relat_1('#skF_3')))), inference(splitRight, [status(thm)], [c_115])).
% 3.27/1.66  tff(c_260, plain, (~v1_funct_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_247])).
% 3.27/1.66  tff(c_263, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_260])).
% 3.27/1.66  tff(c_267, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_263])).
% 3.27/1.66  tff(c_269, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_247])).
% 3.27/1.66  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.27/1.66  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.27/1.66  tff(c_20, plain, (![A_8, B_12]: (r2_hidden('#skF_1'(A_8, B_12), k1_relat_1(A_8)) | B_12=A_8 | k1_relat_1(B_12)!=k1_relat_1(A_8) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.27/1.66  tff(c_26, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.27/1.66  tff(c_91, plain, (![B_29, A_30]: (r2_hidden(k1_funct_1(B_29, A_30), k2_relat_1(B_29)) | ~r2_hidden(A_30, k1_relat_1(B_29)) | ~v1_funct_1(B_29) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.27/1.66  tff(c_97, plain, (![A_30]: (r2_hidden(k1_funct_1('#skF_3', A_30), k1_relat_1('#skF_2')) | ~r2_hidden(A_30, k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_26, c_91])).
% 3.27/1.66  tff(c_102, plain, (![A_30]: (r2_hidden(k1_funct_1('#skF_3', A_30), k1_relat_1('#skF_2')) | ~r2_hidden(A_30, k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_97])).
% 3.27/1.66  tff(c_281, plain, (![A_44, B_45]: (r2_hidden('#skF_1'(A_44, B_45), k1_relat_1(A_44)) | B_45=A_44 | k1_relat_1(B_45)!=k1_relat_1(A_44) | ~v1_funct_1(B_45) | ~v1_relat_1(B_45) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.27/1.66  tff(c_118, plain, (![D_32]: (k1_funct_1('#skF_2', k1_funct_1('#skF_3', D_32))=D_32 | ~r2_hidden(D_32, k1_relat_1('#skF_3')) | ~r2_hidden(k1_funct_1('#skF_3', D_32), k1_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.27/1.66  tff(c_122, plain, (![A_30]: (k1_funct_1('#skF_2', k1_funct_1('#skF_3', A_30))=A_30 | ~r2_hidden(A_30, k1_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_102, c_118])).
% 3.27/1.66  tff(c_289, plain, (![B_45]: (k1_funct_1('#skF_2', k1_funct_1('#skF_3', '#skF_1'('#skF_3', B_45)))='#skF_1'('#skF_3', B_45) | B_45='#skF_3' | k1_relat_1(B_45)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_45) | ~v1_relat_1(B_45) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_281, c_122])).
% 3.27/1.66  tff(c_442, plain, (![B_52]: (k1_funct_1('#skF_2', k1_funct_1('#skF_3', '#skF_1'('#skF_3', B_52)))='#skF_1'('#skF_3', B_52) | B_52='#skF_3' | k1_relat_1(B_52)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_52) | ~v1_relat_1(B_52))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_289])).
% 3.27/1.66  tff(c_16, plain, (![B_7, A_6]: (k1_funct_1(k2_funct_1(B_7), k1_funct_1(B_7, A_6))=A_6 | ~r2_hidden(A_6, k1_relat_1(B_7)) | ~v2_funct_1(B_7) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.27/1.66  tff(c_451, plain, (![B_52]: (k1_funct_1(k2_funct_1('#skF_2'), '#skF_1'('#skF_3', B_52))=k1_funct_1('#skF_3', '#skF_1'('#skF_3', B_52)) | ~r2_hidden(k1_funct_1('#skF_3', '#skF_1'('#skF_3', B_52)), k1_relat_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | B_52='#skF_3' | k1_relat_1(B_52)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_52) | ~v1_relat_1(B_52))), inference(superposition, [status(thm), theory('equality')], [c_442, c_16])).
% 3.27/1.66  tff(c_749, plain, (![B_67]: (k1_funct_1(k2_funct_1('#skF_2'), '#skF_1'('#skF_3', B_67))=k1_funct_1('#skF_3', '#skF_1'('#skF_3', B_67)) | ~r2_hidden(k1_funct_1('#skF_3', '#skF_1'('#skF_3', B_67)), k1_relat_1('#skF_2')) | B_67='#skF_3' | k1_relat_1(B_67)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_67) | ~v1_relat_1(B_67))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_28, c_451])).
% 3.27/1.66  tff(c_806, plain, (![B_70]: (k1_funct_1(k2_funct_1('#skF_2'), '#skF_1'('#skF_3', B_70))=k1_funct_1('#skF_3', '#skF_1'('#skF_3', B_70)) | B_70='#skF_3' | k1_relat_1(B_70)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_70) | ~v1_relat_1(B_70) | ~r2_hidden('#skF_1'('#skF_3', B_70), k1_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_102, c_749])).
% 3.27/1.66  tff(c_810, plain, (![B_12]: (k1_funct_1(k2_funct_1('#skF_2'), '#skF_1'('#skF_3', B_12))=k1_funct_1('#skF_3', '#skF_1'('#skF_3', B_12)) | B_12='#skF_3' | k1_relat_1(B_12)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_806])).
% 3.27/1.66  tff(c_814, plain, (![B_71]: (k1_funct_1(k2_funct_1('#skF_2'), '#skF_1'('#skF_3', B_71))=k1_funct_1('#skF_3', '#skF_1'('#skF_3', B_71)) | B_71='#skF_3' | k1_relat_1(B_71)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_71) | ~v1_relat_1(B_71))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_810])).
% 3.27/1.66  tff(c_18, plain, (![B_12, A_8]: (k1_funct_1(B_12, '#skF_1'(A_8, B_12))!=k1_funct_1(A_8, '#skF_1'(A_8, B_12)) | B_12=A_8 | k1_relat_1(B_12)!=k1_relat_1(A_8) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.27/1.66  tff(c_827, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | k2_funct_1('#skF_2')='#skF_3' | k1_relat_1(k2_funct_1('#skF_2'))!=k1_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_814, c_18])).
% 3.27/1.66  tff(c_850, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_248, c_269, c_87, c_32, c_30, c_827])).
% 3.27/1.66  tff(c_852, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_850])).
% 3.27/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.66  
% 3.27/1.66  Inference rules
% 3.27/1.66  ----------------------
% 3.27/1.66  #Ref     : 1
% 3.27/1.66  #Sup     : 188
% 3.27/1.66  #Fact    : 0
% 3.27/1.66  #Define  : 0
% 3.27/1.66  #Split   : 6
% 3.27/1.66  #Chain   : 0
% 3.27/1.66  #Close   : 0
% 3.27/1.66  
% 3.27/1.66  Ordering : KBO
% 3.27/1.66  
% 3.27/1.66  Simplification rules
% 3.27/1.66  ----------------------
% 3.27/1.66  #Subsume      : 64
% 3.27/1.66  #Demod        : 217
% 3.27/1.66  #Tautology    : 54
% 3.27/1.66  #SimpNegUnit  : 1
% 3.27/1.66  #BackRed      : 0
% 3.27/1.66  
% 3.27/1.66  #Partial instantiations: 0
% 3.27/1.66  #Strategies tried      : 1
% 3.27/1.66  
% 3.27/1.66  Timing (in seconds)
% 3.27/1.66  ----------------------
% 3.27/1.67  Preprocessing        : 0.45
% 3.27/1.67  Parsing              : 0.23
% 3.27/1.67  CNF conversion       : 0.03
% 3.27/1.67  Main loop            : 0.43
% 3.27/1.67  Inferencing          : 0.16
% 3.27/1.67  Reduction            : 0.13
% 3.27/1.67  Demodulation         : 0.09
% 3.27/1.67  BG Simplification    : 0.03
% 3.27/1.67  Subsumption          : 0.09
% 3.27/1.67  Abstraction          : 0.03
% 3.27/1.67  MUC search           : 0.00
% 3.27/1.67  Cooper               : 0.00
% 3.27/1.67  Total                : 0.92
% 3.27/1.67  Index Insertion      : 0.00
% 3.27/1.67  Index Deletion       : 0.00
% 3.27/1.67  Index Matching       : 0.00
% 3.27/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
