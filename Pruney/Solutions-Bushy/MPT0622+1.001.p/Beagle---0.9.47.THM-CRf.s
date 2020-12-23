%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0622+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:36 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :   52 (  98 expanded)
%              Number of leaves         :   24 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  113 ( 351 expanded)
%              Number of equality atoms :   46 ( 155 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_6 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ( ( k1_relat_1(B) = k1_relat_1(C)
                & k2_relat_1(B) = k1_tarski(A)
                & k2_relat_1(C) = k1_tarski(A) )
             => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_1)).

tff(f_64,axiom,(
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

tff(f_46,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_36,plain,(
    '#skF_10' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_46,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_44,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_42,plain,(
    k1_relat_1('#skF_10') = k1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_50,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_48,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_541,plain,(
    ! [A_99,B_100] :
      ( r2_hidden('#skF_7'(A_99,B_100),k1_relat_1(A_99))
      | B_100 = A_99
      | k1_relat_1(B_100) != k1_relat_1(A_99)
      | ~ v1_funct_1(B_100)
      | ~ v1_relat_1(B_100)
      | ~ v1_funct_1(A_99)
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_40,plain,(
    k2_relat_1('#skF_9') = k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_84,plain,(
    ! [A_64,D_65] :
      ( r2_hidden(k1_funct_1(A_64,D_65),k2_relat_1(A_64))
      | ~ r2_hidden(D_65,k1_relat_1(A_64))
      | ~ v1_funct_1(A_64)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_87,plain,(
    ! [D_65] :
      ( r2_hidden(k1_funct_1('#skF_9',D_65),k1_tarski('#skF_8'))
      | ~ r2_hidden(D_65,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_84])).

tff(c_111,plain,(
    ! [D_68] :
      ( r2_hidden(k1_funct_1('#skF_9',D_68),k1_tarski('#skF_8'))
      | ~ r2_hidden(D_68,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_87])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_115,plain,(
    ! [D_68] :
      ( k1_funct_1('#skF_9',D_68) = '#skF_8'
      | ~ r2_hidden(D_68,k1_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_111,c_2])).

tff(c_549,plain,(
    ! [B_100] :
      ( k1_funct_1('#skF_9','#skF_7'('#skF_9',B_100)) = '#skF_8'
      | B_100 = '#skF_9'
      | k1_relat_1(B_100) != k1_relat_1('#skF_9')
      | ~ v1_funct_1(B_100)
      | ~ v1_relat_1(B_100)
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_541,c_115])).

tff(c_558,plain,(
    ! [B_100] :
      ( k1_funct_1('#skF_9','#skF_7'('#skF_9',B_100)) = '#skF_8'
      | B_100 = '#skF_9'
      | k1_relat_1(B_100) != k1_relat_1('#skF_9')
      | ~ v1_funct_1(B_100)
      | ~ v1_relat_1(B_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_549])).

tff(c_38,plain,(
    k2_relat_1('#skF_10') = k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_90,plain,(
    ! [D_65] :
      ( r2_hidden(k1_funct_1('#skF_10',D_65),k1_tarski('#skF_8'))
      | ~ r2_hidden(D_65,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_84])).

tff(c_134,plain,(
    ! [D_70] :
      ( r2_hidden(k1_funct_1('#skF_10',D_70),k1_tarski('#skF_8'))
      | ~ r2_hidden(D_70,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_90])).

tff(c_138,plain,(
    ! [D_70] :
      ( k1_funct_1('#skF_10',D_70) = '#skF_8'
      | ~ r2_hidden(D_70,k1_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_134,c_2])).

tff(c_545,plain,(
    ! [B_100] :
      ( k1_funct_1('#skF_10','#skF_7'('#skF_9',B_100)) = '#skF_8'
      | B_100 = '#skF_9'
      | k1_relat_1(B_100) != k1_relat_1('#skF_9')
      | ~ v1_funct_1(B_100)
      | ~ v1_relat_1(B_100)
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_541,c_138])).

tff(c_555,plain,(
    ! [B_100] :
      ( k1_funct_1('#skF_10','#skF_7'('#skF_9',B_100)) = '#skF_8'
      | B_100 = '#skF_9'
      | k1_relat_1(B_100) != k1_relat_1('#skF_9')
      | ~ v1_funct_1(B_100)
      | ~ v1_relat_1(B_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_545])).

tff(c_1475,plain,(
    ! [B_130,A_131] :
      ( k1_funct_1(B_130,'#skF_7'(A_131,B_130)) != k1_funct_1(A_131,'#skF_7'(A_131,B_130))
      | B_130 = A_131
      | k1_relat_1(B_130) != k1_relat_1(A_131)
      | ~ v1_funct_1(B_130)
      | ~ v1_relat_1(B_130)
      | ~ v1_funct_1(A_131)
      | ~ v1_relat_1(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1479,plain,
    ( k1_funct_1('#skF_9','#skF_7'('#skF_9','#skF_10')) != '#skF_8'
    | '#skF_10' = '#skF_9'
    | k1_relat_1('#skF_10') != k1_relat_1('#skF_9')
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9')
    | '#skF_10' = '#skF_9'
    | k1_relat_1('#skF_10') != k1_relat_1('#skF_9')
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_555,c_1475])).

tff(c_1487,plain,
    ( k1_funct_1('#skF_9','#skF_7'('#skF_9','#skF_10')) != '#skF_8'
    | '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_50,c_48,c_46,c_44,c_42,c_1479])).

tff(c_1488,plain,(
    k1_funct_1('#skF_9','#skF_7'('#skF_9','#skF_10')) != '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1487])).

tff(c_1495,plain,
    ( '#skF_10' = '#skF_9'
    | k1_relat_1('#skF_10') != k1_relat_1('#skF_9')
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_1488])).

tff(c_1498,plain,(
    '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_1495])).

tff(c_1500,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1498])).

%------------------------------------------------------------------------------
