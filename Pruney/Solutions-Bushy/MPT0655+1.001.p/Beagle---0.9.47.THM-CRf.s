%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0655+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:39 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 216 expanded)
%              Number of leaves         :   24 (  87 expanded)
%              Depth                    :   12
%              Number of atoms          :  151 ( 698 expanded)
%              Number of equality atoms :   25 ( 124 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_6 > #skF_2 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).

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
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( B = k2_funct_1(A)
            <=> ( k1_relat_1(B) = k2_relat_1(A)
                & ! [C,D] :
                    ( ( ( r2_hidden(C,k2_relat_1(A))
                        & D = k1_funct_1(B,C) )
                     => ( r2_hidden(D,k1_relat_1(A))
                        & C = k1_funct_1(A,D) ) )
                    & ( ( r2_hidden(D,k1_relat_1(A))
                        & C = k1_funct_1(A,D) )
                     => ( r2_hidden(C,k2_relat_1(A))
                        & D = k1_funct_1(B,C) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_funct_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k2_relat_1(B)) )
       => ( A = k1_funct_1(B,k1_funct_1(k2_funct_1(B),A))
          & A = k1_funct_1(k5_relat_1(k2_funct_1(B),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).

tff(c_54,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_52,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_12,plain,(
    ! [A_8] :
      ( v1_funct_1(k2_funct_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_48,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_14,plain,(
    ! [A_8] :
      ( v1_relat_1(k2_funct_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_57,plain,(
    ! [A_30] :
      ( '#skF_2'(A_30) != '#skF_1'(A_30)
      | v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_61,plain,
    ( '#skF_2'(k2_funct_1('#skF_7')) != '#skF_1'(k2_funct_1('#skF_7'))
    | ~ v1_funct_1(k2_funct_1('#skF_7'))
    | ~ v1_relat_1(k2_funct_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_57,c_48])).

tff(c_64,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_67,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_14,c_64])).

tff(c_71,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_67])).

tff(c_72,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_7'))
    | '#skF_2'(k2_funct_1('#skF_7')) != '#skF_1'(k2_funct_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_74,plain,(
    '#skF_2'(k2_funct_1('#skF_7')) != '#skF_1'(k2_funct_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_73,plain,(
    v1_relat_1(k2_funct_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_50,plain,(
    v2_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_84,plain,(
    ! [A_34] :
      ( k1_relat_1(k2_funct_1(A_34)) = k2_relat_1(A_34)
      | ~ v1_funct_1(k2_funct_1(A_34))
      | ~ v1_relat_1(k2_funct_1(A_34))
      | ~ v2_funct_1(A_34)
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_87,plain,
    ( k1_relat_1(k2_funct_1('#skF_7')) = k2_relat_1('#skF_7')
    | ~ v1_funct_1(k2_funct_1('#skF_7'))
    | ~ v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_73,c_84])).

tff(c_93,plain,
    ( k1_relat_1(k2_funct_1('#skF_7')) = k2_relat_1('#skF_7')
    | ~ v1_funct_1(k2_funct_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_87])).

tff(c_95,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_98,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_12,c_95])).

tff(c_102,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_98])).

tff(c_104,plain,(
    v1_funct_1(k2_funct_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_103,plain,(
    k1_relat_1(k2_funct_1('#skF_7')) = k2_relat_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_10,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),k1_relat_1(A_1))
      | v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_111,plain,
    ( r2_hidden('#skF_1'(k2_funct_1('#skF_7')),k2_relat_1('#skF_7'))
    | v2_funct_1(k2_funct_1('#skF_7'))
    | ~ v1_funct_1(k2_funct_1('#skF_7'))
    | ~ v1_relat_1(k2_funct_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_10])).

tff(c_118,plain,
    ( r2_hidden('#skF_1'(k2_funct_1('#skF_7')),k2_relat_1('#skF_7'))
    | v2_funct_1(k2_funct_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_104,c_111])).

tff(c_119,plain,(
    r2_hidden('#skF_1'(k2_funct_1('#skF_7')),k2_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_118])).

tff(c_8,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_2'(A_1),k1_relat_1(A_1))
      | v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_108,plain,
    ( r2_hidden('#skF_2'(k2_funct_1('#skF_7')),k2_relat_1('#skF_7'))
    | v2_funct_1(k2_funct_1('#skF_7'))
    | ~ v1_funct_1(k2_funct_1('#skF_7'))
    | ~ v1_relat_1(k2_funct_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_8])).

tff(c_115,plain,
    ( r2_hidden('#skF_2'(k2_funct_1('#skF_7')),k2_relat_1('#skF_7'))
    | v2_funct_1(k2_funct_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_104,c_108])).

tff(c_116,plain,(
    r2_hidden('#skF_2'(k2_funct_1('#skF_7')),k2_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_115])).

tff(c_6,plain,(
    ! [A_1] :
      ( k1_funct_1(A_1,'#skF_2'(A_1)) = k1_funct_1(A_1,'#skF_1'(A_1))
      | v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_159,plain,(
    ! [B_37,A_38] :
      ( k1_funct_1(B_37,k1_funct_1(k2_funct_1(B_37),A_38)) = A_38
      | ~ r2_hidden(A_38,k2_relat_1(B_37))
      | ~ v2_funct_1(B_37)
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_412,plain,(
    ! [B_60] :
      ( k1_funct_1(B_60,k1_funct_1(k2_funct_1(B_60),'#skF_1'(k2_funct_1(B_60)))) = '#skF_2'(k2_funct_1(B_60))
      | ~ r2_hidden('#skF_2'(k2_funct_1(B_60)),k2_relat_1(B_60))
      | ~ v2_funct_1(B_60)
      | ~ v1_funct_1(B_60)
      | ~ v1_relat_1(B_60)
      | v2_funct_1(k2_funct_1(B_60))
      | ~ v1_funct_1(k2_funct_1(B_60))
      | ~ v1_relat_1(k2_funct_1(B_60)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_159])).

tff(c_46,plain,(
    ! [B_27,A_26] :
      ( k1_funct_1(B_27,k1_funct_1(k2_funct_1(B_27),A_26)) = A_26
      | ~ r2_hidden(A_26,k2_relat_1(B_27))
      | ~ v2_funct_1(B_27)
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_771,plain,(
    ! [B_89] :
      ( '#skF_2'(k2_funct_1(B_89)) = '#skF_1'(k2_funct_1(B_89))
      | ~ r2_hidden('#skF_1'(k2_funct_1(B_89)),k2_relat_1(B_89))
      | ~ v2_funct_1(B_89)
      | ~ v1_funct_1(B_89)
      | ~ v1_relat_1(B_89)
      | ~ r2_hidden('#skF_2'(k2_funct_1(B_89)),k2_relat_1(B_89))
      | ~ v2_funct_1(B_89)
      | ~ v1_funct_1(B_89)
      | ~ v1_relat_1(B_89)
      | v2_funct_1(k2_funct_1(B_89))
      | ~ v1_funct_1(k2_funct_1(B_89))
      | ~ v1_relat_1(k2_funct_1(B_89)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_46])).

tff(c_777,plain,
    ( '#skF_2'(k2_funct_1('#skF_7')) = '#skF_1'(k2_funct_1('#skF_7'))
    | ~ r2_hidden('#skF_1'(k2_funct_1('#skF_7')),k2_relat_1('#skF_7'))
    | ~ v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | v2_funct_1(k2_funct_1('#skF_7'))
    | ~ v1_funct_1(k2_funct_1('#skF_7'))
    | ~ v1_relat_1(k2_funct_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_116,c_771])).

tff(c_781,plain,
    ( '#skF_2'(k2_funct_1('#skF_7')) = '#skF_1'(k2_funct_1('#skF_7'))
    | v2_funct_1(k2_funct_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_104,c_54,c_52,c_50,c_119,c_777])).

tff(c_783,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_74,c_781])).

tff(c_784,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_797,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_12,c_784])).

tff(c_801,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_797])).

%------------------------------------------------------------------------------
