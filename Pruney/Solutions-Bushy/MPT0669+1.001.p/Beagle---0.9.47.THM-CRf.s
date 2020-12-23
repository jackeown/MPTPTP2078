%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0669+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:40 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 169 expanded)
%              Number of leaves         :   19 (  66 expanded)
%              Depth                    :    8
%              Number of atoms          :  110 ( 480 expanded)
%              Number of equality atoms :    2 (  12 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k8_relat_1 > k1_funct_1 > #nlpp > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k1_relat_1(k8_relat_1(B,C)))
        <=> ( r2_hidden(A,k1_relat_1(C))
            & r2_hidden(k1_funct_1(C,A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_funct_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k8_relat_1(A,B))
        & v1_funct_1(k8_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_funct_1)).

tff(f_28,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( B = k8_relat_1(A,C)
          <=> ( ! [D] :
                  ( r2_hidden(D,k1_relat_1(B))
                <=> ( r2_hidden(D,k1_relat_1(C))
                    & r2_hidden(k1_funct_1(C,D),A) ) )
              & ! [D] :
                  ( r2_hidden(D,k1_relat_1(B))
                 => k1_funct_1(B,D) = k1_funct_1(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_40,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( v1_funct_1(k8_relat_1(A_3,B_4))
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k8_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_54,plain,
    ( r2_hidden('#skF_4',k1_relat_1(k8_relat_1('#skF_5','#skF_6')))
    | r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_57,plain,(
    r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_50,plain,
    ( r2_hidden('#skF_4',k1_relat_1(k8_relat_1('#skF_5','#skF_6')))
    | r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_58,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_64,plain,(
    ! [D_36,A_37,C_38] :
      ( r2_hidden(D_36,k1_relat_1(k8_relat_1(A_37,C_38)))
      | ~ r2_hidden(k1_funct_1(C_38,D_36),A_37)
      | ~ r2_hidden(D_36,k1_relat_1(C_38))
      | ~ v1_funct_1(C_38)
      | ~ v1_relat_1(C_38)
      | ~ v1_funct_1(k8_relat_1(A_37,C_38))
      | ~ v1_relat_1(k8_relat_1(A_37,C_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_44,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5')
    | ~ r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | ~ r2_hidden('#skF_4',k1_relat_1(k8_relat_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_60,plain,(
    ~ r2_hidden('#skF_4',k1_relat_1(k8_relat_1('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_58,c_44])).

tff(c_76,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5')
    | ~ r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_64,c_60])).

tff(c_82,plain,
    ( ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_57,c_58,c_76])).

tff(c_83,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_86,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_83])).

tff(c_90,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_86])).

tff(c_91,plain,(
    ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_126,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_91])).

tff(c_130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_126])).

tff(c_132,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_131,plain,(
    r2_hidden('#skF_4',k1_relat_1(k8_relat_1('#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_142,plain,(
    ! [C_45,D_46,A_47] :
      ( r2_hidden(k1_funct_1(C_45,D_46),A_47)
      | ~ r2_hidden(D_46,k1_relat_1(k8_relat_1(A_47,C_45)))
      | ~ v1_funct_1(C_45)
      | ~ v1_relat_1(C_45)
      | ~ v1_funct_1(k8_relat_1(A_47,C_45))
      | ~ v1_relat_1(k8_relat_1(A_47,C_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_145,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_131,c_142])).

tff(c_148,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5')
    | ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_145])).

tff(c_149,plain,
    ( ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_148])).

tff(c_150,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_149])).

tff(c_153,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_150])).

tff(c_157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_153])).

tff(c_158,plain,(
    ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_149])).

tff(c_169,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_158])).

tff(c_173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_169])).

tff(c_175,plain,(
    ~ r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_174,plain,(
    r2_hidden('#skF_4',k1_relat_1(k8_relat_1('#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_179,plain,(
    ! [D_51,C_52,A_53] :
      ( r2_hidden(D_51,k1_relat_1(C_52))
      | ~ r2_hidden(D_51,k1_relat_1(k8_relat_1(A_53,C_52)))
      | ~ v1_funct_1(C_52)
      | ~ v1_relat_1(C_52)
      | ~ v1_funct_1(k8_relat_1(A_53,C_52))
      | ~ v1_relat_1(k8_relat_1(A_53,C_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_182,plain,
    ( r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_174,c_179])).

tff(c_185,plain,
    ( r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_182])).

tff(c_186,plain,
    ( ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_175,c_185])).

tff(c_187,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_197,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_187])).

tff(c_201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_197])).

tff(c_202,plain,(
    ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_206,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_202])).

tff(c_210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_206])).

%------------------------------------------------------------------------------
