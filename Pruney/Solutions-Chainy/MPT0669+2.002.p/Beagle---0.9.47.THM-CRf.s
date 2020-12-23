%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:19 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 202 expanded)
%              Number of leaves         :   23 (  78 expanded)
%              Depth                    :    9
%              Number of atoms          :  163 ( 565 expanded)
%              Number of equality atoms :    4 (  18 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k8_relat_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k1_relat_1(k8_relat_1(B,C)))
        <=> ( r2_hidden(A,k1_relat_1(C))
            & r2_hidden(k1_funct_1(C,A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_funct_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_72,axiom,(
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

tff(c_48,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_46,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_10,plain,(
    ! [A_7] : v1_relat_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [A_7] : v1_funct_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( k5_relat_1(B_4,k6_relat_1(A_3)) = k8_relat_1(A_3,B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_199,plain,(
    ! [A_67,B_68] :
      ( v1_funct_1(k5_relat_1(A_67,B_68))
      | ~ v1_funct_1(B_68)
      | ~ v1_relat_1(B_68)
      | ~ v1_funct_1(A_67)
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_202,plain,(
    ! [A_3,B_4] :
      ( v1_funct_1(k8_relat_1(A_3,B_4))
      | ~ v1_funct_1(k6_relat_1(A_3))
      | ~ v1_relat_1(k6_relat_1(A_3))
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_199])).

tff(c_204,plain,(
    ! [A_3,B_4] :
      ( v1_funct_1(k8_relat_1(A_3,B_4))
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12,c_202])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k8_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_136,plain,(
    ! [A_50,B_51] :
      ( v1_funct_1(k5_relat_1(A_50,B_51))
      | ~ v1_funct_1(B_51)
      | ~ v1_relat_1(B_51)
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_139,plain,(
    ! [A_3,B_4] :
      ( v1_funct_1(k8_relat_1(A_3,B_4))
      | ~ v1_funct_1(k6_relat_1(A_3))
      | ~ v1_relat_1(k6_relat_1(A_3))
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_136])).

tff(c_141,plain,(
    ! [A_3,B_4] :
      ( v1_funct_1(k8_relat_1(A_3,B_4))
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12,c_139])).

tff(c_56,plain,
    ( r2_hidden('#skF_4',k1_relat_1(k8_relat_1('#skF_5','#skF_6')))
    | r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_74,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_84,plain,(
    ! [A_34,B_35] :
      ( v1_funct_1(k5_relat_1(A_34,B_35))
      | ~ v1_funct_1(B_35)
      | ~ v1_relat_1(B_35)
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_87,plain,(
    ! [A_3,B_4] :
      ( v1_funct_1(k8_relat_1(A_3,B_4))
      | ~ v1_funct_1(k6_relat_1(A_3))
      | ~ v1_relat_1(k6_relat_1(A_3))
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_84])).

tff(c_89,plain,(
    ! [A_3,B_4] :
      ( v1_funct_1(k8_relat_1(A_3,B_4))
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12,c_87])).

tff(c_60,plain,
    ( r2_hidden('#skF_4',k1_relat_1(k8_relat_1('#skF_5','#skF_6')))
    | r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_73,plain,(
    r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_94,plain,(
    ! [D_47,A_48,C_49] :
      ( r2_hidden(D_47,k1_relat_1(k8_relat_1(A_48,C_49)))
      | ~ r2_hidden(k1_funct_1(C_49,D_47),A_48)
      | ~ r2_hidden(D_47,k1_relat_1(C_49))
      | ~ v1_funct_1(C_49)
      | ~ v1_relat_1(C_49)
      | ~ v1_funct_1(k8_relat_1(A_48,C_49))
      | ~ v1_relat_1(k8_relat_1(A_48,C_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_50,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5')
    | ~ r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | ~ r2_hidden('#skF_4',k1_relat_1(k8_relat_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_76,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5')
    | ~ r2_hidden('#skF_4',k1_relat_1(k8_relat_1('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_50])).

tff(c_77,plain,(
    ~ r2_hidden('#skF_4',k1_relat_1(k8_relat_1('#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_106,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5')
    | ~ r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_94,c_77])).

tff(c_112,plain,
    ( ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_73,c_74,c_106])).

tff(c_113,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_116,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_113])).

tff(c_120,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_116])).

tff(c_121,plain,(
    ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_125,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_89,c_121])).

tff(c_129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_125])).

tff(c_130,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_130])).

tff(c_135,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_134,plain,(
    r2_hidden('#skF_4',k1_relat_1(k8_relat_1('#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_158,plain,(
    ! [C_59,D_60,A_61] :
      ( r2_hidden(k1_funct_1(C_59,D_60),A_61)
      | ~ r2_hidden(D_60,k1_relat_1(k8_relat_1(A_61,C_59)))
      | ~ v1_funct_1(C_59)
      | ~ v1_relat_1(C_59)
      | ~ v1_funct_1(k8_relat_1(A_61,C_59))
      | ~ v1_relat_1(k8_relat_1(A_61,C_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_161,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_134,c_158])).

tff(c_164,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5')
    | ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_161])).

tff(c_165,plain,
    ( ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_164])).

tff(c_166,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_165])).

tff(c_169,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_166])).

tff(c_173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_169])).

tff(c_174,plain,(
    ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_185,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_141,c_174])).

tff(c_189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_185])).

tff(c_191,plain,(
    ~ r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_190,plain,(
    r2_hidden('#skF_4',k1_relat_1(k8_relat_1('#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_208,plain,(
    ! [D_71,C_72,A_73] :
      ( r2_hidden(D_71,k1_relat_1(C_72))
      | ~ r2_hidden(D_71,k1_relat_1(k8_relat_1(A_73,C_72)))
      | ~ v1_funct_1(C_72)
      | ~ v1_relat_1(C_72)
      | ~ v1_funct_1(k8_relat_1(A_73,C_72))
      | ~ v1_relat_1(k8_relat_1(A_73,C_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_211,plain,
    ( r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_190,c_208])).

tff(c_214,plain,
    ( r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_211])).

tff(c_215,plain,
    ( ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_214])).

tff(c_216,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_215])).

tff(c_219,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_216])).

tff(c_223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_219])).

tff(c_224,plain,(
    ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_228,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_204,c_224])).

tff(c_232,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_228])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:46:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.30  
% 2.27/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.30  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k8_relat_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.27/1.30  
% 2.27/1.30  %Foreground sorts:
% 2.27/1.30  
% 2.27/1.30  
% 2.27/1.30  %Background operators:
% 2.27/1.30  
% 2.27/1.30  
% 2.27/1.30  %Foreground operators:
% 2.27/1.30  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.27/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.27/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.27/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.30  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.27/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.27/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.27/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.27/1.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.27/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.27/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.27/1.30  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.27/1.30  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.27/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.27/1.30  
% 2.54/1.32  tff(f_83, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k8_relat_1(B, C))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_funct_1)).
% 2.54/1.32  tff(f_49, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.54/1.32  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 2.54/1.32  tff(f_45, axiom, (![A, B]: ((((v1_relat_1(A) & v1_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v1_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funct_1)).
% 2.54/1.32  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 2.54/1.32  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((B = k8_relat_1(A, C)) <=> ((![D]: (r2_hidden(D, k1_relat_1(B)) <=> (r2_hidden(D, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, D), A)))) & (![D]: (r2_hidden(D, k1_relat_1(B)) => (k1_funct_1(B, D) = k1_funct_1(C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_funct_1)).
% 2.54/1.32  tff(c_48, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.54/1.32  tff(c_46, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.54/1.32  tff(c_10, plain, (![A_7]: (v1_relat_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.54/1.32  tff(c_12, plain, (![A_7]: (v1_funct_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.54/1.32  tff(c_4, plain, (![B_4, A_3]: (k5_relat_1(B_4, k6_relat_1(A_3))=k8_relat_1(A_3, B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.54/1.32  tff(c_199, plain, (![A_67, B_68]: (v1_funct_1(k5_relat_1(A_67, B_68)) | ~v1_funct_1(B_68) | ~v1_relat_1(B_68) | ~v1_funct_1(A_67) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.54/1.32  tff(c_202, plain, (![A_3, B_4]: (v1_funct_1(k8_relat_1(A_3, B_4)) | ~v1_funct_1(k6_relat_1(A_3)) | ~v1_relat_1(k6_relat_1(A_3)) | ~v1_funct_1(B_4) | ~v1_relat_1(B_4) | ~v1_relat_1(B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_199])).
% 2.54/1.32  tff(c_204, plain, (![A_3, B_4]: (v1_funct_1(k8_relat_1(A_3, B_4)) | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12, c_202])).
% 2.54/1.32  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k8_relat_1(A_1, B_2)) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.54/1.32  tff(c_136, plain, (![A_50, B_51]: (v1_funct_1(k5_relat_1(A_50, B_51)) | ~v1_funct_1(B_51) | ~v1_relat_1(B_51) | ~v1_funct_1(A_50) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.54/1.32  tff(c_139, plain, (![A_3, B_4]: (v1_funct_1(k8_relat_1(A_3, B_4)) | ~v1_funct_1(k6_relat_1(A_3)) | ~v1_relat_1(k6_relat_1(A_3)) | ~v1_funct_1(B_4) | ~v1_relat_1(B_4) | ~v1_relat_1(B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_136])).
% 2.54/1.32  tff(c_141, plain, (![A_3, B_4]: (v1_funct_1(k8_relat_1(A_3, B_4)) | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12, c_139])).
% 2.54/1.32  tff(c_56, plain, (r2_hidden('#skF_4', k1_relat_1(k8_relat_1('#skF_5', '#skF_6'))) | r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.54/1.32  tff(c_74, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_56])).
% 2.54/1.32  tff(c_84, plain, (![A_34, B_35]: (v1_funct_1(k5_relat_1(A_34, B_35)) | ~v1_funct_1(B_35) | ~v1_relat_1(B_35) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.54/1.32  tff(c_87, plain, (![A_3, B_4]: (v1_funct_1(k8_relat_1(A_3, B_4)) | ~v1_funct_1(k6_relat_1(A_3)) | ~v1_relat_1(k6_relat_1(A_3)) | ~v1_funct_1(B_4) | ~v1_relat_1(B_4) | ~v1_relat_1(B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_84])).
% 2.54/1.32  tff(c_89, plain, (![A_3, B_4]: (v1_funct_1(k8_relat_1(A_3, B_4)) | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12, c_87])).
% 2.54/1.32  tff(c_60, plain, (r2_hidden('#skF_4', k1_relat_1(k8_relat_1('#skF_5', '#skF_6'))) | r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.54/1.32  tff(c_73, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_60])).
% 2.54/1.32  tff(c_94, plain, (![D_47, A_48, C_49]: (r2_hidden(D_47, k1_relat_1(k8_relat_1(A_48, C_49))) | ~r2_hidden(k1_funct_1(C_49, D_47), A_48) | ~r2_hidden(D_47, k1_relat_1(C_49)) | ~v1_funct_1(C_49) | ~v1_relat_1(C_49) | ~v1_funct_1(k8_relat_1(A_48, C_49)) | ~v1_relat_1(k8_relat_1(A_48, C_49)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.54/1.32  tff(c_50, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5') | ~r2_hidden('#skF_4', k1_relat_1('#skF_6')) | ~r2_hidden('#skF_4', k1_relat_1(k8_relat_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.54/1.32  tff(c_76, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5') | ~r2_hidden('#skF_4', k1_relat_1(k8_relat_1('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_50])).
% 2.54/1.32  tff(c_77, plain, (~r2_hidden('#skF_4', k1_relat_1(k8_relat_1('#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_76])).
% 2.54/1.32  tff(c_106, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5') | ~r2_hidden('#skF_4', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1(k8_relat_1('#skF_5', '#skF_6')) | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_94, c_77])).
% 2.54/1.32  tff(c_112, plain, (~v1_funct_1(k8_relat_1('#skF_5', '#skF_6')) | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_73, c_74, c_106])).
% 2.54/1.32  tff(c_113, plain, (~v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_112])).
% 2.54/1.32  tff(c_116, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2, c_113])).
% 2.54/1.32  tff(c_120, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_116])).
% 2.54/1.32  tff(c_121, plain, (~v1_funct_1(k8_relat_1('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_112])).
% 2.54/1.32  tff(c_125, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_89, c_121])).
% 2.54/1.32  tff(c_129, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_125])).
% 2.54/1.32  tff(c_130, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_76])).
% 2.54/1.32  tff(c_133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_130])).
% 2.54/1.32  tff(c_135, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_56])).
% 2.54/1.32  tff(c_134, plain, (r2_hidden('#skF_4', k1_relat_1(k8_relat_1('#skF_5', '#skF_6')))), inference(splitRight, [status(thm)], [c_56])).
% 2.54/1.32  tff(c_158, plain, (![C_59, D_60, A_61]: (r2_hidden(k1_funct_1(C_59, D_60), A_61) | ~r2_hidden(D_60, k1_relat_1(k8_relat_1(A_61, C_59))) | ~v1_funct_1(C_59) | ~v1_relat_1(C_59) | ~v1_funct_1(k8_relat_1(A_61, C_59)) | ~v1_relat_1(k8_relat_1(A_61, C_59)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.54/1.32  tff(c_161, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1(k8_relat_1('#skF_5', '#skF_6')) | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_134, c_158])).
% 2.54/1.32  tff(c_164, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5') | ~v1_funct_1(k8_relat_1('#skF_5', '#skF_6')) | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_161])).
% 2.54/1.32  tff(c_165, plain, (~v1_funct_1(k8_relat_1('#skF_5', '#skF_6')) | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_135, c_164])).
% 2.54/1.32  tff(c_166, plain, (~v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_165])).
% 2.54/1.32  tff(c_169, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2, c_166])).
% 2.54/1.32  tff(c_173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_169])).
% 2.54/1.32  tff(c_174, plain, (~v1_funct_1(k8_relat_1('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_165])).
% 2.54/1.32  tff(c_185, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_141, c_174])).
% 2.54/1.32  tff(c_189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_185])).
% 2.54/1.32  tff(c_191, plain, (~r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_60])).
% 2.54/1.32  tff(c_190, plain, (r2_hidden('#skF_4', k1_relat_1(k8_relat_1('#skF_5', '#skF_6')))), inference(splitRight, [status(thm)], [c_60])).
% 2.54/1.32  tff(c_208, plain, (![D_71, C_72, A_73]: (r2_hidden(D_71, k1_relat_1(C_72)) | ~r2_hidden(D_71, k1_relat_1(k8_relat_1(A_73, C_72))) | ~v1_funct_1(C_72) | ~v1_relat_1(C_72) | ~v1_funct_1(k8_relat_1(A_73, C_72)) | ~v1_relat_1(k8_relat_1(A_73, C_72)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.54/1.32  tff(c_211, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1(k8_relat_1('#skF_5', '#skF_6')) | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_190, c_208])).
% 2.54/1.32  tff(c_214, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_6')) | ~v1_funct_1(k8_relat_1('#skF_5', '#skF_6')) | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_211])).
% 2.54/1.32  tff(c_215, plain, (~v1_funct_1(k8_relat_1('#skF_5', '#skF_6')) | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_191, c_214])).
% 2.54/1.32  tff(c_216, plain, (~v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_215])).
% 2.54/1.32  tff(c_219, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2, c_216])).
% 2.54/1.32  tff(c_223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_219])).
% 2.54/1.32  tff(c_224, plain, (~v1_funct_1(k8_relat_1('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_215])).
% 2.54/1.32  tff(c_228, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_204, c_224])).
% 2.54/1.32  tff(c_232, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_228])).
% 2.54/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.32  
% 2.54/1.32  Inference rules
% 2.54/1.32  ----------------------
% 2.54/1.32  #Ref     : 0
% 2.54/1.32  #Sup     : 22
% 2.54/1.32  #Fact    : 0
% 2.54/1.32  #Define  : 0
% 2.54/1.32  #Split   : 7
% 2.54/1.32  #Chain   : 0
% 2.54/1.32  #Close   : 0
% 2.54/1.32  
% 2.54/1.32  Ordering : KBO
% 2.54/1.32  
% 2.54/1.32  Simplification rules
% 2.54/1.32  ----------------------
% 2.54/1.32  #Subsume      : 5
% 2.54/1.32  #Demod        : 40
% 2.54/1.32  #Tautology    : 8
% 2.54/1.32  #SimpNegUnit  : 2
% 2.54/1.32  #BackRed      : 0
% 2.54/1.32  
% 2.54/1.32  #Partial instantiations: 0
% 2.54/1.32  #Strategies tried      : 1
% 2.54/1.32  
% 2.54/1.32  Timing (in seconds)
% 2.54/1.32  ----------------------
% 2.54/1.33  Preprocessing        : 0.34
% 2.54/1.33  Parsing              : 0.18
% 2.54/1.33  CNF conversion       : 0.03
% 2.54/1.33  Main loop            : 0.27
% 2.54/1.33  Inferencing          : 0.09
% 2.54/1.33  Reduction            : 0.08
% 2.54/1.33  Demodulation         : 0.06
% 2.54/1.33  BG Simplification    : 0.02
% 2.54/1.33  Subsumption          : 0.07
% 2.54/1.33  Abstraction          : 0.01
% 2.54/1.33  MUC search           : 0.00
% 2.54/1.33  Cooper               : 0.00
% 2.54/1.33  Total                : 0.65
% 2.54/1.33  Index Insertion      : 0.00
% 2.54/1.33  Index Deletion       : 0.00
% 2.54/1.33  Index Matching       : 0.00
% 2.54/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
