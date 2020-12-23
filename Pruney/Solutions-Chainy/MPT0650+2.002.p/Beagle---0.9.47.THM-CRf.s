%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:44 EST 2020

% Result     : Theorem 15.45s
% Output     : CNFRefutation 15.57s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 953 expanded)
%              Number of leaves         :   36 ( 367 expanded)
%              Depth                    :   13
%              Number of atoms          :  280 (2860 expanded)
%              Number of equality atoms :   71 ( 890 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_173,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( v2_funct_1(B)
            & r2_hidden(A,k2_relat_1(B)) )
         => ( A = k1_funct_1(B,k1_funct_1(k2_funct_1(B),A))
            & A = k1_funct_1(k5_relat_1(k2_funct_1(B),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).

tff(f_102,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_94,axiom,(
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

tff(f_160,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k1_relat_1(B)) )
       => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
          & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

tff(f_110,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_122,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_135,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

tff(c_76,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_82,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_80,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_78,plain,(
    v2_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_15536,plain,(
    ! [A_470] :
      ( k4_relat_1(A_470) = k2_funct_1(A_470)
      | ~ v2_funct_1(A_470)
      | ~ v1_funct_1(A_470)
      | ~ v1_relat_1(A_470) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_15539,plain,
    ( k4_relat_1('#skF_8') = k2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_78,c_15536])).

tff(c_15542,plain,(
    k4_relat_1('#skF_8') = k2_funct_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_15539])).

tff(c_14,plain,(
    ! [A_8] :
      ( v1_relat_1(k4_relat_1(A_8))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_15555,plain,
    ( v1_relat_1(k2_funct_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_15542,c_14])).

tff(c_15565,plain,(
    v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_15555])).

tff(c_16,plain,(
    ! [A_9] :
      ( k4_relat_1(k4_relat_1(A_9)) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_15552,plain,
    ( k4_relat_1(k2_funct_1('#skF_8')) = '#skF_8'
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_15542,c_16])).

tff(c_15563,plain,(
    k4_relat_1(k2_funct_1('#skF_8')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_15552])).

tff(c_18,plain,(
    ! [A_10] :
      ( k2_relat_1(k4_relat_1(A_10)) = k1_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_15546,plain,
    ( k2_relat_1(k2_funct_1('#skF_8')) = k1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_15542,c_18])).

tff(c_15559,plain,(
    k2_relat_1(k2_funct_1('#skF_8')) = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_15546])).

tff(c_20,plain,(
    ! [A_10] :
      ( k1_relat_1(k4_relat_1(A_10)) = k2_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16470,plain,(
    ! [A_509,C_510] :
      ( r2_hidden('#skF_5'(A_509,k2_relat_1(A_509),C_510),k1_relat_1(A_509))
      | ~ r2_hidden(C_510,k2_relat_1(A_509))
      | ~ v1_funct_1(A_509)
      | ~ v1_relat_1(A_509) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_26241,plain,(
    ! [A_758,C_759] :
      ( r2_hidden('#skF_5'(k4_relat_1(A_758),k2_relat_1(k4_relat_1(A_758)),C_759),k2_relat_1(A_758))
      | ~ r2_hidden(C_759,k2_relat_1(k4_relat_1(A_758)))
      | ~ v1_funct_1(k4_relat_1(A_758))
      | ~ v1_relat_1(k4_relat_1(A_758))
      | ~ v1_relat_1(A_758) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_16470])).

tff(c_26339,plain,(
    ! [C_759] :
      ( r2_hidden('#skF_5'(k4_relat_1(k2_funct_1('#skF_8')),k2_relat_1(k4_relat_1(k2_funct_1('#skF_8'))),C_759),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_759,k2_relat_1(k4_relat_1(k2_funct_1('#skF_8'))))
      | ~ v1_funct_1(k4_relat_1(k2_funct_1('#skF_8')))
      | ~ v1_relat_1(k4_relat_1(k2_funct_1('#skF_8')))
      | ~ v1_relat_1(k2_funct_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15559,c_26241])).

tff(c_26384,plain,(
    ! [C_759] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_759),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_759,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15565,c_82,c_15563,c_80,c_15563,c_15563,c_15563,c_15563,c_26339])).

tff(c_32,plain,(
    ! [A_21,C_57] :
      ( k1_funct_1(A_21,'#skF_5'(A_21,k2_relat_1(A_21),C_57)) = C_57
      | ~ r2_hidden(C_57,k2_relat_1(A_21))
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_17118,plain,(
    ! [B_542,A_543] :
      ( k1_funct_1(k2_funct_1(B_542),k1_funct_1(B_542,A_543)) = A_543
      | ~ r2_hidden(A_543,k1_relat_1(B_542))
      | ~ v2_funct_1(B_542)
      | ~ v1_funct_1(B_542)
      | ~ v1_relat_1(B_542) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_30732,plain,(
    ! [A_822,C_823] :
      ( k1_funct_1(k2_funct_1(A_822),C_823) = '#skF_5'(A_822,k2_relat_1(A_822),C_823)
      | ~ r2_hidden('#skF_5'(A_822,k2_relat_1(A_822),C_823),k1_relat_1(A_822))
      | ~ v2_funct_1(A_822)
      | ~ v1_funct_1(A_822)
      | ~ v1_relat_1(A_822)
      | ~ r2_hidden(C_823,k2_relat_1(A_822))
      | ~ v1_funct_1(A_822)
      | ~ v1_relat_1(A_822) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_17118])).

tff(c_30738,plain,(
    ! [C_759] :
      ( k1_funct_1(k2_funct_1('#skF_8'),C_759) = '#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_759)
      | ~ v2_funct_1('#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(C_759,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_26384,c_30732])).

tff(c_30809,plain,(
    ! [C_824] :
      ( k1_funct_1(k2_funct_1('#skF_8'),C_824) = '#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_824)
      | ~ r2_hidden(C_824,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_30738])).

tff(c_30982,plain,(
    k1_funct_1(k2_funct_1('#skF_8'),'#skF_7') = '#skF_5'('#skF_8',k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_76,c_30809])).

tff(c_202,plain,(
    ! [A_100] :
      ( k4_relat_1(A_100) = k2_funct_1(A_100)
      | ~ v2_funct_1(A_100)
      | ~ v1_funct_1(A_100)
      | ~ v1_relat_1(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_205,plain,
    ( k4_relat_1('#skF_8') = k2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_78,c_202])).

tff(c_208,plain,(
    k4_relat_1('#skF_8') = k2_funct_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_205])).

tff(c_221,plain,
    ( v1_relat_1(k2_funct_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_14])).

tff(c_231,plain,(
    v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_221])).

tff(c_218,plain,
    ( k4_relat_1(k2_funct_1('#skF_8')) = '#skF_8'
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_16])).

tff(c_229,plain,(
    k4_relat_1(k2_funct_1('#skF_8')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_218])).

tff(c_215,plain,
    ( k1_relat_1(k2_funct_1('#skF_8')) = k2_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_20])).

tff(c_227,plain,(
    k1_relat_1(k2_funct_1('#skF_8')) = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_215])).

tff(c_1131,plain,(
    ! [A_139,C_140] :
      ( k1_funct_1(A_139,'#skF_5'(A_139,k2_relat_1(A_139),C_140)) = C_140
      | ~ r2_hidden(C_140,k2_relat_1(A_139))
      | ~ v1_funct_1(A_139)
      | ~ v1_relat_1(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_11189,plain,(
    ! [A_387,C_388] :
      ( k1_funct_1(k4_relat_1(A_387),'#skF_5'(k4_relat_1(A_387),k1_relat_1(A_387),C_388)) = C_388
      | ~ r2_hidden(C_388,k2_relat_1(k4_relat_1(A_387)))
      | ~ v1_funct_1(k4_relat_1(A_387))
      | ~ v1_relat_1(k4_relat_1(A_387))
      | ~ v1_relat_1(A_387) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1131])).

tff(c_11325,plain,(
    ! [C_388] :
      ( k1_funct_1(k4_relat_1(k2_funct_1('#skF_8')),'#skF_5'(k4_relat_1(k2_funct_1('#skF_8')),k2_relat_1('#skF_8'),C_388)) = C_388
      | ~ r2_hidden(C_388,k2_relat_1(k4_relat_1(k2_funct_1('#skF_8'))))
      | ~ v1_funct_1(k4_relat_1(k2_funct_1('#skF_8')))
      | ~ v1_relat_1(k4_relat_1(k2_funct_1('#skF_8')))
      | ~ v1_relat_1(k2_funct_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_11189])).

tff(c_11373,plain,(
    ! [C_388] :
      ( k1_funct_1('#skF_8','#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_388)) = C_388
      | ~ r2_hidden(C_388,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_82,c_229,c_80,c_229,c_229,c_229,c_229,c_11325])).

tff(c_1382,plain,(
    ! [A_151,C_152] :
      ( r2_hidden('#skF_5'(A_151,k2_relat_1(A_151),C_152),k1_relat_1(A_151))
      | ~ r2_hidden(C_152,k2_relat_1(A_151))
      | ~ v1_funct_1(A_151)
      | ~ v1_relat_1(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_10881,plain,(
    ! [A_380,C_381] :
      ( r2_hidden('#skF_5'(k4_relat_1(A_380),k1_relat_1(A_380),C_381),k1_relat_1(k4_relat_1(A_380)))
      | ~ r2_hidden(C_381,k2_relat_1(k4_relat_1(A_380)))
      | ~ v1_funct_1(k4_relat_1(A_380))
      | ~ v1_relat_1(k4_relat_1(A_380))
      | ~ v1_relat_1(A_380) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1382])).

tff(c_11003,plain,(
    ! [C_381] :
      ( r2_hidden('#skF_5'(k4_relat_1(k2_funct_1('#skF_8')),k2_relat_1('#skF_8'),C_381),k1_relat_1(k4_relat_1(k2_funct_1('#skF_8'))))
      | ~ r2_hidden(C_381,k2_relat_1(k4_relat_1(k2_funct_1('#skF_8'))))
      | ~ v1_funct_1(k4_relat_1(k2_funct_1('#skF_8')))
      | ~ v1_relat_1(k4_relat_1(k2_funct_1('#skF_8')))
      | ~ v1_relat_1(k2_funct_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_10881])).

tff(c_11053,plain,(
    ! [C_381] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_381),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_381,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_82,c_229,c_80,c_229,c_229,c_229,c_229,c_11003])).

tff(c_1881,plain,(
    ! [B_181,A_182] :
      ( k1_funct_1(k2_funct_1(B_181),k1_funct_1(B_181,A_182)) = A_182
      | ~ r2_hidden(A_182,k1_relat_1(B_181))
      | ~ v2_funct_1(B_181)
      | ~ v1_funct_1(B_181)
      | ~ v1_relat_1(B_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_15149,plain,(
    ! [A_449,C_450] :
      ( k1_funct_1(k2_funct_1(A_449),C_450) = '#skF_5'(A_449,k2_relat_1(A_449),C_450)
      | ~ r2_hidden('#skF_5'(A_449,k2_relat_1(A_449),C_450),k1_relat_1(A_449))
      | ~ v2_funct_1(A_449)
      | ~ v1_funct_1(A_449)
      | ~ v1_relat_1(A_449)
      | ~ r2_hidden(C_450,k2_relat_1(A_449))
      | ~ v1_funct_1(A_449)
      | ~ v1_relat_1(A_449) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1881])).

tff(c_15164,plain,(
    ! [C_381] :
      ( k1_funct_1(k2_funct_1('#skF_8'),C_381) = '#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_381)
      | ~ v2_funct_1('#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(C_381,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_11053,c_15149])).

tff(c_15226,plain,(
    ! [C_451] :
      ( k1_funct_1(k2_funct_1('#skF_8'),C_451) = '#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_451)
      | ~ r2_hidden(C_451,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_15164])).

tff(c_15380,plain,(
    k1_funct_1(k2_funct_1('#skF_8'),'#skF_7') = '#skF_5'('#skF_8',k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_76,c_15226])).

tff(c_74,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_8'),'#skF_8'),'#skF_7') != '#skF_7'
    | k1_funct_1('#skF_8',k1_funct_1(k2_funct_1('#skF_8'),'#skF_7')) != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_105,plain,(
    k1_funct_1('#skF_8',k1_funct_1(k2_funct_1('#skF_8'),'#skF_7')) != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_15381,plain,(
    k1_funct_1('#skF_8','#skF_5'('#skF_8',k2_relat_1('#skF_8'),'#skF_7')) != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15380,c_105])).

tff(c_15426,plain,(
    ~ r2_hidden('#skF_7',k2_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11373,c_15381])).

tff(c_15433,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_15426])).

tff(c_15435,plain,(
    k1_funct_1('#skF_8',k1_funct_1(k2_funct_1('#skF_8'),'#skF_7')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_30987,plain,(
    k1_funct_1('#skF_8','#skF_5'('#skF_8',k2_relat_1('#skF_8'),'#skF_7')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30982,c_15435])).

tff(c_50,plain,(
    ! [A_62] :
      ( v1_funct_1(k2_funct_1(A_62))
      | ~ v1_funct_1(A_62)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_15549,plain,
    ( k1_relat_1(k2_funct_1('#skF_8')) = k2_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_15542,c_20])).

tff(c_15561,plain,(
    k1_relat_1(k2_funct_1('#skF_8')) = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_15549])).

tff(c_15797,plain,(
    ! [B_479,A_480] :
      ( r2_hidden(k1_funct_1(B_479,A_480),k2_relat_1(B_479))
      | ~ r2_hidden(A_480,k1_relat_1(B_479))
      | ~ v1_funct_1(B_479)
      | ~ v1_relat_1(B_479) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_15802,plain,(
    ! [A_480] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_8'),A_480),k1_relat_1('#skF_8'))
      | ~ r2_hidden(A_480,k1_relat_1(k2_funct_1('#skF_8')))
      | ~ v1_funct_1(k2_funct_1('#skF_8'))
      | ~ v1_relat_1(k2_funct_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15559,c_15797])).

tff(c_15814,plain,(
    ! [A_480] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_8'),A_480),k1_relat_1('#skF_8'))
      | ~ r2_hidden(A_480,k2_relat_1('#skF_8'))
      | ~ v1_funct_1(k2_funct_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15565,c_15561,c_15802])).

tff(c_17801,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_15814])).

tff(c_17804,plain,
    ( ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_50,c_17801])).

tff(c_17808,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_17804])).

tff(c_17810,plain,(
    v1_funct_1(k2_funct_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_15814])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_15997,plain,(
    ! [A_494,B_495] :
      ( k1_relat_1(k5_relat_1(A_494,B_495)) = k1_relat_1(A_494)
      | ~ r1_tarski(k2_relat_1(A_494),k1_relat_1(B_495))
      | ~ v1_relat_1(B_495)
      | ~ v1_relat_1(A_494) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16012,plain,(
    ! [B_495] :
      ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_8'),B_495)) = k1_relat_1(k2_funct_1('#skF_8'))
      | ~ r1_tarski(k1_relat_1('#skF_8'),k1_relat_1(B_495))
      | ~ v1_relat_1(B_495)
      | ~ v1_relat_1(k2_funct_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15559,c_15997])).

tff(c_17639,plain,(
    ! [B_569] :
      ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_8'),B_569)) = k2_relat_1('#skF_8')
      | ~ r1_tarski(k1_relat_1('#skF_8'),k1_relat_1(B_569))
      | ~ v1_relat_1(B_569) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15565,c_15561,c_16012])).

tff(c_17658,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_8'),'#skF_8')) = k2_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_12,c_17639])).

tff(c_17667,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_8'),'#skF_8')) = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_17658])).

tff(c_15662,plain,(
    ! [B_474,A_475] :
      ( k5_relat_1(k4_relat_1(B_474),k4_relat_1(A_475)) = k4_relat_1(k5_relat_1(A_475,B_474))
      | ~ v1_relat_1(B_474)
      | ~ v1_relat_1(A_475) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_15680,plain,(
    ! [A_475] :
      ( k5_relat_1(k2_funct_1('#skF_8'),k4_relat_1(A_475)) = k4_relat_1(k5_relat_1(A_475,'#skF_8'))
      | ~ v1_relat_1('#skF_8')
      | ~ v1_relat_1(A_475) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15542,c_15662])).

tff(c_15720,plain,(
    ! [A_477] :
      ( k5_relat_1(k2_funct_1('#skF_8'),k4_relat_1(A_477)) = k4_relat_1(k5_relat_1(A_477,'#skF_8'))
      | ~ v1_relat_1(A_477) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_15680])).

tff(c_15732,plain,
    ( k4_relat_1(k5_relat_1(k2_funct_1('#skF_8'),'#skF_8')) = k5_relat_1(k2_funct_1('#skF_8'),'#skF_8')
    | ~ v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_15563,c_15720])).

tff(c_15744,plain,(
    k4_relat_1(k5_relat_1(k2_funct_1('#skF_8'),'#skF_8')) = k5_relat_1(k2_funct_1('#skF_8'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15565,c_15732])).

tff(c_26,plain,(
    ! [B_19,A_17] :
      ( k5_relat_1(k4_relat_1(B_19),k4_relat_1(A_17)) = k4_relat_1(k5_relat_1(A_17,B_19))
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_18626,plain,(
    ! [C_608,B_609,A_610] :
      ( k1_funct_1(k5_relat_1(C_608,B_609),A_610) = k1_funct_1(B_609,k1_funct_1(C_608,A_610))
      | ~ r2_hidden(A_610,k1_relat_1(k5_relat_1(C_608,B_609)))
      | ~ v1_funct_1(C_608)
      | ~ v1_relat_1(C_608)
      | ~ v1_funct_1(B_609)
      | ~ v1_relat_1(B_609) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_32773,plain,(
    ! [B_865,A_866,A_867] :
      ( k1_funct_1(k5_relat_1(k4_relat_1(B_865),k4_relat_1(A_866)),A_867) = k1_funct_1(k4_relat_1(A_866),k1_funct_1(k4_relat_1(B_865),A_867))
      | ~ r2_hidden(A_867,k1_relat_1(k4_relat_1(k5_relat_1(A_866,B_865))))
      | ~ v1_funct_1(k4_relat_1(B_865))
      | ~ v1_relat_1(k4_relat_1(B_865))
      | ~ v1_funct_1(k4_relat_1(A_866))
      | ~ v1_relat_1(k4_relat_1(A_866))
      | ~ v1_relat_1(B_865)
      | ~ v1_relat_1(A_866) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_18626])).

tff(c_32996,plain,(
    ! [A_867] :
      ( k1_funct_1(k5_relat_1(k4_relat_1('#skF_8'),k4_relat_1(k2_funct_1('#skF_8'))),A_867) = k1_funct_1(k4_relat_1(k2_funct_1('#skF_8')),k1_funct_1(k4_relat_1('#skF_8'),A_867))
      | ~ r2_hidden(A_867,k1_relat_1(k5_relat_1(k2_funct_1('#skF_8'),'#skF_8')))
      | ~ v1_funct_1(k4_relat_1('#skF_8'))
      | ~ v1_relat_1(k4_relat_1('#skF_8'))
      | ~ v1_funct_1(k4_relat_1(k2_funct_1('#skF_8')))
      | ~ v1_relat_1(k4_relat_1(k2_funct_1('#skF_8')))
      | ~ v1_relat_1('#skF_8')
      | ~ v1_relat_1(k2_funct_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15744,c_32773])).

tff(c_38553,plain,(
    ! [A_947] :
      ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_8'),'#skF_8'),A_947) = k1_funct_1('#skF_8',k1_funct_1(k2_funct_1('#skF_8'),A_947))
      | ~ r2_hidden(A_947,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15565,c_82,c_82,c_15563,c_80,c_15563,c_15565,c_15542,c_17810,c_15542,c_17667,c_15542,c_15542,c_15563,c_15563,c_32996])).

tff(c_15434,plain,(
    k1_funct_1(k5_relat_1(k2_funct_1('#skF_8'),'#skF_8'),'#skF_7') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_38602,plain,
    ( k1_funct_1('#skF_8',k1_funct_1(k2_funct_1('#skF_8'),'#skF_7')) != '#skF_7'
    | ~ r2_hidden('#skF_7',k2_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_38553,c_15434])).

tff(c_38641,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_30987,c_30982,c_38602])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:20:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.45/7.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.45/7.06  
% 15.45/7.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.45/7.06  %$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 15.45/7.06  
% 15.45/7.06  %Foreground sorts:
% 15.45/7.06  
% 15.45/7.06  
% 15.45/7.06  %Background operators:
% 15.45/7.06  
% 15.45/7.06  
% 15.45/7.06  %Foreground operators:
% 15.45/7.06  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 15.45/7.06  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 15.45/7.06  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 15.45/7.06  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 15.45/7.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.45/7.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.45/7.06  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 15.45/7.06  tff('#skF_7', type, '#skF_7': $i).
% 15.45/7.06  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 15.45/7.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.45/7.06  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 15.45/7.06  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 15.45/7.06  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 15.45/7.06  tff('#skF_8', type, '#skF_8': $i).
% 15.45/7.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.45/7.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.45/7.06  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 15.45/7.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.45/7.06  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 15.45/7.06  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 15.45/7.06  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 15.45/7.06  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 15.45/7.06  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 15.45/7.06  
% 15.57/7.08  tff(f_173, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k2_relat_1(B))) => ((A = k1_funct_1(B, k1_funct_1(k2_funct_1(B), A))) & (A = k1_funct_1(k5_relat_1(k2_funct_1(B), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_funct_1)).
% 15.57/7.08  tff(f_102, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 15.57/7.08  tff(f_42, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 15.57/7.08  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 15.57/7.08  tff(f_52, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 15.57/7.08  tff(f_94, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 15.57/7.08  tff(f_160, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_funct_1)).
% 15.57/7.08  tff(f_110, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 15.57/7.08  tff(f_122, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 15.57/7.08  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.57/7.08  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 15.57/7.08  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 15.57/7.08  tff(f_135, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 15.57/7.08  tff(c_76, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_173])).
% 15.57/7.08  tff(c_82, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_173])).
% 15.57/7.08  tff(c_80, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_173])).
% 15.57/7.08  tff(c_78, plain, (v2_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_173])).
% 15.57/7.08  tff(c_15536, plain, (![A_470]: (k4_relat_1(A_470)=k2_funct_1(A_470) | ~v2_funct_1(A_470) | ~v1_funct_1(A_470) | ~v1_relat_1(A_470))), inference(cnfTransformation, [status(thm)], [f_102])).
% 15.57/7.08  tff(c_15539, plain, (k4_relat_1('#skF_8')=k2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_78, c_15536])).
% 15.57/7.08  tff(c_15542, plain, (k4_relat_1('#skF_8')=k2_funct_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_15539])).
% 15.57/7.08  tff(c_14, plain, (![A_8]: (v1_relat_1(k4_relat_1(A_8)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 15.57/7.08  tff(c_15555, plain, (v1_relat_1(k2_funct_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_15542, c_14])).
% 15.57/7.08  tff(c_15565, plain, (v1_relat_1(k2_funct_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_15555])).
% 15.57/7.08  tff(c_16, plain, (![A_9]: (k4_relat_1(k4_relat_1(A_9))=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 15.57/7.08  tff(c_15552, plain, (k4_relat_1(k2_funct_1('#skF_8'))='#skF_8' | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_15542, c_16])).
% 15.57/7.08  tff(c_15563, plain, (k4_relat_1(k2_funct_1('#skF_8'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_15552])).
% 15.57/7.08  tff(c_18, plain, (![A_10]: (k2_relat_1(k4_relat_1(A_10))=k1_relat_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 15.57/7.08  tff(c_15546, plain, (k2_relat_1(k2_funct_1('#skF_8'))=k1_relat_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_15542, c_18])).
% 15.57/7.08  tff(c_15559, plain, (k2_relat_1(k2_funct_1('#skF_8'))=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_15546])).
% 15.57/7.08  tff(c_20, plain, (![A_10]: (k1_relat_1(k4_relat_1(A_10))=k2_relat_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 15.57/7.08  tff(c_16470, plain, (![A_509, C_510]: (r2_hidden('#skF_5'(A_509, k2_relat_1(A_509), C_510), k1_relat_1(A_509)) | ~r2_hidden(C_510, k2_relat_1(A_509)) | ~v1_funct_1(A_509) | ~v1_relat_1(A_509))), inference(cnfTransformation, [status(thm)], [f_94])).
% 15.57/7.08  tff(c_26241, plain, (![A_758, C_759]: (r2_hidden('#skF_5'(k4_relat_1(A_758), k2_relat_1(k4_relat_1(A_758)), C_759), k2_relat_1(A_758)) | ~r2_hidden(C_759, k2_relat_1(k4_relat_1(A_758))) | ~v1_funct_1(k4_relat_1(A_758)) | ~v1_relat_1(k4_relat_1(A_758)) | ~v1_relat_1(A_758))), inference(superposition, [status(thm), theory('equality')], [c_20, c_16470])).
% 15.57/7.08  tff(c_26339, plain, (![C_759]: (r2_hidden('#skF_5'(k4_relat_1(k2_funct_1('#skF_8')), k2_relat_1(k4_relat_1(k2_funct_1('#skF_8'))), C_759), k1_relat_1('#skF_8')) | ~r2_hidden(C_759, k2_relat_1(k4_relat_1(k2_funct_1('#skF_8')))) | ~v1_funct_1(k4_relat_1(k2_funct_1('#skF_8'))) | ~v1_relat_1(k4_relat_1(k2_funct_1('#skF_8'))) | ~v1_relat_1(k2_funct_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_15559, c_26241])).
% 15.57/7.08  tff(c_26384, plain, (![C_759]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_759), k1_relat_1('#skF_8')) | ~r2_hidden(C_759, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_15565, c_82, c_15563, c_80, c_15563, c_15563, c_15563, c_15563, c_26339])).
% 15.57/7.08  tff(c_32, plain, (![A_21, C_57]: (k1_funct_1(A_21, '#skF_5'(A_21, k2_relat_1(A_21), C_57))=C_57 | ~r2_hidden(C_57, k2_relat_1(A_21)) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_94])).
% 15.57/7.08  tff(c_17118, plain, (![B_542, A_543]: (k1_funct_1(k2_funct_1(B_542), k1_funct_1(B_542, A_543))=A_543 | ~r2_hidden(A_543, k1_relat_1(B_542)) | ~v2_funct_1(B_542) | ~v1_funct_1(B_542) | ~v1_relat_1(B_542))), inference(cnfTransformation, [status(thm)], [f_160])).
% 15.57/7.08  tff(c_30732, plain, (![A_822, C_823]: (k1_funct_1(k2_funct_1(A_822), C_823)='#skF_5'(A_822, k2_relat_1(A_822), C_823) | ~r2_hidden('#skF_5'(A_822, k2_relat_1(A_822), C_823), k1_relat_1(A_822)) | ~v2_funct_1(A_822) | ~v1_funct_1(A_822) | ~v1_relat_1(A_822) | ~r2_hidden(C_823, k2_relat_1(A_822)) | ~v1_funct_1(A_822) | ~v1_relat_1(A_822))), inference(superposition, [status(thm), theory('equality')], [c_32, c_17118])).
% 15.57/7.08  tff(c_30738, plain, (![C_759]: (k1_funct_1(k2_funct_1('#skF_8'), C_759)='#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_759) | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(C_759, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_26384, c_30732])).
% 15.57/7.08  tff(c_30809, plain, (![C_824]: (k1_funct_1(k2_funct_1('#skF_8'), C_824)='#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_824) | ~r2_hidden(C_824, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_30738])).
% 15.57/7.08  tff(c_30982, plain, (k1_funct_1(k2_funct_1('#skF_8'), '#skF_7')='#skF_5'('#skF_8', k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_76, c_30809])).
% 15.57/7.08  tff(c_202, plain, (![A_100]: (k4_relat_1(A_100)=k2_funct_1(A_100) | ~v2_funct_1(A_100) | ~v1_funct_1(A_100) | ~v1_relat_1(A_100))), inference(cnfTransformation, [status(thm)], [f_102])).
% 15.57/7.08  tff(c_205, plain, (k4_relat_1('#skF_8')=k2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_78, c_202])).
% 15.57/7.08  tff(c_208, plain, (k4_relat_1('#skF_8')=k2_funct_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_205])).
% 15.57/7.08  tff(c_221, plain, (v1_relat_1(k2_funct_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_208, c_14])).
% 15.57/7.08  tff(c_231, plain, (v1_relat_1(k2_funct_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_221])).
% 15.57/7.08  tff(c_218, plain, (k4_relat_1(k2_funct_1('#skF_8'))='#skF_8' | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_208, c_16])).
% 15.57/7.08  tff(c_229, plain, (k4_relat_1(k2_funct_1('#skF_8'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_218])).
% 15.57/7.08  tff(c_215, plain, (k1_relat_1(k2_funct_1('#skF_8'))=k2_relat_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_208, c_20])).
% 15.57/7.08  tff(c_227, plain, (k1_relat_1(k2_funct_1('#skF_8'))=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_215])).
% 15.57/7.08  tff(c_1131, plain, (![A_139, C_140]: (k1_funct_1(A_139, '#skF_5'(A_139, k2_relat_1(A_139), C_140))=C_140 | ~r2_hidden(C_140, k2_relat_1(A_139)) | ~v1_funct_1(A_139) | ~v1_relat_1(A_139))), inference(cnfTransformation, [status(thm)], [f_94])).
% 15.57/7.08  tff(c_11189, plain, (![A_387, C_388]: (k1_funct_1(k4_relat_1(A_387), '#skF_5'(k4_relat_1(A_387), k1_relat_1(A_387), C_388))=C_388 | ~r2_hidden(C_388, k2_relat_1(k4_relat_1(A_387))) | ~v1_funct_1(k4_relat_1(A_387)) | ~v1_relat_1(k4_relat_1(A_387)) | ~v1_relat_1(A_387))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1131])).
% 15.57/7.08  tff(c_11325, plain, (![C_388]: (k1_funct_1(k4_relat_1(k2_funct_1('#skF_8')), '#skF_5'(k4_relat_1(k2_funct_1('#skF_8')), k2_relat_1('#skF_8'), C_388))=C_388 | ~r2_hidden(C_388, k2_relat_1(k4_relat_1(k2_funct_1('#skF_8')))) | ~v1_funct_1(k4_relat_1(k2_funct_1('#skF_8'))) | ~v1_relat_1(k4_relat_1(k2_funct_1('#skF_8'))) | ~v1_relat_1(k2_funct_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_227, c_11189])).
% 15.57/7.08  tff(c_11373, plain, (![C_388]: (k1_funct_1('#skF_8', '#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_388))=C_388 | ~r2_hidden(C_388, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_82, c_229, c_80, c_229, c_229, c_229, c_229, c_11325])).
% 15.57/7.08  tff(c_1382, plain, (![A_151, C_152]: (r2_hidden('#skF_5'(A_151, k2_relat_1(A_151), C_152), k1_relat_1(A_151)) | ~r2_hidden(C_152, k2_relat_1(A_151)) | ~v1_funct_1(A_151) | ~v1_relat_1(A_151))), inference(cnfTransformation, [status(thm)], [f_94])).
% 15.57/7.08  tff(c_10881, plain, (![A_380, C_381]: (r2_hidden('#skF_5'(k4_relat_1(A_380), k1_relat_1(A_380), C_381), k1_relat_1(k4_relat_1(A_380))) | ~r2_hidden(C_381, k2_relat_1(k4_relat_1(A_380))) | ~v1_funct_1(k4_relat_1(A_380)) | ~v1_relat_1(k4_relat_1(A_380)) | ~v1_relat_1(A_380))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1382])).
% 15.57/7.08  tff(c_11003, plain, (![C_381]: (r2_hidden('#skF_5'(k4_relat_1(k2_funct_1('#skF_8')), k2_relat_1('#skF_8'), C_381), k1_relat_1(k4_relat_1(k2_funct_1('#skF_8')))) | ~r2_hidden(C_381, k2_relat_1(k4_relat_1(k2_funct_1('#skF_8')))) | ~v1_funct_1(k4_relat_1(k2_funct_1('#skF_8'))) | ~v1_relat_1(k4_relat_1(k2_funct_1('#skF_8'))) | ~v1_relat_1(k2_funct_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_227, c_10881])).
% 15.57/7.08  tff(c_11053, plain, (![C_381]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_381), k1_relat_1('#skF_8')) | ~r2_hidden(C_381, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_82, c_229, c_80, c_229, c_229, c_229, c_229, c_11003])).
% 15.57/7.08  tff(c_1881, plain, (![B_181, A_182]: (k1_funct_1(k2_funct_1(B_181), k1_funct_1(B_181, A_182))=A_182 | ~r2_hidden(A_182, k1_relat_1(B_181)) | ~v2_funct_1(B_181) | ~v1_funct_1(B_181) | ~v1_relat_1(B_181))), inference(cnfTransformation, [status(thm)], [f_160])).
% 15.57/7.08  tff(c_15149, plain, (![A_449, C_450]: (k1_funct_1(k2_funct_1(A_449), C_450)='#skF_5'(A_449, k2_relat_1(A_449), C_450) | ~r2_hidden('#skF_5'(A_449, k2_relat_1(A_449), C_450), k1_relat_1(A_449)) | ~v2_funct_1(A_449) | ~v1_funct_1(A_449) | ~v1_relat_1(A_449) | ~r2_hidden(C_450, k2_relat_1(A_449)) | ~v1_funct_1(A_449) | ~v1_relat_1(A_449))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1881])).
% 15.57/7.08  tff(c_15164, plain, (![C_381]: (k1_funct_1(k2_funct_1('#skF_8'), C_381)='#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_381) | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(C_381, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_11053, c_15149])).
% 15.57/7.08  tff(c_15226, plain, (![C_451]: (k1_funct_1(k2_funct_1('#skF_8'), C_451)='#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_451) | ~r2_hidden(C_451, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_15164])).
% 15.57/7.08  tff(c_15380, plain, (k1_funct_1(k2_funct_1('#skF_8'), '#skF_7')='#skF_5'('#skF_8', k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_76, c_15226])).
% 15.57/7.08  tff(c_74, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_8'), '#skF_8'), '#skF_7')!='#skF_7' | k1_funct_1('#skF_8', k1_funct_1(k2_funct_1('#skF_8'), '#skF_7'))!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_173])).
% 15.57/7.08  tff(c_105, plain, (k1_funct_1('#skF_8', k1_funct_1(k2_funct_1('#skF_8'), '#skF_7'))!='#skF_7'), inference(splitLeft, [status(thm)], [c_74])).
% 15.57/7.08  tff(c_15381, plain, (k1_funct_1('#skF_8', '#skF_5'('#skF_8', k2_relat_1('#skF_8'), '#skF_7'))!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_15380, c_105])).
% 15.57/7.08  tff(c_15426, plain, (~r2_hidden('#skF_7', k2_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_11373, c_15381])).
% 15.57/7.08  tff(c_15433, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_15426])).
% 15.57/7.08  tff(c_15435, plain, (k1_funct_1('#skF_8', k1_funct_1(k2_funct_1('#skF_8'), '#skF_7'))='#skF_7'), inference(splitRight, [status(thm)], [c_74])).
% 15.57/7.08  tff(c_30987, plain, (k1_funct_1('#skF_8', '#skF_5'('#skF_8', k2_relat_1('#skF_8'), '#skF_7'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_30982, c_15435])).
% 15.57/7.08  tff(c_50, plain, (![A_62]: (v1_funct_1(k2_funct_1(A_62)) | ~v1_funct_1(A_62) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_110])).
% 15.57/7.08  tff(c_15549, plain, (k1_relat_1(k2_funct_1('#skF_8'))=k2_relat_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_15542, c_20])).
% 15.57/7.08  tff(c_15561, plain, (k1_relat_1(k2_funct_1('#skF_8'))=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_15549])).
% 15.57/7.08  tff(c_15797, plain, (![B_479, A_480]: (r2_hidden(k1_funct_1(B_479, A_480), k2_relat_1(B_479)) | ~r2_hidden(A_480, k1_relat_1(B_479)) | ~v1_funct_1(B_479) | ~v1_relat_1(B_479))), inference(cnfTransformation, [status(thm)], [f_122])).
% 15.57/7.08  tff(c_15802, plain, (![A_480]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_8'), A_480), k1_relat_1('#skF_8')) | ~r2_hidden(A_480, k1_relat_1(k2_funct_1('#skF_8'))) | ~v1_funct_1(k2_funct_1('#skF_8')) | ~v1_relat_1(k2_funct_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_15559, c_15797])).
% 15.57/7.08  tff(c_15814, plain, (![A_480]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_8'), A_480), k1_relat_1('#skF_8')) | ~r2_hidden(A_480, k2_relat_1('#skF_8')) | ~v1_funct_1(k2_funct_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_15565, c_15561, c_15802])).
% 15.57/7.08  tff(c_17801, plain, (~v1_funct_1(k2_funct_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_15814])).
% 15.57/7.08  tff(c_17804, plain, (~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_50, c_17801])).
% 15.57/7.08  tff(c_17808, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_17804])).
% 15.57/7.08  tff(c_17810, plain, (v1_funct_1(k2_funct_1('#skF_8'))), inference(splitRight, [status(thm)], [c_15814])).
% 15.57/7.08  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 15.57/7.08  tff(c_15997, plain, (![A_494, B_495]: (k1_relat_1(k5_relat_1(A_494, B_495))=k1_relat_1(A_494) | ~r1_tarski(k2_relat_1(A_494), k1_relat_1(B_495)) | ~v1_relat_1(B_495) | ~v1_relat_1(A_494))), inference(cnfTransformation, [status(thm)], [f_68])).
% 15.57/7.08  tff(c_16012, plain, (![B_495]: (k1_relat_1(k5_relat_1(k2_funct_1('#skF_8'), B_495))=k1_relat_1(k2_funct_1('#skF_8')) | ~r1_tarski(k1_relat_1('#skF_8'), k1_relat_1(B_495)) | ~v1_relat_1(B_495) | ~v1_relat_1(k2_funct_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_15559, c_15997])).
% 15.57/7.08  tff(c_17639, plain, (![B_569]: (k1_relat_1(k5_relat_1(k2_funct_1('#skF_8'), B_569))=k2_relat_1('#skF_8') | ~r1_tarski(k1_relat_1('#skF_8'), k1_relat_1(B_569)) | ~v1_relat_1(B_569))), inference(demodulation, [status(thm), theory('equality')], [c_15565, c_15561, c_16012])).
% 15.57/7.08  tff(c_17658, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_8'), '#skF_8'))=k2_relat_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_12, c_17639])).
% 15.57/7.08  tff(c_17667, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_8'), '#skF_8'))=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_17658])).
% 15.57/7.08  tff(c_15662, plain, (![B_474, A_475]: (k5_relat_1(k4_relat_1(B_474), k4_relat_1(A_475))=k4_relat_1(k5_relat_1(A_475, B_474)) | ~v1_relat_1(B_474) | ~v1_relat_1(A_475))), inference(cnfTransformation, [status(thm)], [f_75])).
% 15.57/7.08  tff(c_15680, plain, (![A_475]: (k5_relat_1(k2_funct_1('#skF_8'), k4_relat_1(A_475))=k4_relat_1(k5_relat_1(A_475, '#skF_8')) | ~v1_relat_1('#skF_8') | ~v1_relat_1(A_475))), inference(superposition, [status(thm), theory('equality')], [c_15542, c_15662])).
% 15.57/7.08  tff(c_15720, plain, (![A_477]: (k5_relat_1(k2_funct_1('#skF_8'), k4_relat_1(A_477))=k4_relat_1(k5_relat_1(A_477, '#skF_8')) | ~v1_relat_1(A_477))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_15680])).
% 15.57/7.08  tff(c_15732, plain, (k4_relat_1(k5_relat_1(k2_funct_1('#skF_8'), '#skF_8'))=k5_relat_1(k2_funct_1('#skF_8'), '#skF_8') | ~v1_relat_1(k2_funct_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_15563, c_15720])).
% 15.57/7.08  tff(c_15744, plain, (k4_relat_1(k5_relat_1(k2_funct_1('#skF_8'), '#skF_8'))=k5_relat_1(k2_funct_1('#skF_8'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_15565, c_15732])).
% 15.57/7.08  tff(c_26, plain, (![B_19, A_17]: (k5_relat_1(k4_relat_1(B_19), k4_relat_1(A_17))=k4_relat_1(k5_relat_1(A_17, B_19)) | ~v1_relat_1(B_19) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_75])).
% 15.57/7.08  tff(c_18626, plain, (![C_608, B_609, A_610]: (k1_funct_1(k5_relat_1(C_608, B_609), A_610)=k1_funct_1(B_609, k1_funct_1(C_608, A_610)) | ~r2_hidden(A_610, k1_relat_1(k5_relat_1(C_608, B_609))) | ~v1_funct_1(C_608) | ~v1_relat_1(C_608) | ~v1_funct_1(B_609) | ~v1_relat_1(B_609))), inference(cnfTransformation, [status(thm)], [f_135])).
% 15.57/7.08  tff(c_32773, plain, (![B_865, A_866, A_867]: (k1_funct_1(k5_relat_1(k4_relat_1(B_865), k4_relat_1(A_866)), A_867)=k1_funct_1(k4_relat_1(A_866), k1_funct_1(k4_relat_1(B_865), A_867)) | ~r2_hidden(A_867, k1_relat_1(k4_relat_1(k5_relat_1(A_866, B_865)))) | ~v1_funct_1(k4_relat_1(B_865)) | ~v1_relat_1(k4_relat_1(B_865)) | ~v1_funct_1(k4_relat_1(A_866)) | ~v1_relat_1(k4_relat_1(A_866)) | ~v1_relat_1(B_865) | ~v1_relat_1(A_866))), inference(superposition, [status(thm), theory('equality')], [c_26, c_18626])).
% 15.57/7.08  tff(c_32996, plain, (![A_867]: (k1_funct_1(k5_relat_1(k4_relat_1('#skF_8'), k4_relat_1(k2_funct_1('#skF_8'))), A_867)=k1_funct_1(k4_relat_1(k2_funct_1('#skF_8')), k1_funct_1(k4_relat_1('#skF_8'), A_867)) | ~r2_hidden(A_867, k1_relat_1(k5_relat_1(k2_funct_1('#skF_8'), '#skF_8'))) | ~v1_funct_1(k4_relat_1('#skF_8')) | ~v1_relat_1(k4_relat_1('#skF_8')) | ~v1_funct_1(k4_relat_1(k2_funct_1('#skF_8'))) | ~v1_relat_1(k4_relat_1(k2_funct_1('#skF_8'))) | ~v1_relat_1('#skF_8') | ~v1_relat_1(k2_funct_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_15744, c_32773])).
% 15.57/7.08  tff(c_38553, plain, (![A_947]: (k1_funct_1(k5_relat_1(k2_funct_1('#skF_8'), '#skF_8'), A_947)=k1_funct_1('#skF_8', k1_funct_1(k2_funct_1('#skF_8'), A_947)) | ~r2_hidden(A_947, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_15565, c_82, c_82, c_15563, c_80, c_15563, c_15565, c_15542, c_17810, c_15542, c_17667, c_15542, c_15542, c_15563, c_15563, c_32996])).
% 15.57/7.08  tff(c_15434, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_8'), '#skF_8'), '#skF_7')!='#skF_7'), inference(splitRight, [status(thm)], [c_74])).
% 15.57/7.08  tff(c_38602, plain, (k1_funct_1('#skF_8', k1_funct_1(k2_funct_1('#skF_8'), '#skF_7'))!='#skF_7' | ~r2_hidden('#skF_7', k2_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_38553, c_15434])).
% 15.57/7.08  tff(c_38641, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_30987, c_30982, c_38602])).
% 15.57/7.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.57/7.08  
% 15.57/7.08  Inference rules
% 15.57/7.08  ----------------------
% 15.57/7.08  #Ref     : 8
% 15.57/7.08  #Sup     : 9258
% 15.57/7.08  #Fact    : 0
% 15.57/7.08  #Define  : 0
% 15.57/7.08  #Split   : 41
% 15.57/7.08  #Chain   : 0
% 15.57/7.08  #Close   : 0
% 15.57/7.08  
% 15.57/7.08  Ordering : KBO
% 15.57/7.08  
% 15.57/7.08  Simplification rules
% 15.57/7.08  ----------------------
% 15.57/7.08  #Subsume      : 1503
% 15.57/7.08  #Demod        : 15865
% 15.57/7.08  #Tautology    : 2278
% 15.57/7.08  #SimpNegUnit  : 73
% 15.57/7.08  #BackRed      : 347
% 15.57/7.08  
% 15.57/7.08  #Partial instantiations: 0
% 15.57/7.08  #Strategies tried      : 1
% 15.57/7.08  
% 15.57/7.08  Timing (in seconds)
% 15.57/7.08  ----------------------
% 15.57/7.09  Preprocessing        : 0.36
% 15.57/7.09  Parsing              : 0.18
% 15.57/7.09  CNF conversion       : 0.03
% 15.57/7.09  Main loop            : 5.96
% 15.57/7.09  Inferencing          : 1.38
% 15.57/7.09  Reduction            : 2.43
% 15.57/7.09  Demodulation         : 1.91
% 15.57/7.09  BG Simplification    : 0.20
% 15.57/7.09  Subsumption          : 1.55
% 15.57/7.09  Abstraction          : 0.28
% 15.57/7.09  MUC search           : 0.00
% 15.57/7.09  Cooper               : 0.00
% 15.57/7.09  Total                : 6.37
% 15.57/7.09  Index Insertion      : 0.00
% 15.57/7.09  Index Deletion       : 0.00
% 15.57/7.09  Index Matching       : 0.00
% 15.57/7.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
