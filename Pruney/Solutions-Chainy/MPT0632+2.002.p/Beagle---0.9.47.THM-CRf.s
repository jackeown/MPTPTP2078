%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:19 EST 2020

% Result     : Theorem 4.15s
% Output     : CNFRefutation 4.63s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 397 expanded)
%              Number of leaves         :   28 ( 145 expanded)
%              Depth                    :   18
%              Number of atoms          :  285 (1095 expanded)
%              Number of equality atoms :   97 ( 546 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_109,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( B = k6_relat_1(A)
        <=> ( k1_relat_1(B) = A
            & ! [C] :
                ( r2_hidden(C,A)
               => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_95,axiom,(
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

tff(f_52,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(c_56,plain,
    ( k6_relat_1('#skF_6') = '#skF_7'
    | k1_relat_1('#skF_7') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_81,plain,(
    k1_relat_1('#skF_7') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_48,plain,
    ( r2_hidden('#skF_8','#skF_6')
    | k1_relat_1('#skF_7') != '#skF_6'
    | k6_relat_1('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_106,plain,
    ( r2_hidden('#skF_8','#skF_6')
    | k6_relat_1('#skF_6') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_48])).

tff(c_107,plain,(
    k6_relat_1('#skF_6') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_28,plain,(
    ! [A_44] : v1_relat_1(k6_relat_1(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_30,plain,(
    ! [A_44] : v1_funct_1(k6_relat_1(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [A_1] : k1_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_40,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_732,plain,(
    ! [A_106,B_107] :
      ( r2_hidden('#skF_5'(A_106,B_107),k1_relat_1(A_106))
      | B_107 = A_106
      | k1_relat_1(B_107) != k1_relat_1(A_106)
      | ~ v1_funct_1(B_107)
      | ~ v1_relat_1(B_107)
      | ~ v1_funct_1(A_106)
      | ~ v1_relat_1(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_735,plain,(
    ! [B_107] :
      ( r2_hidden('#skF_5'('#skF_7',B_107),'#skF_6')
      | B_107 = '#skF_7'
      | k1_relat_1(B_107) != k1_relat_1('#skF_7')
      | ~ v1_funct_1(B_107)
      | ~ v1_relat_1(B_107)
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_732])).

tff(c_740,plain,(
    ! [B_107] :
      ( r2_hidden('#skF_5'('#skF_7',B_107),'#skF_6')
      | B_107 = '#skF_7'
      | k1_relat_1(B_107) != '#skF_6'
      | ~ v1_funct_1(B_107)
      | ~ v1_relat_1(B_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_81,c_735])).

tff(c_4,plain,(
    ! [A_1] : k2_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_169,plain,(
    ! [A_73,C_74] :
      ( r2_hidden('#skF_4'(A_73,k2_relat_1(A_73),C_74),k1_relat_1(A_73))
      | ~ r2_hidden(C_74,k2_relat_1(A_73))
      | ~ v1_funct_1(A_73)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_175,plain,(
    ! [A_1,C_74] :
      ( r2_hidden('#skF_4'(k6_relat_1(A_1),k2_relat_1(k6_relat_1(A_1)),C_74),A_1)
      | ~ r2_hidden(C_74,k2_relat_1(k6_relat_1(A_1)))
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_169])).

tff(c_182,plain,(
    ! [A_1,C_74] :
      ( r2_hidden('#skF_4'(k6_relat_1(A_1),A_1,C_74),A_1)
      | ~ r2_hidden(C_74,A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_4,c_4,c_175])).

tff(c_12,plain,(
    ! [A_4,C_40] :
      ( k1_funct_1(A_4,'#skF_4'(A_4,k2_relat_1(A_4),C_40)) = C_40
      | ~ r2_hidden(C_40,k2_relat_1(A_4))
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_86,plain,(
    ! [A_64] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_64)),A_64) = A_64
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_95,plain,
    ( k5_relat_1(k6_relat_1('#skF_6'),'#skF_7') = '#skF_7'
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_86])).

tff(c_102,plain,(
    k5_relat_1(k6_relat_1('#skF_6'),'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_95])).

tff(c_1226,plain,(
    ! [B_131,C_132,A_133] :
      ( k1_funct_1(k5_relat_1(B_131,C_132),A_133) = k1_funct_1(C_132,k1_funct_1(B_131,A_133))
      | ~ r2_hidden(A_133,k1_relat_1(B_131))
      | ~ v1_funct_1(C_132)
      | ~ v1_relat_1(C_132)
      | ~ v1_funct_1(B_131)
      | ~ v1_relat_1(B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1269,plain,(
    ! [A_1,C_132,A_133] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_1),C_132),A_133) = k1_funct_1(C_132,k1_funct_1(k6_relat_1(A_1),A_133))
      | ~ r2_hidden(A_133,A_1)
      | ~ v1_funct_1(C_132)
      | ~ v1_relat_1(C_132)
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1226])).

tff(c_1383,plain,(
    ! [A_137,C_138,A_139] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_137),C_138),A_139) = k1_funct_1(C_138,k1_funct_1(k6_relat_1(A_137),A_139))
      | ~ r2_hidden(A_139,A_137)
      | ~ v1_funct_1(C_138)
      | ~ v1_relat_1(C_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_1269])).

tff(c_1418,plain,(
    ! [A_139] :
      ( k1_funct_1('#skF_7',k1_funct_1(k6_relat_1('#skF_6'),A_139)) = k1_funct_1('#skF_7',A_139)
      | ~ r2_hidden(A_139,'#skF_6')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_1383])).

tff(c_1430,plain,(
    ! [A_140] :
      ( k1_funct_1('#skF_7',k1_funct_1(k6_relat_1('#skF_6'),A_140)) = k1_funct_1('#skF_7',A_140)
      | ~ r2_hidden(A_140,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1418])).

tff(c_141,plain,(
    ! [B_68,A_69] :
      ( r2_hidden(k1_funct_1(B_68,A_69),k2_relat_1(B_68))
      | ~ r2_hidden(A_69,k1_relat_1(B_68))
      | ~ v1_funct_1(B_68)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_144,plain,(
    ! [A_1,A_69] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_1),A_69),A_1)
      | ~ r2_hidden(A_69,k1_relat_1(k6_relat_1(A_1)))
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_141])).

tff(c_147,plain,(
    ! [A_70,A_71] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_70),A_71),A_70)
      | ~ r2_hidden(A_71,A_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_2,c_144])).

tff(c_50,plain,(
    ! [C_59] :
      ( k6_relat_1('#skF_6') = '#skF_7'
      | k1_funct_1('#skF_7',C_59) = C_59
      | ~ r2_hidden(C_59,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_137,plain,(
    ! [C_59] :
      ( k1_funct_1('#skF_7',C_59) = C_59
      | ~ r2_hidden(C_59,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_50])).

tff(c_152,plain,(
    ! [A_71] :
      ( k1_funct_1('#skF_7',k1_funct_1(k6_relat_1('#skF_6'),A_71)) = k1_funct_1(k6_relat_1('#skF_6'),A_71)
      | ~ r2_hidden(A_71,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_147,c_137])).

tff(c_1485,plain,(
    ! [A_141] :
      ( k1_funct_1(k6_relat_1('#skF_6'),A_141) = k1_funct_1('#skF_7',A_141)
      | ~ r2_hidden(A_141,'#skF_6')
      | ~ r2_hidden(A_141,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1430,c_152])).

tff(c_1542,plain,(
    ! [C_40] :
      ( k1_funct_1('#skF_7','#skF_4'(k6_relat_1('#skF_6'),k2_relat_1(k6_relat_1('#skF_6')),C_40)) = C_40
      | ~ r2_hidden('#skF_4'(k6_relat_1('#skF_6'),k2_relat_1(k6_relat_1('#skF_6')),C_40),'#skF_6')
      | ~ r2_hidden('#skF_4'(k6_relat_1('#skF_6'),k2_relat_1(k6_relat_1('#skF_6')),C_40),'#skF_6')
      | ~ r2_hidden(C_40,k2_relat_1(k6_relat_1('#skF_6')))
      | ~ v1_funct_1(k6_relat_1('#skF_6'))
      | ~ v1_relat_1(k6_relat_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1485])).

tff(c_1716,plain,(
    ! [C_149] :
      ( k1_funct_1('#skF_7','#skF_4'(k6_relat_1('#skF_6'),'#skF_6',C_149)) = C_149
      | ~ r2_hidden('#skF_4'(k6_relat_1('#skF_6'),'#skF_6',C_149),'#skF_6')
      | ~ r2_hidden(C_149,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_4,c_4,c_4,c_4,c_1542])).

tff(c_1844,plain,(
    ! [C_151] :
      ( k1_funct_1('#skF_7','#skF_4'(k6_relat_1('#skF_6'),'#skF_6',C_151)) = C_151
      | ~ r2_hidden(C_151,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_182,c_1716])).

tff(c_185,plain,(
    ! [A_75,C_76] :
      ( r2_hidden('#skF_4'(k6_relat_1(A_75),A_75,C_76),A_75)
      | ~ r2_hidden(C_76,A_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_4,c_4,c_175])).

tff(c_190,plain,(
    ! [C_76] :
      ( k1_funct_1('#skF_7','#skF_4'(k6_relat_1('#skF_6'),'#skF_6',C_76)) = '#skF_4'(k6_relat_1('#skF_6'),'#skF_6',C_76)
      | ~ r2_hidden(C_76,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_185,c_137])).

tff(c_1882,plain,(
    ! [C_152] :
      ( '#skF_4'(k6_relat_1('#skF_6'),'#skF_6',C_152) = C_152
      | ~ r2_hidden(C_152,'#skF_6')
      | ~ r2_hidden(C_152,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1844,c_190])).

tff(c_196,plain,(
    ! [A_78,C_79] :
      ( k1_funct_1(A_78,'#skF_4'(A_78,k2_relat_1(A_78),C_79)) = C_79
      | ~ r2_hidden(C_79,k2_relat_1(A_78))
      | ~ v1_funct_1(A_78)
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_216,plain,(
    ! [A_1,C_79] :
      ( k1_funct_1(k6_relat_1(A_1),'#skF_4'(k6_relat_1(A_1),A_1,C_79)) = C_79
      | ~ r2_hidden(C_79,k2_relat_1(k6_relat_1(A_1)))
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_196])).

tff(c_224,plain,(
    ! [A_1,C_79] :
      ( k1_funct_1(k6_relat_1(A_1),'#skF_4'(k6_relat_1(A_1),A_1,C_79)) = C_79
      | ~ r2_hidden(C_79,A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_4,c_216])).

tff(c_1900,plain,(
    ! [C_152] :
      ( k1_funct_1(k6_relat_1('#skF_6'),C_152) = C_152
      | ~ r2_hidden(C_152,'#skF_6')
      | ~ r2_hidden(C_152,'#skF_6')
      | ~ r2_hidden(C_152,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1882,c_224])).

tff(c_842,plain,(
    ! [B_112] :
      ( r2_hidden('#skF_5'('#skF_7',B_112),'#skF_6')
      | B_112 = '#skF_7'
      | k1_relat_1(B_112) != '#skF_6'
      | ~ v1_funct_1(B_112)
      | ~ v1_relat_1(B_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_81,c_735])).

tff(c_850,plain,(
    ! [B_112] :
      ( k1_funct_1('#skF_7','#skF_5'('#skF_7',B_112)) = '#skF_5'('#skF_7',B_112)
      | B_112 = '#skF_7'
      | k1_relat_1(B_112) != '#skF_6'
      | ~ v1_funct_1(B_112)
      | ~ v1_relat_1(B_112) ) ),
    inference(resolution,[status(thm)],[c_842,c_137])).

tff(c_2028,plain,(
    ! [B_156,A_157] :
      ( k1_funct_1(B_156,'#skF_5'(A_157,B_156)) != k1_funct_1(A_157,'#skF_5'(A_157,B_156))
      | B_156 = A_157
      | k1_relat_1(B_156) != k1_relat_1(A_157)
      | ~ v1_funct_1(B_156)
      | ~ v1_relat_1(B_156)
      | ~ v1_funct_1(A_157)
      | ~ v1_relat_1(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2063,plain,(
    ! [B_112] :
      ( k1_funct_1(B_112,'#skF_5'('#skF_7',B_112)) != '#skF_5'('#skF_7',B_112)
      | B_112 = '#skF_7'
      | k1_relat_1(B_112) != k1_relat_1('#skF_7')
      | ~ v1_funct_1(B_112)
      | ~ v1_relat_1(B_112)
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | B_112 = '#skF_7'
      | k1_relat_1(B_112) != '#skF_6'
      | ~ v1_funct_1(B_112)
      | ~ v1_relat_1(B_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_850,c_2028])).

tff(c_2138,plain,(
    ! [B_161] :
      ( k1_funct_1(B_161,'#skF_5'('#skF_7',B_161)) != '#skF_5'('#skF_7',B_161)
      | B_161 = '#skF_7'
      | k1_relat_1(B_161) != '#skF_6'
      | ~ v1_funct_1(B_161)
      | ~ v1_relat_1(B_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_81,c_2063])).

tff(c_2142,plain,
    ( k6_relat_1('#skF_6') = '#skF_7'
    | k1_relat_1(k6_relat_1('#skF_6')) != '#skF_6'
    | ~ v1_funct_1(k6_relat_1('#skF_6'))
    | ~ v1_relat_1(k6_relat_1('#skF_6'))
    | ~ r2_hidden('#skF_5'('#skF_7',k6_relat_1('#skF_6')),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1900,c_2138])).

tff(c_2161,plain,
    ( k6_relat_1('#skF_6') = '#skF_7'
    | ~ r2_hidden('#skF_5'('#skF_7',k6_relat_1('#skF_6')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_2,c_2142])).

tff(c_2162,plain,(
    ~ r2_hidden('#skF_5'('#skF_7',k6_relat_1('#skF_6')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_2161])).

tff(c_2172,plain,
    ( k6_relat_1('#skF_6') = '#skF_7'
    | k1_relat_1(k6_relat_1('#skF_6')) != '#skF_6'
    | ~ v1_funct_1(k6_relat_1('#skF_6'))
    | ~ v1_relat_1(k6_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_740,c_2162])).

tff(c_2175,plain,(
    k6_relat_1('#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_2,c_2172])).

tff(c_2177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_2175])).

tff(c_2179,plain,(
    k6_relat_1('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_46,plain,
    ( k1_funct_1('#skF_7','#skF_8') != '#skF_8'
    | k1_relat_1('#skF_7') != '#skF_6'
    | k6_relat_1('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2245,plain,(
    k1_funct_1('#skF_7','#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2179,c_81,c_46])).

tff(c_2178,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_2186,plain,(
    k2_relat_1('#skF_7') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_2179,c_4])).

tff(c_2317,plain,(
    ! [A_172,C_173] :
      ( r2_hidden('#skF_4'(A_172,k2_relat_1(A_172),C_173),k1_relat_1(A_172))
      | ~ r2_hidden(C_173,k2_relat_1(A_172))
      | ~ v1_funct_1(A_172)
      | ~ v1_relat_1(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2323,plain,(
    ! [C_173] :
      ( r2_hidden('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_173),'#skF_6')
      | ~ r2_hidden(C_173,k2_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_2317])).

tff(c_2333,plain,(
    ! [C_173] :
      ( r2_hidden('#skF_4'('#skF_7','#skF_6',C_173),'#skF_6')
      | ~ r2_hidden(C_173,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_2186,c_2186,c_2323])).

tff(c_8,plain,(
    ! [A_3] :
      ( k5_relat_1(A_3,k6_relat_1(k2_relat_1(A_3))) = A_3
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2438,plain,(
    ! [B_197,C_198,A_199] :
      ( k1_funct_1(k5_relat_1(B_197,C_198),A_199) = k1_funct_1(C_198,k1_funct_1(B_197,A_199))
      | ~ r2_hidden(A_199,k1_relat_1(B_197))
      | ~ v1_funct_1(C_198)
      | ~ v1_relat_1(C_198)
      | ~ v1_funct_1(B_197)
      | ~ v1_relat_1(B_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2479,plain,(
    ! [C_198,A_199] :
      ( k1_funct_1(k5_relat_1('#skF_7',C_198),A_199) = k1_funct_1(C_198,k1_funct_1('#skF_7',A_199))
      | ~ r2_hidden(A_199,'#skF_6')
      | ~ v1_funct_1(C_198)
      | ~ v1_relat_1(C_198)
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_2438])).

tff(c_2505,plain,(
    ! [C_201,A_202] :
      ( k1_funct_1(k5_relat_1('#skF_7',C_201),A_202) = k1_funct_1(C_201,k1_funct_1('#skF_7',A_202))
      | ~ r2_hidden(A_202,'#skF_6')
      | ~ v1_funct_1(C_201)
      | ~ v1_relat_1(C_201) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_2479])).

tff(c_2537,plain,(
    ! [A_202] :
      ( k1_funct_1(k6_relat_1(k2_relat_1('#skF_7')),k1_funct_1('#skF_7',A_202)) = k1_funct_1('#skF_7',A_202)
      | ~ r2_hidden(A_202,'#skF_6')
      | ~ v1_funct_1(k6_relat_1(k2_relat_1('#skF_7')))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1('#skF_7')))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2505])).

tff(c_2544,plain,(
    ! [A_203] :
      ( k1_funct_1('#skF_7',k1_funct_1('#skF_7',A_203)) = k1_funct_1('#skF_7',A_203)
      | ~ r2_hidden(A_203,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_28,c_30,c_2179,c_2186,c_2537])).

tff(c_2571,plain,(
    ! [C_40] :
      ( k1_funct_1('#skF_7','#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_40)) = k1_funct_1('#skF_7',C_40)
      | ~ r2_hidden('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_40),'#skF_6')
      | ~ r2_hidden(C_40,k2_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2544])).

tff(c_2580,plain,(
    ! [C_204] :
      ( k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_6',C_204)) = k1_funct_1('#skF_7',C_204)
      | ~ r2_hidden('#skF_4'('#skF_7','#skF_6',C_204),'#skF_6')
      | ~ r2_hidden(C_204,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_2186,c_2186,c_2186,c_2571])).

tff(c_2585,plain,(
    ! [C_205] :
      ( k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_6',C_205)) = k1_funct_1('#skF_7',C_205)
      | ~ r2_hidden(C_205,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2333,c_2580])).

tff(c_2261,plain,(
    ! [A_166,C_167] :
      ( k1_funct_1(A_166,'#skF_4'(A_166,k2_relat_1(A_166),C_167)) = C_167
      | ~ r2_hidden(C_167,k2_relat_1(A_166))
      | ~ v1_funct_1(A_166)
      | ~ v1_relat_1(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2273,plain,(
    ! [C_167] :
      ( k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_6',C_167)) = C_167
      | ~ r2_hidden(C_167,k2_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2186,c_2261])).

tff(c_2280,plain,(
    ! [C_167] :
      ( k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_6',C_167)) = C_167
      | ~ r2_hidden(C_167,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_2186,c_2273])).

tff(c_2611,plain,(
    ! [C_206] :
      ( k1_funct_1('#skF_7',C_206) = C_206
      | ~ r2_hidden(C_206,'#skF_6')
      | ~ r2_hidden(C_206,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2585,c_2280])).

tff(c_2649,plain,
    ( k1_funct_1('#skF_7','#skF_8') = '#skF_8'
    | ~ r2_hidden('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_2178,c_2611])).

tff(c_2669,plain,(
    k1_funct_1('#skF_7','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2178,c_2649])).

tff(c_2671,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2245,c_2669])).

tff(c_2673,plain,(
    k1_relat_1('#skF_7') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2672,plain,(
    k6_relat_1('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2677,plain,(
    k1_relat_1('#skF_7') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_2672,c_2])).

tff(c_2694,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2673,c_2677])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:40:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.15/1.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/1.78  
% 4.15/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.48/1.78  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_5
% 4.48/1.78  
% 4.48/1.78  %Foreground sorts:
% 4.48/1.78  
% 4.48/1.78  
% 4.48/1.78  %Background operators:
% 4.48/1.78  
% 4.48/1.78  
% 4.48/1.78  %Foreground operators:
% 4.48/1.78  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.48/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.48/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.48/1.78  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.48/1.78  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.48/1.78  tff('#skF_7', type, '#skF_7': $i).
% 4.48/1.78  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.48/1.78  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.48/1.78  tff('#skF_6', type, '#skF_6': $i).
% 4.48/1.78  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.48/1.78  tff('#skF_8', type, '#skF_8': $i).
% 4.48/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.48/1.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.48/1.78  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.48/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.48/1.78  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.48/1.78  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.48/1.78  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.48/1.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.48/1.78  
% 4.63/1.82  tff(f_109, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 4.63/1.82  tff(f_56, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 4.63/1.82  tff(f_29, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 4.63/1.82  tff(f_95, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 4.63/1.82  tff(f_52, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 4.63/1.82  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 4.63/1.82  tff(f_77, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 4.63/1.82  tff(f_64, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 4.63/1.82  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 4.63/1.82  tff(c_56, plain, (k6_relat_1('#skF_6')='#skF_7' | k1_relat_1('#skF_7')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.63/1.82  tff(c_81, plain, (k1_relat_1('#skF_7')='#skF_6'), inference(splitLeft, [status(thm)], [c_56])).
% 4.63/1.82  tff(c_48, plain, (r2_hidden('#skF_8', '#skF_6') | k1_relat_1('#skF_7')!='#skF_6' | k6_relat_1('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.63/1.82  tff(c_106, plain, (r2_hidden('#skF_8', '#skF_6') | k6_relat_1('#skF_6')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_81, c_48])).
% 4.63/1.82  tff(c_107, plain, (k6_relat_1('#skF_6')!='#skF_7'), inference(splitLeft, [status(thm)], [c_106])).
% 4.63/1.82  tff(c_28, plain, (![A_44]: (v1_relat_1(k6_relat_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.63/1.82  tff(c_30, plain, (![A_44]: (v1_funct_1(k6_relat_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.63/1.82  tff(c_2, plain, (![A_1]: (k1_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.63/1.82  tff(c_42, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.63/1.82  tff(c_40, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.63/1.82  tff(c_732, plain, (![A_106, B_107]: (r2_hidden('#skF_5'(A_106, B_107), k1_relat_1(A_106)) | B_107=A_106 | k1_relat_1(B_107)!=k1_relat_1(A_106) | ~v1_funct_1(B_107) | ~v1_relat_1(B_107) | ~v1_funct_1(A_106) | ~v1_relat_1(A_106))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.63/1.82  tff(c_735, plain, (![B_107]: (r2_hidden('#skF_5'('#skF_7', B_107), '#skF_6') | B_107='#skF_7' | k1_relat_1(B_107)!=k1_relat_1('#skF_7') | ~v1_funct_1(B_107) | ~v1_relat_1(B_107) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_732])).
% 4.63/1.82  tff(c_740, plain, (![B_107]: (r2_hidden('#skF_5'('#skF_7', B_107), '#skF_6') | B_107='#skF_7' | k1_relat_1(B_107)!='#skF_6' | ~v1_funct_1(B_107) | ~v1_relat_1(B_107))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_81, c_735])).
% 4.63/1.82  tff(c_4, plain, (![A_1]: (k2_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.63/1.82  tff(c_169, plain, (![A_73, C_74]: (r2_hidden('#skF_4'(A_73, k2_relat_1(A_73), C_74), k1_relat_1(A_73)) | ~r2_hidden(C_74, k2_relat_1(A_73)) | ~v1_funct_1(A_73) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.63/1.82  tff(c_175, plain, (![A_1, C_74]: (r2_hidden('#skF_4'(k6_relat_1(A_1), k2_relat_1(k6_relat_1(A_1)), C_74), A_1) | ~r2_hidden(C_74, k2_relat_1(k6_relat_1(A_1))) | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_169])).
% 4.63/1.82  tff(c_182, plain, (![A_1, C_74]: (r2_hidden('#skF_4'(k6_relat_1(A_1), A_1, C_74), A_1) | ~r2_hidden(C_74, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_4, c_4, c_175])).
% 4.63/1.82  tff(c_12, plain, (![A_4, C_40]: (k1_funct_1(A_4, '#skF_4'(A_4, k2_relat_1(A_4), C_40))=C_40 | ~r2_hidden(C_40, k2_relat_1(A_4)) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.63/1.82  tff(c_86, plain, (![A_64]: (k5_relat_1(k6_relat_1(k1_relat_1(A_64)), A_64)=A_64 | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.63/1.82  tff(c_95, plain, (k5_relat_1(k6_relat_1('#skF_6'), '#skF_7')='#skF_7' | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_81, c_86])).
% 4.63/1.82  tff(c_102, plain, (k5_relat_1(k6_relat_1('#skF_6'), '#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_95])).
% 4.63/1.82  tff(c_1226, plain, (![B_131, C_132, A_133]: (k1_funct_1(k5_relat_1(B_131, C_132), A_133)=k1_funct_1(C_132, k1_funct_1(B_131, A_133)) | ~r2_hidden(A_133, k1_relat_1(B_131)) | ~v1_funct_1(C_132) | ~v1_relat_1(C_132) | ~v1_funct_1(B_131) | ~v1_relat_1(B_131))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.63/1.82  tff(c_1269, plain, (![A_1, C_132, A_133]: (k1_funct_1(k5_relat_1(k6_relat_1(A_1), C_132), A_133)=k1_funct_1(C_132, k1_funct_1(k6_relat_1(A_1), A_133)) | ~r2_hidden(A_133, A_1) | ~v1_funct_1(C_132) | ~v1_relat_1(C_132) | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1226])).
% 4.63/1.82  tff(c_1383, plain, (![A_137, C_138, A_139]: (k1_funct_1(k5_relat_1(k6_relat_1(A_137), C_138), A_139)=k1_funct_1(C_138, k1_funct_1(k6_relat_1(A_137), A_139)) | ~r2_hidden(A_139, A_137) | ~v1_funct_1(C_138) | ~v1_relat_1(C_138))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_1269])).
% 4.63/1.82  tff(c_1418, plain, (![A_139]: (k1_funct_1('#skF_7', k1_funct_1(k6_relat_1('#skF_6'), A_139))=k1_funct_1('#skF_7', A_139) | ~r2_hidden(A_139, '#skF_6') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_1383])).
% 4.63/1.82  tff(c_1430, plain, (![A_140]: (k1_funct_1('#skF_7', k1_funct_1(k6_relat_1('#skF_6'), A_140))=k1_funct_1('#skF_7', A_140) | ~r2_hidden(A_140, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1418])).
% 4.63/1.82  tff(c_141, plain, (![B_68, A_69]: (r2_hidden(k1_funct_1(B_68, A_69), k2_relat_1(B_68)) | ~r2_hidden(A_69, k1_relat_1(B_68)) | ~v1_funct_1(B_68) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.63/1.82  tff(c_144, plain, (![A_1, A_69]: (r2_hidden(k1_funct_1(k6_relat_1(A_1), A_69), A_1) | ~r2_hidden(A_69, k1_relat_1(k6_relat_1(A_1))) | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_141])).
% 4.63/1.82  tff(c_147, plain, (![A_70, A_71]: (r2_hidden(k1_funct_1(k6_relat_1(A_70), A_71), A_70) | ~r2_hidden(A_71, A_70))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_2, c_144])).
% 4.63/1.82  tff(c_50, plain, (![C_59]: (k6_relat_1('#skF_6')='#skF_7' | k1_funct_1('#skF_7', C_59)=C_59 | ~r2_hidden(C_59, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.63/1.82  tff(c_137, plain, (![C_59]: (k1_funct_1('#skF_7', C_59)=C_59 | ~r2_hidden(C_59, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_107, c_50])).
% 4.63/1.82  tff(c_152, plain, (![A_71]: (k1_funct_1('#skF_7', k1_funct_1(k6_relat_1('#skF_6'), A_71))=k1_funct_1(k6_relat_1('#skF_6'), A_71) | ~r2_hidden(A_71, '#skF_6'))), inference(resolution, [status(thm)], [c_147, c_137])).
% 4.63/1.82  tff(c_1485, plain, (![A_141]: (k1_funct_1(k6_relat_1('#skF_6'), A_141)=k1_funct_1('#skF_7', A_141) | ~r2_hidden(A_141, '#skF_6') | ~r2_hidden(A_141, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1430, c_152])).
% 4.63/1.82  tff(c_1542, plain, (![C_40]: (k1_funct_1('#skF_7', '#skF_4'(k6_relat_1('#skF_6'), k2_relat_1(k6_relat_1('#skF_6')), C_40))=C_40 | ~r2_hidden('#skF_4'(k6_relat_1('#skF_6'), k2_relat_1(k6_relat_1('#skF_6')), C_40), '#skF_6') | ~r2_hidden('#skF_4'(k6_relat_1('#skF_6'), k2_relat_1(k6_relat_1('#skF_6')), C_40), '#skF_6') | ~r2_hidden(C_40, k2_relat_1(k6_relat_1('#skF_6'))) | ~v1_funct_1(k6_relat_1('#skF_6')) | ~v1_relat_1(k6_relat_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1485])).
% 4.63/1.82  tff(c_1716, plain, (![C_149]: (k1_funct_1('#skF_7', '#skF_4'(k6_relat_1('#skF_6'), '#skF_6', C_149))=C_149 | ~r2_hidden('#skF_4'(k6_relat_1('#skF_6'), '#skF_6', C_149), '#skF_6') | ~r2_hidden(C_149, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_4, c_4, c_4, c_4, c_1542])).
% 4.63/1.82  tff(c_1844, plain, (![C_151]: (k1_funct_1('#skF_7', '#skF_4'(k6_relat_1('#skF_6'), '#skF_6', C_151))=C_151 | ~r2_hidden(C_151, '#skF_6'))), inference(resolution, [status(thm)], [c_182, c_1716])).
% 4.63/1.82  tff(c_185, plain, (![A_75, C_76]: (r2_hidden('#skF_4'(k6_relat_1(A_75), A_75, C_76), A_75) | ~r2_hidden(C_76, A_75))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_4, c_4, c_175])).
% 4.63/1.82  tff(c_190, plain, (![C_76]: (k1_funct_1('#skF_7', '#skF_4'(k6_relat_1('#skF_6'), '#skF_6', C_76))='#skF_4'(k6_relat_1('#skF_6'), '#skF_6', C_76) | ~r2_hidden(C_76, '#skF_6'))), inference(resolution, [status(thm)], [c_185, c_137])).
% 4.63/1.82  tff(c_1882, plain, (![C_152]: ('#skF_4'(k6_relat_1('#skF_6'), '#skF_6', C_152)=C_152 | ~r2_hidden(C_152, '#skF_6') | ~r2_hidden(C_152, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1844, c_190])).
% 4.63/1.82  tff(c_196, plain, (![A_78, C_79]: (k1_funct_1(A_78, '#skF_4'(A_78, k2_relat_1(A_78), C_79))=C_79 | ~r2_hidden(C_79, k2_relat_1(A_78)) | ~v1_funct_1(A_78) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.63/1.82  tff(c_216, plain, (![A_1, C_79]: (k1_funct_1(k6_relat_1(A_1), '#skF_4'(k6_relat_1(A_1), A_1, C_79))=C_79 | ~r2_hidden(C_79, k2_relat_1(k6_relat_1(A_1))) | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_196])).
% 4.63/1.82  tff(c_224, plain, (![A_1, C_79]: (k1_funct_1(k6_relat_1(A_1), '#skF_4'(k6_relat_1(A_1), A_1, C_79))=C_79 | ~r2_hidden(C_79, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_4, c_216])).
% 4.63/1.82  tff(c_1900, plain, (![C_152]: (k1_funct_1(k6_relat_1('#skF_6'), C_152)=C_152 | ~r2_hidden(C_152, '#skF_6') | ~r2_hidden(C_152, '#skF_6') | ~r2_hidden(C_152, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1882, c_224])).
% 4.63/1.82  tff(c_842, plain, (![B_112]: (r2_hidden('#skF_5'('#skF_7', B_112), '#skF_6') | B_112='#skF_7' | k1_relat_1(B_112)!='#skF_6' | ~v1_funct_1(B_112) | ~v1_relat_1(B_112))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_81, c_735])).
% 4.63/1.82  tff(c_850, plain, (![B_112]: (k1_funct_1('#skF_7', '#skF_5'('#skF_7', B_112))='#skF_5'('#skF_7', B_112) | B_112='#skF_7' | k1_relat_1(B_112)!='#skF_6' | ~v1_funct_1(B_112) | ~v1_relat_1(B_112))), inference(resolution, [status(thm)], [c_842, c_137])).
% 4.63/1.82  tff(c_2028, plain, (![B_156, A_157]: (k1_funct_1(B_156, '#skF_5'(A_157, B_156))!=k1_funct_1(A_157, '#skF_5'(A_157, B_156)) | B_156=A_157 | k1_relat_1(B_156)!=k1_relat_1(A_157) | ~v1_funct_1(B_156) | ~v1_relat_1(B_156) | ~v1_funct_1(A_157) | ~v1_relat_1(A_157))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.63/1.82  tff(c_2063, plain, (![B_112]: (k1_funct_1(B_112, '#skF_5'('#skF_7', B_112))!='#skF_5'('#skF_7', B_112) | B_112='#skF_7' | k1_relat_1(B_112)!=k1_relat_1('#skF_7') | ~v1_funct_1(B_112) | ~v1_relat_1(B_112) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | B_112='#skF_7' | k1_relat_1(B_112)!='#skF_6' | ~v1_funct_1(B_112) | ~v1_relat_1(B_112))), inference(superposition, [status(thm), theory('equality')], [c_850, c_2028])).
% 4.63/1.82  tff(c_2138, plain, (![B_161]: (k1_funct_1(B_161, '#skF_5'('#skF_7', B_161))!='#skF_5'('#skF_7', B_161) | B_161='#skF_7' | k1_relat_1(B_161)!='#skF_6' | ~v1_funct_1(B_161) | ~v1_relat_1(B_161))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_81, c_2063])).
% 4.63/1.82  tff(c_2142, plain, (k6_relat_1('#skF_6')='#skF_7' | k1_relat_1(k6_relat_1('#skF_6'))!='#skF_6' | ~v1_funct_1(k6_relat_1('#skF_6')) | ~v1_relat_1(k6_relat_1('#skF_6')) | ~r2_hidden('#skF_5'('#skF_7', k6_relat_1('#skF_6')), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1900, c_2138])).
% 4.63/1.82  tff(c_2161, plain, (k6_relat_1('#skF_6')='#skF_7' | ~r2_hidden('#skF_5'('#skF_7', k6_relat_1('#skF_6')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_2, c_2142])).
% 4.63/1.82  tff(c_2162, plain, (~r2_hidden('#skF_5'('#skF_7', k6_relat_1('#skF_6')), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_107, c_2161])).
% 4.63/1.82  tff(c_2172, plain, (k6_relat_1('#skF_6')='#skF_7' | k1_relat_1(k6_relat_1('#skF_6'))!='#skF_6' | ~v1_funct_1(k6_relat_1('#skF_6')) | ~v1_relat_1(k6_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_740, c_2162])).
% 4.63/1.82  tff(c_2175, plain, (k6_relat_1('#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_2, c_2172])).
% 4.63/1.82  tff(c_2177, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_2175])).
% 4.63/1.82  tff(c_2179, plain, (k6_relat_1('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_106])).
% 4.63/1.82  tff(c_46, plain, (k1_funct_1('#skF_7', '#skF_8')!='#skF_8' | k1_relat_1('#skF_7')!='#skF_6' | k6_relat_1('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.63/1.82  tff(c_2245, plain, (k1_funct_1('#skF_7', '#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2179, c_81, c_46])).
% 4.63/1.82  tff(c_2178, plain, (r2_hidden('#skF_8', '#skF_6')), inference(splitRight, [status(thm)], [c_106])).
% 4.63/1.82  tff(c_2186, plain, (k2_relat_1('#skF_7')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_2179, c_4])).
% 4.63/1.82  tff(c_2317, plain, (![A_172, C_173]: (r2_hidden('#skF_4'(A_172, k2_relat_1(A_172), C_173), k1_relat_1(A_172)) | ~r2_hidden(C_173, k2_relat_1(A_172)) | ~v1_funct_1(A_172) | ~v1_relat_1(A_172))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.63/1.82  tff(c_2323, plain, (![C_173]: (r2_hidden('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_173), '#skF_6') | ~r2_hidden(C_173, k2_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_2317])).
% 4.63/1.82  tff(c_2333, plain, (![C_173]: (r2_hidden('#skF_4'('#skF_7', '#skF_6', C_173), '#skF_6') | ~r2_hidden(C_173, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_2186, c_2186, c_2323])).
% 4.63/1.82  tff(c_8, plain, (![A_3]: (k5_relat_1(A_3, k6_relat_1(k2_relat_1(A_3)))=A_3 | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.63/1.82  tff(c_2438, plain, (![B_197, C_198, A_199]: (k1_funct_1(k5_relat_1(B_197, C_198), A_199)=k1_funct_1(C_198, k1_funct_1(B_197, A_199)) | ~r2_hidden(A_199, k1_relat_1(B_197)) | ~v1_funct_1(C_198) | ~v1_relat_1(C_198) | ~v1_funct_1(B_197) | ~v1_relat_1(B_197))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.63/1.82  tff(c_2479, plain, (![C_198, A_199]: (k1_funct_1(k5_relat_1('#skF_7', C_198), A_199)=k1_funct_1(C_198, k1_funct_1('#skF_7', A_199)) | ~r2_hidden(A_199, '#skF_6') | ~v1_funct_1(C_198) | ~v1_relat_1(C_198) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_2438])).
% 4.63/1.82  tff(c_2505, plain, (![C_201, A_202]: (k1_funct_1(k5_relat_1('#skF_7', C_201), A_202)=k1_funct_1(C_201, k1_funct_1('#skF_7', A_202)) | ~r2_hidden(A_202, '#skF_6') | ~v1_funct_1(C_201) | ~v1_relat_1(C_201))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_2479])).
% 4.63/1.82  tff(c_2537, plain, (![A_202]: (k1_funct_1(k6_relat_1(k2_relat_1('#skF_7')), k1_funct_1('#skF_7', A_202))=k1_funct_1('#skF_7', A_202) | ~r2_hidden(A_202, '#skF_6') | ~v1_funct_1(k6_relat_1(k2_relat_1('#skF_7'))) | ~v1_relat_1(k6_relat_1(k2_relat_1('#skF_7'))) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_8, c_2505])).
% 4.63/1.82  tff(c_2544, plain, (![A_203]: (k1_funct_1('#skF_7', k1_funct_1('#skF_7', A_203))=k1_funct_1('#skF_7', A_203) | ~r2_hidden(A_203, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_28, c_30, c_2179, c_2186, c_2537])).
% 4.63/1.82  tff(c_2571, plain, (![C_40]: (k1_funct_1('#skF_7', '#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_40))=k1_funct_1('#skF_7', C_40) | ~r2_hidden('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_40), '#skF_6') | ~r2_hidden(C_40, k2_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2544])).
% 4.63/1.82  tff(c_2580, plain, (![C_204]: (k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_6', C_204))=k1_funct_1('#skF_7', C_204) | ~r2_hidden('#skF_4'('#skF_7', '#skF_6', C_204), '#skF_6') | ~r2_hidden(C_204, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_2186, c_2186, c_2186, c_2571])).
% 4.63/1.82  tff(c_2585, plain, (![C_205]: (k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_6', C_205))=k1_funct_1('#skF_7', C_205) | ~r2_hidden(C_205, '#skF_6'))), inference(resolution, [status(thm)], [c_2333, c_2580])).
% 4.63/1.82  tff(c_2261, plain, (![A_166, C_167]: (k1_funct_1(A_166, '#skF_4'(A_166, k2_relat_1(A_166), C_167))=C_167 | ~r2_hidden(C_167, k2_relat_1(A_166)) | ~v1_funct_1(A_166) | ~v1_relat_1(A_166))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.63/1.82  tff(c_2273, plain, (![C_167]: (k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_6', C_167))=C_167 | ~r2_hidden(C_167, k2_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2186, c_2261])).
% 4.63/1.82  tff(c_2280, plain, (![C_167]: (k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_6', C_167))=C_167 | ~r2_hidden(C_167, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_2186, c_2273])).
% 4.63/1.82  tff(c_2611, plain, (![C_206]: (k1_funct_1('#skF_7', C_206)=C_206 | ~r2_hidden(C_206, '#skF_6') | ~r2_hidden(C_206, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2585, c_2280])).
% 4.63/1.82  tff(c_2649, plain, (k1_funct_1('#skF_7', '#skF_8')='#skF_8' | ~r2_hidden('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_2178, c_2611])).
% 4.63/1.82  tff(c_2669, plain, (k1_funct_1('#skF_7', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2178, c_2649])).
% 4.63/1.82  tff(c_2671, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2245, c_2669])).
% 4.63/1.82  tff(c_2673, plain, (k1_relat_1('#skF_7')!='#skF_6'), inference(splitRight, [status(thm)], [c_56])).
% 4.63/1.82  tff(c_2672, plain, (k6_relat_1('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_56])).
% 4.63/1.82  tff(c_2677, plain, (k1_relat_1('#skF_7')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_2672, c_2])).
% 4.63/1.82  tff(c_2694, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2673, c_2677])).
% 4.63/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.82  
% 4.63/1.82  Inference rules
% 4.63/1.82  ----------------------
% 4.63/1.82  #Ref     : 2
% 4.63/1.82  #Sup     : 606
% 4.63/1.82  #Fact    : 0
% 4.63/1.82  #Define  : 0
% 4.63/1.82  #Split   : 3
% 4.63/1.82  #Chain   : 0
% 4.63/1.82  #Close   : 0
% 4.63/1.82  
% 4.63/1.82  Ordering : KBO
% 4.63/1.82  
% 4.63/1.82  Simplification rules
% 4.63/1.82  ----------------------
% 4.63/1.82  #Subsume      : 123
% 4.63/1.82  #Demod        : 570
% 4.63/1.82  #Tautology    : 206
% 4.63/1.82  #SimpNegUnit  : 6
% 4.63/1.82  #BackRed      : 8
% 4.63/1.82  
% 4.63/1.82  #Partial instantiations: 0
% 4.63/1.82  #Strategies tried      : 1
% 4.63/1.82  
% 4.63/1.82  Timing (in seconds)
% 4.63/1.82  ----------------------
% 4.63/1.82  Preprocessing        : 0.31
% 4.63/1.82  Parsing              : 0.16
% 4.63/1.82  CNF conversion       : 0.03
% 4.63/1.82  Main loop            : 0.71
% 4.63/1.82  Inferencing          : 0.27
% 4.63/1.82  Reduction            : 0.22
% 4.63/1.82  Demodulation         : 0.16
% 4.63/1.82  BG Simplification    : 0.04
% 4.63/1.82  Subsumption          : 0.13
% 4.63/1.82  Abstraction          : 0.04
% 4.63/1.82  MUC search           : 0.00
% 4.63/1.82  Cooper               : 0.00
% 4.63/1.82  Total                : 1.08
% 4.63/1.82  Index Insertion      : 0.00
% 4.63/1.82  Index Deletion       : 0.00
% 4.63/1.82  Index Matching       : 0.00
% 4.63/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
