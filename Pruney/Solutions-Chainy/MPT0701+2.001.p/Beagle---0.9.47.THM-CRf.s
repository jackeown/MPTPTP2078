%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:01 EST 2020

% Result     : Theorem 19.93s
% Output     : CNFRefutation 19.93s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 508 expanded)
%              Number of leaves         :   35 ( 197 expanded)
%              Depth                    :   22
%              Number of atoms          :  340 (1934 expanded)
%              Number of equality atoms :   54 ( 542 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_15 > #skF_3 > #skF_14 > #skF_13 > #skF_10 > #skF_8 > #skF_11 > #skF_7 > #skF_2 > #skF_1 > #skF_9 > #skF_5 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_119,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ! [D] :
                ( ( v1_relat_1(D)
                  & v1_funct_1(D) )
               => ( ( A = k2_relat_1(B)
                    & k1_relat_1(C) = A
                    & k1_relat_1(D) = A
                    & k5_relat_1(B,C) = k5_relat_1(B,D) )
                 => C = D ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_71,axiom,(
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

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_58,plain,(
    '#skF_15' != '#skF_14' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_64,plain,(
    k1_relat_1('#skF_14') = '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_127,plain,(
    ! [C_114,A_115] :
      ( r2_hidden(k4_tarski(C_114,'#skF_7'(A_115,k1_relat_1(A_115),C_114)),A_115)
      | ~ r2_hidden(C_114,k1_relat_1(A_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2838,plain,(
    ! [C_325,A_326,B_327] :
      ( r2_hidden(k4_tarski(C_325,'#skF_7'(A_326,k1_relat_1(A_326),C_325)),B_327)
      | ~ r1_tarski(A_326,B_327)
      | ~ r2_hidden(C_325,k1_relat_1(A_326)) ) ),
    inference(resolution,[status(thm)],[c_127,c_2])).

tff(c_62,plain,(
    k1_relat_1('#skF_15') = '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_141,plain,(
    ! [C_114] :
      ( r2_hidden(k4_tarski(C_114,'#skF_7'('#skF_15','#skF_12',C_114)),'#skF_15')
      | ~ r2_hidden(C_114,k1_relat_1('#skF_15')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_127])).

tff(c_178,plain,(
    ! [C_118] :
      ( r2_hidden(k4_tarski(C_118,'#skF_7'('#skF_15','#skF_12',C_118)),'#skF_15')
      | ~ r2_hidden(C_118,'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_141])).

tff(c_452,plain,(
    ! [C_146,B_147] :
      ( r2_hidden(k4_tarski(C_146,'#skF_7'('#skF_15','#skF_12',C_146)),B_147)
      | ~ r1_tarski('#skF_15',B_147)
      | ~ r2_hidden(C_146,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_178,c_2])).

tff(c_22,plain,(
    ! [C_40,A_25,D_43] :
      ( r2_hidden(C_40,k1_relat_1(A_25))
      | ~ r2_hidden(k4_tarski(C_40,D_43),A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_474,plain,(
    ! [C_148,B_149] :
      ( r2_hidden(C_148,k1_relat_1(B_149))
      | ~ r1_tarski('#skF_15',B_149)
      | ~ r2_hidden(C_148,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_452,c_22])).

tff(c_501,plain,(
    ! [C_40,B_149,D_43] :
      ( r2_hidden(C_40,k1_relat_1(k1_relat_1(B_149)))
      | ~ r1_tarski('#skF_15',B_149)
      | ~ r2_hidden(k4_tarski(C_40,D_43),'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_474,c_22])).

tff(c_2957,plain,(
    ! [C_333,B_334,A_335] :
      ( r2_hidden(C_333,k1_relat_1(k1_relat_1(B_334)))
      | ~ r1_tarski('#skF_15',B_334)
      | ~ r1_tarski(A_335,'#skF_12')
      | ~ r2_hidden(C_333,k1_relat_1(A_335)) ) ),
    inference(resolution,[status(thm)],[c_2838,c_501])).

tff(c_10625,plain,(
    ! [A_657,B_658,B_659] :
      ( r2_hidden('#skF_1'(k1_relat_1(A_657),B_658),k1_relat_1(k1_relat_1(B_659)))
      | ~ r1_tarski('#skF_15',B_659)
      | ~ r1_tarski(A_657,'#skF_12')
      | r1_tarski(k1_relat_1(A_657),B_658) ) ),
    inference(resolution,[status(thm)],[c_6,c_2957])).

tff(c_10649,plain,(
    ! [A_657,B_658] :
      ( r2_hidden('#skF_1'(k1_relat_1(A_657),B_658),k1_relat_1('#skF_12'))
      | ~ r1_tarski('#skF_15','#skF_14')
      | ~ r1_tarski(A_657,'#skF_12')
      | r1_tarski(k1_relat_1(A_657),B_658) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_10625])).

tff(c_11178,plain,(
    ~ r1_tarski('#skF_15','#skF_14') ),
    inference(splitLeft,[status(thm)],[c_10649])).

tff(c_70,plain,(
    v1_relat_1('#skF_15') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_262,plain,(
    ! [A_127,B_128] :
      ( r2_hidden(k4_tarski('#skF_2'(A_127,B_128),'#skF_3'(A_127,B_128)),A_127)
      | r1_tarski(A_127,B_128)
      | ~ v1_relat_1(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4316,plain,(
    ! [A_376,B_377,B_378] :
      ( r2_hidden(k4_tarski('#skF_2'(A_376,B_377),'#skF_3'(A_376,B_377)),B_378)
      | ~ r1_tarski(A_376,B_378)
      | r1_tarski(A_376,B_377)
      | ~ v1_relat_1(A_376) ) ),
    inference(resolution,[status(thm)],[c_262,c_2])).

tff(c_4468,plain,(
    ! [A_381,B_382,B_383] :
      ( r2_hidden('#skF_2'(A_381,B_382),k1_relat_1(B_383))
      | ~ r1_tarski(A_381,B_383)
      | r1_tarski(A_381,B_382)
      | ~ v1_relat_1(A_381) ) ),
    inference(resolution,[status(thm)],[c_4316,c_22])).

tff(c_4512,plain,(
    ! [A_386,B_387] :
      ( r2_hidden('#skF_2'(A_386,B_387),'#skF_12')
      | ~ r1_tarski(A_386,'#skF_15')
      | r1_tarski(A_386,B_387)
      | ~ v1_relat_1(A_386) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_4468])).

tff(c_4523,plain,(
    ! [A_386,B_387,B_2] :
      ( r2_hidden('#skF_2'(A_386,B_387),B_2)
      | ~ r1_tarski('#skF_12',B_2)
      | ~ r1_tarski(A_386,'#skF_15')
      | r1_tarski(A_386,B_387)
      | ~ v1_relat_1(A_386) ) ),
    inference(resolution,[status(thm)],[c_4512,c_2])).

tff(c_74,plain,(
    v1_relat_1('#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_72,plain,(
    v1_funct_1('#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_68,plain,(
    v1_funct_1('#skF_15') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_333,plain,(
    ! [A_133,B_134] :
      ( r2_hidden('#skF_2'(A_133,B_134),k1_relat_1(A_133))
      | r1_tarski(A_133,B_134)
      | ~ v1_relat_1(A_133) ) ),
    inference(resolution,[status(thm)],[c_262,c_22])).

tff(c_341,plain,(
    ! [B_134] :
      ( r2_hidden('#skF_2'('#skF_15',B_134),'#skF_12')
      | r1_tarski('#skF_15',B_134)
      | ~ v1_relat_1('#skF_15') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_333])).

tff(c_346,plain,(
    ! [B_134] :
      ( r2_hidden('#skF_2'('#skF_15',B_134),'#skF_12')
      | r1_tarski('#skF_15',B_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_341])).

tff(c_78,plain,(
    v1_relat_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_76,plain,(
    v1_funct_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_66,plain,(
    k2_relat_1('#skF_13') = '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1106,plain,(
    ! [A_215,C_216] :
      ( k1_funct_1(A_215,'#skF_11'(A_215,k2_relat_1(A_215),C_216)) = C_216
      | ~ r2_hidden(C_216,k2_relat_1(A_215))
      | ~ v1_funct_1(A_215)
      | ~ v1_relat_1(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1129,plain,(
    ! [C_216] :
      ( k1_funct_1('#skF_13','#skF_11'('#skF_13','#skF_12',C_216)) = C_216
      | ~ r2_hidden(C_216,k2_relat_1('#skF_13'))
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_1106])).

tff(c_1137,plain,(
    ! [C_216] :
      ( k1_funct_1('#skF_13','#skF_11'('#skF_13','#skF_12',C_216)) = C_216
      | ~ r2_hidden(C_216,'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_66,c_1129])).

tff(c_60,plain,(
    k5_relat_1('#skF_13','#skF_15') = k5_relat_1('#skF_13','#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_36,plain,(
    ! [A_44,C_80] :
      ( r2_hidden('#skF_11'(A_44,k2_relat_1(A_44),C_80),k1_relat_1(A_44))
      | ~ r2_hidden(C_80,k2_relat_1(A_44))
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2394,plain,(
    ! [B_290,C_291,A_292] :
      ( k1_funct_1(k5_relat_1(B_290,C_291),A_292) = k1_funct_1(C_291,k1_funct_1(B_290,A_292))
      | ~ r2_hidden(A_292,k1_relat_1(B_290))
      | ~ v1_funct_1(C_291)
      | ~ v1_relat_1(C_291)
      | ~ v1_funct_1(B_290)
      | ~ v1_relat_1(B_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_9208,plain,(
    ! [A_576,C_577,C_578] :
      ( k1_funct_1(k5_relat_1(A_576,C_577),'#skF_11'(A_576,k2_relat_1(A_576),C_578)) = k1_funct_1(C_577,k1_funct_1(A_576,'#skF_11'(A_576,k2_relat_1(A_576),C_578)))
      | ~ v1_funct_1(C_577)
      | ~ v1_relat_1(C_577)
      | ~ r2_hidden(C_578,k2_relat_1(A_576))
      | ~ v1_funct_1(A_576)
      | ~ v1_relat_1(A_576) ) ),
    inference(resolution,[status(thm)],[c_36,c_2394])).

tff(c_9249,plain,(
    ! [C_578] :
      ( k1_funct_1(k5_relat_1('#skF_13','#skF_14'),'#skF_11'('#skF_13',k2_relat_1('#skF_13'),C_578)) = k1_funct_1('#skF_15',k1_funct_1('#skF_13','#skF_11'('#skF_13',k2_relat_1('#skF_13'),C_578)))
      | ~ v1_funct_1('#skF_15')
      | ~ v1_relat_1('#skF_15')
      | ~ r2_hidden(C_578,k2_relat_1('#skF_13'))
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_9208])).

tff(c_9268,plain,(
    ! [C_578] :
      ( k1_funct_1(k5_relat_1('#skF_13','#skF_14'),'#skF_11'('#skF_13','#skF_12',C_578)) = k1_funct_1('#skF_15',k1_funct_1('#skF_13','#skF_11'('#skF_13','#skF_12',C_578)))
      | ~ r2_hidden(C_578,'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_66,c_70,c_68,c_66,c_66,c_9249])).

tff(c_9252,plain,(
    ! [C_577,C_578] :
      ( k1_funct_1(C_577,k1_funct_1('#skF_13','#skF_11'('#skF_13',k2_relat_1('#skF_13'),C_578))) = k1_funct_1(k5_relat_1('#skF_13',C_577),'#skF_11'('#skF_13','#skF_12',C_578))
      | ~ v1_funct_1(C_577)
      | ~ v1_relat_1(C_577)
      | ~ r2_hidden(C_578,k2_relat_1('#skF_13'))
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_9208])).

tff(c_12553,plain,(
    ! [C_693,C_694] :
      ( k1_funct_1(k5_relat_1('#skF_13',C_693),'#skF_11'('#skF_13','#skF_12',C_694)) = k1_funct_1(C_693,k1_funct_1('#skF_13','#skF_11'('#skF_13','#skF_12',C_694)))
      | ~ v1_funct_1(C_693)
      | ~ v1_relat_1(C_693)
      | ~ r2_hidden(C_694,'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_66,c_66,c_9252])).

tff(c_12582,plain,(
    ! [C_578] :
      ( k1_funct_1('#skF_15',k1_funct_1('#skF_13','#skF_11'('#skF_13','#skF_12',C_578))) = k1_funct_1('#skF_14',k1_funct_1('#skF_13','#skF_11'('#skF_13','#skF_12',C_578)))
      | ~ v1_funct_1('#skF_14')
      | ~ v1_relat_1('#skF_14')
      | ~ r2_hidden(C_578,'#skF_12')
      | ~ r2_hidden(C_578,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9268,c_12553])).

tff(c_25026,plain,(
    ! [C_1066] :
      ( k1_funct_1('#skF_15',k1_funct_1('#skF_13','#skF_11'('#skF_13','#skF_12',C_1066))) = k1_funct_1('#skF_14',k1_funct_1('#skF_13','#skF_11'('#skF_13','#skF_12',C_1066)))
      | ~ r2_hidden(C_1066,'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_12582])).

tff(c_25090,plain,(
    ! [C_1067] :
      ( k1_funct_1('#skF_14',k1_funct_1('#skF_13','#skF_11'('#skF_13','#skF_12',C_1067))) = k1_funct_1('#skF_15',C_1067)
      | ~ r2_hidden(C_1067,'#skF_12')
      | ~ r2_hidden(C_1067,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1137,c_25026])).

tff(c_25154,plain,(
    ! [C_1068] :
      ( k1_funct_1('#skF_15',C_1068) = k1_funct_1('#skF_14',C_1068)
      | ~ r2_hidden(C_1068,'#skF_12')
      | ~ r2_hidden(C_1068,'#skF_12')
      | ~ r2_hidden(C_1068,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1137,c_25090])).

tff(c_25873,plain,(
    ! [B_1076] :
      ( k1_funct_1('#skF_15','#skF_2'('#skF_15',B_1076)) = k1_funct_1('#skF_14','#skF_2'('#skF_15',B_1076))
      | ~ r2_hidden('#skF_2'('#skF_15',B_1076),'#skF_12')
      | r1_tarski('#skF_15',B_1076) ) ),
    inference(resolution,[status(thm)],[c_346,c_25154])).

tff(c_25877,plain,(
    ! [B_387] :
      ( k1_funct_1('#skF_15','#skF_2'('#skF_15',B_387)) = k1_funct_1('#skF_14','#skF_2'('#skF_15',B_387))
      | ~ r1_tarski('#skF_12','#skF_12')
      | ~ r1_tarski('#skF_15','#skF_15')
      | r1_tarski('#skF_15',B_387)
      | ~ v1_relat_1('#skF_15') ) ),
    inference(resolution,[status(thm)],[c_4523,c_25873])).

tff(c_25920,plain,(
    ! [B_1077] :
      ( k1_funct_1('#skF_15','#skF_2'('#skF_15',B_1077)) = k1_funct_1('#skF_14','#skF_2'('#skF_15',B_1077))
      | r1_tarski('#skF_15',B_1077) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_12,c_12,c_25877])).

tff(c_54,plain,(
    ! [C_90,A_88,B_89] :
      ( k1_funct_1(C_90,A_88) = B_89
      | ~ r2_hidden(k4_tarski(A_88,B_89),C_90)
      | ~ v1_funct_1(C_90)
      | ~ v1_relat_1(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4382,plain,(
    ! [B_378,A_376,B_377] :
      ( k1_funct_1(B_378,'#skF_2'(A_376,B_377)) = '#skF_3'(A_376,B_377)
      | ~ v1_funct_1(B_378)
      | ~ v1_relat_1(B_378)
      | ~ r1_tarski(A_376,B_378)
      | r1_tarski(A_376,B_377)
      | ~ v1_relat_1(A_376) ) ),
    inference(resolution,[status(thm)],[c_4316,c_54])).

tff(c_25950,plain,(
    ! [B_1077] :
      ( k1_funct_1('#skF_14','#skF_2'('#skF_15',B_1077)) = '#skF_3'('#skF_15',B_1077)
      | ~ v1_funct_1('#skF_15')
      | ~ v1_relat_1('#skF_15')
      | ~ r1_tarski('#skF_15','#skF_15')
      | r1_tarski('#skF_15',B_1077)
      | ~ v1_relat_1('#skF_15')
      | r1_tarski('#skF_15',B_1077) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25920,c_4382])).

tff(c_26037,plain,(
    ! [B_1078] :
      ( k1_funct_1('#skF_14','#skF_2'('#skF_15',B_1078)) = '#skF_3'('#skF_15',B_1078)
      | r1_tarski('#skF_15',B_1078) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_12,c_70,c_68,c_25950])).

tff(c_52,plain,(
    ! [A_88,C_90] :
      ( r2_hidden(k4_tarski(A_88,k1_funct_1(C_90,A_88)),C_90)
      | ~ r2_hidden(A_88,k1_relat_1(C_90))
      | ~ v1_funct_1(C_90)
      | ~ v1_relat_1(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_26089,plain,(
    ! [B_1078] :
      ( r2_hidden(k4_tarski('#skF_2'('#skF_15',B_1078),'#skF_3'('#skF_15',B_1078)),'#skF_14')
      | ~ r2_hidden('#skF_2'('#skF_15',B_1078),k1_relat_1('#skF_14'))
      | ~ v1_funct_1('#skF_14')
      | ~ v1_relat_1('#skF_14')
      | r1_tarski('#skF_15',B_1078) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26037,c_52])).

tff(c_26554,plain,(
    ! [B_1086] :
      ( r2_hidden(k4_tarski('#skF_2'('#skF_15',B_1086),'#skF_3'('#skF_15',B_1086)),'#skF_14')
      | ~ r2_hidden('#skF_2'('#skF_15',B_1086),'#skF_12')
      | r1_tarski('#skF_15',B_1086) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_64,c_26089])).

tff(c_16,plain,(
    ! [A_8,B_18] :
      ( ~ r2_hidden(k4_tarski('#skF_2'(A_8,B_18),'#skF_3'(A_8,B_18)),B_18)
      | r1_tarski(A_8,B_18)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_26558,plain,
    ( ~ v1_relat_1('#skF_15')
    | ~ r2_hidden('#skF_2'('#skF_15','#skF_14'),'#skF_12')
    | r1_tarski('#skF_15','#skF_14') ),
    inference(resolution,[status(thm)],[c_26554,c_16])).

tff(c_26569,plain,
    ( ~ r2_hidden('#skF_2'('#skF_15','#skF_14'),'#skF_12')
    | r1_tarski('#skF_15','#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_26558])).

tff(c_26570,plain,(
    ~ r2_hidden('#skF_2'('#skF_15','#skF_14'),'#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_11178,c_26569])).

tff(c_26644,plain,
    ( ~ r1_tarski('#skF_12','#skF_12')
    | ~ r1_tarski('#skF_15','#skF_15')
    | r1_tarski('#skF_15','#skF_14')
    | ~ v1_relat_1('#skF_15') ),
    inference(resolution,[status(thm)],[c_4523,c_26570])).

tff(c_26665,plain,(
    r1_tarski('#skF_15','#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_12,c_12,c_26644])).

tff(c_26667,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11178,c_26665])).

tff(c_26669,plain,(
    r1_tarski('#skF_15','#skF_14') ),
    inference(splitRight,[status(thm)],[c_10649])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_26711,plain,
    ( '#skF_15' = '#skF_14'
    | ~ r1_tarski('#skF_14','#skF_15') ),
    inference(resolution,[status(thm)],[c_26669,c_8])).

tff(c_26739,plain,(
    ~ r1_tarski('#skF_14','#skF_15') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_26711])).

tff(c_4500,plain,(
    ! [A_384,B_385] :
      ( r2_hidden('#skF_2'(A_384,B_385),'#skF_12')
      | ~ r1_tarski(A_384,'#skF_14')
      | r1_tarski(A_384,B_385)
      | ~ v1_relat_1(A_384) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_4468])).

tff(c_4511,plain,(
    ! [A_384,B_385,B_2] :
      ( r2_hidden('#skF_2'(A_384,B_385),B_2)
      | ~ r1_tarski('#skF_12',B_2)
      | ~ r1_tarski(A_384,'#skF_14')
      | r1_tarski(A_384,B_385)
      | ~ v1_relat_1(A_384) ) ),
    inference(resolution,[status(thm)],[c_4500,c_2])).

tff(c_4489,plain,(
    ! [A_381,B_382] :
      ( r2_hidden('#skF_2'(A_381,B_382),'#skF_12')
      | ~ r1_tarski(A_381,'#skF_14')
      | r1_tarski(A_381,B_382)
      | ~ v1_relat_1(A_381) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_4468])).

tff(c_471,plain,(
    ! [B_147,C_146] :
      ( k1_funct_1(B_147,C_146) = '#skF_7'('#skF_15','#skF_12',C_146)
      | ~ v1_funct_1(B_147)
      | ~ v1_relat_1(B_147)
      | ~ r1_tarski('#skF_15',B_147)
      | ~ r2_hidden(C_146,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_452,c_54])).

tff(c_26689,plain,(
    ! [C_146] :
      ( k1_funct_1('#skF_14',C_146) = '#skF_7'('#skF_15','#skF_12',C_146)
      | ~ v1_funct_1('#skF_14')
      | ~ v1_relat_1('#skF_14')
      | ~ r2_hidden(C_146,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_26669,c_471])).

tff(c_26789,plain,(
    ! [C_1092] :
      ( k1_funct_1('#skF_14',C_1092) = '#skF_7'('#skF_15','#skF_12',C_1092)
      | ~ r2_hidden(C_1092,'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_26689])).

tff(c_27870,plain,(
    ! [A_1107,B_1108] :
      ( k1_funct_1('#skF_14','#skF_2'(A_1107,B_1108)) = '#skF_7'('#skF_15','#skF_12','#skF_2'(A_1107,B_1108))
      | ~ r1_tarski(A_1107,'#skF_14')
      | r1_tarski(A_1107,B_1108)
      | ~ v1_relat_1(A_1107) ) ),
    inference(resolution,[status(thm)],[c_4489,c_26789])).

tff(c_1480,plain,(
    ! [A_236,B_237] :
      ( k1_funct_1(A_236,'#skF_2'(A_236,B_237)) = '#skF_3'(A_236,B_237)
      | ~ v1_funct_1(A_236)
      | r1_tarski(A_236,B_237)
      | ~ v1_relat_1(A_236) ) ),
    inference(resolution,[status(thm)],[c_262,c_54])).

tff(c_338,plain,(
    ! [B_134] :
      ( r2_hidden('#skF_2'('#skF_14',B_134),'#skF_12')
      | r1_tarski('#skF_14',B_134)
      | ~ v1_relat_1('#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_333])).

tff(c_347,plain,(
    ! [B_135] :
      ( r2_hidden('#skF_2'('#skF_14',B_135),'#skF_12')
      | r1_tarski('#skF_14',B_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_338])).

tff(c_138,plain,(
    ! [C_114] :
      ( r2_hidden(k4_tarski(C_114,'#skF_7'('#skF_14','#skF_12',C_114)),'#skF_14')
      | ~ r2_hidden(C_114,k1_relat_1('#skF_14')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_127])).

tff(c_147,plain,(
    ! [C_116] :
      ( r2_hidden(k4_tarski(C_116,'#skF_7'('#skF_14','#skF_12',C_116)),'#skF_14')
      | ~ r2_hidden(C_116,'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_138])).

tff(c_150,plain,(
    ! [C_116] :
      ( k1_funct_1('#skF_14',C_116) = '#skF_7'('#skF_14','#skF_12',C_116)
      | ~ v1_funct_1('#skF_14')
      | ~ v1_relat_1('#skF_14')
      | ~ r2_hidden(C_116,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_147,c_54])).

tff(c_158,plain,(
    ! [C_116] :
      ( k1_funct_1('#skF_14',C_116) = '#skF_7'('#skF_14','#skF_12',C_116)
      | ~ r2_hidden(C_116,'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_150])).

tff(c_357,plain,(
    ! [B_135] :
      ( k1_funct_1('#skF_14','#skF_2'('#skF_14',B_135)) = '#skF_7'('#skF_14','#skF_12','#skF_2'('#skF_14',B_135))
      | r1_tarski('#skF_14',B_135) ) ),
    inference(resolution,[status(thm)],[c_347,c_158])).

tff(c_1487,plain,(
    ! [B_237] :
      ( '#skF_7'('#skF_14','#skF_12','#skF_2'('#skF_14',B_237)) = '#skF_3'('#skF_14',B_237)
      | r1_tarski('#skF_14',B_237)
      | ~ v1_funct_1('#skF_14')
      | r1_tarski('#skF_14',B_237)
      | ~ v1_relat_1('#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1480,c_357])).

tff(c_1529,plain,(
    ! [B_238] :
      ( '#skF_7'('#skF_14','#skF_12','#skF_2'('#skF_14',B_238)) = '#skF_3'('#skF_14',B_238)
      | r1_tarski('#skF_14',B_238) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_1487])).

tff(c_145,plain,(
    ! [C_114] :
      ( r2_hidden(k4_tarski(C_114,'#skF_7'('#skF_14','#skF_12',C_114)),'#skF_14')
      | ~ r2_hidden(C_114,'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_138])).

tff(c_3638,plain,(
    ! [B_348] :
      ( r2_hidden(k4_tarski('#skF_2'('#skF_14',B_348),'#skF_3'('#skF_14',B_348)),'#skF_14')
      | ~ r2_hidden('#skF_2'('#skF_14',B_348),'#skF_12')
      | r1_tarski('#skF_14',B_348) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1529,c_145])).

tff(c_3645,plain,(
    ! [B_348] :
      ( k1_funct_1('#skF_14','#skF_2'('#skF_14',B_348)) = '#skF_3'('#skF_14',B_348)
      | ~ v1_funct_1('#skF_14')
      | ~ v1_relat_1('#skF_14')
      | ~ r2_hidden('#skF_2'('#skF_14',B_348),'#skF_12')
      | r1_tarski('#skF_14',B_348) ) ),
    inference(resolution,[status(thm)],[c_3638,c_54])).

tff(c_4968,plain,(
    ! [B_407] :
      ( k1_funct_1('#skF_14','#skF_2'('#skF_14',B_407)) = '#skF_3'('#skF_14',B_407)
      | ~ r2_hidden('#skF_2'('#skF_14',B_407),'#skF_12')
      | r1_tarski('#skF_14',B_407) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_3645])).

tff(c_4976,plain,(
    ! [B_385] :
      ( k1_funct_1('#skF_14','#skF_2'('#skF_14',B_385)) = '#skF_3'('#skF_14',B_385)
      | ~ r1_tarski('#skF_12','#skF_12')
      | ~ r1_tarski('#skF_14','#skF_14')
      | r1_tarski('#skF_14',B_385)
      | ~ v1_relat_1('#skF_14') ) ),
    inference(resolution,[status(thm)],[c_4511,c_4968])).

tff(c_5001,plain,(
    ! [B_385] :
      ( k1_funct_1('#skF_14','#skF_2'('#skF_14',B_385)) = '#skF_3'('#skF_14',B_385)
      | r1_tarski('#skF_14',B_385) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_12,c_12,c_4976])).

tff(c_27883,plain,(
    ! [B_1108] :
      ( '#skF_7'('#skF_15','#skF_12','#skF_2'('#skF_14',B_1108)) = '#skF_3'('#skF_14',B_1108)
      | r1_tarski('#skF_14',B_1108)
      | ~ r1_tarski('#skF_14','#skF_14')
      | r1_tarski('#skF_14',B_1108)
      | ~ v1_relat_1('#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27870,c_5001])).

tff(c_27964,plain,(
    ! [B_1109] :
      ( '#skF_7'('#skF_15','#skF_12','#skF_2'('#skF_14',B_1109)) = '#skF_3'('#skF_14',B_1109)
      | r1_tarski('#skF_14',B_1109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_12,c_27883])).

tff(c_146,plain,(
    ! [C_114] :
      ( r2_hidden(k4_tarski(C_114,'#skF_7'('#skF_15','#skF_12',C_114)),'#skF_15')
      | ~ r2_hidden(C_114,'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_141])).

tff(c_46906,plain,(
    ! [B_1434] :
      ( r2_hidden(k4_tarski('#skF_2'('#skF_14',B_1434),'#skF_3'('#skF_14',B_1434)),'#skF_15')
      | ~ r2_hidden('#skF_2'('#skF_14',B_1434),'#skF_12')
      | r1_tarski('#skF_14',B_1434) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27964,c_146])).

tff(c_46910,plain,
    ( ~ v1_relat_1('#skF_14')
    | ~ r2_hidden('#skF_2'('#skF_14','#skF_15'),'#skF_12')
    | r1_tarski('#skF_14','#skF_15') ),
    inference(resolution,[status(thm)],[c_46906,c_16])).

tff(c_46921,plain,
    ( ~ r2_hidden('#skF_2'('#skF_14','#skF_15'),'#skF_12')
    | r1_tarski('#skF_14','#skF_15') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_46910])).

tff(c_46922,plain,(
    ~ r2_hidden('#skF_2'('#skF_14','#skF_15'),'#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_26739,c_46921])).

tff(c_46937,plain,
    ( ~ r1_tarski('#skF_12','#skF_12')
    | ~ r1_tarski('#skF_14','#skF_14')
    | r1_tarski('#skF_14','#skF_15')
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_4511,c_46922])).

tff(c_46963,plain,(
    r1_tarski('#skF_14','#skF_15') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_12,c_12,c_46937])).

tff(c_46965,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26739,c_46963])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:21:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.93/10.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.93/10.02  
% 19.93/10.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.93/10.03  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_15 > #skF_3 > #skF_14 > #skF_13 > #skF_10 > #skF_8 > #skF_11 > #skF_7 > #skF_2 > #skF_1 > #skF_9 > #skF_5 > #skF_12 > #skF_4
% 19.93/10.03  
% 19.93/10.03  %Foreground sorts:
% 19.93/10.03  
% 19.93/10.03  
% 19.93/10.03  %Background operators:
% 19.93/10.03  
% 19.93/10.03  
% 19.93/10.03  %Foreground operators:
% 19.93/10.03  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 19.93/10.03  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 19.93/10.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.93/10.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 19.93/10.03  tff('#skF_15', type, '#skF_15': $i).
% 19.93/10.03  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 19.93/10.03  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 19.93/10.03  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 19.93/10.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.93/10.03  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 19.93/10.03  tff('#skF_14', type, '#skF_14': $i).
% 19.93/10.03  tff('#skF_13', type, '#skF_13': $i).
% 19.93/10.03  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 19.93/10.03  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 19.93/10.03  tff('#skF_11', type, '#skF_11': ($i * $i * $i) > $i).
% 19.93/10.03  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 19.93/10.03  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 19.93/10.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.93/10.03  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 19.93/10.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.93/10.03  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 19.93/10.03  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 19.93/10.03  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 19.93/10.03  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 19.93/10.03  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 19.93/10.03  tff('#skF_12', type, '#skF_12': $i).
% 19.93/10.03  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 19.93/10.03  
% 19.93/10.05  tff(f_119, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (![D]: ((v1_relat_1(D) & v1_funct_1(D)) => (((((A = k2_relat_1(B)) & (k1_relat_1(C) = A)) & (k1_relat_1(D) = A)) & (k5_relat_1(B, C) = k5_relat_1(B, D))) => (C = D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_funct_1)).
% 19.93/10.05  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 19.93/10.05  tff(f_56, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 19.93/10.05  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 19.93/10.05  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 19.93/10.05  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 19.93/10.05  tff(f_84, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 19.93/10.05  tff(f_94, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 19.93/10.05  tff(c_58, plain, ('#skF_15'!='#skF_14'), inference(cnfTransformation, [status(thm)], [f_119])).
% 19.93/10.05  tff(c_64, plain, (k1_relat_1('#skF_14')='#skF_12'), inference(cnfTransformation, [status(thm)], [f_119])).
% 19.93/10.05  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 19.93/10.05  tff(c_127, plain, (![C_114, A_115]: (r2_hidden(k4_tarski(C_114, '#skF_7'(A_115, k1_relat_1(A_115), C_114)), A_115) | ~r2_hidden(C_114, k1_relat_1(A_115)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 19.93/10.05  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 19.93/10.05  tff(c_2838, plain, (![C_325, A_326, B_327]: (r2_hidden(k4_tarski(C_325, '#skF_7'(A_326, k1_relat_1(A_326), C_325)), B_327) | ~r1_tarski(A_326, B_327) | ~r2_hidden(C_325, k1_relat_1(A_326)))), inference(resolution, [status(thm)], [c_127, c_2])).
% 19.93/10.05  tff(c_62, plain, (k1_relat_1('#skF_15')='#skF_12'), inference(cnfTransformation, [status(thm)], [f_119])).
% 19.93/10.05  tff(c_141, plain, (![C_114]: (r2_hidden(k4_tarski(C_114, '#skF_7'('#skF_15', '#skF_12', C_114)), '#skF_15') | ~r2_hidden(C_114, k1_relat_1('#skF_15')))), inference(superposition, [status(thm), theory('equality')], [c_62, c_127])).
% 19.93/10.05  tff(c_178, plain, (![C_118]: (r2_hidden(k4_tarski(C_118, '#skF_7'('#skF_15', '#skF_12', C_118)), '#skF_15') | ~r2_hidden(C_118, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_141])).
% 19.93/10.05  tff(c_452, plain, (![C_146, B_147]: (r2_hidden(k4_tarski(C_146, '#skF_7'('#skF_15', '#skF_12', C_146)), B_147) | ~r1_tarski('#skF_15', B_147) | ~r2_hidden(C_146, '#skF_12'))), inference(resolution, [status(thm)], [c_178, c_2])).
% 19.93/10.05  tff(c_22, plain, (![C_40, A_25, D_43]: (r2_hidden(C_40, k1_relat_1(A_25)) | ~r2_hidden(k4_tarski(C_40, D_43), A_25))), inference(cnfTransformation, [status(thm)], [f_56])).
% 19.93/10.05  tff(c_474, plain, (![C_148, B_149]: (r2_hidden(C_148, k1_relat_1(B_149)) | ~r1_tarski('#skF_15', B_149) | ~r2_hidden(C_148, '#skF_12'))), inference(resolution, [status(thm)], [c_452, c_22])).
% 19.93/10.05  tff(c_501, plain, (![C_40, B_149, D_43]: (r2_hidden(C_40, k1_relat_1(k1_relat_1(B_149))) | ~r1_tarski('#skF_15', B_149) | ~r2_hidden(k4_tarski(C_40, D_43), '#skF_12'))), inference(resolution, [status(thm)], [c_474, c_22])).
% 19.93/10.05  tff(c_2957, plain, (![C_333, B_334, A_335]: (r2_hidden(C_333, k1_relat_1(k1_relat_1(B_334))) | ~r1_tarski('#skF_15', B_334) | ~r1_tarski(A_335, '#skF_12') | ~r2_hidden(C_333, k1_relat_1(A_335)))), inference(resolution, [status(thm)], [c_2838, c_501])).
% 19.93/10.05  tff(c_10625, plain, (![A_657, B_658, B_659]: (r2_hidden('#skF_1'(k1_relat_1(A_657), B_658), k1_relat_1(k1_relat_1(B_659))) | ~r1_tarski('#skF_15', B_659) | ~r1_tarski(A_657, '#skF_12') | r1_tarski(k1_relat_1(A_657), B_658))), inference(resolution, [status(thm)], [c_6, c_2957])).
% 19.93/10.05  tff(c_10649, plain, (![A_657, B_658]: (r2_hidden('#skF_1'(k1_relat_1(A_657), B_658), k1_relat_1('#skF_12')) | ~r1_tarski('#skF_15', '#skF_14') | ~r1_tarski(A_657, '#skF_12') | r1_tarski(k1_relat_1(A_657), B_658))), inference(superposition, [status(thm), theory('equality')], [c_64, c_10625])).
% 19.93/10.05  tff(c_11178, plain, (~r1_tarski('#skF_15', '#skF_14')), inference(splitLeft, [status(thm)], [c_10649])).
% 19.93/10.05  tff(c_70, plain, (v1_relat_1('#skF_15')), inference(cnfTransformation, [status(thm)], [f_119])).
% 19.93/10.05  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 19.93/10.05  tff(c_262, plain, (![A_127, B_128]: (r2_hidden(k4_tarski('#skF_2'(A_127, B_128), '#skF_3'(A_127, B_128)), A_127) | r1_tarski(A_127, B_128) | ~v1_relat_1(A_127))), inference(cnfTransformation, [status(thm)], [f_48])).
% 19.93/10.05  tff(c_4316, plain, (![A_376, B_377, B_378]: (r2_hidden(k4_tarski('#skF_2'(A_376, B_377), '#skF_3'(A_376, B_377)), B_378) | ~r1_tarski(A_376, B_378) | r1_tarski(A_376, B_377) | ~v1_relat_1(A_376))), inference(resolution, [status(thm)], [c_262, c_2])).
% 19.93/10.05  tff(c_4468, plain, (![A_381, B_382, B_383]: (r2_hidden('#skF_2'(A_381, B_382), k1_relat_1(B_383)) | ~r1_tarski(A_381, B_383) | r1_tarski(A_381, B_382) | ~v1_relat_1(A_381))), inference(resolution, [status(thm)], [c_4316, c_22])).
% 19.93/10.05  tff(c_4512, plain, (![A_386, B_387]: (r2_hidden('#skF_2'(A_386, B_387), '#skF_12') | ~r1_tarski(A_386, '#skF_15') | r1_tarski(A_386, B_387) | ~v1_relat_1(A_386))), inference(superposition, [status(thm), theory('equality')], [c_62, c_4468])).
% 19.93/10.05  tff(c_4523, plain, (![A_386, B_387, B_2]: (r2_hidden('#skF_2'(A_386, B_387), B_2) | ~r1_tarski('#skF_12', B_2) | ~r1_tarski(A_386, '#skF_15') | r1_tarski(A_386, B_387) | ~v1_relat_1(A_386))), inference(resolution, [status(thm)], [c_4512, c_2])).
% 19.93/10.05  tff(c_74, plain, (v1_relat_1('#skF_14')), inference(cnfTransformation, [status(thm)], [f_119])).
% 19.93/10.05  tff(c_72, plain, (v1_funct_1('#skF_14')), inference(cnfTransformation, [status(thm)], [f_119])).
% 19.93/10.05  tff(c_68, plain, (v1_funct_1('#skF_15')), inference(cnfTransformation, [status(thm)], [f_119])).
% 19.93/10.05  tff(c_333, plain, (![A_133, B_134]: (r2_hidden('#skF_2'(A_133, B_134), k1_relat_1(A_133)) | r1_tarski(A_133, B_134) | ~v1_relat_1(A_133))), inference(resolution, [status(thm)], [c_262, c_22])).
% 19.93/10.05  tff(c_341, plain, (![B_134]: (r2_hidden('#skF_2'('#skF_15', B_134), '#skF_12') | r1_tarski('#skF_15', B_134) | ~v1_relat_1('#skF_15'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_333])).
% 19.93/10.05  tff(c_346, plain, (![B_134]: (r2_hidden('#skF_2'('#skF_15', B_134), '#skF_12') | r1_tarski('#skF_15', B_134))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_341])).
% 19.93/10.05  tff(c_78, plain, (v1_relat_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_119])).
% 19.93/10.05  tff(c_76, plain, (v1_funct_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_119])).
% 19.93/10.05  tff(c_66, plain, (k2_relat_1('#skF_13')='#skF_12'), inference(cnfTransformation, [status(thm)], [f_119])).
% 19.93/10.05  tff(c_1106, plain, (![A_215, C_216]: (k1_funct_1(A_215, '#skF_11'(A_215, k2_relat_1(A_215), C_216))=C_216 | ~r2_hidden(C_216, k2_relat_1(A_215)) | ~v1_funct_1(A_215) | ~v1_relat_1(A_215))), inference(cnfTransformation, [status(thm)], [f_71])).
% 19.93/10.05  tff(c_1129, plain, (![C_216]: (k1_funct_1('#skF_13', '#skF_11'('#skF_13', '#skF_12', C_216))=C_216 | ~r2_hidden(C_216, k2_relat_1('#skF_13')) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_1106])).
% 19.93/10.05  tff(c_1137, plain, (![C_216]: (k1_funct_1('#skF_13', '#skF_11'('#skF_13', '#skF_12', C_216))=C_216 | ~r2_hidden(C_216, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_66, c_1129])).
% 19.93/10.05  tff(c_60, plain, (k5_relat_1('#skF_13', '#skF_15')=k5_relat_1('#skF_13', '#skF_14')), inference(cnfTransformation, [status(thm)], [f_119])).
% 19.93/10.05  tff(c_36, plain, (![A_44, C_80]: (r2_hidden('#skF_11'(A_44, k2_relat_1(A_44), C_80), k1_relat_1(A_44)) | ~r2_hidden(C_80, k2_relat_1(A_44)) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_71])).
% 19.93/10.05  tff(c_2394, plain, (![B_290, C_291, A_292]: (k1_funct_1(k5_relat_1(B_290, C_291), A_292)=k1_funct_1(C_291, k1_funct_1(B_290, A_292)) | ~r2_hidden(A_292, k1_relat_1(B_290)) | ~v1_funct_1(C_291) | ~v1_relat_1(C_291) | ~v1_funct_1(B_290) | ~v1_relat_1(B_290))), inference(cnfTransformation, [status(thm)], [f_84])).
% 19.93/10.05  tff(c_9208, plain, (![A_576, C_577, C_578]: (k1_funct_1(k5_relat_1(A_576, C_577), '#skF_11'(A_576, k2_relat_1(A_576), C_578))=k1_funct_1(C_577, k1_funct_1(A_576, '#skF_11'(A_576, k2_relat_1(A_576), C_578))) | ~v1_funct_1(C_577) | ~v1_relat_1(C_577) | ~r2_hidden(C_578, k2_relat_1(A_576)) | ~v1_funct_1(A_576) | ~v1_relat_1(A_576))), inference(resolution, [status(thm)], [c_36, c_2394])).
% 19.93/10.05  tff(c_9249, plain, (![C_578]: (k1_funct_1(k5_relat_1('#skF_13', '#skF_14'), '#skF_11'('#skF_13', k2_relat_1('#skF_13'), C_578))=k1_funct_1('#skF_15', k1_funct_1('#skF_13', '#skF_11'('#skF_13', k2_relat_1('#skF_13'), C_578))) | ~v1_funct_1('#skF_15') | ~v1_relat_1('#skF_15') | ~r2_hidden(C_578, k2_relat_1('#skF_13')) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_9208])).
% 19.93/10.05  tff(c_9268, plain, (![C_578]: (k1_funct_1(k5_relat_1('#skF_13', '#skF_14'), '#skF_11'('#skF_13', '#skF_12', C_578))=k1_funct_1('#skF_15', k1_funct_1('#skF_13', '#skF_11'('#skF_13', '#skF_12', C_578))) | ~r2_hidden(C_578, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_66, c_70, c_68, c_66, c_66, c_9249])).
% 19.93/10.05  tff(c_9252, plain, (![C_577, C_578]: (k1_funct_1(C_577, k1_funct_1('#skF_13', '#skF_11'('#skF_13', k2_relat_1('#skF_13'), C_578)))=k1_funct_1(k5_relat_1('#skF_13', C_577), '#skF_11'('#skF_13', '#skF_12', C_578)) | ~v1_funct_1(C_577) | ~v1_relat_1(C_577) | ~r2_hidden(C_578, k2_relat_1('#skF_13')) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_9208])).
% 19.93/10.05  tff(c_12553, plain, (![C_693, C_694]: (k1_funct_1(k5_relat_1('#skF_13', C_693), '#skF_11'('#skF_13', '#skF_12', C_694))=k1_funct_1(C_693, k1_funct_1('#skF_13', '#skF_11'('#skF_13', '#skF_12', C_694))) | ~v1_funct_1(C_693) | ~v1_relat_1(C_693) | ~r2_hidden(C_694, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_66, c_66, c_9252])).
% 19.93/10.05  tff(c_12582, plain, (![C_578]: (k1_funct_1('#skF_15', k1_funct_1('#skF_13', '#skF_11'('#skF_13', '#skF_12', C_578)))=k1_funct_1('#skF_14', k1_funct_1('#skF_13', '#skF_11'('#skF_13', '#skF_12', C_578))) | ~v1_funct_1('#skF_14') | ~v1_relat_1('#skF_14') | ~r2_hidden(C_578, '#skF_12') | ~r2_hidden(C_578, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_9268, c_12553])).
% 19.93/10.05  tff(c_25026, plain, (![C_1066]: (k1_funct_1('#skF_15', k1_funct_1('#skF_13', '#skF_11'('#skF_13', '#skF_12', C_1066)))=k1_funct_1('#skF_14', k1_funct_1('#skF_13', '#skF_11'('#skF_13', '#skF_12', C_1066))) | ~r2_hidden(C_1066, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_12582])).
% 19.93/10.05  tff(c_25090, plain, (![C_1067]: (k1_funct_1('#skF_14', k1_funct_1('#skF_13', '#skF_11'('#skF_13', '#skF_12', C_1067)))=k1_funct_1('#skF_15', C_1067) | ~r2_hidden(C_1067, '#skF_12') | ~r2_hidden(C_1067, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_1137, c_25026])).
% 19.93/10.05  tff(c_25154, plain, (![C_1068]: (k1_funct_1('#skF_15', C_1068)=k1_funct_1('#skF_14', C_1068) | ~r2_hidden(C_1068, '#skF_12') | ~r2_hidden(C_1068, '#skF_12') | ~r2_hidden(C_1068, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_1137, c_25090])).
% 19.93/10.05  tff(c_25873, plain, (![B_1076]: (k1_funct_1('#skF_15', '#skF_2'('#skF_15', B_1076))=k1_funct_1('#skF_14', '#skF_2'('#skF_15', B_1076)) | ~r2_hidden('#skF_2'('#skF_15', B_1076), '#skF_12') | r1_tarski('#skF_15', B_1076))), inference(resolution, [status(thm)], [c_346, c_25154])).
% 19.93/10.05  tff(c_25877, plain, (![B_387]: (k1_funct_1('#skF_15', '#skF_2'('#skF_15', B_387))=k1_funct_1('#skF_14', '#skF_2'('#skF_15', B_387)) | ~r1_tarski('#skF_12', '#skF_12') | ~r1_tarski('#skF_15', '#skF_15') | r1_tarski('#skF_15', B_387) | ~v1_relat_1('#skF_15'))), inference(resolution, [status(thm)], [c_4523, c_25873])).
% 19.93/10.05  tff(c_25920, plain, (![B_1077]: (k1_funct_1('#skF_15', '#skF_2'('#skF_15', B_1077))=k1_funct_1('#skF_14', '#skF_2'('#skF_15', B_1077)) | r1_tarski('#skF_15', B_1077))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_12, c_12, c_25877])).
% 19.93/10.05  tff(c_54, plain, (![C_90, A_88, B_89]: (k1_funct_1(C_90, A_88)=B_89 | ~r2_hidden(k4_tarski(A_88, B_89), C_90) | ~v1_funct_1(C_90) | ~v1_relat_1(C_90))), inference(cnfTransformation, [status(thm)], [f_94])).
% 19.93/10.05  tff(c_4382, plain, (![B_378, A_376, B_377]: (k1_funct_1(B_378, '#skF_2'(A_376, B_377))='#skF_3'(A_376, B_377) | ~v1_funct_1(B_378) | ~v1_relat_1(B_378) | ~r1_tarski(A_376, B_378) | r1_tarski(A_376, B_377) | ~v1_relat_1(A_376))), inference(resolution, [status(thm)], [c_4316, c_54])).
% 19.93/10.05  tff(c_25950, plain, (![B_1077]: (k1_funct_1('#skF_14', '#skF_2'('#skF_15', B_1077))='#skF_3'('#skF_15', B_1077) | ~v1_funct_1('#skF_15') | ~v1_relat_1('#skF_15') | ~r1_tarski('#skF_15', '#skF_15') | r1_tarski('#skF_15', B_1077) | ~v1_relat_1('#skF_15') | r1_tarski('#skF_15', B_1077))), inference(superposition, [status(thm), theory('equality')], [c_25920, c_4382])).
% 19.93/10.05  tff(c_26037, plain, (![B_1078]: (k1_funct_1('#skF_14', '#skF_2'('#skF_15', B_1078))='#skF_3'('#skF_15', B_1078) | r1_tarski('#skF_15', B_1078))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_12, c_70, c_68, c_25950])).
% 19.93/10.05  tff(c_52, plain, (![A_88, C_90]: (r2_hidden(k4_tarski(A_88, k1_funct_1(C_90, A_88)), C_90) | ~r2_hidden(A_88, k1_relat_1(C_90)) | ~v1_funct_1(C_90) | ~v1_relat_1(C_90))), inference(cnfTransformation, [status(thm)], [f_94])).
% 19.93/10.05  tff(c_26089, plain, (![B_1078]: (r2_hidden(k4_tarski('#skF_2'('#skF_15', B_1078), '#skF_3'('#skF_15', B_1078)), '#skF_14') | ~r2_hidden('#skF_2'('#skF_15', B_1078), k1_relat_1('#skF_14')) | ~v1_funct_1('#skF_14') | ~v1_relat_1('#skF_14') | r1_tarski('#skF_15', B_1078))), inference(superposition, [status(thm), theory('equality')], [c_26037, c_52])).
% 19.93/10.05  tff(c_26554, plain, (![B_1086]: (r2_hidden(k4_tarski('#skF_2'('#skF_15', B_1086), '#skF_3'('#skF_15', B_1086)), '#skF_14') | ~r2_hidden('#skF_2'('#skF_15', B_1086), '#skF_12') | r1_tarski('#skF_15', B_1086))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_64, c_26089])).
% 19.93/10.05  tff(c_16, plain, (![A_8, B_18]: (~r2_hidden(k4_tarski('#skF_2'(A_8, B_18), '#skF_3'(A_8, B_18)), B_18) | r1_tarski(A_8, B_18) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 19.93/10.05  tff(c_26558, plain, (~v1_relat_1('#skF_15') | ~r2_hidden('#skF_2'('#skF_15', '#skF_14'), '#skF_12') | r1_tarski('#skF_15', '#skF_14')), inference(resolution, [status(thm)], [c_26554, c_16])).
% 19.93/10.05  tff(c_26569, plain, (~r2_hidden('#skF_2'('#skF_15', '#skF_14'), '#skF_12') | r1_tarski('#skF_15', '#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_26558])).
% 19.93/10.05  tff(c_26570, plain, (~r2_hidden('#skF_2'('#skF_15', '#skF_14'), '#skF_12')), inference(negUnitSimplification, [status(thm)], [c_11178, c_26569])).
% 19.93/10.05  tff(c_26644, plain, (~r1_tarski('#skF_12', '#skF_12') | ~r1_tarski('#skF_15', '#skF_15') | r1_tarski('#skF_15', '#skF_14') | ~v1_relat_1('#skF_15')), inference(resolution, [status(thm)], [c_4523, c_26570])).
% 19.93/10.05  tff(c_26665, plain, (r1_tarski('#skF_15', '#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_12, c_12, c_26644])).
% 19.93/10.05  tff(c_26667, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11178, c_26665])).
% 19.93/10.05  tff(c_26669, plain, (r1_tarski('#skF_15', '#skF_14')), inference(splitRight, [status(thm)], [c_10649])).
% 19.93/10.05  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 19.93/10.05  tff(c_26711, plain, ('#skF_15'='#skF_14' | ~r1_tarski('#skF_14', '#skF_15')), inference(resolution, [status(thm)], [c_26669, c_8])).
% 19.93/10.05  tff(c_26739, plain, (~r1_tarski('#skF_14', '#skF_15')), inference(negUnitSimplification, [status(thm)], [c_58, c_26711])).
% 19.93/10.05  tff(c_4500, plain, (![A_384, B_385]: (r2_hidden('#skF_2'(A_384, B_385), '#skF_12') | ~r1_tarski(A_384, '#skF_14') | r1_tarski(A_384, B_385) | ~v1_relat_1(A_384))), inference(superposition, [status(thm), theory('equality')], [c_64, c_4468])).
% 19.93/10.05  tff(c_4511, plain, (![A_384, B_385, B_2]: (r2_hidden('#skF_2'(A_384, B_385), B_2) | ~r1_tarski('#skF_12', B_2) | ~r1_tarski(A_384, '#skF_14') | r1_tarski(A_384, B_385) | ~v1_relat_1(A_384))), inference(resolution, [status(thm)], [c_4500, c_2])).
% 19.93/10.05  tff(c_4489, plain, (![A_381, B_382]: (r2_hidden('#skF_2'(A_381, B_382), '#skF_12') | ~r1_tarski(A_381, '#skF_14') | r1_tarski(A_381, B_382) | ~v1_relat_1(A_381))), inference(superposition, [status(thm), theory('equality')], [c_64, c_4468])).
% 19.93/10.05  tff(c_471, plain, (![B_147, C_146]: (k1_funct_1(B_147, C_146)='#skF_7'('#skF_15', '#skF_12', C_146) | ~v1_funct_1(B_147) | ~v1_relat_1(B_147) | ~r1_tarski('#skF_15', B_147) | ~r2_hidden(C_146, '#skF_12'))), inference(resolution, [status(thm)], [c_452, c_54])).
% 19.93/10.05  tff(c_26689, plain, (![C_146]: (k1_funct_1('#skF_14', C_146)='#skF_7'('#skF_15', '#skF_12', C_146) | ~v1_funct_1('#skF_14') | ~v1_relat_1('#skF_14') | ~r2_hidden(C_146, '#skF_12'))), inference(resolution, [status(thm)], [c_26669, c_471])).
% 19.93/10.05  tff(c_26789, plain, (![C_1092]: (k1_funct_1('#skF_14', C_1092)='#skF_7'('#skF_15', '#skF_12', C_1092) | ~r2_hidden(C_1092, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_26689])).
% 19.93/10.05  tff(c_27870, plain, (![A_1107, B_1108]: (k1_funct_1('#skF_14', '#skF_2'(A_1107, B_1108))='#skF_7'('#skF_15', '#skF_12', '#skF_2'(A_1107, B_1108)) | ~r1_tarski(A_1107, '#skF_14') | r1_tarski(A_1107, B_1108) | ~v1_relat_1(A_1107))), inference(resolution, [status(thm)], [c_4489, c_26789])).
% 19.93/10.05  tff(c_1480, plain, (![A_236, B_237]: (k1_funct_1(A_236, '#skF_2'(A_236, B_237))='#skF_3'(A_236, B_237) | ~v1_funct_1(A_236) | r1_tarski(A_236, B_237) | ~v1_relat_1(A_236))), inference(resolution, [status(thm)], [c_262, c_54])).
% 19.93/10.05  tff(c_338, plain, (![B_134]: (r2_hidden('#skF_2'('#skF_14', B_134), '#skF_12') | r1_tarski('#skF_14', B_134) | ~v1_relat_1('#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_333])).
% 19.93/10.05  tff(c_347, plain, (![B_135]: (r2_hidden('#skF_2'('#skF_14', B_135), '#skF_12') | r1_tarski('#skF_14', B_135))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_338])).
% 19.93/10.05  tff(c_138, plain, (![C_114]: (r2_hidden(k4_tarski(C_114, '#skF_7'('#skF_14', '#skF_12', C_114)), '#skF_14') | ~r2_hidden(C_114, k1_relat_1('#skF_14')))), inference(superposition, [status(thm), theory('equality')], [c_64, c_127])).
% 19.93/10.05  tff(c_147, plain, (![C_116]: (r2_hidden(k4_tarski(C_116, '#skF_7'('#skF_14', '#skF_12', C_116)), '#skF_14') | ~r2_hidden(C_116, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_138])).
% 19.93/10.05  tff(c_150, plain, (![C_116]: (k1_funct_1('#skF_14', C_116)='#skF_7'('#skF_14', '#skF_12', C_116) | ~v1_funct_1('#skF_14') | ~v1_relat_1('#skF_14') | ~r2_hidden(C_116, '#skF_12'))), inference(resolution, [status(thm)], [c_147, c_54])).
% 19.93/10.05  tff(c_158, plain, (![C_116]: (k1_funct_1('#skF_14', C_116)='#skF_7'('#skF_14', '#skF_12', C_116) | ~r2_hidden(C_116, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_150])).
% 19.93/10.05  tff(c_357, plain, (![B_135]: (k1_funct_1('#skF_14', '#skF_2'('#skF_14', B_135))='#skF_7'('#skF_14', '#skF_12', '#skF_2'('#skF_14', B_135)) | r1_tarski('#skF_14', B_135))), inference(resolution, [status(thm)], [c_347, c_158])).
% 19.93/10.05  tff(c_1487, plain, (![B_237]: ('#skF_7'('#skF_14', '#skF_12', '#skF_2'('#skF_14', B_237))='#skF_3'('#skF_14', B_237) | r1_tarski('#skF_14', B_237) | ~v1_funct_1('#skF_14') | r1_tarski('#skF_14', B_237) | ~v1_relat_1('#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_1480, c_357])).
% 19.93/10.05  tff(c_1529, plain, (![B_238]: ('#skF_7'('#skF_14', '#skF_12', '#skF_2'('#skF_14', B_238))='#skF_3'('#skF_14', B_238) | r1_tarski('#skF_14', B_238))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_1487])).
% 19.93/10.05  tff(c_145, plain, (![C_114]: (r2_hidden(k4_tarski(C_114, '#skF_7'('#skF_14', '#skF_12', C_114)), '#skF_14') | ~r2_hidden(C_114, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_138])).
% 19.93/10.05  tff(c_3638, plain, (![B_348]: (r2_hidden(k4_tarski('#skF_2'('#skF_14', B_348), '#skF_3'('#skF_14', B_348)), '#skF_14') | ~r2_hidden('#skF_2'('#skF_14', B_348), '#skF_12') | r1_tarski('#skF_14', B_348))), inference(superposition, [status(thm), theory('equality')], [c_1529, c_145])).
% 19.93/10.05  tff(c_3645, plain, (![B_348]: (k1_funct_1('#skF_14', '#skF_2'('#skF_14', B_348))='#skF_3'('#skF_14', B_348) | ~v1_funct_1('#skF_14') | ~v1_relat_1('#skF_14') | ~r2_hidden('#skF_2'('#skF_14', B_348), '#skF_12') | r1_tarski('#skF_14', B_348))), inference(resolution, [status(thm)], [c_3638, c_54])).
% 19.93/10.05  tff(c_4968, plain, (![B_407]: (k1_funct_1('#skF_14', '#skF_2'('#skF_14', B_407))='#skF_3'('#skF_14', B_407) | ~r2_hidden('#skF_2'('#skF_14', B_407), '#skF_12') | r1_tarski('#skF_14', B_407))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_3645])).
% 19.93/10.05  tff(c_4976, plain, (![B_385]: (k1_funct_1('#skF_14', '#skF_2'('#skF_14', B_385))='#skF_3'('#skF_14', B_385) | ~r1_tarski('#skF_12', '#skF_12') | ~r1_tarski('#skF_14', '#skF_14') | r1_tarski('#skF_14', B_385) | ~v1_relat_1('#skF_14'))), inference(resolution, [status(thm)], [c_4511, c_4968])).
% 19.93/10.05  tff(c_5001, plain, (![B_385]: (k1_funct_1('#skF_14', '#skF_2'('#skF_14', B_385))='#skF_3'('#skF_14', B_385) | r1_tarski('#skF_14', B_385))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_12, c_12, c_4976])).
% 19.93/10.05  tff(c_27883, plain, (![B_1108]: ('#skF_7'('#skF_15', '#skF_12', '#skF_2'('#skF_14', B_1108))='#skF_3'('#skF_14', B_1108) | r1_tarski('#skF_14', B_1108) | ~r1_tarski('#skF_14', '#skF_14') | r1_tarski('#skF_14', B_1108) | ~v1_relat_1('#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_27870, c_5001])).
% 19.93/10.05  tff(c_27964, plain, (![B_1109]: ('#skF_7'('#skF_15', '#skF_12', '#skF_2'('#skF_14', B_1109))='#skF_3'('#skF_14', B_1109) | r1_tarski('#skF_14', B_1109))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_12, c_27883])).
% 19.93/10.05  tff(c_146, plain, (![C_114]: (r2_hidden(k4_tarski(C_114, '#skF_7'('#skF_15', '#skF_12', C_114)), '#skF_15') | ~r2_hidden(C_114, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_141])).
% 19.93/10.05  tff(c_46906, plain, (![B_1434]: (r2_hidden(k4_tarski('#skF_2'('#skF_14', B_1434), '#skF_3'('#skF_14', B_1434)), '#skF_15') | ~r2_hidden('#skF_2'('#skF_14', B_1434), '#skF_12') | r1_tarski('#skF_14', B_1434))), inference(superposition, [status(thm), theory('equality')], [c_27964, c_146])).
% 19.93/10.05  tff(c_46910, plain, (~v1_relat_1('#skF_14') | ~r2_hidden('#skF_2'('#skF_14', '#skF_15'), '#skF_12') | r1_tarski('#skF_14', '#skF_15')), inference(resolution, [status(thm)], [c_46906, c_16])).
% 19.93/10.05  tff(c_46921, plain, (~r2_hidden('#skF_2'('#skF_14', '#skF_15'), '#skF_12') | r1_tarski('#skF_14', '#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_46910])).
% 19.93/10.05  tff(c_46922, plain, (~r2_hidden('#skF_2'('#skF_14', '#skF_15'), '#skF_12')), inference(negUnitSimplification, [status(thm)], [c_26739, c_46921])).
% 19.93/10.05  tff(c_46937, plain, (~r1_tarski('#skF_12', '#skF_12') | ~r1_tarski('#skF_14', '#skF_14') | r1_tarski('#skF_14', '#skF_15') | ~v1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_4511, c_46922])).
% 19.93/10.05  tff(c_46963, plain, (r1_tarski('#skF_14', '#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_12, c_12, c_46937])).
% 19.93/10.05  tff(c_46965, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26739, c_46963])).
% 19.93/10.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.93/10.05  
% 19.93/10.05  Inference rules
% 19.93/10.05  ----------------------
% 19.93/10.05  #Ref     : 5
% 19.93/10.05  #Sup     : 11326
% 19.93/10.05  #Fact    : 0
% 19.93/10.05  #Define  : 0
% 19.93/10.05  #Split   : 46
% 19.93/10.05  #Chain   : 0
% 19.93/10.05  #Close   : 0
% 19.93/10.05  
% 19.93/10.05  Ordering : KBO
% 19.93/10.05  
% 19.93/10.05  Simplification rules
% 19.93/10.05  ----------------------
% 19.93/10.05  #Subsume      : 3769
% 19.93/10.05  #Demod        : 5032
% 19.93/10.05  #Tautology    : 885
% 19.93/10.05  #SimpNegUnit  : 15
% 19.93/10.05  #BackRed      : 34
% 19.93/10.05  
% 19.93/10.05  #Partial instantiations: 0
% 19.93/10.05  #Strategies tried      : 1
% 19.93/10.05  
% 19.93/10.05  Timing (in seconds)
% 19.93/10.05  ----------------------
% 19.93/10.05  Preprocessing        : 0.35
% 19.93/10.06  Parsing              : 0.17
% 19.93/10.06  CNF conversion       : 0.03
% 19.93/10.06  Main loop            : 8.89
% 19.93/10.06  Inferencing          : 2.02
% 19.93/10.06  Reduction            : 1.84
% 19.93/10.06  Demodulation         : 1.10
% 19.93/10.06  BG Simplification    : 0.21
% 19.93/10.06  Subsumption          : 4.15
% 19.93/10.06  Abstraction          : 0.33
% 19.93/10.06  MUC search           : 0.00
% 19.93/10.06  Cooper               : 0.00
% 19.93/10.06  Total                : 9.29
% 19.93/10.06  Index Insertion      : 0.00
% 19.93/10.06  Index Deletion       : 0.00
% 19.93/10.06  Index Matching       : 0.00
% 19.93/10.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
