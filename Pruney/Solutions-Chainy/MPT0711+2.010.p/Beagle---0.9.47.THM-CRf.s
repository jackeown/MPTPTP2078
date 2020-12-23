%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:30 EST 2020

% Result     : Theorem 3.69s
% Output     : CNFRefutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 305 expanded)
%              Number of leaves         :   20 ( 113 expanded)
%              Depth                    :   17
%              Number of atoms          :  162 (1109 expanded)
%              Number of equality atoms :   51 ( 393 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k1_relat_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( ( k1_relat_1(A) = k1_relat_1(B)
                  & ! [D] :
                      ( r2_hidden(D,C)
                     => k1_funct_1(A,D) = k1_funct_1(B,D) ) )
               => k7_relat_1(A,C) = k7_relat_1(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( ( k1_relat_1(B) = k3_xboole_0(k1_relat_1(C),A)
              & ! [D] :
                  ( r2_hidden(D,k1_relat_1(B))
                 => k1_funct_1(B,D) = k1_funct_1(C,D) ) )
           => B = k7_relat_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_funct_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,B)
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).

tff(c_20,plain,(
    k7_relat_1('#skF_2','#skF_4') != k7_relat_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_26,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k7_relat_1(A_6,B_7))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_221,plain,(
    ! [A_62,B_63,C_64] :
      ( r2_hidden('#skF_1'(A_62,B_63,C_64),k1_relat_1(B_63))
      | k7_relat_1(C_64,A_62) = B_63
      | k3_xboole_0(k1_relat_1(C_64),A_62) != k1_relat_1(B_63)
      | ~ v1_funct_1(C_64)
      | ~ v1_relat_1(C_64)
      | ~ v1_funct_1(B_63)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_32,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_24,plain,(
    k1_relat_1('#skF_2') = k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_40,plain,(
    ! [B_35,A_36] :
      ( k3_xboole_0(k1_relat_1(B_35),A_36) = k1_relat_1(k7_relat_1(B_35,A_36))
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_49,plain,(
    ! [A_36] :
      ( k3_xboole_0(k1_relat_1('#skF_3'),A_36) = k1_relat_1(k7_relat_1('#skF_2',A_36))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_40])).

tff(c_54,plain,(
    ! [A_37] : k3_xboole_0(k1_relat_1('#skF_3'),A_37) = k1_relat_1(k7_relat_1('#skF_2',A_37)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_49])).

tff(c_8,plain,(
    ! [B_5,A_4] :
      ( k3_xboole_0(k1_relat_1(B_5),A_4) = k1_relat_1(k7_relat_1(B_5,A_4))
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_60,plain,(
    ! [A_37] :
      ( k1_relat_1(k7_relat_1('#skF_2',A_37)) = k1_relat_1(k7_relat_1('#skF_3',A_37))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_8])).

tff(c_70,plain,(
    ! [A_37] : k1_relat_1(k7_relat_1('#skF_2',A_37)) = k1_relat_1(k7_relat_1('#skF_3',A_37)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_60])).

tff(c_110,plain,(
    ! [A_40,B_41,C_42] :
      ( r2_hidden(A_40,B_41)
      | ~ r2_hidden(A_40,k1_relat_1(k7_relat_1(C_42,B_41)))
      | ~ v1_relat_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_113,plain,(
    ! [A_40,A_37] :
      ( r2_hidden(A_40,A_37)
      | ~ r2_hidden(A_40,k1_relat_1(k7_relat_1('#skF_3',A_37)))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_110])).

tff(c_115,plain,(
    ! [A_40,A_37] :
      ( r2_hidden(A_40,A_37)
      | ~ r2_hidden(A_40,k1_relat_1(k7_relat_1('#skF_3',A_37))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_113])).

tff(c_328,plain,(
    ! [A_81,A_82,C_83] :
      ( r2_hidden('#skF_1'(A_81,k7_relat_1('#skF_3',A_82),C_83),A_82)
      | k7_relat_1(C_83,A_81) = k7_relat_1('#skF_3',A_82)
      | k3_xboole_0(k1_relat_1(C_83),A_81) != k1_relat_1(k7_relat_1('#skF_3',A_82))
      | ~ v1_funct_1(C_83)
      | ~ v1_relat_1(C_83)
      | ~ v1_funct_1(k7_relat_1('#skF_3',A_82))
      | ~ v1_relat_1(k7_relat_1('#skF_3',A_82)) ) ),
    inference(resolution,[status(thm)],[c_221,c_115])).

tff(c_22,plain,(
    ! [D_29] :
      ( k1_funct_1('#skF_2',D_29) = k1_funct_1('#skF_3',D_29)
      | ~ r2_hidden(D_29,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_353,plain,(
    ! [A_81,C_83] :
      ( k1_funct_1('#skF_2','#skF_1'(A_81,k7_relat_1('#skF_3','#skF_4'),C_83)) = k1_funct_1('#skF_3','#skF_1'(A_81,k7_relat_1('#skF_3','#skF_4'),C_83))
      | k7_relat_1(C_83,A_81) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1(C_83),A_81) != k1_relat_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_funct_1(C_83)
      | ~ v1_relat_1(C_83)
      | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_328,c_22])).

tff(c_446,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_353])).

tff(c_449,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_446])).

tff(c_453,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_449])).

tff(c_455,plain,(
    v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_353])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( v1_funct_1(k7_relat_1(A_6,B_7))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_454,plain,(
    ! [A_81,C_83] :
      ( ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4'))
      | k1_funct_1('#skF_2','#skF_1'(A_81,k7_relat_1('#skF_3','#skF_4'),C_83)) = k1_funct_1('#skF_3','#skF_1'(A_81,k7_relat_1('#skF_3','#skF_4'),C_83))
      | k7_relat_1(C_83,A_81) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1(C_83),A_81) != k1_relat_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_funct_1(C_83)
      | ~ v1_relat_1(C_83) ) ),
    inference(splitRight,[status(thm)],[c_353])).

tff(c_990,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_454])).

tff(c_1033,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_990])).

tff(c_1037,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1033])).

tff(c_1039,plain,(
    v1_funct_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_454])).

tff(c_30,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_53,plain,(
    ! [A_36] : k3_xboole_0(k1_relat_1('#skF_3'),A_36) = k1_relat_1(k7_relat_1('#skF_2',A_36)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_49])).

tff(c_74,plain,(
    ! [A_36] : k3_xboole_0(k1_relat_1('#skF_3'),A_36) = k1_relat_1(k7_relat_1('#skF_3',A_36)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_53])).

tff(c_6,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden(A_1,B_2)
      | ~ r2_hidden(A_1,k1_relat_1(k7_relat_1(C_3,B_2)))
      | ~ v1_relat_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_250,plain,(
    ! [A_62,C_3,B_2,C_64] :
      ( r2_hidden('#skF_1'(A_62,k7_relat_1(C_3,B_2),C_64),B_2)
      | ~ v1_relat_1(C_3)
      | k7_relat_1(C_64,A_62) = k7_relat_1(C_3,B_2)
      | k3_xboole_0(k1_relat_1(C_64),A_62) != k1_relat_1(k7_relat_1(C_3,B_2))
      | ~ v1_funct_1(C_64)
      | ~ v1_relat_1(C_64)
      | ~ v1_funct_1(k7_relat_1(C_3,B_2))
      | ~ v1_relat_1(k7_relat_1(C_3,B_2)) ) ),
    inference(resolution,[status(thm)],[c_221,c_6])).

tff(c_1040,plain,(
    ! [A_171,C_172] :
      ( k1_funct_1('#skF_2','#skF_1'(A_171,k7_relat_1('#skF_3','#skF_4'),C_172)) = k1_funct_1('#skF_3','#skF_1'(A_171,k7_relat_1('#skF_3','#skF_4'),C_172))
      | k7_relat_1(C_172,A_171) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1(C_172),A_171) != k1_relat_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_funct_1(C_172)
      | ~ v1_relat_1(C_172) ) ),
    inference(splitRight,[status(thm)],[c_454])).

tff(c_18,plain,(
    ! [C_17,B_16,A_15] :
      ( k1_funct_1(k7_relat_1(C_17,B_16),A_15) = k1_funct_1(C_17,A_15)
      | ~ r2_hidden(A_15,B_16)
      | ~ v1_funct_1(C_17)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_257,plain,(
    ! [C_65,A_66,B_67] :
      ( k1_funct_1(C_65,'#skF_1'(A_66,B_67,C_65)) != k1_funct_1(B_67,'#skF_1'(A_66,B_67,C_65))
      | k7_relat_1(C_65,A_66) = B_67
      | k3_xboole_0(k1_relat_1(C_65),A_66) != k1_relat_1(B_67)
      | ~ v1_funct_1(C_65)
      | ~ v1_relat_1(C_65)
      | ~ v1_funct_1(B_67)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_263,plain,(
    ! [C_65,A_66,C_17,B_16] :
      ( k1_funct_1(C_65,'#skF_1'(A_66,k7_relat_1(C_17,B_16),C_65)) != k1_funct_1(C_17,'#skF_1'(A_66,k7_relat_1(C_17,B_16),C_65))
      | k7_relat_1(C_65,A_66) = k7_relat_1(C_17,B_16)
      | k3_xboole_0(k1_relat_1(C_65),A_66) != k1_relat_1(k7_relat_1(C_17,B_16))
      | ~ v1_funct_1(C_65)
      | ~ v1_relat_1(C_65)
      | ~ v1_funct_1(k7_relat_1(C_17,B_16))
      | ~ v1_relat_1(k7_relat_1(C_17,B_16))
      | ~ r2_hidden('#skF_1'(A_66,k7_relat_1(C_17,B_16),C_65),B_16)
      | ~ v1_funct_1(C_17)
      | ~ v1_relat_1(C_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_257])).

tff(c_1049,plain,(
    ! [A_171] :
      ( ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ r2_hidden('#skF_1'(A_171,k7_relat_1('#skF_3','#skF_4'),'#skF_2'),'#skF_4')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | k7_relat_1('#skF_2',A_171) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1('#skF_2'),A_171) != k1_relat_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1040,c_263])).

tff(c_1091,plain,(
    ! [A_175] :
      ( ~ r2_hidden('#skF_1'(A_175,k7_relat_1('#skF_3','#skF_4'),'#skF_2'),'#skF_4')
      | k7_relat_1('#skF_2',A_175) = k7_relat_1('#skF_3','#skF_4')
      | k1_relat_1(k7_relat_1('#skF_3',A_175)) != k1_relat_1(k7_relat_1('#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_74,c_24,c_28,c_26,c_455,c_1039,c_1049])).

tff(c_1095,plain,(
    ! [A_62] :
      ( k1_relat_1(k7_relat_1('#skF_3',A_62)) != k1_relat_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_relat_1('#skF_3')
      | k7_relat_1('#skF_2',A_62) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1('#skF_2'),A_62) != k1_relat_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_250,c_1091])).

tff(c_1102,plain,(
    ! [A_62] :
      ( k7_relat_1('#skF_2',A_62) = k7_relat_1('#skF_3','#skF_4')
      | k1_relat_1(k7_relat_1('#skF_3',A_62)) != k1_relat_1(k7_relat_1('#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_1039,c_32,c_30,c_74,c_24,c_28,c_1095])).

tff(c_1108,plain,(
    k7_relat_1('#skF_2','#skF_4') = k7_relat_1('#skF_3','#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1102])).

tff(c_1110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_1108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:53:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.69/1.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.69/1.72  
% 3.69/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.69/1.73  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k1_relat_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.69/1.73  
% 3.69/1.73  %Foreground sorts:
% 3.69/1.73  
% 3.69/1.73  
% 3.69/1.73  %Background operators:
% 3.69/1.73  
% 3.69/1.73  
% 3.69/1.73  %Foreground operators:
% 3.69/1.73  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.69/1.73  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.69/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.69/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.69/1.73  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.69/1.73  tff('#skF_2', type, '#skF_2': $i).
% 3.69/1.73  tff('#skF_3', type, '#skF_3': $i).
% 3.69/1.73  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.69/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.69/1.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.69/1.73  tff('#skF_4', type, '#skF_4': $i).
% 3.69/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.69/1.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.69/1.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.69/1.73  
% 3.69/1.74  tff(f_91, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (((k1_relat_1(A) = k1_relat_1(B)) & (![D]: (r2_hidden(D, C) => (k1_funct_1(A, D) = k1_funct_1(B, D))))) => (k7_relat_1(A, C) = k7_relat_1(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_funct_1)).
% 3.69/1.74  tff(f_45, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 3.69/1.74  tff(f_63, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = k3_xboole_0(k1_relat_1(C), A)) & (![D]: (r2_hidden(D, k1_relat_1(B)) => (k1_funct_1(B, D) = k1_funct_1(C, D))))) => (B = k7_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_funct_1)).
% 3.69/1.74  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 3.69/1.74  tff(f_33, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 3.69/1.74  tff(f_71, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, B) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_funct_1)).
% 3.69/1.74  tff(c_20, plain, (k7_relat_1('#skF_2', '#skF_4')!=k7_relat_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.69/1.74  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.69/1.74  tff(c_26, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.69/1.74  tff(c_12, plain, (![A_6, B_7]: (v1_relat_1(k7_relat_1(A_6, B_7)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.69/1.74  tff(c_221, plain, (![A_62, B_63, C_64]: (r2_hidden('#skF_1'(A_62, B_63, C_64), k1_relat_1(B_63)) | k7_relat_1(C_64, A_62)=B_63 | k3_xboole_0(k1_relat_1(C_64), A_62)!=k1_relat_1(B_63) | ~v1_funct_1(C_64) | ~v1_relat_1(C_64) | ~v1_funct_1(B_63) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.69/1.74  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.69/1.74  tff(c_24, plain, (k1_relat_1('#skF_2')=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.69/1.74  tff(c_40, plain, (![B_35, A_36]: (k3_xboole_0(k1_relat_1(B_35), A_36)=k1_relat_1(k7_relat_1(B_35, A_36)) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.69/1.74  tff(c_49, plain, (![A_36]: (k3_xboole_0(k1_relat_1('#skF_3'), A_36)=k1_relat_1(k7_relat_1('#skF_2', A_36)) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_40])).
% 3.69/1.74  tff(c_54, plain, (![A_37]: (k3_xboole_0(k1_relat_1('#skF_3'), A_37)=k1_relat_1(k7_relat_1('#skF_2', A_37)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_49])).
% 3.69/1.74  tff(c_8, plain, (![B_5, A_4]: (k3_xboole_0(k1_relat_1(B_5), A_4)=k1_relat_1(k7_relat_1(B_5, A_4)) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.69/1.74  tff(c_60, plain, (![A_37]: (k1_relat_1(k7_relat_1('#skF_2', A_37))=k1_relat_1(k7_relat_1('#skF_3', A_37)) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_8])).
% 3.69/1.74  tff(c_70, plain, (![A_37]: (k1_relat_1(k7_relat_1('#skF_2', A_37))=k1_relat_1(k7_relat_1('#skF_3', A_37)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_60])).
% 3.69/1.74  tff(c_110, plain, (![A_40, B_41, C_42]: (r2_hidden(A_40, B_41) | ~r2_hidden(A_40, k1_relat_1(k7_relat_1(C_42, B_41))) | ~v1_relat_1(C_42))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.69/1.74  tff(c_113, plain, (![A_40, A_37]: (r2_hidden(A_40, A_37) | ~r2_hidden(A_40, k1_relat_1(k7_relat_1('#skF_3', A_37))) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_110])).
% 3.69/1.74  tff(c_115, plain, (![A_40, A_37]: (r2_hidden(A_40, A_37) | ~r2_hidden(A_40, k1_relat_1(k7_relat_1('#skF_3', A_37))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_113])).
% 3.69/1.74  tff(c_328, plain, (![A_81, A_82, C_83]: (r2_hidden('#skF_1'(A_81, k7_relat_1('#skF_3', A_82), C_83), A_82) | k7_relat_1(C_83, A_81)=k7_relat_1('#skF_3', A_82) | k3_xboole_0(k1_relat_1(C_83), A_81)!=k1_relat_1(k7_relat_1('#skF_3', A_82)) | ~v1_funct_1(C_83) | ~v1_relat_1(C_83) | ~v1_funct_1(k7_relat_1('#skF_3', A_82)) | ~v1_relat_1(k7_relat_1('#skF_3', A_82)))), inference(resolution, [status(thm)], [c_221, c_115])).
% 3.69/1.74  tff(c_22, plain, (![D_29]: (k1_funct_1('#skF_2', D_29)=k1_funct_1('#skF_3', D_29) | ~r2_hidden(D_29, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.69/1.74  tff(c_353, plain, (![A_81, C_83]: (k1_funct_1('#skF_2', '#skF_1'(A_81, k7_relat_1('#skF_3', '#skF_4'), C_83))=k1_funct_1('#skF_3', '#skF_1'(A_81, k7_relat_1('#skF_3', '#skF_4'), C_83)) | k7_relat_1(C_83, A_81)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1(C_83), A_81)!=k1_relat_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_funct_1(C_83) | ~v1_relat_1(C_83) | ~v1_funct_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_328, c_22])).
% 3.69/1.74  tff(c_446, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_353])).
% 3.69/1.74  tff(c_449, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_446])).
% 3.69/1.74  tff(c_453, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_449])).
% 3.69/1.74  tff(c_455, plain, (v1_relat_1(k7_relat_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_353])).
% 3.69/1.74  tff(c_10, plain, (![A_6, B_7]: (v1_funct_1(k7_relat_1(A_6, B_7)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.69/1.74  tff(c_454, plain, (![A_81, C_83]: (~v1_funct_1(k7_relat_1('#skF_3', '#skF_4')) | k1_funct_1('#skF_2', '#skF_1'(A_81, k7_relat_1('#skF_3', '#skF_4'), C_83))=k1_funct_1('#skF_3', '#skF_1'(A_81, k7_relat_1('#skF_3', '#skF_4'), C_83)) | k7_relat_1(C_83, A_81)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1(C_83), A_81)!=k1_relat_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_funct_1(C_83) | ~v1_relat_1(C_83))), inference(splitRight, [status(thm)], [c_353])).
% 3.69/1.74  tff(c_990, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_454])).
% 3.69/1.74  tff(c_1033, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_990])).
% 3.69/1.74  tff(c_1037, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_1033])).
% 3.69/1.74  tff(c_1039, plain, (v1_funct_1(k7_relat_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_454])).
% 3.69/1.74  tff(c_30, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.69/1.74  tff(c_53, plain, (![A_36]: (k3_xboole_0(k1_relat_1('#skF_3'), A_36)=k1_relat_1(k7_relat_1('#skF_2', A_36)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_49])).
% 3.69/1.74  tff(c_74, plain, (![A_36]: (k3_xboole_0(k1_relat_1('#skF_3'), A_36)=k1_relat_1(k7_relat_1('#skF_3', A_36)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_53])).
% 3.69/1.74  tff(c_6, plain, (![A_1, B_2, C_3]: (r2_hidden(A_1, B_2) | ~r2_hidden(A_1, k1_relat_1(k7_relat_1(C_3, B_2))) | ~v1_relat_1(C_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.69/1.74  tff(c_250, plain, (![A_62, C_3, B_2, C_64]: (r2_hidden('#skF_1'(A_62, k7_relat_1(C_3, B_2), C_64), B_2) | ~v1_relat_1(C_3) | k7_relat_1(C_64, A_62)=k7_relat_1(C_3, B_2) | k3_xboole_0(k1_relat_1(C_64), A_62)!=k1_relat_1(k7_relat_1(C_3, B_2)) | ~v1_funct_1(C_64) | ~v1_relat_1(C_64) | ~v1_funct_1(k7_relat_1(C_3, B_2)) | ~v1_relat_1(k7_relat_1(C_3, B_2)))), inference(resolution, [status(thm)], [c_221, c_6])).
% 3.69/1.74  tff(c_1040, plain, (![A_171, C_172]: (k1_funct_1('#skF_2', '#skF_1'(A_171, k7_relat_1('#skF_3', '#skF_4'), C_172))=k1_funct_1('#skF_3', '#skF_1'(A_171, k7_relat_1('#skF_3', '#skF_4'), C_172)) | k7_relat_1(C_172, A_171)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1(C_172), A_171)!=k1_relat_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_funct_1(C_172) | ~v1_relat_1(C_172))), inference(splitRight, [status(thm)], [c_454])).
% 3.69/1.74  tff(c_18, plain, (![C_17, B_16, A_15]: (k1_funct_1(k7_relat_1(C_17, B_16), A_15)=k1_funct_1(C_17, A_15) | ~r2_hidden(A_15, B_16) | ~v1_funct_1(C_17) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.69/1.74  tff(c_257, plain, (![C_65, A_66, B_67]: (k1_funct_1(C_65, '#skF_1'(A_66, B_67, C_65))!=k1_funct_1(B_67, '#skF_1'(A_66, B_67, C_65)) | k7_relat_1(C_65, A_66)=B_67 | k3_xboole_0(k1_relat_1(C_65), A_66)!=k1_relat_1(B_67) | ~v1_funct_1(C_65) | ~v1_relat_1(C_65) | ~v1_funct_1(B_67) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.69/1.74  tff(c_263, plain, (![C_65, A_66, C_17, B_16]: (k1_funct_1(C_65, '#skF_1'(A_66, k7_relat_1(C_17, B_16), C_65))!=k1_funct_1(C_17, '#skF_1'(A_66, k7_relat_1(C_17, B_16), C_65)) | k7_relat_1(C_65, A_66)=k7_relat_1(C_17, B_16) | k3_xboole_0(k1_relat_1(C_65), A_66)!=k1_relat_1(k7_relat_1(C_17, B_16)) | ~v1_funct_1(C_65) | ~v1_relat_1(C_65) | ~v1_funct_1(k7_relat_1(C_17, B_16)) | ~v1_relat_1(k7_relat_1(C_17, B_16)) | ~r2_hidden('#skF_1'(A_66, k7_relat_1(C_17, B_16), C_65), B_16) | ~v1_funct_1(C_17) | ~v1_relat_1(C_17))), inference(superposition, [status(thm), theory('equality')], [c_18, c_257])).
% 3.69/1.74  tff(c_1049, plain, (![A_171]: (~v1_funct_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_4')) | ~r2_hidden('#skF_1'(A_171, k7_relat_1('#skF_3', '#skF_4'), '#skF_2'), '#skF_4') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | k7_relat_1('#skF_2', A_171)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1('#skF_2'), A_171)!=k1_relat_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1040, c_263])).
% 3.69/1.74  tff(c_1091, plain, (![A_175]: (~r2_hidden('#skF_1'(A_175, k7_relat_1('#skF_3', '#skF_4'), '#skF_2'), '#skF_4') | k7_relat_1('#skF_2', A_175)=k7_relat_1('#skF_3', '#skF_4') | k1_relat_1(k7_relat_1('#skF_3', A_175))!=k1_relat_1(k7_relat_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_74, c_24, c_28, c_26, c_455, c_1039, c_1049])).
% 3.69/1.74  tff(c_1095, plain, (![A_62]: (k1_relat_1(k7_relat_1('#skF_3', A_62))!=k1_relat_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1('#skF_3') | k7_relat_1('#skF_2', A_62)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1('#skF_2'), A_62)!=k1_relat_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_funct_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_250, c_1091])).
% 3.69/1.74  tff(c_1102, plain, (![A_62]: (k7_relat_1('#skF_2', A_62)=k7_relat_1('#skF_3', '#skF_4') | k1_relat_1(k7_relat_1('#skF_3', A_62))!=k1_relat_1(k7_relat_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_455, c_1039, c_32, c_30, c_74, c_24, c_28, c_1095])).
% 3.69/1.74  tff(c_1108, plain, (k7_relat_1('#skF_2', '#skF_4')=k7_relat_1('#skF_3', '#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_1102])).
% 3.69/1.74  tff(c_1110, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_1108])).
% 3.69/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.69/1.74  
% 3.69/1.74  Inference rules
% 3.69/1.74  ----------------------
% 3.69/1.74  #Ref     : 11
% 3.69/1.74  #Sup     : 210
% 3.69/1.74  #Fact    : 0
% 3.69/1.74  #Define  : 0
% 3.69/1.74  #Split   : 9
% 3.69/1.74  #Chain   : 0
% 3.69/1.74  #Close   : 0
% 3.69/1.74  
% 3.69/1.74  Ordering : KBO
% 3.69/1.74  
% 3.69/1.74  Simplification rules
% 3.69/1.74  ----------------------
% 3.69/1.74  #Subsume      : 25
% 3.69/1.74  #Demod        : 260
% 3.69/1.74  #Tautology    : 50
% 3.69/1.74  #SimpNegUnit  : 1
% 3.69/1.74  #BackRed      : 1
% 3.69/1.74  
% 3.69/1.74  #Partial instantiations: 0
% 3.69/1.74  #Strategies tried      : 1
% 4.04/1.74  
% 4.04/1.74  Timing (in seconds)
% 4.04/1.74  ----------------------
% 4.04/1.74  Preprocessing        : 0.30
% 4.04/1.74  Parsing              : 0.16
% 4.04/1.74  CNF conversion       : 0.02
% 4.04/1.74  Main loop            : 0.58
% 4.04/1.74  Inferencing          : 0.22
% 4.04/1.74  Reduction            : 0.16
% 4.04/1.74  Demodulation         : 0.11
% 4.04/1.74  BG Simplification    : 0.03
% 4.04/1.74  Subsumption          : 0.14
% 4.04/1.74  Abstraction          : 0.04
% 4.04/1.74  MUC search           : 0.00
% 4.04/1.74  Cooper               : 0.00
% 4.04/1.74  Total                : 0.91
% 4.04/1.74  Index Insertion      : 0.00
% 4.04/1.74  Index Deletion       : 0.00
% 4.04/1.74  Index Matching       : 0.00
% 4.04/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
