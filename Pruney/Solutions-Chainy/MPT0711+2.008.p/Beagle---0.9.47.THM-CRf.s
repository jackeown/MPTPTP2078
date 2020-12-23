%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:30 EST 2020

% Result     : Theorem 6.90s
% Output     : CNFRefutation 7.24s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 215 expanded)
%              Number of leaves         :   20 (  82 expanded)
%              Depth                    :   15
%              Number of atoms          :  153 ( 783 expanded)
%              Number of equality atoms :   49 ( 275 expanded)
%              Maximal formula depth    :   20 (   5 average)
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

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

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
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_funct_1)).

tff(c_20,plain,(
    k7_relat_1('#skF_2','#skF_4') != k7_relat_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_32,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_30,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
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

tff(c_53,plain,(
    ! [A_36] : k3_xboole_0(k1_relat_1('#skF_3'),A_36) = k1_relat_1(k7_relat_1('#skF_2',A_36)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_49])).

tff(c_74,plain,(
    ! [A_36] : k3_xboole_0(k1_relat_1('#skF_3'),A_36) = k1_relat_1(k7_relat_1('#skF_3',A_36)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_53])).

tff(c_26,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k7_relat_1(A_6,B_7))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_219,plain,(
    ! [A_66,B_67,C_68] :
      ( r2_hidden('#skF_1'(A_66,B_67,C_68),k1_relat_1(B_67))
      | k7_relat_1(C_68,A_66) = B_67
      | k3_xboole_0(k1_relat_1(C_68),A_66) != k1_relat_1(B_67)
      | ~ v1_funct_1(C_68)
      | ~ v1_relat_1(C_68)
      | ~ v1_funct_1(B_67)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

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

tff(c_618,plain,(
    ! [A_117,A_118,C_119] :
      ( r2_hidden('#skF_1'(A_117,k7_relat_1('#skF_3',A_118),C_119),A_118)
      | k7_relat_1(C_119,A_117) = k7_relat_1('#skF_3',A_118)
      | k3_xboole_0(k1_relat_1(C_119),A_117) != k1_relat_1(k7_relat_1('#skF_3',A_118))
      | ~ v1_funct_1(C_119)
      | ~ v1_relat_1(C_119)
      | ~ v1_funct_1(k7_relat_1('#skF_3',A_118))
      | ~ v1_relat_1(k7_relat_1('#skF_3',A_118)) ) ),
    inference(resolution,[status(thm)],[c_219,c_115])).

tff(c_22,plain,(
    ! [D_29] :
      ( k1_funct_1('#skF_2',D_29) = k1_funct_1('#skF_3',D_29)
      | ~ r2_hidden(D_29,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_669,plain,(
    ! [A_117,C_119] :
      ( k1_funct_1('#skF_2','#skF_1'(A_117,k7_relat_1('#skF_3','#skF_4'),C_119)) = k1_funct_1('#skF_3','#skF_1'(A_117,k7_relat_1('#skF_3','#skF_4'),C_119))
      | k7_relat_1(C_119,A_117) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1(C_119),A_117) != k1_relat_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_funct_1(C_119)
      | ~ v1_relat_1(C_119)
      | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_618,c_22])).

tff(c_684,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_669])).

tff(c_687,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_684])).

tff(c_691,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_687])).

tff(c_693,plain,(
    v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_669])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( v1_funct_1(k7_relat_1(A_6,B_7))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_692,plain,(
    ! [A_117,C_119] :
      ( ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4'))
      | k1_funct_1('#skF_2','#skF_1'(A_117,k7_relat_1('#skF_3','#skF_4'),C_119)) = k1_funct_1('#skF_3','#skF_1'(A_117,k7_relat_1('#skF_3','#skF_4'),C_119))
      | k7_relat_1(C_119,A_117) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1(C_119),A_117) != k1_relat_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_funct_1(C_119)
      | ~ v1_relat_1(C_119) ) ),
    inference(splitRight,[status(thm)],[c_669])).

tff(c_892,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_692])).

tff(c_895,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_892])).

tff(c_899,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_895])).

tff(c_901,plain,(
    v1_funct_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_692])).

tff(c_900,plain,(
    ! [A_117,C_119] :
      ( k1_funct_1('#skF_2','#skF_1'(A_117,k7_relat_1('#skF_3','#skF_4'),C_119)) = k1_funct_1('#skF_3','#skF_1'(A_117,k7_relat_1('#skF_3','#skF_4'),C_119))
      | k7_relat_1(C_119,A_117) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1(C_119),A_117) != k1_relat_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_funct_1(C_119)
      | ~ v1_relat_1(C_119) ) ),
    inference(splitRight,[status(thm)],[c_692])).

tff(c_18,plain,(
    ! [C_17,B_16,A_15] :
      ( k1_funct_1(k7_relat_1(C_17,B_16),A_15) = k1_funct_1(C_17,A_15)
      | ~ r2_hidden(A_15,k1_relat_1(k7_relat_1(C_17,B_16)))
      | ~ v1_funct_1(C_17)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_733,plain,(
    ! [C_128,B_129,A_130,C_131] :
      ( k1_funct_1(k7_relat_1(C_128,B_129),'#skF_1'(A_130,k7_relat_1(C_128,B_129),C_131)) = k1_funct_1(C_128,'#skF_1'(A_130,k7_relat_1(C_128,B_129),C_131))
      | ~ v1_funct_1(C_128)
      | ~ v1_relat_1(C_128)
      | k7_relat_1(C_131,A_130) = k7_relat_1(C_128,B_129)
      | k3_xboole_0(k1_relat_1(C_131),A_130) != k1_relat_1(k7_relat_1(C_128,B_129))
      | ~ v1_funct_1(C_131)
      | ~ v1_relat_1(C_131)
      | ~ v1_funct_1(k7_relat_1(C_128,B_129))
      | ~ v1_relat_1(k7_relat_1(C_128,B_129)) ) ),
    inference(resolution,[status(thm)],[c_219,c_18])).

tff(c_14,plain,(
    ! [C_13,A_8,B_9] :
      ( k1_funct_1(C_13,'#skF_1'(A_8,B_9,C_13)) != k1_funct_1(B_9,'#skF_1'(A_8,B_9,C_13))
      | k7_relat_1(C_13,A_8) = B_9
      | k3_xboole_0(k1_relat_1(C_13),A_8) != k1_relat_1(B_9)
      | ~ v1_funct_1(C_13)
      | ~ v1_relat_1(C_13)
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2997,plain,(
    ! [C_324,A_323,B_325,C_322] :
      ( k1_funct_1(C_324,'#skF_1'(A_323,k7_relat_1(C_324,B_325),C_322)) != k1_funct_1(C_322,'#skF_1'(A_323,k7_relat_1(C_324,B_325),C_322))
      | k7_relat_1(C_324,B_325) = k7_relat_1(C_322,A_323)
      | k3_xboole_0(k1_relat_1(C_322),A_323) != k1_relat_1(k7_relat_1(C_324,B_325))
      | ~ v1_funct_1(C_322)
      | ~ v1_relat_1(C_322)
      | ~ v1_funct_1(k7_relat_1(C_324,B_325))
      | ~ v1_relat_1(k7_relat_1(C_324,B_325))
      | ~ v1_funct_1(C_324)
      | ~ v1_relat_1(C_324)
      | k7_relat_1(C_324,B_325) = k7_relat_1(C_322,A_323)
      | k3_xboole_0(k1_relat_1(C_322),A_323) != k1_relat_1(k7_relat_1(C_324,B_325))
      | ~ v1_funct_1(C_322)
      | ~ v1_relat_1(C_322)
      | ~ v1_funct_1(k7_relat_1(C_324,B_325))
      | ~ v1_relat_1(k7_relat_1(C_324,B_325)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_733,c_14])).

tff(c_3071,plain,(
    ! [A_117] :
      ( ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4'))
      | k7_relat_1('#skF_2',A_117) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1('#skF_2'),A_117) != k1_relat_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_900,c_2997])).

tff(c_3133,plain,(
    ! [A_117] :
      ( k7_relat_1('#skF_2',A_117) = k7_relat_1('#skF_3','#skF_4')
      | k1_relat_1(k7_relat_1('#skF_3',A_117)) != k1_relat_1(k7_relat_1('#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_74,c_24,c_693,c_901,c_28,c_26,c_3071])).

tff(c_3141,plain,(
    k7_relat_1('#skF_2','#skF_4') = k7_relat_1('#skF_3','#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3133])).

tff(c_3143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_3141])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n009.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 20:50:11 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.90/2.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.90/2.37  
% 6.90/2.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.90/2.38  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k1_relat_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 6.90/2.38  
% 6.90/2.38  %Foreground sorts:
% 6.90/2.38  
% 6.90/2.38  
% 6.90/2.38  %Background operators:
% 6.90/2.38  
% 6.90/2.38  
% 6.90/2.38  %Foreground operators:
% 6.90/2.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.90/2.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.90/2.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.90/2.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.90/2.38  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.90/2.38  tff('#skF_2', type, '#skF_2': $i).
% 6.90/2.38  tff('#skF_3', type, '#skF_3': $i).
% 6.90/2.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.90/2.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.90/2.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.90/2.38  tff('#skF_4', type, '#skF_4': $i).
% 6.90/2.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.90/2.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.90/2.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.90/2.38  
% 7.24/2.39  tff(f_91, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (((k1_relat_1(A) = k1_relat_1(B)) & (![D]: (r2_hidden(D, C) => (k1_funct_1(A, D) = k1_funct_1(B, D))))) => (k7_relat_1(A, C) = k7_relat_1(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_funct_1)).
% 7.24/2.39  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 7.24/2.39  tff(f_45, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 7.24/2.39  tff(f_63, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = k3_xboole_0(k1_relat_1(C), A)) & (![D]: (r2_hidden(D, k1_relat_1(B)) => (k1_funct_1(B, D) = k1_funct_1(C, D))))) => (B = k7_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_funct_1)).
% 7.24/2.39  tff(f_33, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 7.24/2.39  tff(f_71, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_funct_1)).
% 7.24/2.39  tff(c_20, plain, (k7_relat_1('#skF_2', '#skF_4')!=k7_relat_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.24/2.39  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.24/2.39  tff(c_30, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.24/2.39  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.24/2.39  tff(c_24, plain, (k1_relat_1('#skF_2')=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.24/2.39  tff(c_40, plain, (![B_35, A_36]: (k3_xboole_0(k1_relat_1(B_35), A_36)=k1_relat_1(k7_relat_1(B_35, A_36)) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.24/2.39  tff(c_49, plain, (![A_36]: (k3_xboole_0(k1_relat_1('#skF_3'), A_36)=k1_relat_1(k7_relat_1('#skF_2', A_36)) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_40])).
% 7.24/2.39  tff(c_54, plain, (![A_37]: (k3_xboole_0(k1_relat_1('#skF_3'), A_37)=k1_relat_1(k7_relat_1('#skF_2', A_37)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_49])).
% 7.24/2.39  tff(c_8, plain, (![B_5, A_4]: (k3_xboole_0(k1_relat_1(B_5), A_4)=k1_relat_1(k7_relat_1(B_5, A_4)) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.24/2.39  tff(c_60, plain, (![A_37]: (k1_relat_1(k7_relat_1('#skF_2', A_37))=k1_relat_1(k7_relat_1('#skF_3', A_37)) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_8])).
% 7.24/2.39  tff(c_70, plain, (![A_37]: (k1_relat_1(k7_relat_1('#skF_2', A_37))=k1_relat_1(k7_relat_1('#skF_3', A_37)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_60])).
% 7.24/2.39  tff(c_53, plain, (![A_36]: (k3_xboole_0(k1_relat_1('#skF_3'), A_36)=k1_relat_1(k7_relat_1('#skF_2', A_36)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_49])).
% 7.24/2.39  tff(c_74, plain, (![A_36]: (k3_xboole_0(k1_relat_1('#skF_3'), A_36)=k1_relat_1(k7_relat_1('#skF_3', A_36)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_53])).
% 7.24/2.39  tff(c_26, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.24/2.39  tff(c_12, plain, (![A_6, B_7]: (v1_relat_1(k7_relat_1(A_6, B_7)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.24/2.39  tff(c_219, plain, (![A_66, B_67, C_68]: (r2_hidden('#skF_1'(A_66, B_67, C_68), k1_relat_1(B_67)) | k7_relat_1(C_68, A_66)=B_67 | k3_xboole_0(k1_relat_1(C_68), A_66)!=k1_relat_1(B_67) | ~v1_funct_1(C_68) | ~v1_relat_1(C_68) | ~v1_funct_1(B_67) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.24/2.39  tff(c_110, plain, (![A_40, B_41, C_42]: (r2_hidden(A_40, B_41) | ~r2_hidden(A_40, k1_relat_1(k7_relat_1(C_42, B_41))) | ~v1_relat_1(C_42))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.24/2.39  tff(c_113, plain, (![A_40, A_37]: (r2_hidden(A_40, A_37) | ~r2_hidden(A_40, k1_relat_1(k7_relat_1('#skF_3', A_37))) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_110])).
% 7.24/2.39  tff(c_115, plain, (![A_40, A_37]: (r2_hidden(A_40, A_37) | ~r2_hidden(A_40, k1_relat_1(k7_relat_1('#skF_3', A_37))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_113])).
% 7.24/2.39  tff(c_618, plain, (![A_117, A_118, C_119]: (r2_hidden('#skF_1'(A_117, k7_relat_1('#skF_3', A_118), C_119), A_118) | k7_relat_1(C_119, A_117)=k7_relat_1('#skF_3', A_118) | k3_xboole_0(k1_relat_1(C_119), A_117)!=k1_relat_1(k7_relat_1('#skF_3', A_118)) | ~v1_funct_1(C_119) | ~v1_relat_1(C_119) | ~v1_funct_1(k7_relat_1('#skF_3', A_118)) | ~v1_relat_1(k7_relat_1('#skF_3', A_118)))), inference(resolution, [status(thm)], [c_219, c_115])).
% 7.24/2.39  tff(c_22, plain, (![D_29]: (k1_funct_1('#skF_2', D_29)=k1_funct_1('#skF_3', D_29) | ~r2_hidden(D_29, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.24/2.39  tff(c_669, plain, (![A_117, C_119]: (k1_funct_1('#skF_2', '#skF_1'(A_117, k7_relat_1('#skF_3', '#skF_4'), C_119))=k1_funct_1('#skF_3', '#skF_1'(A_117, k7_relat_1('#skF_3', '#skF_4'), C_119)) | k7_relat_1(C_119, A_117)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1(C_119), A_117)!=k1_relat_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_funct_1(C_119) | ~v1_relat_1(C_119) | ~v1_funct_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_618, c_22])).
% 7.24/2.39  tff(c_684, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_669])).
% 7.24/2.39  tff(c_687, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_684])).
% 7.24/2.39  tff(c_691, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_687])).
% 7.24/2.39  tff(c_693, plain, (v1_relat_1(k7_relat_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_669])).
% 7.24/2.39  tff(c_10, plain, (![A_6, B_7]: (v1_funct_1(k7_relat_1(A_6, B_7)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.24/2.39  tff(c_692, plain, (![A_117, C_119]: (~v1_funct_1(k7_relat_1('#skF_3', '#skF_4')) | k1_funct_1('#skF_2', '#skF_1'(A_117, k7_relat_1('#skF_3', '#skF_4'), C_119))=k1_funct_1('#skF_3', '#skF_1'(A_117, k7_relat_1('#skF_3', '#skF_4'), C_119)) | k7_relat_1(C_119, A_117)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1(C_119), A_117)!=k1_relat_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_funct_1(C_119) | ~v1_relat_1(C_119))), inference(splitRight, [status(thm)], [c_669])).
% 7.24/2.39  tff(c_892, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_692])).
% 7.24/2.39  tff(c_895, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_892])).
% 7.24/2.39  tff(c_899, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_895])).
% 7.24/2.39  tff(c_901, plain, (v1_funct_1(k7_relat_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_692])).
% 7.24/2.39  tff(c_900, plain, (![A_117, C_119]: (k1_funct_1('#skF_2', '#skF_1'(A_117, k7_relat_1('#skF_3', '#skF_4'), C_119))=k1_funct_1('#skF_3', '#skF_1'(A_117, k7_relat_1('#skF_3', '#skF_4'), C_119)) | k7_relat_1(C_119, A_117)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1(C_119), A_117)!=k1_relat_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_funct_1(C_119) | ~v1_relat_1(C_119))), inference(splitRight, [status(thm)], [c_692])).
% 7.24/2.39  tff(c_18, plain, (![C_17, B_16, A_15]: (k1_funct_1(k7_relat_1(C_17, B_16), A_15)=k1_funct_1(C_17, A_15) | ~r2_hidden(A_15, k1_relat_1(k7_relat_1(C_17, B_16))) | ~v1_funct_1(C_17) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.24/2.39  tff(c_733, plain, (![C_128, B_129, A_130, C_131]: (k1_funct_1(k7_relat_1(C_128, B_129), '#skF_1'(A_130, k7_relat_1(C_128, B_129), C_131))=k1_funct_1(C_128, '#skF_1'(A_130, k7_relat_1(C_128, B_129), C_131)) | ~v1_funct_1(C_128) | ~v1_relat_1(C_128) | k7_relat_1(C_131, A_130)=k7_relat_1(C_128, B_129) | k3_xboole_0(k1_relat_1(C_131), A_130)!=k1_relat_1(k7_relat_1(C_128, B_129)) | ~v1_funct_1(C_131) | ~v1_relat_1(C_131) | ~v1_funct_1(k7_relat_1(C_128, B_129)) | ~v1_relat_1(k7_relat_1(C_128, B_129)))), inference(resolution, [status(thm)], [c_219, c_18])).
% 7.24/2.39  tff(c_14, plain, (![C_13, A_8, B_9]: (k1_funct_1(C_13, '#skF_1'(A_8, B_9, C_13))!=k1_funct_1(B_9, '#skF_1'(A_8, B_9, C_13)) | k7_relat_1(C_13, A_8)=B_9 | k3_xboole_0(k1_relat_1(C_13), A_8)!=k1_relat_1(B_9) | ~v1_funct_1(C_13) | ~v1_relat_1(C_13) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.24/2.39  tff(c_2997, plain, (![C_324, A_323, B_325, C_322]: (k1_funct_1(C_324, '#skF_1'(A_323, k7_relat_1(C_324, B_325), C_322))!=k1_funct_1(C_322, '#skF_1'(A_323, k7_relat_1(C_324, B_325), C_322)) | k7_relat_1(C_324, B_325)=k7_relat_1(C_322, A_323) | k3_xboole_0(k1_relat_1(C_322), A_323)!=k1_relat_1(k7_relat_1(C_324, B_325)) | ~v1_funct_1(C_322) | ~v1_relat_1(C_322) | ~v1_funct_1(k7_relat_1(C_324, B_325)) | ~v1_relat_1(k7_relat_1(C_324, B_325)) | ~v1_funct_1(C_324) | ~v1_relat_1(C_324) | k7_relat_1(C_324, B_325)=k7_relat_1(C_322, A_323) | k3_xboole_0(k1_relat_1(C_322), A_323)!=k1_relat_1(k7_relat_1(C_324, B_325)) | ~v1_funct_1(C_322) | ~v1_relat_1(C_322) | ~v1_funct_1(k7_relat_1(C_324, B_325)) | ~v1_relat_1(k7_relat_1(C_324, B_325)))), inference(superposition, [status(thm), theory('equality')], [c_733, c_14])).
% 7.24/2.39  tff(c_3071, plain, (![A_117]: (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_4')) | k7_relat_1('#skF_2', A_117)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1('#skF_2'), A_117)!=k1_relat_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_900, c_2997])).
% 7.24/2.39  tff(c_3133, plain, (![A_117]: (k7_relat_1('#skF_2', A_117)=k7_relat_1('#skF_3', '#skF_4') | k1_relat_1(k7_relat_1('#skF_3', A_117))!=k1_relat_1(k7_relat_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_74, c_24, c_693, c_901, c_28, c_26, c_3071])).
% 7.24/2.39  tff(c_3141, plain, (k7_relat_1('#skF_2', '#skF_4')=k7_relat_1('#skF_3', '#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_3133])).
% 7.24/2.39  tff(c_3143, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_3141])).
% 7.24/2.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.24/2.39  
% 7.24/2.39  Inference rules
% 7.24/2.39  ----------------------
% 7.24/2.39  #Ref     : 5
% 7.24/2.39  #Sup     : 636
% 7.24/2.39  #Fact    : 0
% 7.24/2.39  #Define  : 0
% 7.24/2.39  #Split   : 8
% 7.24/2.39  #Chain   : 0
% 7.24/2.39  #Close   : 0
% 7.24/2.39  
% 7.24/2.39  Ordering : KBO
% 7.24/2.39  
% 7.24/2.39  Simplification rules
% 7.24/2.39  ----------------------
% 7.24/2.39  #Subsume      : 39
% 7.24/2.39  #Demod        : 716
% 7.24/2.39  #Tautology    : 189
% 7.24/2.39  #SimpNegUnit  : 1
% 7.24/2.39  #BackRed      : 1
% 7.24/2.39  
% 7.24/2.39  #Partial instantiations: 0
% 7.24/2.39  #Strategies tried      : 1
% 7.24/2.39  
% 7.24/2.39  Timing (in seconds)
% 7.24/2.39  ----------------------
% 7.24/2.39  Preprocessing        : 0.30
% 7.24/2.39  Parsing              : 0.16
% 7.24/2.39  CNF conversion       : 0.02
% 7.24/2.39  Main loop            : 1.33
% 7.24/2.39  Inferencing          : 0.46
% 7.24/2.39  Reduction            : 0.34
% 7.24/2.39  Demodulation         : 0.25
% 7.24/2.39  BG Simplification    : 0.08
% 7.24/2.39  Subsumption          : 0.37
% 7.24/2.39  Abstraction          : 0.10
% 7.24/2.39  MUC search           : 0.00
% 7.24/2.39  Cooper               : 0.00
% 7.24/2.40  Total                : 1.66
% 7.24/2.40  Index Insertion      : 0.00
% 7.24/2.40  Index Deletion       : 0.00
% 7.24/2.40  Index Matching       : 0.00
% 7.28/2.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
