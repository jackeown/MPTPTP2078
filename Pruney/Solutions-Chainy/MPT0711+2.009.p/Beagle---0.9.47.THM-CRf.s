%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:30 EST 2020

% Result     : Theorem 12.69s
% Output     : CNFRefutation 12.69s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 218 expanded)
%              Number of leaves         :   20 (  83 expanded)
%              Depth                    :   15
%              Number of atoms          :  165 ( 792 expanded)
%              Number of equality atoms :   52 ( 278 expanded)
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
     => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_funct_1)).

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

tff(c_234,plain,(
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

tff(c_878,plain,(
    ! [A_146,A_147,C_148] :
      ( r2_hidden('#skF_1'(A_146,k7_relat_1('#skF_3',A_147),C_148),A_147)
      | k7_relat_1(C_148,A_146) = k7_relat_1('#skF_3',A_147)
      | k3_xboole_0(k1_relat_1(C_148),A_146) != k1_relat_1(k7_relat_1('#skF_3',A_147))
      | ~ v1_funct_1(C_148)
      | ~ v1_relat_1(C_148)
      | ~ v1_funct_1(k7_relat_1('#skF_3',A_147))
      | ~ v1_relat_1(k7_relat_1('#skF_3',A_147)) ) ),
    inference(resolution,[status(thm)],[c_234,c_115])).

tff(c_22,plain,(
    ! [D_29] :
      ( k1_funct_1('#skF_2',D_29) = k1_funct_1('#skF_3',D_29)
      | ~ r2_hidden(D_29,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_958,plain,(
    ! [A_146,C_148] :
      ( k1_funct_1('#skF_2','#skF_1'(A_146,k7_relat_1('#skF_3','#skF_4'),C_148)) = k1_funct_1('#skF_3','#skF_1'(A_146,k7_relat_1('#skF_3','#skF_4'),C_148))
      | k7_relat_1(C_148,A_146) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1(C_148),A_146) != k1_relat_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_funct_1(C_148)
      | ~ v1_relat_1(C_148)
      | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_878,c_22])).

tff(c_1093,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_958])).

tff(c_1096,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_1093])).

tff(c_1100,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1096])).

tff(c_1102,plain,(
    v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_958])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( v1_funct_1(k7_relat_1(A_6,B_7))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1101,plain,(
    ! [A_146,C_148] :
      ( ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4'))
      | k1_funct_1('#skF_2','#skF_1'(A_146,k7_relat_1('#skF_3','#skF_4'),C_148)) = k1_funct_1('#skF_3','#skF_1'(A_146,k7_relat_1('#skF_3','#skF_4'),C_148))
      | k7_relat_1(C_148,A_146) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1(C_148),A_146) != k1_relat_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_funct_1(C_148)
      | ~ v1_relat_1(C_148) ) ),
    inference(splitRight,[status(thm)],[c_958])).

tff(c_1886,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1101])).

tff(c_1889,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_1886])).

tff(c_1893,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1889])).

tff(c_1895,plain,(
    v1_funct_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1101])).

tff(c_1894,plain,(
    ! [A_146,C_148] :
      ( k1_funct_1('#skF_2','#skF_1'(A_146,k7_relat_1('#skF_3','#skF_4'),C_148)) = k1_funct_1('#skF_3','#skF_1'(A_146,k7_relat_1('#skF_3','#skF_4'),C_148))
      | k7_relat_1(C_148,A_146) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1(C_148),A_146) != k1_relat_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_funct_1(C_148)
      | ~ v1_relat_1(C_148) ) ),
    inference(splitRight,[status(thm)],[c_1101])).

tff(c_16,plain,(
    ! [A_8,B_9,C_13] :
      ( r2_hidden('#skF_1'(A_8,B_9,C_13),k1_relat_1(B_9))
      | k7_relat_1(C_13,A_8) = B_9
      | k3_xboole_0(k1_relat_1(C_13),A_8) != k1_relat_1(B_9)
      | ~ v1_funct_1(C_13)
      | ~ v1_relat_1(C_13)
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_189,plain,(
    ! [C_57,B_58,A_59] :
      ( k1_funct_1(k7_relat_1(C_57,B_58),A_59) = k1_funct_1(C_57,A_59)
      | ~ r2_hidden(A_59,k3_xboole_0(k1_relat_1(C_57),B_58))
      | ~ v1_funct_1(C_57)
      | ~ v1_relat_1(C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_294,plain,(
    ! [B_73,A_74,A_75] :
      ( k1_funct_1(k7_relat_1(B_73,A_74),A_75) = k1_funct_1(B_73,A_75)
      | ~ r2_hidden(A_75,k1_relat_1(k7_relat_1(B_73,A_74)))
      | ~ v1_funct_1(B_73)
      | ~ v1_relat_1(B_73)
      | ~ v1_relat_1(B_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_189])).

tff(c_769,plain,(
    ! [B_131,A_132,A_133,C_134] :
      ( k1_funct_1(k7_relat_1(B_131,A_132),'#skF_1'(A_133,k7_relat_1(B_131,A_132),C_134)) = k1_funct_1(B_131,'#skF_1'(A_133,k7_relat_1(B_131,A_132),C_134))
      | ~ v1_funct_1(B_131)
      | ~ v1_relat_1(B_131)
      | k7_relat_1(C_134,A_133) = k7_relat_1(B_131,A_132)
      | k3_xboole_0(k1_relat_1(C_134),A_133) != k1_relat_1(k7_relat_1(B_131,A_132))
      | ~ v1_funct_1(C_134)
      | ~ v1_relat_1(C_134)
      | ~ v1_funct_1(k7_relat_1(B_131,A_132))
      | ~ v1_relat_1(k7_relat_1(B_131,A_132)) ) ),
    inference(resolution,[status(thm)],[c_16,c_294])).

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

tff(c_11078,plain,(
    ! [C_738,A_739,B_740,A_741] :
      ( k1_funct_1(C_738,'#skF_1'(A_739,k7_relat_1(B_740,A_741),C_738)) != k1_funct_1(B_740,'#skF_1'(A_739,k7_relat_1(B_740,A_741),C_738))
      | k7_relat_1(C_738,A_739) = k7_relat_1(B_740,A_741)
      | k3_xboole_0(k1_relat_1(C_738),A_739) != k1_relat_1(k7_relat_1(B_740,A_741))
      | ~ v1_funct_1(C_738)
      | ~ v1_relat_1(C_738)
      | ~ v1_funct_1(k7_relat_1(B_740,A_741))
      | ~ v1_relat_1(k7_relat_1(B_740,A_741))
      | ~ v1_funct_1(B_740)
      | ~ v1_relat_1(B_740)
      | k7_relat_1(C_738,A_739) = k7_relat_1(B_740,A_741)
      | k3_xboole_0(k1_relat_1(C_738),A_739) != k1_relat_1(k7_relat_1(B_740,A_741))
      | ~ v1_funct_1(C_738)
      | ~ v1_relat_1(C_738)
      | ~ v1_funct_1(k7_relat_1(B_740,A_741))
      | ~ v1_relat_1(k7_relat_1(B_740,A_741)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_769,c_14])).

tff(c_11297,plain,(
    ! [A_146] :
      ( ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4'))
      | k7_relat_1('#skF_2',A_146) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1('#skF_2'),A_146) != k1_relat_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1894,c_11078])).

tff(c_11434,plain,(
    ! [A_146] :
      ( k7_relat_1('#skF_2',A_146) = k7_relat_1('#skF_3','#skF_4')
      | k1_relat_1(k7_relat_1('#skF_3',A_146)) != k1_relat_1(k7_relat_1('#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_74,c_24,c_1102,c_1895,c_28,c_26,c_11297])).

tff(c_11448,plain,(
    k7_relat_1('#skF_2','#skF_4') = k7_relat_1('#skF_3','#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_11434])).

tff(c_11450,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_11448])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:13:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.69/5.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.69/5.71  
% 12.69/5.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.69/5.71  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k1_relat_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 12.69/5.71  
% 12.69/5.71  %Foreground sorts:
% 12.69/5.71  
% 12.69/5.71  
% 12.69/5.71  %Background operators:
% 12.69/5.71  
% 12.69/5.71  
% 12.69/5.71  %Foreground operators:
% 12.69/5.71  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 12.69/5.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.69/5.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.69/5.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.69/5.71  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 12.69/5.71  tff('#skF_2', type, '#skF_2': $i).
% 12.69/5.71  tff('#skF_3', type, '#skF_3': $i).
% 12.69/5.71  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 12.69/5.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.69/5.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.69/5.71  tff('#skF_4', type, '#skF_4': $i).
% 12.69/5.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.69/5.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.69/5.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.69/5.71  
% 12.69/5.72  tff(f_91, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (((k1_relat_1(A) = k1_relat_1(B)) & (![D]: (r2_hidden(D, C) => (k1_funct_1(A, D) = k1_funct_1(B, D))))) => (k7_relat_1(A, C) = k7_relat_1(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_funct_1)).
% 12.69/5.72  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 12.69/5.72  tff(f_45, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 12.69/5.72  tff(f_63, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = k3_xboole_0(k1_relat_1(C), A)) & (![D]: (r2_hidden(D, k1_relat_1(B)) => (k1_funct_1(B, D) = k1_funct_1(C, D))))) => (B = k7_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_funct_1)).
% 12.69/5.72  tff(f_33, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 12.69/5.72  tff(f_71, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_funct_1)).
% 12.69/5.72  tff(c_20, plain, (k7_relat_1('#skF_2', '#skF_4')!=k7_relat_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.69/5.72  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.69/5.72  tff(c_30, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.69/5.72  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.69/5.72  tff(c_24, plain, (k1_relat_1('#skF_2')=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.69/5.72  tff(c_40, plain, (![B_35, A_36]: (k3_xboole_0(k1_relat_1(B_35), A_36)=k1_relat_1(k7_relat_1(B_35, A_36)) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.69/5.72  tff(c_49, plain, (![A_36]: (k3_xboole_0(k1_relat_1('#skF_3'), A_36)=k1_relat_1(k7_relat_1('#skF_2', A_36)) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_40])).
% 12.69/5.72  tff(c_54, plain, (![A_37]: (k3_xboole_0(k1_relat_1('#skF_3'), A_37)=k1_relat_1(k7_relat_1('#skF_2', A_37)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_49])).
% 12.69/5.72  tff(c_8, plain, (![B_5, A_4]: (k3_xboole_0(k1_relat_1(B_5), A_4)=k1_relat_1(k7_relat_1(B_5, A_4)) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.69/5.72  tff(c_60, plain, (![A_37]: (k1_relat_1(k7_relat_1('#skF_2', A_37))=k1_relat_1(k7_relat_1('#skF_3', A_37)) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_8])).
% 12.69/5.72  tff(c_70, plain, (![A_37]: (k1_relat_1(k7_relat_1('#skF_2', A_37))=k1_relat_1(k7_relat_1('#skF_3', A_37)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_60])).
% 12.69/5.72  tff(c_53, plain, (![A_36]: (k3_xboole_0(k1_relat_1('#skF_3'), A_36)=k1_relat_1(k7_relat_1('#skF_2', A_36)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_49])).
% 12.69/5.72  tff(c_74, plain, (![A_36]: (k3_xboole_0(k1_relat_1('#skF_3'), A_36)=k1_relat_1(k7_relat_1('#skF_3', A_36)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_53])).
% 12.69/5.72  tff(c_26, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.69/5.72  tff(c_12, plain, (![A_6, B_7]: (v1_relat_1(k7_relat_1(A_6, B_7)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.69/5.72  tff(c_234, plain, (![A_66, B_67, C_68]: (r2_hidden('#skF_1'(A_66, B_67, C_68), k1_relat_1(B_67)) | k7_relat_1(C_68, A_66)=B_67 | k3_xboole_0(k1_relat_1(C_68), A_66)!=k1_relat_1(B_67) | ~v1_funct_1(C_68) | ~v1_relat_1(C_68) | ~v1_funct_1(B_67) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.69/5.72  tff(c_110, plain, (![A_40, B_41, C_42]: (r2_hidden(A_40, B_41) | ~r2_hidden(A_40, k1_relat_1(k7_relat_1(C_42, B_41))) | ~v1_relat_1(C_42))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.69/5.72  tff(c_113, plain, (![A_40, A_37]: (r2_hidden(A_40, A_37) | ~r2_hidden(A_40, k1_relat_1(k7_relat_1('#skF_3', A_37))) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_110])).
% 12.69/5.72  tff(c_115, plain, (![A_40, A_37]: (r2_hidden(A_40, A_37) | ~r2_hidden(A_40, k1_relat_1(k7_relat_1('#skF_3', A_37))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_113])).
% 12.69/5.72  tff(c_878, plain, (![A_146, A_147, C_148]: (r2_hidden('#skF_1'(A_146, k7_relat_1('#skF_3', A_147), C_148), A_147) | k7_relat_1(C_148, A_146)=k7_relat_1('#skF_3', A_147) | k3_xboole_0(k1_relat_1(C_148), A_146)!=k1_relat_1(k7_relat_1('#skF_3', A_147)) | ~v1_funct_1(C_148) | ~v1_relat_1(C_148) | ~v1_funct_1(k7_relat_1('#skF_3', A_147)) | ~v1_relat_1(k7_relat_1('#skF_3', A_147)))), inference(resolution, [status(thm)], [c_234, c_115])).
% 12.69/5.72  tff(c_22, plain, (![D_29]: (k1_funct_1('#skF_2', D_29)=k1_funct_1('#skF_3', D_29) | ~r2_hidden(D_29, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.69/5.72  tff(c_958, plain, (![A_146, C_148]: (k1_funct_1('#skF_2', '#skF_1'(A_146, k7_relat_1('#skF_3', '#skF_4'), C_148))=k1_funct_1('#skF_3', '#skF_1'(A_146, k7_relat_1('#skF_3', '#skF_4'), C_148)) | k7_relat_1(C_148, A_146)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1(C_148), A_146)!=k1_relat_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_funct_1(C_148) | ~v1_relat_1(C_148) | ~v1_funct_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_878, c_22])).
% 12.69/5.72  tff(c_1093, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_958])).
% 12.69/5.72  tff(c_1096, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_1093])).
% 12.69/5.72  tff(c_1100, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_1096])).
% 12.69/5.72  tff(c_1102, plain, (v1_relat_1(k7_relat_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_958])).
% 12.69/5.72  tff(c_10, plain, (![A_6, B_7]: (v1_funct_1(k7_relat_1(A_6, B_7)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.69/5.72  tff(c_1101, plain, (![A_146, C_148]: (~v1_funct_1(k7_relat_1('#skF_3', '#skF_4')) | k1_funct_1('#skF_2', '#skF_1'(A_146, k7_relat_1('#skF_3', '#skF_4'), C_148))=k1_funct_1('#skF_3', '#skF_1'(A_146, k7_relat_1('#skF_3', '#skF_4'), C_148)) | k7_relat_1(C_148, A_146)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1(C_148), A_146)!=k1_relat_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_funct_1(C_148) | ~v1_relat_1(C_148))), inference(splitRight, [status(thm)], [c_958])).
% 12.69/5.72  tff(c_1886, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_1101])).
% 12.69/5.72  tff(c_1889, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_1886])).
% 12.69/5.72  tff(c_1893, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_1889])).
% 12.69/5.72  tff(c_1895, plain, (v1_funct_1(k7_relat_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_1101])).
% 12.69/5.72  tff(c_1894, plain, (![A_146, C_148]: (k1_funct_1('#skF_2', '#skF_1'(A_146, k7_relat_1('#skF_3', '#skF_4'), C_148))=k1_funct_1('#skF_3', '#skF_1'(A_146, k7_relat_1('#skF_3', '#skF_4'), C_148)) | k7_relat_1(C_148, A_146)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1(C_148), A_146)!=k1_relat_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_funct_1(C_148) | ~v1_relat_1(C_148))), inference(splitRight, [status(thm)], [c_1101])).
% 12.69/5.72  tff(c_16, plain, (![A_8, B_9, C_13]: (r2_hidden('#skF_1'(A_8, B_9, C_13), k1_relat_1(B_9)) | k7_relat_1(C_13, A_8)=B_9 | k3_xboole_0(k1_relat_1(C_13), A_8)!=k1_relat_1(B_9) | ~v1_funct_1(C_13) | ~v1_relat_1(C_13) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.69/5.72  tff(c_189, plain, (![C_57, B_58, A_59]: (k1_funct_1(k7_relat_1(C_57, B_58), A_59)=k1_funct_1(C_57, A_59) | ~r2_hidden(A_59, k3_xboole_0(k1_relat_1(C_57), B_58)) | ~v1_funct_1(C_57) | ~v1_relat_1(C_57))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.69/5.72  tff(c_294, plain, (![B_73, A_74, A_75]: (k1_funct_1(k7_relat_1(B_73, A_74), A_75)=k1_funct_1(B_73, A_75) | ~r2_hidden(A_75, k1_relat_1(k7_relat_1(B_73, A_74))) | ~v1_funct_1(B_73) | ~v1_relat_1(B_73) | ~v1_relat_1(B_73))), inference(superposition, [status(thm), theory('equality')], [c_8, c_189])).
% 12.69/5.72  tff(c_769, plain, (![B_131, A_132, A_133, C_134]: (k1_funct_1(k7_relat_1(B_131, A_132), '#skF_1'(A_133, k7_relat_1(B_131, A_132), C_134))=k1_funct_1(B_131, '#skF_1'(A_133, k7_relat_1(B_131, A_132), C_134)) | ~v1_funct_1(B_131) | ~v1_relat_1(B_131) | k7_relat_1(C_134, A_133)=k7_relat_1(B_131, A_132) | k3_xboole_0(k1_relat_1(C_134), A_133)!=k1_relat_1(k7_relat_1(B_131, A_132)) | ~v1_funct_1(C_134) | ~v1_relat_1(C_134) | ~v1_funct_1(k7_relat_1(B_131, A_132)) | ~v1_relat_1(k7_relat_1(B_131, A_132)))), inference(resolution, [status(thm)], [c_16, c_294])).
% 12.69/5.72  tff(c_14, plain, (![C_13, A_8, B_9]: (k1_funct_1(C_13, '#skF_1'(A_8, B_9, C_13))!=k1_funct_1(B_9, '#skF_1'(A_8, B_9, C_13)) | k7_relat_1(C_13, A_8)=B_9 | k3_xboole_0(k1_relat_1(C_13), A_8)!=k1_relat_1(B_9) | ~v1_funct_1(C_13) | ~v1_relat_1(C_13) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.69/5.72  tff(c_11078, plain, (![C_738, A_739, B_740, A_741]: (k1_funct_1(C_738, '#skF_1'(A_739, k7_relat_1(B_740, A_741), C_738))!=k1_funct_1(B_740, '#skF_1'(A_739, k7_relat_1(B_740, A_741), C_738)) | k7_relat_1(C_738, A_739)=k7_relat_1(B_740, A_741) | k3_xboole_0(k1_relat_1(C_738), A_739)!=k1_relat_1(k7_relat_1(B_740, A_741)) | ~v1_funct_1(C_738) | ~v1_relat_1(C_738) | ~v1_funct_1(k7_relat_1(B_740, A_741)) | ~v1_relat_1(k7_relat_1(B_740, A_741)) | ~v1_funct_1(B_740) | ~v1_relat_1(B_740) | k7_relat_1(C_738, A_739)=k7_relat_1(B_740, A_741) | k3_xboole_0(k1_relat_1(C_738), A_739)!=k1_relat_1(k7_relat_1(B_740, A_741)) | ~v1_funct_1(C_738) | ~v1_relat_1(C_738) | ~v1_funct_1(k7_relat_1(B_740, A_741)) | ~v1_relat_1(k7_relat_1(B_740, A_741)))), inference(superposition, [status(thm), theory('equality')], [c_769, c_14])).
% 12.69/5.72  tff(c_11297, plain, (![A_146]: (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_4')) | k7_relat_1('#skF_2', A_146)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1('#skF_2'), A_146)!=k1_relat_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1894, c_11078])).
% 12.69/5.72  tff(c_11434, plain, (![A_146]: (k7_relat_1('#skF_2', A_146)=k7_relat_1('#skF_3', '#skF_4') | k1_relat_1(k7_relat_1('#skF_3', A_146))!=k1_relat_1(k7_relat_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_74, c_24, c_1102, c_1895, c_28, c_26, c_11297])).
% 12.69/5.72  tff(c_11448, plain, (k7_relat_1('#skF_2', '#skF_4')=k7_relat_1('#skF_3', '#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_11434])).
% 12.69/5.72  tff(c_11450, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_11448])).
% 12.69/5.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.69/5.72  
% 12.69/5.72  Inference rules
% 12.69/5.72  ----------------------
% 12.69/5.72  #Ref     : 7
% 12.69/5.72  #Sup     : 2277
% 12.69/5.72  #Fact    : 0
% 12.69/5.72  #Define  : 0
% 12.69/5.72  #Split   : 16
% 12.69/5.72  #Chain   : 0
% 12.69/5.72  #Close   : 0
% 12.69/5.72  
% 12.69/5.72  Ordering : KBO
% 12.69/5.72  
% 12.69/5.72  Simplification rules
% 12.69/5.72  ----------------------
% 12.69/5.72  #Subsume      : 215
% 12.69/5.72  #Demod        : 3728
% 12.69/5.72  #Tautology    : 674
% 12.69/5.72  #SimpNegUnit  : 1
% 12.69/5.72  #BackRed      : 1
% 12.69/5.72  
% 12.69/5.72  #Partial instantiations: 0
% 12.69/5.72  #Strategies tried      : 1
% 12.69/5.72  
% 12.69/5.72  Timing (in seconds)
% 12.69/5.72  ----------------------
% 12.69/5.73  Preprocessing        : 0.29
% 12.69/5.73  Parsing              : 0.16
% 12.69/5.73  CNF conversion       : 0.02
% 12.69/5.73  Main loop            : 4.67
% 12.69/5.73  Inferencing          : 1.27
% 12.69/5.73  Reduction            : 1.07
% 12.69/5.73  Demodulation         : 0.81
% 12.69/5.73  BG Simplification    : 0.19
% 12.69/5.73  Subsumption          : 1.92
% 12.69/5.73  Abstraction          : 0.35
% 12.69/5.73  MUC search           : 0.00
% 12.69/5.73  Cooper               : 0.00
% 12.69/5.73  Total                : 4.99
% 12.69/5.73  Index Insertion      : 0.00
% 12.69/5.73  Index Deletion       : 0.00
% 12.69/5.73  Index Matching       : 0.00
% 12.69/5.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
