%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:40 EST 2020

% Result     : Theorem 19.28s
% Output     : CNFRefutation 19.50s
% Verified   : 
% Statistics : Number of formulae       :  235 (19552 expanded)
%              Number of leaves         :   31 (6870 expanded)
%              Depth                    :   41
%              Number of atoms          :  751 (72308 expanded)
%              Number of equality atoms :  180 (15792 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_5 > #skF_4 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_1 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(f_143,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v2_funct_1(k5_relat_1(B,A))
                & k2_relat_1(B) = k1_relat_1(A) )
             => ( v2_funct_1(B)
                & v2_funct_1(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_57,axiom,(
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

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_110,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_125,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & r1_tarski(k2_relat_1(B),k1_relat_1(A)) )
           => v2_funct_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_1)).

tff(f_72,axiom,(
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

tff(f_97,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

tff(c_58,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_56,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_12,plain,(
    ! [A_7,C_43] :
      ( r2_hidden('#skF_4'(A_7,k2_relat_1(A_7),C_43),k1_relat_1(A_7))
      | ~ r2_hidden(C_43,k2_relat_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10,plain,(
    ! [A_7,C_43] :
      ( k1_funct_1(A_7,'#skF_4'(A_7,k2_relat_1(A_7),C_43)) = C_43
      | ~ r2_hidden(C_43,k2_relat_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_54,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_92,plain,(
    ! [A_73,B_74] :
      ( k10_relat_1(A_73,k1_relat_1(B_74)) = k1_relat_1(k5_relat_1(A_73,B_74))
      | ~ v1_relat_1(B_74)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_48,plain,(
    k2_relat_1('#skF_8') = k1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_65,plain,(
    ! [A_69] :
      ( k10_relat_1(A_69,k2_relat_1(A_69)) = k1_relat_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_74,plain,
    ( k10_relat_1('#skF_8',k1_relat_1('#skF_7')) = k1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_65])).

tff(c_78,plain,(
    k10_relat_1('#skF_8',k1_relat_1('#skF_7')) = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_74])).

tff(c_98,plain,
    ( k1_relat_1(k5_relat_1('#skF_8','#skF_7')) = k1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_78])).

tff(c_107,plain,(
    k1_relat_1(k5_relat_1('#skF_8','#skF_7')) = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_58,c_98])).

tff(c_50,plain,(
    v2_funct_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_52,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_300,plain,(
    ! [B_96,A_97] :
      ( r1_tarski(k2_relat_1(B_96),k1_relat_1(A_97))
      | k1_relat_1(k5_relat_1(B_96,A_97)) != k1_relat_1(B_96)
      | ~ v1_funct_1(B_96)
      | ~ v1_relat_1(B_96)
      | ~ v1_funct_1(A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_312,plain,(
    ! [A_97] :
      ( r1_tarski(k1_relat_1('#skF_7'),k1_relat_1(A_97))
      | k1_relat_1(k5_relat_1('#skF_8',A_97)) != k1_relat_1('#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ v1_funct_1(A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_300])).

tff(c_332,plain,(
    ! [A_100] :
      ( r1_tarski(k1_relat_1('#skF_7'),k1_relat_1(A_100))
      | k1_relat_1(k5_relat_1('#skF_8',A_100)) != k1_relat_1('#skF_8')
      | ~ v1_funct_1(A_100)
      | ~ v1_relat_1(A_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_312])).

tff(c_46,plain,
    ( ~ v2_funct_1('#skF_7')
    | ~ v2_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_63,plain,(
    ~ v2_funct_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_258,plain,(
    ! [B_92,A_93] :
      ( v2_funct_1(B_92)
      | ~ r1_tarski(k2_relat_1(B_92),k1_relat_1(A_93))
      | ~ v2_funct_1(k5_relat_1(B_92,A_93))
      | ~ v1_funct_1(B_92)
      | ~ v1_relat_1(B_92)
      | ~ v1_funct_1(A_93)
      | ~ v1_relat_1(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_267,plain,(
    ! [A_93] :
      ( v2_funct_1('#skF_8')
      | ~ r1_tarski(k1_relat_1('#skF_7'),k1_relat_1(A_93))
      | ~ v2_funct_1(k5_relat_1('#skF_8',A_93))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ v1_funct_1(A_93)
      | ~ v1_relat_1(A_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_258])).

tff(c_271,plain,(
    ! [A_93] :
      ( v2_funct_1('#skF_8')
      | ~ r1_tarski(k1_relat_1('#skF_7'),k1_relat_1(A_93))
      | ~ v2_funct_1(k5_relat_1('#skF_8',A_93))
      | ~ v1_funct_1(A_93)
      | ~ v1_relat_1(A_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_267])).

tff(c_272,plain,(
    ! [A_93] :
      ( ~ r1_tarski(k1_relat_1('#skF_7'),k1_relat_1(A_93))
      | ~ v2_funct_1(k5_relat_1('#skF_8',A_93))
      | ~ v1_funct_1(A_93)
      | ~ v1_relat_1(A_93) ) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_271])).

tff(c_357,plain,(
    ! [A_101] :
      ( ~ v2_funct_1(k5_relat_1('#skF_8',A_101))
      | k1_relat_1(k5_relat_1('#skF_8',A_101)) != k1_relat_1('#skF_8')
      | ~ v1_funct_1(A_101)
      | ~ v1_relat_1(A_101) ) ),
    inference(resolution,[status(thm)],[c_332,c_272])).

tff(c_363,plain,
    ( k1_relat_1(k5_relat_1('#skF_8','#skF_7')) != k1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_50,c_357])).

tff(c_368,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_107,c_363])).

tff(c_369,plain,(
    ~ v2_funct_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_32,plain,(
    ! [A_47] :
      ( r2_hidden('#skF_6'(A_47),k1_relat_1(A_47))
      | v2_funct_1(A_47)
      | ~ v1_funct_1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_453,plain,(
    ! [A_115,C_116] :
      ( r2_hidden('#skF_4'(A_115,k2_relat_1(A_115),C_116),k1_relat_1(A_115))
      | ~ r2_hidden(C_116,k2_relat_1(A_115))
      | ~ v1_funct_1(A_115)
      | ~ v1_relat_1(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_459,plain,(
    ! [C_116] :
      ( r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_116),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_116,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_453])).

tff(c_461,plain,(
    ! [C_116] :
      ( r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_116),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_116,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_459])).

tff(c_34,plain,(
    ! [A_47] :
      ( r2_hidden('#skF_5'(A_47),k1_relat_1(A_47))
      | v2_funct_1(A_47)
      | ~ v1_funct_1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_30,plain,(
    ! [A_47] :
      ( k1_funct_1(A_47,'#skF_5'(A_47)) = k1_funct_1(A_47,'#skF_6'(A_47))
      | v2_funct_1(A_47)
      | ~ v1_funct_1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_470,plain,(
    ! [A_119,C_120] :
      ( k1_funct_1(A_119,'#skF_4'(A_119,k2_relat_1(A_119),C_120)) = C_120
      | ~ r2_hidden(C_120,k2_relat_1(A_119))
      | ~ v1_funct_1(A_119)
      | ~ v1_relat_1(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_486,plain,(
    ! [C_120] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_120)) = C_120
      | ~ r2_hidden(C_120,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_470])).

tff(c_492,plain,(
    ! [C_120] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_120)) = C_120
      | ~ r2_hidden(C_120,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_486])).

tff(c_701,plain,(
    ! [B_147,C_148,A_149] :
      ( k1_funct_1(k5_relat_1(B_147,C_148),A_149) = k1_funct_1(C_148,k1_funct_1(B_147,A_149))
      | ~ r2_hidden(A_149,k1_relat_1(B_147))
      | ~ v1_funct_1(C_148)
      | ~ v1_relat_1(C_148)
      | ~ v1_funct_1(B_147)
      | ~ v1_relat_1(B_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_742,plain,(
    ! [A_7,C_148,C_43] :
      ( k1_funct_1(k5_relat_1(A_7,C_148),'#skF_4'(A_7,k2_relat_1(A_7),C_43)) = k1_funct_1(C_148,k1_funct_1(A_7,'#skF_4'(A_7,k2_relat_1(A_7),C_43)))
      | ~ v1_funct_1(C_148)
      | ~ v1_relat_1(C_148)
      | ~ r2_hidden(C_43,k2_relat_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_701])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k5_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_399,plain,(
    ! [A_108,B_109] :
      ( k10_relat_1(A_108,k1_relat_1(B_109)) = k1_relat_1(k5_relat_1(A_108,B_109))
      | ~ v1_relat_1(B_109)
      | ~ v1_relat_1(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_372,plain,(
    ! [A_104] :
      ( k10_relat_1(A_104,k2_relat_1(A_104)) = k1_relat_1(A_104)
      | ~ v1_relat_1(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_381,plain,
    ( k10_relat_1('#skF_8',k1_relat_1('#skF_7')) = k1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_372])).

tff(c_385,plain,(
    k10_relat_1('#skF_8',k1_relat_1('#skF_7')) = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_381])).

tff(c_405,plain,
    ( k1_relat_1(k5_relat_1('#skF_8','#skF_7')) = k1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_385])).

tff(c_414,plain,(
    k1_relat_1(k5_relat_1('#skF_8','#skF_7')) = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_58,c_405])).

tff(c_6,plain,(
    ! [A_4,B_6] :
      ( k10_relat_1(A_4,k1_relat_1(B_6)) = k1_relat_1(k5_relat_1(A_4,B_6))
      | ~ v1_relat_1(B_6)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_421,plain,(
    ! [A_4] :
      ( k1_relat_1(k5_relat_1(A_4,k5_relat_1('#skF_8','#skF_7'))) = k10_relat_1(A_4,k1_relat_1('#skF_8'))
      | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1(A_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_6])).

tff(c_510,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_421])).

tff(c_513,plain,
    ( ~ v1_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_2,c_510])).

tff(c_517,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_58,c_513])).

tff(c_519,plain,(
    v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_421])).

tff(c_36,plain,(
    ! [A_54,B_55] :
      ( v1_funct_1(k5_relat_1(A_54,B_55))
      | ~ v1_funct_1(B_55)
      | ~ v1_relat_1(B_55)
      | ~ v1_funct_1(A_54)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_565,plain,(
    ! [B_129,A_130] :
      ( r1_tarski(k2_relat_1(B_129),k1_relat_1(A_130))
      | k1_relat_1(k5_relat_1(B_129,A_130)) != k1_relat_1(B_129)
      | ~ v1_funct_1(B_129)
      | ~ v1_relat_1(B_129)
      | ~ v1_funct_1(A_130)
      | ~ v1_relat_1(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_577,plain,(
    ! [A_130] :
      ( r1_tarski(k1_relat_1('#skF_7'),k1_relat_1(A_130))
      | k1_relat_1(k5_relat_1('#skF_8',A_130)) != k1_relat_1('#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ v1_funct_1(A_130)
      | ~ v1_relat_1(A_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_565])).

tff(c_583,plain,(
    ! [A_131] :
      ( r1_tarski(k1_relat_1('#skF_7'),k1_relat_1(A_131))
      | k1_relat_1(k5_relat_1('#skF_8',A_131)) != k1_relat_1('#skF_8')
      | ~ v1_funct_1(A_131)
      | ~ v1_relat_1(A_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_577])).

tff(c_589,plain,
    ( r1_tarski(k1_relat_1('#skF_7'),k1_relat_1('#skF_8'))
    | k1_relat_1(k5_relat_1('#skF_8',k5_relat_1('#skF_8','#skF_7'))) != k1_relat_1('#skF_8')
    | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
    | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_583])).

tff(c_591,plain,
    ( r1_tarski(k1_relat_1('#skF_7'),k1_relat_1('#skF_8'))
    | k1_relat_1(k5_relat_1('#skF_8',k5_relat_1('#skF_8','#skF_7'))) != k1_relat_1('#skF_8')
    | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_589])).

tff(c_599,plain,(
    ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_591])).

tff(c_602,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_599])).

tff(c_606,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_58,c_56,c_602])).

tff(c_608,plain,(
    v1_funct_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_591])).

tff(c_8,plain,(
    ! [A_7,D_46] :
      ( r2_hidden(k1_funct_1(A_7,D_46),k2_relat_1(A_7))
      | ~ r2_hidden(D_46,k1_relat_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_456,plain,(
    ! [C_116] :
      ( r2_hidden('#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_116),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_116,k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_453])).

tff(c_646,plain,(
    ! [C_116] :
      ( r2_hidden('#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_116),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_116,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_608,c_456])).

tff(c_444,plain,(
    ! [A_113,D_114] :
      ( r2_hidden(k1_funct_1(A_113,D_114),k2_relat_1(A_113))
      | ~ r2_hidden(D_114,k1_relat_1(A_113))
      | ~ v1_funct_1(A_113)
      | ~ v1_relat_1(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_450,plain,(
    ! [D_114] :
      ( r2_hidden(k1_funct_1('#skF_8',D_114),k1_relat_1('#skF_7'))
      | ~ r2_hidden(D_114,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_444])).

tff(c_452,plain,(
    ! [D_114] :
      ( r2_hidden(k1_funct_1('#skF_8',D_114),k1_relat_1('#skF_7'))
      | ~ r2_hidden(D_114,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_450])).

tff(c_703,plain,(
    ! [C_148,C_116] :
      ( k1_funct_1(k5_relat_1('#skF_8',C_148),'#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_116)) = k1_funct_1(C_148,k1_funct_1('#skF_8','#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_116)))
      | ~ v1_funct_1(C_148)
      | ~ v1_relat_1(C_148)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(C_116,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(resolution,[status(thm)],[c_646,c_701])).

tff(c_3659,plain,(
    ! [C_323,C_324] :
      ( k1_funct_1(k5_relat_1('#skF_8',C_323),'#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_324)) = k1_funct_1(C_323,k1_funct_1('#skF_8','#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_324)))
      | ~ v1_funct_1(C_323)
      | ~ v1_relat_1(C_323)
      | ~ r2_hidden(C_324,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_703])).

tff(c_3684,plain,(
    ! [C_324] :
      ( k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_324))) = C_324
      | ~ r2_hidden(C_324,k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(C_324,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3659,c_10])).

tff(c_3705,plain,(
    ! [C_325] :
      ( k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_325))) = C_325
      | ~ r2_hidden(C_325,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_519,c_608,c_3684])).

tff(c_3724,plain,(
    ! [C_325] :
      ( r2_hidden(C_325,k2_relat_1('#skF_7'))
      | ~ r2_hidden(k1_funct_1('#skF_8','#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_325)),k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(C_325,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3705,c_8])).

tff(c_3814,plain,(
    ! [C_329] :
      ( r2_hidden(C_329,k2_relat_1('#skF_7'))
      | ~ r2_hidden(k1_funct_1('#skF_8','#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_329)),k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_329,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_3724])).

tff(c_3819,plain,(
    ! [C_330] :
      ( r2_hidden(C_330,k2_relat_1('#skF_7'))
      | ~ r2_hidden(C_330,k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden('#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_330),k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_452,c_3814])).

tff(c_3824,plain,(
    ! [C_331] :
      ( r2_hidden(C_331,k2_relat_1('#skF_7'))
      | ~ r2_hidden(C_331,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(resolution,[status(thm)],[c_646,c_3819])).

tff(c_3915,plain,(
    ! [D_46] :
      ( r2_hidden(k1_funct_1(k5_relat_1('#skF_8','#skF_7'),D_46),k2_relat_1('#skF_7'))
      | ~ r2_hidden(D_46,k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_8,c_3824])).

tff(c_21793,plain,(
    ! [D_674] :
      ( r2_hidden(k1_funct_1(k5_relat_1('#skF_8','#skF_7'),D_674),k2_relat_1('#skF_7'))
      | ~ r2_hidden(D_674,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_608,c_414,c_3915])).

tff(c_21827,plain,(
    ! [C_43] :
      ( r2_hidden(k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_43))),k2_relat_1('#skF_7'))
      | ~ r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_43),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(C_43,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_742,c_21793])).

tff(c_21916,plain,(
    ! [C_676] :
      ( r2_hidden(k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_676))),k2_relat_1('#skF_7'))
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_676),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_676,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_58,c_56,c_48,c_48,c_21827])).

tff(c_21929,plain,(
    ! [C_677] :
      ( r2_hidden(k1_funct_1('#skF_7',C_677),k2_relat_1('#skF_7'))
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_677),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_677,k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_677,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_492,c_21916])).

tff(c_21937,plain,(
    ! [C_678] :
      ( r2_hidden(k1_funct_1('#skF_7',C_678),k2_relat_1('#skF_7'))
      | ~ r2_hidden(C_678,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_461,c_21929])).

tff(c_21965,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_6'('#skF_7')),k2_relat_1('#skF_7'))
    | ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7'))
    | v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_21937])).

tff(c_21976,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_6'('#skF_7')),k2_relat_1('#skF_7'))
    | ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7'))
    | v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_21965])).

tff(c_21977,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_6'('#skF_7')),k2_relat_1('#skF_7'))
    | ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_369,c_21976])).

tff(c_21978,plain,(
    ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_21977])).

tff(c_21981,plain,
    ( v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_34,c_21978])).

tff(c_21984,plain,(
    v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_21981])).

tff(c_21986,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_369,c_21984])).

tff(c_21988,plain,(
    r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_21977])).

tff(c_390,plain,(
    ! [A_105] :
      ( '#skF_5'(A_105) != '#skF_6'(A_105)
      | v2_funct_1(A_105)
      | ~ v1_funct_1(A_105)
      | ~ v1_relat_1(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_393,plain,
    ( '#skF_5'('#skF_7') != '#skF_6'('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_390,c_369])).

tff(c_396,plain,(
    '#skF_5'('#skF_7') != '#skF_6'('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_393])).

tff(c_24,plain,(
    ! [A_7,B_29] :
      ( r2_hidden('#skF_2'(A_7,B_29),k1_relat_1(A_7))
      | r2_hidden('#skF_3'(A_7,B_29),B_29)
      | k2_relat_1(A_7) = B_29
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_370,plain,(
    v2_funct_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_22,plain,(
    ! [A_7,B_29] :
      ( k1_funct_1(A_7,'#skF_2'(A_7,B_29)) = '#skF_1'(A_7,B_29)
      | r2_hidden('#skF_3'(A_7,B_29),B_29)
      | k2_relat_1(A_7) = B_29
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_751,plain,(
    ! [C_150,B_151,A_152] :
      ( C_150 = B_151
      | k1_funct_1(A_152,C_150) != k1_funct_1(A_152,B_151)
      | ~ r2_hidden(C_150,k1_relat_1(A_152))
      | ~ r2_hidden(B_151,k1_relat_1(A_152))
      | ~ v2_funct_1(A_152)
      | ~ v1_funct_1(A_152)
      | ~ v1_relat_1(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3743,plain,(
    ! [B_326,A_327,B_328] :
      ( B_326 = '#skF_2'(A_327,B_328)
      | k1_funct_1(A_327,B_326) != '#skF_1'(A_327,B_328)
      | ~ r2_hidden('#skF_2'(A_327,B_328),k1_relat_1(A_327))
      | ~ r2_hidden(B_326,k1_relat_1(A_327))
      | ~ v2_funct_1(A_327)
      | ~ v1_funct_1(A_327)
      | ~ v1_relat_1(A_327)
      | r2_hidden('#skF_3'(A_327,B_328),B_328)
      | k2_relat_1(A_327) = B_328
      | ~ v1_funct_1(A_327)
      | ~ v1_relat_1(A_327) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_751])).

tff(c_3803,plain,(
    ! [C_120,B_328] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_120) = '#skF_2'('#skF_8',B_328)
      | C_120 != '#skF_1'('#skF_8',B_328)
      | ~ r2_hidden('#skF_2'('#skF_8',B_328),k1_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_120),k1_relat_1('#skF_8'))
      | ~ v2_funct_1('#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | r2_hidden('#skF_3'('#skF_8',B_328),B_328)
      | k2_relat_1('#skF_8') = B_328
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(C_120,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_492,c_3743])).

tff(c_24044,plain,(
    ! [C_722,B_723] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_722) = '#skF_2'('#skF_8',B_723)
      | C_722 != '#skF_1'('#skF_8',B_723)
      | ~ r2_hidden('#skF_2'('#skF_8',B_723),k1_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_722),k1_relat_1('#skF_8'))
      | r2_hidden('#skF_3'('#skF_8',B_723),B_723)
      | k1_relat_1('#skF_7') = B_723
      | ~ r2_hidden(C_722,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_54,c_52,c_370,c_3803])).

tff(c_24059,plain,(
    ! [C_722,B_29] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_722) = '#skF_2'('#skF_8',B_29)
      | C_722 != '#skF_1'('#skF_8',B_29)
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_722),k1_relat_1('#skF_8'))
      | k1_relat_1('#skF_7') = B_29
      | ~ r2_hidden(C_722,k1_relat_1('#skF_7'))
      | r2_hidden('#skF_3'('#skF_8',B_29),B_29)
      | k2_relat_1('#skF_8') = B_29
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_24,c_24044])).

tff(c_24965,plain,(
    ! [C_756,B_757] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_756) = '#skF_2'('#skF_8',B_757)
      | C_756 != '#skF_1'('#skF_8',B_757)
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_756),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_756,k1_relat_1('#skF_7'))
      | r2_hidden('#skF_3'('#skF_8',B_757),B_757)
      | k1_relat_1('#skF_7') = B_757 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_24059])).

tff(c_24972,plain,(
    ! [C_758,B_759] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_758) = '#skF_2'('#skF_8',B_759)
      | C_758 != '#skF_1'('#skF_8',B_759)
      | r2_hidden('#skF_3'('#skF_8',B_759),B_759)
      | k1_relat_1('#skF_7') = B_759
      | ~ r2_hidden(C_758,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_461,c_24965])).

tff(c_25063,plain,(
    ! [B_759] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) = '#skF_2'('#skF_8',B_759)
      | '#skF_5'('#skF_7') != '#skF_1'('#skF_8',B_759)
      | r2_hidden('#skF_3'('#skF_8',B_759),B_759)
      | k1_relat_1('#skF_7') = B_759
      | v2_funct_1('#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_34,c_24972])).

tff(c_25130,plain,(
    ! [B_759] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) = '#skF_2'('#skF_8',B_759)
      | '#skF_5'('#skF_7') != '#skF_1'('#skF_8',B_759)
      | r2_hidden('#skF_3'('#skF_8',B_759),B_759)
      | k1_relat_1('#skF_7') = B_759
      | v2_funct_1('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_25063])).

tff(c_25273,plain,(
    ! [B_761] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) = '#skF_2'('#skF_8',B_761)
      | '#skF_5'('#skF_7') != '#skF_1'('#skF_8',B_761)
      | r2_hidden('#skF_3'('#skF_8',B_761),B_761)
      | k1_relat_1('#skF_7') = B_761 ) ),
    inference(negUnitSimplification,[status(thm)],[c_369,c_25130])).

tff(c_25337,plain,(
    ! [B_761] :
      ( r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_relat_1('#skF_8'))
      | r2_hidden('#skF_3'('#skF_8',B_761),B_761)
      | k2_relat_1('#skF_8') = B_761
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | '#skF_5'('#skF_7') != '#skF_1'('#skF_8',B_761)
      | r2_hidden('#skF_3'('#skF_8',B_761),B_761)
      | k1_relat_1('#skF_7') = B_761 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25273,c_24])).

tff(c_25411,plain,(
    ! [B_761] :
      ( r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_relat_1('#skF_8'))
      | '#skF_5'('#skF_7') != '#skF_1'('#skF_8',B_761)
      | r2_hidden('#skF_3'('#skF_8',B_761),B_761)
      | k1_relat_1('#skF_7') = B_761 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_25337])).

tff(c_26046,plain,(
    r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_25411])).

tff(c_22036,plain,(
    ! [A_684] :
      ( r2_hidden('#skF_3'(A_684,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7'))
      | r2_hidden('#skF_2'(A_684,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k1_relat_1(A_684))
      | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1(A_684)
      | ~ v1_funct_1(A_684)
      | ~ v1_relat_1(A_684) ) ),
    inference(resolution,[status(thm)],[c_24,c_3824])).

tff(c_915,plain,(
    ! [A_162,B_163,D_164] :
      ( r2_hidden('#skF_2'(A_162,B_163),k1_relat_1(A_162))
      | k1_funct_1(A_162,D_164) != '#skF_3'(A_162,B_163)
      | ~ r2_hidden(D_164,k1_relat_1(A_162))
      | k2_relat_1(A_162) = B_163
      | ~ v1_funct_1(A_162)
      | ~ v1_relat_1(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_929,plain,(
    ! [A_7,B_163,C_43] :
      ( r2_hidden('#skF_2'(A_7,B_163),k1_relat_1(A_7))
      | C_43 != '#skF_3'(A_7,B_163)
      | ~ r2_hidden('#skF_4'(A_7,k2_relat_1(A_7),C_43),k1_relat_1(A_7))
      | k2_relat_1(A_7) = B_163
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7)
      | ~ r2_hidden(C_43,k2_relat_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_915])).

tff(c_2680,plain,(
    ! [A_267,B_268] :
      ( r2_hidden('#skF_2'(A_267,B_268),k1_relat_1(A_267))
      | ~ r2_hidden('#skF_4'(A_267,k2_relat_1(A_267),'#skF_3'(A_267,B_268)),k1_relat_1(A_267))
      | k2_relat_1(A_267) = B_268
      | ~ v1_funct_1(A_267)
      | ~ v1_relat_1(A_267)
      | ~ r2_hidden('#skF_3'(A_267,B_268),k2_relat_1(A_267))
      | ~ v1_funct_1(A_267)
      | ~ v1_relat_1(A_267) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_929])).

tff(c_2697,plain,(
    ! [A_7,B_268] :
      ( r2_hidden('#skF_2'(A_7,B_268),k1_relat_1(A_7))
      | k2_relat_1(A_7) = B_268
      | ~ r2_hidden('#skF_3'(A_7,B_268),k2_relat_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_2680])).

tff(c_22044,plain,
    ( r2_hidden('#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k1_relat_1('#skF_7'))
    | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_22036,c_2697])).

tff(c_22063,plain,
    ( r2_hidden('#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k1_relat_1('#skF_7'))
    | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_22044])).

tff(c_22068,plain,(
    k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_22063])).

tff(c_3959,plain,(
    ! [D_46] :
      ( r2_hidden(k1_funct_1(k5_relat_1('#skF_8','#skF_7'),D_46),k2_relat_1('#skF_7'))
      | ~ r2_hidden(D_46,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_608,c_414,c_3915])).

tff(c_763,plain,(
    ! [C_150,A_7,C_43] :
      ( C_150 = '#skF_4'(A_7,k2_relat_1(A_7),C_43)
      | k1_funct_1(A_7,C_150) != C_43
      | ~ r2_hidden(C_150,k1_relat_1(A_7))
      | ~ r2_hidden('#skF_4'(A_7,k2_relat_1(A_7),C_43),k1_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7)
      | ~ r2_hidden(C_43,k2_relat_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_751])).

tff(c_23033,plain,(
    ! [A_709,C_710] :
      ( '#skF_4'(A_709,k2_relat_1(A_709),k1_funct_1(A_709,C_710)) = C_710
      | ~ r2_hidden(C_710,k1_relat_1(A_709))
      | ~ r2_hidden('#skF_4'(A_709,k2_relat_1(A_709),k1_funct_1(A_709,C_710)),k1_relat_1(A_709))
      | ~ v2_funct_1(A_709)
      | ~ v1_funct_1(A_709)
      | ~ v1_relat_1(A_709)
      | ~ r2_hidden(k1_funct_1(A_709,C_710),k2_relat_1(A_709))
      | ~ v1_funct_1(A_709)
      | ~ v1_relat_1(A_709) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_763])).

tff(c_23170,plain,(
    ! [A_711,C_712] :
      ( '#skF_4'(A_711,k2_relat_1(A_711),k1_funct_1(A_711,C_712)) = C_712
      | ~ r2_hidden(C_712,k1_relat_1(A_711))
      | ~ v2_funct_1(A_711)
      | ~ r2_hidden(k1_funct_1(A_711,C_712),k2_relat_1(A_711))
      | ~ v1_funct_1(A_711)
      | ~ v1_relat_1(A_711) ) ),
    inference(resolution,[status(thm)],[c_12,c_23033])).

tff(c_23281,plain,(
    ! [A_713,D_714] :
      ( '#skF_4'(A_713,k2_relat_1(A_713),k1_funct_1(A_713,D_714)) = D_714
      | ~ v2_funct_1(A_713)
      | ~ r2_hidden(D_714,k1_relat_1(A_713))
      | ~ v1_funct_1(A_713)
      | ~ v1_relat_1(A_713) ) ),
    inference(resolution,[status(thm)],[c_8,c_23170])).

tff(c_23321,plain,(
    ! [D_714] :
      ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1('#skF_7'),k1_funct_1(k5_relat_1('#skF_8','#skF_7'),D_714)) = D_714
      | ~ v2_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ r2_hidden(D_714,k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22068,c_23281])).

tff(c_23427,plain,(
    ! [D_715] :
      ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1('#skF_7'),k1_funct_1(k5_relat_1('#skF_8','#skF_7'),D_715)) = D_715
      | ~ r2_hidden(D_715,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_608,c_414,c_50,c_23321])).

tff(c_3701,plain,(
    ! [C_324] :
      ( k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_324))) = C_324
      | ~ r2_hidden(C_324,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_519,c_608,c_3684])).

tff(c_22073,plain,(
    ! [C_324] :
      ( k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1('#skF_7'),C_324))) = C_324
      | ~ r2_hidden(C_324,k2_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22068,c_22068,c_3701])).

tff(c_23600,plain,(
    ! [D_718] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),D_718) = k1_funct_1('#skF_7',k1_funct_1('#skF_8',D_718))
      | ~ r2_hidden(k1_funct_1(k5_relat_1('#skF_8','#skF_7'),D_718),k2_relat_1('#skF_7'))
      | ~ r2_hidden(D_718,k1_relat_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23427,c_22073])).

tff(c_23679,plain,(
    ! [D_46] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),D_46) = k1_funct_1('#skF_7',k1_funct_1('#skF_8',D_46))
      | ~ r2_hidden(D_46,k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_3959,c_23600])).

tff(c_26055,plain,(
    k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))) = k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')))) ),
    inference(resolution,[status(thm)],[c_26046,c_23679])).

tff(c_23278,plain,(
    ! [A_7,D_46] :
      ( '#skF_4'(A_7,k2_relat_1(A_7),k1_funct_1(A_7,D_46)) = D_46
      | ~ v2_funct_1(A_7)
      | ~ r2_hidden(D_46,k1_relat_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_8,c_23170])).

tff(c_26073,plain,
    ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))
    | ~ v2_funct_1(k5_relat_1('#skF_8','#skF_7'))
    | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
    | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_26055,c_23278])).

tff(c_26114,plain,(
    '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1('#skF_7'),k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_608,c_26046,c_414,c_50,c_22068,c_26073])).

tff(c_26190,plain,
    ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1('#skF_7'),k1_funct_1('#skF_7','#skF_5'('#skF_7'))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))
    | ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_492,c_26114])).

tff(c_26207,plain,(
    '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1('#skF_7'),k1_funct_1('#skF_7','#skF_5'('#skF_7'))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21988,c_26190])).

tff(c_26230,plain,
    ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1('#skF_7'),k1_funct_1('#skF_7','#skF_6'('#skF_7'))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))
    | v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_26207])).

tff(c_26246,plain,
    ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1('#skF_7'),k1_funct_1('#skF_7','#skF_6'('#skF_7'))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))
    | v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_26230])).

tff(c_26247,plain,(
    '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1('#skF_7'),k1_funct_1('#skF_7','#skF_6'('#skF_7'))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_369,c_26246])).

tff(c_25060,plain,(
    ! [B_759] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')) = '#skF_2'('#skF_8',B_759)
      | '#skF_1'('#skF_8',B_759) != '#skF_6'('#skF_7')
      | r2_hidden('#skF_3'('#skF_8',B_759),B_759)
      | k1_relat_1('#skF_7') = B_759
      | v2_funct_1('#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_32,c_24972])).

tff(c_25126,plain,(
    ! [B_759] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')) = '#skF_2'('#skF_8',B_759)
      | '#skF_1'('#skF_8',B_759) != '#skF_6'('#skF_7')
      | r2_hidden('#skF_3'('#skF_8',B_759),B_759)
      | k1_relat_1('#skF_7') = B_759
      | v2_funct_1('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_25060])).

tff(c_25133,plain,(
    ! [B_760] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')) = '#skF_2'('#skF_8',B_760)
      | '#skF_1'('#skF_8',B_760) != '#skF_6'('#skF_7')
      | r2_hidden('#skF_3'('#skF_8',B_760),B_760)
      | k1_relat_1('#skF_7') = B_760 ) ),
    inference(negUnitSimplification,[status(thm)],[c_369,c_25126])).

tff(c_25194,plain,(
    ! [B_760] :
      ( r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')),k1_relat_1('#skF_8'))
      | r2_hidden('#skF_3'('#skF_8',B_760),B_760)
      | k2_relat_1('#skF_8') = B_760
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | '#skF_1'('#skF_8',B_760) != '#skF_6'('#skF_7')
      | r2_hidden('#skF_3'('#skF_8',B_760),B_760)
      | k1_relat_1('#skF_7') = B_760 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25133,c_24])).

tff(c_25249,plain,(
    ! [B_760] :
      ( r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')),k1_relat_1('#skF_8'))
      | '#skF_1'('#skF_8',B_760) != '#skF_6'('#skF_7')
      | r2_hidden('#skF_3'('#skF_8',B_760),B_760)
      | k1_relat_1('#skF_7') = B_760 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_25194])).

tff(c_25564,plain,(
    r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')),k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_25249])).

tff(c_25573,plain,(
    k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))) = k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')))) ),
    inference(resolution,[status(thm)],[c_25564,c_23679])).

tff(c_25811,plain,
    ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))
    | ~ v2_funct_1(k5_relat_1('#skF_8','#skF_7'))
    | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')),k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
    | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_25573,c_23278])).

tff(c_25850,plain,(
    '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1('#skF_7'),k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_608,c_25564,c_414,c_50,c_22068,c_25811])).

tff(c_27299,plain,
    ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1('#skF_7'),k1_funct_1('#skF_7','#skF_6'('#skF_7'))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))
    | ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_492,c_25850])).

tff(c_27315,plain,
    ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))
    | ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26247,c_27299])).

tff(c_27318,plain,(
    ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_27315])).

tff(c_27321,plain,
    ( v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_27318])).

tff(c_27324,plain,(
    v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_27321])).

tff(c_27326,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_369,c_27324])).

tff(c_27328,plain,(
    r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_27315])).

tff(c_27327,plain,(
    '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_27315])).

tff(c_27373,plain,
    ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))) = '#skF_5'('#skF_7')
    | ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_27327,c_492])).

tff(c_27396,plain,(
    k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))) = '#skF_5'('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21988,c_27373])).

tff(c_27456,plain,
    ( '#skF_5'('#skF_7') = '#skF_6'('#skF_7')
    | ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_27396,c_492])).

tff(c_27506,plain,(
    '#skF_5'('#skF_7') = '#skF_6'('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27328,c_27456])).

tff(c_27508,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_396,c_27506])).

tff(c_27510,plain,(
    ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_25411])).

tff(c_27514,plain,(
    ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_461,c_27510])).

tff(c_27518,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21988,c_27514])).

tff(c_27520,plain,(
    ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')),k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_25249])).

tff(c_27525,plain,(
    ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_461,c_27520])).

tff(c_27528,plain,
    ( v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_27525])).

tff(c_27531,plain,(
    v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_27528])).

tff(c_27533,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_369,c_27531])).

tff(c_27535,plain,(
    k2_relat_1(k5_relat_1('#skF_8','#skF_7')) != k2_relat_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_22063])).

tff(c_27534,plain,(
    r2_hidden('#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_22063])).

tff(c_28345,plain,(
    ! [A_806] :
      ( r2_hidden('#skF_3'(A_806,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7'))
      | k1_funct_1(A_806,'#skF_2'(A_806,k2_relat_1(k5_relat_1('#skF_8','#skF_7')))) = '#skF_1'(A_806,k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1(A_806)
      | ~ v1_funct_1(A_806)
      | ~ v1_relat_1(A_806) ) ),
    inference(resolution,[status(thm)],[c_22,c_3824])).

tff(c_934,plain,(
    ! [A_165,B_166,D_167] :
      ( k1_funct_1(A_165,'#skF_2'(A_165,B_166)) = '#skF_1'(A_165,B_166)
      | k1_funct_1(A_165,D_167) != '#skF_3'(A_165,B_166)
      | ~ r2_hidden(D_167,k1_relat_1(A_165))
      | k2_relat_1(A_165) = B_166
      | ~ v1_funct_1(A_165)
      | ~ v1_relat_1(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_948,plain,(
    ! [A_7,B_166,C_43] :
      ( k1_funct_1(A_7,'#skF_2'(A_7,B_166)) = '#skF_1'(A_7,B_166)
      | C_43 != '#skF_3'(A_7,B_166)
      | ~ r2_hidden('#skF_4'(A_7,k2_relat_1(A_7),C_43),k1_relat_1(A_7))
      | k2_relat_1(A_7) = B_166
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7)
      | ~ r2_hidden(C_43,k2_relat_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_934])).

tff(c_3127,plain,(
    ! [A_286,B_287] :
      ( k1_funct_1(A_286,'#skF_2'(A_286,B_287)) = '#skF_1'(A_286,B_287)
      | ~ r2_hidden('#skF_4'(A_286,k2_relat_1(A_286),'#skF_3'(A_286,B_287)),k1_relat_1(A_286))
      | k2_relat_1(A_286) = B_287
      | ~ v1_funct_1(A_286)
      | ~ v1_relat_1(A_286)
      | ~ r2_hidden('#skF_3'(A_286,B_287),k2_relat_1(A_286))
      | ~ v1_funct_1(A_286)
      | ~ v1_relat_1(A_286) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_948])).

tff(c_3144,plain,(
    ! [A_7,B_287] :
      ( k1_funct_1(A_7,'#skF_2'(A_7,B_287)) = '#skF_1'(A_7,B_287)
      | k2_relat_1(A_7) = B_287
      | ~ r2_hidden('#skF_3'(A_7,B_287),k2_relat_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_3127])).

tff(c_28349,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))) = '#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_28345,c_3144])).

tff(c_28440,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))) = '#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_28349])).

tff(c_28441,plain,(
    k1_funct_1('#skF_7','#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))) = '#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_27535,c_28440])).

tff(c_29159,plain,(
    ! [A_819,C_820] :
      ( '#skF_4'(A_819,k2_relat_1(A_819),k1_funct_1(A_819,C_820)) = C_820
      | ~ r2_hidden(C_820,k1_relat_1(A_819))
      | ~ r2_hidden('#skF_4'(A_819,k2_relat_1(A_819),k1_funct_1(A_819,C_820)),k1_relat_1(A_819))
      | ~ v2_funct_1(A_819)
      | ~ v1_funct_1(A_819)
      | ~ v1_relat_1(A_819)
      | ~ r2_hidden(k1_funct_1(A_819,C_820),k2_relat_1(A_819))
      | ~ v1_funct_1(A_819)
      | ~ v1_relat_1(A_819) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_763])).

tff(c_29306,plain,(
    ! [A_821,C_822] :
      ( '#skF_4'(A_821,k2_relat_1(A_821),k1_funct_1(A_821,C_822)) = C_822
      | ~ r2_hidden(C_822,k1_relat_1(A_821))
      | ~ v2_funct_1(A_821)
      | ~ r2_hidden(k1_funct_1(A_821,C_822),k2_relat_1(A_821))
      | ~ v1_funct_1(A_821)
      | ~ v1_relat_1(A_821) ) ),
    inference(resolution,[status(thm)],[c_12,c_29159])).

tff(c_29428,plain,(
    ! [A_823,D_824] :
      ( '#skF_4'(A_823,k2_relat_1(A_823),k1_funct_1(A_823,D_824)) = D_824
      | ~ v2_funct_1(A_823)
      | ~ r2_hidden(D_824,k1_relat_1(A_823))
      | ~ v1_funct_1(A_823)
      | ~ v1_relat_1(A_823) ) ),
    inference(resolution,[status(thm)],[c_8,c_29306])).

tff(c_29435,plain,(
    ! [D_824] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),D_824) = k1_funct_1('#skF_7',k1_funct_1('#skF_8',D_824))
      | ~ r2_hidden(k1_funct_1(k5_relat_1('#skF_8','#skF_7'),D_824),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ v2_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ r2_hidden(D_824,k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29428,c_3701])).

tff(c_29602,plain,(
    ! [D_825] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),D_825) = k1_funct_1('#skF_7',k1_funct_1('#skF_8',D_825))
      | ~ r2_hidden(k1_funct_1(k5_relat_1('#skF_8','#skF_7'),D_825),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden(D_825,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_608,c_414,c_50,c_29435])).

tff(c_29684,plain,(
    ! [D_46] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),D_46) = k1_funct_1('#skF_7',k1_funct_1('#skF_8',D_46))
      | ~ r2_hidden(D_46,k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_46,k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_8,c_29602])).

tff(c_29751,plain,(
    ! [D_827] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),D_827) = k1_funct_1('#skF_7',k1_funct_1('#skF_8',D_827))
      | ~ r2_hidden(D_827,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_608,c_414,c_29684])).

tff(c_30039,plain,(
    ! [C_829] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_829)) = k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_829)))
      | ~ r2_hidden(C_829,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_461,c_29751])).

tff(c_30066,plain,(
    ! [C_829] :
      ( r2_hidden(k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_829))),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_829),k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ r2_hidden(C_829,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30039,c_8])).

tff(c_30170,plain,(
    ! [C_833] :
      ( r2_hidden(k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_833))),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_833),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_833,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_608,c_414,c_30066])).

tff(c_30187,plain,(
    ! [C_834] :
      ( r2_hidden(k1_funct_1('#skF_7',C_834),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_834),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_834,k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_834,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_492,c_30170])).

tff(c_30195,plain,(
    ! [C_835] :
      ( r2_hidden(k1_funct_1('#skF_7',C_835),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden(C_835,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_461,c_30187])).

tff(c_30201,plain,
    ( r2_hidden('#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | ~ r2_hidden('#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_28441,c_30195])).

tff(c_30236,plain,(
    r2_hidden('#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27534,c_30201])).

tff(c_14,plain,(
    ! [A_7,B_29,D_42] :
      ( ~ r2_hidden('#skF_1'(A_7,B_29),B_29)
      | k1_funct_1(A_7,D_42) != '#skF_3'(A_7,B_29)
      | ~ r2_hidden(D_42,k1_relat_1(A_7))
      | k2_relat_1(A_7) = B_29
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30261,plain,(
    ! [D_42] :
      ( k1_funct_1('#skF_7',D_42) != '#skF_3'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden(D_42,k1_relat_1('#skF_7'))
      | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_30236,c_14])).

tff(c_30270,plain,(
    ! [D_42] :
      ( k1_funct_1('#skF_7',D_42) != '#skF_3'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden(D_42,k1_relat_1('#skF_7'))
      | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_30261])).

tff(c_30286,plain,(
    ! [D_836] :
      ( k1_funct_1('#skF_7',D_836) != '#skF_3'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden(D_836,k1_relat_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_27535,c_30270])).

tff(c_30307,plain,(
    ! [C_43] :
      ( C_43 != '#skF_3'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_43),k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_43,k2_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_30286])).

tff(c_30484,plain,(
    ! [C_843] :
      ( C_843 != '#skF_3'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_843),k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_843,k2_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_30307])).

tff(c_30492,plain,(
    ! [C_43] :
      ( C_43 != '#skF_3'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden(C_43,k2_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_12,c_30484])).

tff(c_30518,plain,(
    ~ r2_hidden('#skF_3'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_30492])).

tff(c_20,plain,(
    ! [A_7,B_29] :
      ( ~ r2_hidden('#skF_1'(A_7,B_29),B_29)
      | r2_hidden('#skF_3'(A_7,B_29),B_29)
      | k2_relat_1(A_7) = B_29
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3956,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7'))
      | ~ r2_hidden('#skF_1'(A_7,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_20,c_3824])).

tff(c_30256,plain,
    ( r2_hidden('#skF_3'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7'))
    | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_30236,c_3956])).

tff(c_30264,plain,
    ( r2_hidden('#skF_3'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7'))
    | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_30256])).

tff(c_30265,plain,(
    r2_hidden('#skF_3'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_27535,c_30264])).

tff(c_30520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30518,c_30265])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:37:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.28/9.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.28/9.67  
% 19.28/9.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.28/9.67  %$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_5 > #skF_4 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_1 > #skF_6
% 19.28/9.67  
% 19.28/9.67  %Foreground sorts:
% 19.28/9.67  
% 19.28/9.67  
% 19.28/9.67  %Background operators:
% 19.28/9.67  
% 19.28/9.67  
% 19.28/9.67  %Foreground operators:
% 19.28/9.67  tff('#skF_5', type, '#skF_5': $i > $i).
% 19.28/9.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 19.28/9.67  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 19.28/9.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.28/9.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 19.28/9.67  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 19.28/9.67  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 19.28/9.67  tff('#skF_7', type, '#skF_7': $i).
% 19.28/9.67  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 19.28/9.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.28/9.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 19.28/9.67  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 19.28/9.67  tff('#skF_8', type, '#skF_8': $i).
% 19.28/9.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.28/9.67  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 19.28/9.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 19.28/9.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.28/9.67  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 19.28/9.67  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 19.28/9.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 19.28/9.67  tff('#skF_6', type, '#skF_6': $i > $i).
% 19.28/9.67  
% 19.50/9.71  tff(f_143, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 19.50/9.71  tff(f_57, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 19.50/9.71  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 19.50/9.71  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 19.50/9.71  tff(f_110, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_funct_1)).
% 19.50/9.71  tff(f_125, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & r1_tarski(k2_relat_1(B), k1_relat_1(A))) => v2_funct_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_funct_1)).
% 19.50/9.71  tff(f_72, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 19.50/9.71  tff(f_97, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 19.50/9.71  tff(f_31, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 19.50/9.71  tff(f_84, axiom, (![A, B]: ((((v1_relat_1(A) & v1_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v1_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funct_1)).
% 19.50/9.71  tff(c_58, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_143])).
% 19.50/9.71  tff(c_56, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_143])).
% 19.50/9.71  tff(c_12, plain, (![A_7, C_43]: (r2_hidden('#skF_4'(A_7, k2_relat_1(A_7), C_43), k1_relat_1(A_7)) | ~r2_hidden(C_43, k2_relat_1(A_7)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_57])).
% 19.50/9.71  tff(c_10, plain, (![A_7, C_43]: (k1_funct_1(A_7, '#skF_4'(A_7, k2_relat_1(A_7), C_43))=C_43 | ~r2_hidden(C_43, k2_relat_1(A_7)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_57])).
% 19.50/9.71  tff(c_54, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_143])).
% 19.50/9.71  tff(c_92, plain, (![A_73, B_74]: (k10_relat_1(A_73, k1_relat_1(B_74))=k1_relat_1(k5_relat_1(A_73, B_74)) | ~v1_relat_1(B_74) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_42])).
% 19.50/9.71  tff(c_48, plain, (k2_relat_1('#skF_8')=k1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_143])).
% 19.50/9.71  tff(c_65, plain, (![A_69]: (k10_relat_1(A_69, k2_relat_1(A_69))=k1_relat_1(A_69) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_35])).
% 19.50/9.71  tff(c_74, plain, (k10_relat_1('#skF_8', k1_relat_1('#skF_7'))=k1_relat_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_48, c_65])).
% 19.50/9.71  tff(c_78, plain, (k10_relat_1('#skF_8', k1_relat_1('#skF_7'))=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_74])).
% 19.50/9.71  tff(c_98, plain, (k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k1_relat_1('#skF_8') | ~v1_relat_1('#skF_7') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_92, c_78])).
% 19.50/9.71  tff(c_107, plain, (k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_58, c_98])).
% 19.50/9.71  tff(c_50, plain, (v2_funct_1(k5_relat_1('#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 19.50/9.71  tff(c_52, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_143])).
% 19.50/9.71  tff(c_300, plain, (![B_96, A_97]: (r1_tarski(k2_relat_1(B_96), k1_relat_1(A_97)) | k1_relat_1(k5_relat_1(B_96, A_97))!=k1_relat_1(B_96) | ~v1_funct_1(B_96) | ~v1_relat_1(B_96) | ~v1_funct_1(A_97) | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_110])).
% 19.50/9.71  tff(c_312, plain, (![A_97]: (r1_tarski(k1_relat_1('#skF_7'), k1_relat_1(A_97)) | k1_relat_1(k5_relat_1('#skF_8', A_97))!=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~v1_funct_1(A_97) | ~v1_relat_1(A_97))), inference(superposition, [status(thm), theory('equality')], [c_48, c_300])).
% 19.50/9.71  tff(c_332, plain, (![A_100]: (r1_tarski(k1_relat_1('#skF_7'), k1_relat_1(A_100)) | k1_relat_1(k5_relat_1('#skF_8', A_100))!=k1_relat_1('#skF_8') | ~v1_funct_1(A_100) | ~v1_relat_1(A_100))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_312])).
% 19.50/9.71  tff(c_46, plain, (~v2_funct_1('#skF_7') | ~v2_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_143])).
% 19.50/9.71  tff(c_63, plain, (~v2_funct_1('#skF_8')), inference(splitLeft, [status(thm)], [c_46])).
% 19.50/9.71  tff(c_258, plain, (![B_92, A_93]: (v2_funct_1(B_92) | ~r1_tarski(k2_relat_1(B_92), k1_relat_1(A_93)) | ~v2_funct_1(k5_relat_1(B_92, A_93)) | ~v1_funct_1(B_92) | ~v1_relat_1(B_92) | ~v1_funct_1(A_93) | ~v1_relat_1(A_93))), inference(cnfTransformation, [status(thm)], [f_125])).
% 19.50/9.71  tff(c_267, plain, (![A_93]: (v2_funct_1('#skF_8') | ~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1(A_93)) | ~v2_funct_1(k5_relat_1('#skF_8', A_93)) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~v1_funct_1(A_93) | ~v1_relat_1(A_93))), inference(superposition, [status(thm), theory('equality')], [c_48, c_258])).
% 19.50/9.71  tff(c_271, plain, (![A_93]: (v2_funct_1('#skF_8') | ~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1(A_93)) | ~v2_funct_1(k5_relat_1('#skF_8', A_93)) | ~v1_funct_1(A_93) | ~v1_relat_1(A_93))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_267])).
% 19.50/9.71  tff(c_272, plain, (![A_93]: (~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1(A_93)) | ~v2_funct_1(k5_relat_1('#skF_8', A_93)) | ~v1_funct_1(A_93) | ~v1_relat_1(A_93))), inference(negUnitSimplification, [status(thm)], [c_63, c_271])).
% 19.50/9.71  tff(c_357, plain, (![A_101]: (~v2_funct_1(k5_relat_1('#skF_8', A_101)) | k1_relat_1(k5_relat_1('#skF_8', A_101))!=k1_relat_1('#skF_8') | ~v1_funct_1(A_101) | ~v1_relat_1(A_101))), inference(resolution, [status(thm)], [c_332, c_272])).
% 19.50/9.71  tff(c_363, plain, (k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))!=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_50, c_357])).
% 19.50/9.71  tff(c_368, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_107, c_363])).
% 19.50/9.71  tff(c_369, plain, (~v2_funct_1('#skF_7')), inference(splitRight, [status(thm)], [c_46])).
% 19.50/9.71  tff(c_32, plain, (![A_47]: (r2_hidden('#skF_6'(A_47), k1_relat_1(A_47)) | v2_funct_1(A_47) | ~v1_funct_1(A_47) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_72])).
% 19.50/9.71  tff(c_453, plain, (![A_115, C_116]: (r2_hidden('#skF_4'(A_115, k2_relat_1(A_115), C_116), k1_relat_1(A_115)) | ~r2_hidden(C_116, k2_relat_1(A_115)) | ~v1_funct_1(A_115) | ~v1_relat_1(A_115))), inference(cnfTransformation, [status(thm)], [f_57])).
% 19.50/9.71  tff(c_459, plain, (![C_116]: (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_116), k1_relat_1('#skF_8')) | ~r2_hidden(C_116, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_453])).
% 19.50/9.71  tff(c_461, plain, (![C_116]: (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_116), k1_relat_1('#skF_8')) | ~r2_hidden(C_116, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_48, c_459])).
% 19.50/9.71  tff(c_34, plain, (![A_47]: (r2_hidden('#skF_5'(A_47), k1_relat_1(A_47)) | v2_funct_1(A_47) | ~v1_funct_1(A_47) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_72])).
% 19.50/9.71  tff(c_30, plain, (![A_47]: (k1_funct_1(A_47, '#skF_5'(A_47))=k1_funct_1(A_47, '#skF_6'(A_47)) | v2_funct_1(A_47) | ~v1_funct_1(A_47) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_72])).
% 19.50/9.71  tff(c_470, plain, (![A_119, C_120]: (k1_funct_1(A_119, '#skF_4'(A_119, k2_relat_1(A_119), C_120))=C_120 | ~r2_hidden(C_120, k2_relat_1(A_119)) | ~v1_funct_1(A_119) | ~v1_relat_1(A_119))), inference(cnfTransformation, [status(thm)], [f_57])).
% 19.50/9.71  tff(c_486, plain, (![C_120]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_120))=C_120 | ~r2_hidden(C_120, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_470])).
% 19.50/9.71  tff(c_492, plain, (![C_120]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_120))=C_120 | ~r2_hidden(C_120, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_48, c_486])).
% 19.50/9.71  tff(c_701, plain, (![B_147, C_148, A_149]: (k1_funct_1(k5_relat_1(B_147, C_148), A_149)=k1_funct_1(C_148, k1_funct_1(B_147, A_149)) | ~r2_hidden(A_149, k1_relat_1(B_147)) | ~v1_funct_1(C_148) | ~v1_relat_1(C_148) | ~v1_funct_1(B_147) | ~v1_relat_1(B_147))), inference(cnfTransformation, [status(thm)], [f_97])).
% 19.50/9.71  tff(c_742, plain, (![A_7, C_148, C_43]: (k1_funct_1(k5_relat_1(A_7, C_148), '#skF_4'(A_7, k2_relat_1(A_7), C_43))=k1_funct_1(C_148, k1_funct_1(A_7, '#skF_4'(A_7, k2_relat_1(A_7), C_43))) | ~v1_funct_1(C_148) | ~v1_relat_1(C_148) | ~r2_hidden(C_43, k2_relat_1(A_7)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_12, c_701])).
% 19.50/9.71  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k5_relat_1(A_1, B_2)) | ~v1_relat_1(B_2) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 19.50/9.71  tff(c_399, plain, (![A_108, B_109]: (k10_relat_1(A_108, k1_relat_1(B_109))=k1_relat_1(k5_relat_1(A_108, B_109)) | ~v1_relat_1(B_109) | ~v1_relat_1(A_108))), inference(cnfTransformation, [status(thm)], [f_42])).
% 19.50/9.71  tff(c_372, plain, (![A_104]: (k10_relat_1(A_104, k2_relat_1(A_104))=k1_relat_1(A_104) | ~v1_relat_1(A_104))), inference(cnfTransformation, [status(thm)], [f_35])).
% 19.50/9.71  tff(c_381, plain, (k10_relat_1('#skF_8', k1_relat_1('#skF_7'))=k1_relat_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_48, c_372])).
% 19.50/9.71  tff(c_385, plain, (k10_relat_1('#skF_8', k1_relat_1('#skF_7'))=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_381])).
% 19.50/9.71  tff(c_405, plain, (k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k1_relat_1('#skF_8') | ~v1_relat_1('#skF_7') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_399, c_385])).
% 19.50/9.71  tff(c_414, plain, (k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_58, c_405])).
% 19.50/9.71  tff(c_6, plain, (![A_4, B_6]: (k10_relat_1(A_4, k1_relat_1(B_6))=k1_relat_1(k5_relat_1(A_4, B_6)) | ~v1_relat_1(B_6) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 19.50/9.71  tff(c_421, plain, (![A_4]: (k1_relat_1(k5_relat_1(A_4, k5_relat_1('#skF_8', '#skF_7')))=k10_relat_1(A_4, k1_relat_1('#skF_8')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(A_4))), inference(superposition, [status(thm), theory('equality')], [c_414, c_6])).
% 19.50/9.71  tff(c_510, plain, (~v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(splitLeft, [status(thm)], [c_421])).
% 19.50/9.71  tff(c_513, plain, (~v1_relat_1('#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_2, c_510])).
% 19.50/9.71  tff(c_517, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_58, c_513])).
% 19.50/9.71  tff(c_519, plain, (v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(splitRight, [status(thm)], [c_421])).
% 19.50/9.71  tff(c_36, plain, (![A_54, B_55]: (v1_funct_1(k5_relat_1(A_54, B_55)) | ~v1_funct_1(B_55) | ~v1_relat_1(B_55) | ~v1_funct_1(A_54) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_84])).
% 19.50/9.71  tff(c_565, plain, (![B_129, A_130]: (r1_tarski(k2_relat_1(B_129), k1_relat_1(A_130)) | k1_relat_1(k5_relat_1(B_129, A_130))!=k1_relat_1(B_129) | ~v1_funct_1(B_129) | ~v1_relat_1(B_129) | ~v1_funct_1(A_130) | ~v1_relat_1(A_130))), inference(cnfTransformation, [status(thm)], [f_110])).
% 19.50/9.71  tff(c_577, plain, (![A_130]: (r1_tarski(k1_relat_1('#skF_7'), k1_relat_1(A_130)) | k1_relat_1(k5_relat_1('#skF_8', A_130))!=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~v1_funct_1(A_130) | ~v1_relat_1(A_130))), inference(superposition, [status(thm), theory('equality')], [c_48, c_565])).
% 19.50/9.71  tff(c_583, plain, (![A_131]: (r1_tarski(k1_relat_1('#skF_7'), k1_relat_1(A_131)) | k1_relat_1(k5_relat_1('#skF_8', A_131))!=k1_relat_1('#skF_8') | ~v1_funct_1(A_131) | ~v1_relat_1(A_131))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_577])).
% 19.50/9.71  tff(c_589, plain, (r1_tarski(k1_relat_1('#skF_7'), k1_relat_1('#skF_8')) | k1_relat_1(k5_relat_1('#skF_8', k5_relat_1('#skF_8', '#skF_7')))!=k1_relat_1('#skF_8') | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_414, c_583])).
% 19.50/9.71  tff(c_591, plain, (r1_tarski(k1_relat_1('#skF_7'), k1_relat_1('#skF_8')) | k1_relat_1(k5_relat_1('#skF_8', k5_relat_1('#skF_8', '#skF_7')))!=k1_relat_1('#skF_8') | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_519, c_589])).
% 19.50/9.71  tff(c_599, plain, (~v1_funct_1(k5_relat_1('#skF_8', '#skF_7'))), inference(splitLeft, [status(thm)], [c_591])).
% 19.50/9.71  tff(c_602, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_36, c_599])).
% 19.50/9.71  tff(c_606, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_58, c_56, c_602])).
% 19.50/9.71  tff(c_608, plain, (v1_funct_1(k5_relat_1('#skF_8', '#skF_7'))), inference(splitRight, [status(thm)], [c_591])).
% 19.50/9.71  tff(c_8, plain, (![A_7, D_46]: (r2_hidden(k1_funct_1(A_7, D_46), k2_relat_1(A_7)) | ~r2_hidden(D_46, k1_relat_1(A_7)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_57])).
% 19.50/9.71  tff(c_456, plain, (![C_116]: (r2_hidden('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_116), k1_relat_1('#skF_8')) | ~r2_hidden(C_116, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_414, c_453])).
% 19.50/9.71  tff(c_646, plain, (![C_116]: (r2_hidden('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_116), k1_relat_1('#skF_8')) | ~r2_hidden(C_116, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_519, c_608, c_456])).
% 19.50/9.71  tff(c_444, plain, (![A_113, D_114]: (r2_hidden(k1_funct_1(A_113, D_114), k2_relat_1(A_113)) | ~r2_hidden(D_114, k1_relat_1(A_113)) | ~v1_funct_1(A_113) | ~v1_relat_1(A_113))), inference(cnfTransformation, [status(thm)], [f_57])).
% 19.50/9.71  tff(c_450, plain, (![D_114]: (r2_hidden(k1_funct_1('#skF_8', D_114), k1_relat_1('#skF_7')) | ~r2_hidden(D_114, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_444])).
% 19.50/9.71  tff(c_452, plain, (![D_114]: (r2_hidden(k1_funct_1('#skF_8', D_114), k1_relat_1('#skF_7')) | ~r2_hidden(D_114, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_450])).
% 19.50/9.71  tff(c_703, plain, (![C_148, C_116]: (k1_funct_1(k5_relat_1('#skF_8', C_148), '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_116))=k1_funct_1(C_148, k1_funct_1('#skF_8', '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_116))) | ~v1_funct_1(C_148) | ~v1_relat_1(C_148) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(C_116, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(resolution, [status(thm)], [c_646, c_701])).
% 19.50/9.71  tff(c_3659, plain, (![C_323, C_324]: (k1_funct_1(k5_relat_1('#skF_8', C_323), '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_324))=k1_funct_1(C_323, k1_funct_1('#skF_8', '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_324))) | ~v1_funct_1(C_323) | ~v1_relat_1(C_323) | ~r2_hidden(C_324, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_703])).
% 19.50/9.71  tff(c_3684, plain, (![C_324]: (k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_324)))=C_324 | ~r2_hidden(C_324, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(C_324, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_3659, c_10])).
% 19.50/9.71  tff(c_3705, plain, (![C_325]: (k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_325)))=C_325 | ~r2_hidden(C_325, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_519, c_608, c_3684])).
% 19.50/9.71  tff(c_3724, plain, (![C_325]: (r2_hidden(C_325, k2_relat_1('#skF_7')) | ~r2_hidden(k1_funct_1('#skF_8', '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_325)), k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(C_325, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_3705, c_8])).
% 19.50/9.71  tff(c_3814, plain, (![C_329]: (r2_hidden(C_329, k2_relat_1('#skF_7')) | ~r2_hidden(k1_funct_1('#skF_8', '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_329)), k1_relat_1('#skF_7')) | ~r2_hidden(C_329, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_3724])).
% 19.50/9.71  tff(c_3819, plain, (![C_330]: (r2_hidden(C_330, k2_relat_1('#skF_7')) | ~r2_hidden(C_330, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_330), k1_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_452, c_3814])).
% 19.50/9.71  tff(c_3824, plain, (![C_331]: (r2_hidden(C_331, k2_relat_1('#skF_7')) | ~r2_hidden(C_331, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(resolution, [status(thm)], [c_646, c_3819])).
% 19.50/9.71  tff(c_3915, plain, (![D_46]: (r2_hidden(k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), D_46), k2_relat_1('#skF_7')) | ~r2_hidden(D_46, k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')))), inference(resolution, [status(thm)], [c_8, c_3824])).
% 19.50/9.71  tff(c_21793, plain, (![D_674]: (r2_hidden(k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), D_674), k2_relat_1('#skF_7')) | ~r2_hidden(D_674, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_519, c_608, c_414, c_3915])).
% 19.50/9.71  tff(c_21827, plain, (![C_43]: (r2_hidden(k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_43))), k2_relat_1('#skF_7')) | ~r2_hidden('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_43), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(C_43, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_742, c_21793])).
% 19.50/9.71  tff(c_21916, plain, (![C_676]: (r2_hidden(k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_676))), k2_relat_1('#skF_7')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_676), k1_relat_1('#skF_8')) | ~r2_hidden(C_676, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_48, c_58, c_56, c_48, c_48, c_21827])).
% 19.50/9.71  tff(c_21929, plain, (![C_677]: (r2_hidden(k1_funct_1('#skF_7', C_677), k2_relat_1('#skF_7')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_677), k1_relat_1('#skF_8')) | ~r2_hidden(C_677, k1_relat_1('#skF_7')) | ~r2_hidden(C_677, k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_492, c_21916])).
% 19.50/9.71  tff(c_21937, plain, (![C_678]: (r2_hidden(k1_funct_1('#skF_7', C_678), k2_relat_1('#skF_7')) | ~r2_hidden(C_678, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_461, c_21929])).
% 19.50/9.71  tff(c_21965, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_6'('#skF_7')), k2_relat_1('#skF_7')) | ~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7')) | v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_30, c_21937])).
% 19.50/9.71  tff(c_21976, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_6'('#skF_7')), k2_relat_1('#skF_7')) | ~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7')) | v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_21965])).
% 19.50/9.71  tff(c_21977, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_6'('#skF_7')), k2_relat_1('#skF_7')) | ~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_369, c_21976])).
% 19.50/9.71  tff(c_21978, plain, (~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_21977])).
% 19.50/9.71  tff(c_21981, plain, (v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_34, c_21978])).
% 19.50/9.71  tff(c_21984, plain, (v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_21981])).
% 19.50/9.71  tff(c_21986, plain, $false, inference(negUnitSimplification, [status(thm)], [c_369, c_21984])).
% 19.50/9.71  tff(c_21988, plain, (r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_21977])).
% 19.50/9.71  tff(c_390, plain, (![A_105]: ('#skF_5'(A_105)!='#skF_6'(A_105) | v2_funct_1(A_105) | ~v1_funct_1(A_105) | ~v1_relat_1(A_105))), inference(cnfTransformation, [status(thm)], [f_72])).
% 19.50/9.71  tff(c_393, plain, ('#skF_5'('#skF_7')!='#skF_6'('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_390, c_369])).
% 19.50/9.71  tff(c_396, plain, ('#skF_5'('#skF_7')!='#skF_6'('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_393])).
% 19.50/9.71  tff(c_24, plain, (![A_7, B_29]: (r2_hidden('#skF_2'(A_7, B_29), k1_relat_1(A_7)) | r2_hidden('#skF_3'(A_7, B_29), B_29) | k2_relat_1(A_7)=B_29 | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_57])).
% 19.50/9.71  tff(c_370, plain, (v2_funct_1('#skF_8')), inference(splitRight, [status(thm)], [c_46])).
% 19.50/9.71  tff(c_22, plain, (![A_7, B_29]: (k1_funct_1(A_7, '#skF_2'(A_7, B_29))='#skF_1'(A_7, B_29) | r2_hidden('#skF_3'(A_7, B_29), B_29) | k2_relat_1(A_7)=B_29 | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_57])).
% 19.50/9.71  tff(c_751, plain, (![C_150, B_151, A_152]: (C_150=B_151 | k1_funct_1(A_152, C_150)!=k1_funct_1(A_152, B_151) | ~r2_hidden(C_150, k1_relat_1(A_152)) | ~r2_hidden(B_151, k1_relat_1(A_152)) | ~v2_funct_1(A_152) | ~v1_funct_1(A_152) | ~v1_relat_1(A_152))), inference(cnfTransformation, [status(thm)], [f_72])).
% 19.50/9.71  tff(c_3743, plain, (![B_326, A_327, B_328]: (B_326='#skF_2'(A_327, B_328) | k1_funct_1(A_327, B_326)!='#skF_1'(A_327, B_328) | ~r2_hidden('#skF_2'(A_327, B_328), k1_relat_1(A_327)) | ~r2_hidden(B_326, k1_relat_1(A_327)) | ~v2_funct_1(A_327) | ~v1_funct_1(A_327) | ~v1_relat_1(A_327) | r2_hidden('#skF_3'(A_327, B_328), B_328) | k2_relat_1(A_327)=B_328 | ~v1_funct_1(A_327) | ~v1_relat_1(A_327))), inference(superposition, [status(thm), theory('equality')], [c_22, c_751])).
% 19.50/9.71  tff(c_3803, plain, (![C_120, B_328]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_120)='#skF_2'('#skF_8', B_328) | C_120!='#skF_1'('#skF_8', B_328) | ~r2_hidden('#skF_2'('#skF_8', B_328), k1_relat_1('#skF_8')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_120), k1_relat_1('#skF_8')) | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | r2_hidden('#skF_3'('#skF_8', B_328), B_328) | k2_relat_1('#skF_8')=B_328 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(C_120, k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_492, c_3743])).
% 19.50/9.71  tff(c_24044, plain, (![C_722, B_723]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_722)='#skF_2'('#skF_8', B_723) | C_722!='#skF_1'('#skF_8', B_723) | ~r2_hidden('#skF_2'('#skF_8', B_723), k1_relat_1('#skF_8')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_722), k1_relat_1('#skF_8')) | r2_hidden('#skF_3'('#skF_8', B_723), B_723) | k1_relat_1('#skF_7')=B_723 | ~r2_hidden(C_722, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_48, c_54, c_52, c_370, c_3803])).
% 19.50/9.71  tff(c_24059, plain, (![C_722, B_29]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_722)='#skF_2'('#skF_8', B_29) | C_722!='#skF_1'('#skF_8', B_29) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_722), k1_relat_1('#skF_8')) | k1_relat_1('#skF_7')=B_29 | ~r2_hidden(C_722, k1_relat_1('#skF_7')) | r2_hidden('#skF_3'('#skF_8', B_29), B_29) | k2_relat_1('#skF_8')=B_29 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_24, c_24044])).
% 19.50/9.71  tff(c_24965, plain, (![C_756, B_757]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_756)='#skF_2'('#skF_8', B_757) | C_756!='#skF_1'('#skF_8', B_757) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_756), k1_relat_1('#skF_8')) | ~r2_hidden(C_756, k1_relat_1('#skF_7')) | r2_hidden('#skF_3'('#skF_8', B_757), B_757) | k1_relat_1('#skF_7')=B_757)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_48, c_24059])).
% 19.50/9.71  tff(c_24972, plain, (![C_758, B_759]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_758)='#skF_2'('#skF_8', B_759) | C_758!='#skF_1'('#skF_8', B_759) | r2_hidden('#skF_3'('#skF_8', B_759), B_759) | k1_relat_1('#skF_7')=B_759 | ~r2_hidden(C_758, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_461, c_24965])).
% 19.50/9.71  tff(c_25063, plain, (![B_759]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))='#skF_2'('#skF_8', B_759) | '#skF_5'('#skF_7')!='#skF_1'('#skF_8', B_759) | r2_hidden('#skF_3'('#skF_8', B_759), B_759) | k1_relat_1('#skF_7')=B_759 | v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_34, c_24972])).
% 19.50/9.71  tff(c_25130, plain, (![B_759]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))='#skF_2'('#skF_8', B_759) | '#skF_5'('#skF_7')!='#skF_1'('#skF_8', B_759) | r2_hidden('#skF_3'('#skF_8', B_759), B_759) | k1_relat_1('#skF_7')=B_759 | v2_funct_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_25063])).
% 19.50/9.71  tff(c_25273, plain, (![B_761]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))='#skF_2'('#skF_8', B_761) | '#skF_5'('#skF_7')!='#skF_1'('#skF_8', B_761) | r2_hidden('#skF_3'('#skF_8', B_761), B_761) | k1_relat_1('#skF_7')=B_761)), inference(negUnitSimplification, [status(thm)], [c_369, c_25130])).
% 19.50/9.71  tff(c_25337, plain, (![B_761]: (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_relat_1('#skF_8')) | r2_hidden('#skF_3'('#skF_8', B_761), B_761) | k2_relat_1('#skF_8')=B_761 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | '#skF_5'('#skF_7')!='#skF_1'('#skF_8', B_761) | r2_hidden('#skF_3'('#skF_8', B_761), B_761) | k1_relat_1('#skF_7')=B_761)), inference(superposition, [status(thm), theory('equality')], [c_25273, c_24])).
% 19.50/9.71  tff(c_25411, plain, (![B_761]: (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_relat_1('#skF_8')) | '#skF_5'('#skF_7')!='#skF_1'('#skF_8', B_761) | r2_hidden('#skF_3'('#skF_8', B_761), B_761) | k1_relat_1('#skF_7')=B_761)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_48, c_25337])).
% 19.50/9.71  tff(c_26046, plain, (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_25411])).
% 19.50/9.71  tff(c_22036, plain, (![A_684]: (r2_hidden('#skF_3'(A_684, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7')) | r2_hidden('#skF_2'(A_684, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k1_relat_1(A_684)) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1(A_684) | ~v1_funct_1(A_684) | ~v1_relat_1(A_684))), inference(resolution, [status(thm)], [c_24, c_3824])).
% 19.50/9.71  tff(c_915, plain, (![A_162, B_163, D_164]: (r2_hidden('#skF_2'(A_162, B_163), k1_relat_1(A_162)) | k1_funct_1(A_162, D_164)!='#skF_3'(A_162, B_163) | ~r2_hidden(D_164, k1_relat_1(A_162)) | k2_relat_1(A_162)=B_163 | ~v1_funct_1(A_162) | ~v1_relat_1(A_162))), inference(cnfTransformation, [status(thm)], [f_57])).
% 19.50/9.71  tff(c_929, plain, (![A_7, B_163, C_43]: (r2_hidden('#skF_2'(A_7, B_163), k1_relat_1(A_7)) | C_43!='#skF_3'(A_7, B_163) | ~r2_hidden('#skF_4'(A_7, k2_relat_1(A_7), C_43), k1_relat_1(A_7)) | k2_relat_1(A_7)=B_163 | ~v1_funct_1(A_7) | ~v1_relat_1(A_7) | ~r2_hidden(C_43, k2_relat_1(A_7)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_915])).
% 19.50/9.71  tff(c_2680, plain, (![A_267, B_268]: (r2_hidden('#skF_2'(A_267, B_268), k1_relat_1(A_267)) | ~r2_hidden('#skF_4'(A_267, k2_relat_1(A_267), '#skF_3'(A_267, B_268)), k1_relat_1(A_267)) | k2_relat_1(A_267)=B_268 | ~v1_funct_1(A_267) | ~v1_relat_1(A_267) | ~r2_hidden('#skF_3'(A_267, B_268), k2_relat_1(A_267)) | ~v1_funct_1(A_267) | ~v1_relat_1(A_267))), inference(reflexivity, [status(thm), theory('equality')], [c_929])).
% 19.50/9.71  tff(c_2697, plain, (![A_7, B_268]: (r2_hidden('#skF_2'(A_7, B_268), k1_relat_1(A_7)) | k2_relat_1(A_7)=B_268 | ~r2_hidden('#skF_3'(A_7, B_268), k2_relat_1(A_7)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_12, c_2680])).
% 19.50/9.71  tff(c_22044, plain, (r2_hidden('#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k1_relat_1('#skF_7')) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_22036, c_2697])).
% 19.50/9.71  tff(c_22063, plain, (r2_hidden('#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k1_relat_1('#skF_7')) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_22044])).
% 19.50/9.71  tff(c_22068, plain, (k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7')), inference(splitLeft, [status(thm)], [c_22063])).
% 19.50/9.71  tff(c_3959, plain, (![D_46]: (r2_hidden(k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), D_46), k2_relat_1('#skF_7')) | ~r2_hidden(D_46, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_519, c_608, c_414, c_3915])).
% 19.50/9.71  tff(c_763, plain, (![C_150, A_7, C_43]: (C_150='#skF_4'(A_7, k2_relat_1(A_7), C_43) | k1_funct_1(A_7, C_150)!=C_43 | ~r2_hidden(C_150, k1_relat_1(A_7)) | ~r2_hidden('#skF_4'(A_7, k2_relat_1(A_7), C_43), k1_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7) | ~r2_hidden(C_43, k2_relat_1(A_7)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_751])).
% 19.50/9.71  tff(c_23033, plain, (![A_709, C_710]: ('#skF_4'(A_709, k2_relat_1(A_709), k1_funct_1(A_709, C_710))=C_710 | ~r2_hidden(C_710, k1_relat_1(A_709)) | ~r2_hidden('#skF_4'(A_709, k2_relat_1(A_709), k1_funct_1(A_709, C_710)), k1_relat_1(A_709)) | ~v2_funct_1(A_709) | ~v1_funct_1(A_709) | ~v1_relat_1(A_709) | ~r2_hidden(k1_funct_1(A_709, C_710), k2_relat_1(A_709)) | ~v1_funct_1(A_709) | ~v1_relat_1(A_709))), inference(reflexivity, [status(thm), theory('equality')], [c_763])).
% 19.50/9.71  tff(c_23170, plain, (![A_711, C_712]: ('#skF_4'(A_711, k2_relat_1(A_711), k1_funct_1(A_711, C_712))=C_712 | ~r2_hidden(C_712, k1_relat_1(A_711)) | ~v2_funct_1(A_711) | ~r2_hidden(k1_funct_1(A_711, C_712), k2_relat_1(A_711)) | ~v1_funct_1(A_711) | ~v1_relat_1(A_711))), inference(resolution, [status(thm)], [c_12, c_23033])).
% 19.50/9.71  tff(c_23281, plain, (![A_713, D_714]: ('#skF_4'(A_713, k2_relat_1(A_713), k1_funct_1(A_713, D_714))=D_714 | ~v2_funct_1(A_713) | ~r2_hidden(D_714, k1_relat_1(A_713)) | ~v1_funct_1(A_713) | ~v1_relat_1(A_713))), inference(resolution, [status(thm)], [c_8, c_23170])).
% 19.50/9.71  tff(c_23321, plain, (![D_714]: ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1('#skF_7'), k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), D_714))=D_714 | ~v2_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden(D_714, k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_22068, c_23281])).
% 19.50/9.71  tff(c_23427, plain, (![D_715]: ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1('#skF_7'), k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), D_715))=D_715 | ~r2_hidden(D_715, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_519, c_608, c_414, c_50, c_23321])).
% 19.50/9.71  tff(c_3701, plain, (![C_324]: (k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_324)))=C_324 | ~r2_hidden(C_324, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_519, c_608, c_3684])).
% 19.50/9.71  tff(c_22073, plain, (![C_324]: (k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1('#skF_7'), C_324)))=C_324 | ~r2_hidden(C_324, k2_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_22068, c_22068, c_3701])).
% 19.50/9.71  tff(c_23600, plain, (![D_718]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), D_718)=k1_funct_1('#skF_7', k1_funct_1('#skF_8', D_718)) | ~r2_hidden(k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), D_718), k2_relat_1('#skF_7')) | ~r2_hidden(D_718, k1_relat_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_23427, c_22073])).
% 19.50/9.71  tff(c_23679, plain, (![D_46]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), D_46)=k1_funct_1('#skF_7', k1_funct_1('#skF_8', D_46)) | ~r2_hidden(D_46, k1_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_3959, c_23600])).
% 19.50/9.71  tff(c_26055, plain, (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')))=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))))), inference(resolution, [status(thm)], [c_26046, c_23679])).
% 19.50/9.71  tff(c_23278, plain, (![A_7, D_46]: ('#skF_4'(A_7, k2_relat_1(A_7), k1_funct_1(A_7, D_46))=D_46 | ~v2_funct_1(A_7) | ~r2_hidden(D_46, k1_relat_1(A_7)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_8, c_23170])).
% 19.50/9.71  tff(c_26073, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')))))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')) | ~v2_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_26055, c_23278])).
% 19.50/9.71  tff(c_26114, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1('#skF_7'), k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')))))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_519, c_608, c_26046, c_414, c_50, c_22068, c_26073])).
% 19.50/9.71  tff(c_26190, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1('#skF_7'), k1_funct_1('#skF_7', '#skF_5'('#skF_7')))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')) | ~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_492, c_26114])).
% 19.50/9.71  tff(c_26207, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1('#skF_7'), k1_funct_1('#skF_7', '#skF_5'('#skF_7')))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_21988, c_26190])).
% 19.50/9.71  tff(c_26230, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1('#skF_7'), k1_funct_1('#skF_7', '#skF_6'('#skF_7')))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')) | v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_30, c_26207])).
% 19.50/9.71  tff(c_26246, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1('#skF_7'), k1_funct_1('#skF_7', '#skF_6'('#skF_7')))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')) | v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_26230])).
% 19.50/9.71  tff(c_26247, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1('#skF_7'), k1_funct_1('#skF_7', '#skF_6'('#skF_7')))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_369, c_26246])).
% 19.50/9.71  tff(c_25060, plain, (![B_759]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))='#skF_2'('#skF_8', B_759) | '#skF_1'('#skF_8', B_759)!='#skF_6'('#skF_7') | r2_hidden('#skF_3'('#skF_8', B_759), B_759) | k1_relat_1('#skF_7')=B_759 | v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_32, c_24972])).
% 19.50/9.71  tff(c_25126, plain, (![B_759]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))='#skF_2'('#skF_8', B_759) | '#skF_1'('#skF_8', B_759)!='#skF_6'('#skF_7') | r2_hidden('#skF_3'('#skF_8', B_759), B_759) | k1_relat_1('#skF_7')=B_759 | v2_funct_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_25060])).
% 19.50/9.71  tff(c_25133, plain, (![B_760]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))='#skF_2'('#skF_8', B_760) | '#skF_1'('#skF_8', B_760)!='#skF_6'('#skF_7') | r2_hidden('#skF_3'('#skF_8', B_760), B_760) | k1_relat_1('#skF_7')=B_760)), inference(negUnitSimplification, [status(thm)], [c_369, c_25126])).
% 19.50/9.71  tff(c_25194, plain, (![B_760]: (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')), k1_relat_1('#skF_8')) | r2_hidden('#skF_3'('#skF_8', B_760), B_760) | k2_relat_1('#skF_8')=B_760 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | '#skF_1'('#skF_8', B_760)!='#skF_6'('#skF_7') | r2_hidden('#skF_3'('#skF_8', B_760), B_760) | k1_relat_1('#skF_7')=B_760)), inference(superposition, [status(thm), theory('equality')], [c_25133, c_24])).
% 19.50/9.71  tff(c_25249, plain, (![B_760]: (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')), k1_relat_1('#skF_8')) | '#skF_1'('#skF_8', B_760)!='#skF_6'('#skF_7') | r2_hidden('#skF_3'('#skF_8', B_760), B_760) | k1_relat_1('#skF_7')=B_760)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_48, c_25194])).
% 19.50/9.71  tff(c_25564, plain, (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')), k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_25249])).
% 19.50/9.71  tff(c_25573, plain, (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')))=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))))), inference(resolution, [status(thm)], [c_25564, c_23679])).
% 19.50/9.71  tff(c_25811, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')))))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')) | ~v2_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')), k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_25573, c_23278])).
% 19.50/9.71  tff(c_25850, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1('#skF_7'), k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')))))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_519, c_608, c_25564, c_414, c_50, c_22068, c_25811])).
% 19.50/9.71  tff(c_27299, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1('#skF_7'), k1_funct_1('#skF_7', '#skF_6'('#skF_7')))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')) | ~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_492, c_25850])).
% 19.50/9.71  tff(c_27315, plain, ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')) | ~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_26247, c_27299])).
% 19.50/9.71  tff(c_27318, plain, (~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_27315])).
% 19.50/9.71  tff(c_27321, plain, (v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_32, c_27318])).
% 19.50/9.71  tff(c_27324, plain, (v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_27321])).
% 19.50/9.71  tff(c_27326, plain, $false, inference(negUnitSimplification, [status(thm)], [c_369, c_27324])).
% 19.50/9.71  tff(c_27328, plain, (r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_27315])).
% 19.50/9.71  tff(c_27327, plain, ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))), inference(splitRight, [status(thm)], [c_27315])).
% 19.50/9.71  tff(c_27373, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')))='#skF_5'('#skF_7') | ~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_27327, c_492])).
% 19.50/9.71  tff(c_27396, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')))='#skF_5'('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_21988, c_27373])).
% 19.50/9.71  tff(c_27456, plain, ('#skF_5'('#skF_7')='#skF_6'('#skF_7') | ~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_27396, c_492])).
% 19.50/9.71  tff(c_27506, plain, ('#skF_5'('#skF_7')='#skF_6'('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_27328, c_27456])).
% 19.50/9.71  tff(c_27508, plain, $false, inference(negUnitSimplification, [status(thm)], [c_396, c_27506])).
% 19.50/9.71  tff(c_27510, plain, (~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_25411])).
% 19.50/9.71  tff(c_27514, plain, (~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_461, c_27510])).
% 19.50/9.71  tff(c_27518, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21988, c_27514])).
% 19.50/9.71  tff(c_27520, plain, (~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')), k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_25249])).
% 19.50/9.71  tff(c_27525, plain, (~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_461, c_27520])).
% 19.50/9.71  tff(c_27528, plain, (v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_32, c_27525])).
% 19.50/9.71  tff(c_27531, plain, (v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_27528])).
% 19.50/9.71  tff(c_27533, plain, $false, inference(negUnitSimplification, [status(thm)], [c_369, c_27531])).
% 19.50/9.71  tff(c_27535, plain, (k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))!=k2_relat_1('#skF_7')), inference(splitRight, [status(thm)], [c_22063])).
% 19.50/9.71  tff(c_27534, plain, (r2_hidden('#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_22063])).
% 19.50/9.71  tff(c_28345, plain, (![A_806]: (r2_hidden('#skF_3'(A_806, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7')) | k1_funct_1(A_806, '#skF_2'(A_806, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))='#skF_1'(A_806, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1(A_806) | ~v1_funct_1(A_806) | ~v1_relat_1(A_806))), inference(resolution, [status(thm)], [c_22, c_3824])).
% 19.50/9.71  tff(c_934, plain, (![A_165, B_166, D_167]: (k1_funct_1(A_165, '#skF_2'(A_165, B_166))='#skF_1'(A_165, B_166) | k1_funct_1(A_165, D_167)!='#skF_3'(A_165, B_166) | ~r2_hidden(D_167, k1_relat_1(A_165)) | k2_relat_1(A_165)=B_166 | ~v1_funct_1(A_165) | ~v1_relat_1(A_165))), inference(cnfTransformation, [status(thm)], [f_57])).
% 19.50/9.71  tff(c_948, plain, (![A_7, B_166, C_43]: (k1_funct_1(A_7, '#skF_2'(A_7, B_166))='#skF_1'(A_7, B_166) | C_43!='#skF_3'(A_7, B_166) | ~r2_hidden('#skF_4'(A_7, k2_relat_1(A_7), C_43), k1_relat_1(A_7)) | k2_relat_1(A_7)=B_166 | ~v1_funct_1(A_7) | ~v1_relat_1(A_7) | ~r2_hidden(C_43, k2_relat_1(A_7)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_934])).
% 19.50/9.71  tff(c_3127, plain, (![A_286, B_287]: (k1_funct_1(A_286, '#skF_2'(A_286, B_287))='#skF_1'(A_286, B_287) | ~r2_hidden('#skF_4'(A_286, k2_relat_1(A_286), '#skF_3'(A_286, B_287)), k1_relat_1(A_286)) | k2_relat_1(A_286)=B_287 | ~v1_funct_1(A_286) | ~v1_relat_1(A_286) | ~r2_hidden('#skF_3'(A_286, B_287), k2_relat_1(A_286)) | ~v1_funct_1(A_286) | ~v1_relat_1(A_286))), inference(reflexivity, [status(thm), theory('equality')], [c_948])).
% 19.50/9.71  tff(c_3144, plain, (![A_7, B_287]: (k1_funct_1(A_7, '#skF_2'(A_7, B_287))='#skF_1'(A_7, B_287) | k2_relat_1(A_7)=B_287 | ~r2_hidden('#skF_3'(A_7, B_287), k2_relat_1(A_7)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_12, c_3127])).
% 19.50/9.71  tff(c_28349, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))='#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_28345, c_3144])).
% 19.50/9.71  tff(c_28440, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))='#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_28349])).
% 19.50/9.71  tff(c_28441, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))='#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_27535, c_28440])).
% 19.50/9.71  tff(c_29159, plain, (![A_819, C_820]: ('#skF_4'(A_819, k2_relat_1(A_819), k1_funct_1(A_819, C_820))=C_820 | ~r2_hidden(C_820, k1_relat_1(A_819)) | ~r2_hidden('#skF_4'(A_819, k2_relat_1(A_819), k1_funct_1(A_819, C_820)), k1_relat_1(A_819)) | ~v2_funct_1(A_819) | ~v1_funct_1(A_819) | ~v1_relat_1(A_819) | ~r2_hidden(k1_funct_1(A_819, C_820), k2_relat_1(A_819)) | ~v1_funct_1(A_819) | ~v1_relat_1(A_819))), inference(reflexivity, [status(thm), theory('equality')], [c_763])).
% 19.50/9.71  tff(c_29306, plain, (![A_821, C_822]: ('#skF_4'(A_821, k2_relat_1(A_821), k1_funct_1(A_821, C_822))=C_822 | ~r2_hidden(C_822, k1_relat_1(A_821)) | ~v2_funct_1(A_821) | ~r2_hidden(k1_funct_1(A_821, C_822), k2_relat_1(A_821)) | ~v1_funct_1(A_821) | ~v1_relat_1(A_821))), inference(resolution, [status(thm)], [c_12, c_29159])).
% 19.50/9.71  tff(c_29428, plain, (![A_823, D_824]: ('#skF_4'(A_823, k2_relat_1(A_823), k1_funct_1(A_823, D_824))=D_824 | ~v2_funct_1(A_823) | ~r2_hidden(D_824, k1_relat_1(A_823)) | ~v1_funct_1(A_823) | ~v1_relat_1(A_823))), inference(resolution, [status(thm)], [c_8, c_29306])).
% 19.50/9.71  tff(c_29435, plain, (![D_824]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), D_824)=k1_funct_1('#skF_7', k1_funct_1('#skF_8', D_824)) | ~r2_hidden(k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), D_824), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v2_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden(D_824, k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_29428, c_3701])).
% 19.50/9.71  tff(c_29602, plain, (![D_825]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), D_825)=k1_funct_1('#skF_7', k1_funct_1('#skF_8', D_825)) | ~r2_hidden(k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), D_825), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden(D_825, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_519, c_608, c_414, c_50, c_29435])).
% 19.50/9.71  tff(c_29684, plain, (![D_46]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), D_46)=k1_funct_1('#skF_7', k1_funct_1('#skF_8', D_46)) | ~r2_hidden(D_46, k1_relat_1('#skF_8')) | ~r2_hidden(D_46, k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')))), inference(resolution, [status(thm)], [c_8, c_29602])).
% 19.50/9.71  tff(c_29751, plain, (![D_827]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), D_827)=k1_funct_1('#skF_7', k1_funct_1('#skF_8', D_827)) | ~r2_hidden(D_827, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_519, c_608, c_414, c_29684])).
% 19.50/9.71  tff(c_30039, plain, (![C_829]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_829))=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_829))) | ~r2_hidden(C_829, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_461, c_29751])).
% 19.50/9.71  tff(c_30066, plain, (![C_829]: (r2_hidden(k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_829))), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_829), k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden(C_829, k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_30039, c_8])).
% 19.50/9.71  tff(c_30170, plain, (![C_833]: (r2_hidden(k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_833))), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_833), k1_relat_1('#skF_8')) | ~r2_hidden(C_833, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_519, c_608, c_414, c_30066])).
% 19.50/9.71  tff(c_30187, plain, (![C_834]: (r2_hidden(k1_funct_1('#skF_7', C_834), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_834), k1_relat_1('#skF_8')) | ~r2_hidden(C_834, k1_relat_1('#skF_7')) | ~r2_hidden(C_834, k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_492, c_30170])).
% 19.50/9.71  tff(c_30195, plain, (![C_835]: (r2_hidden(k1_funct_1('#skF_7', C_835), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden(C_835, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_461, c_30187])).
% 19.50/9.71  tff(c_30201, plain, (r2_hidden('#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_28441, c_30195])).
% 19.50/9.71  tff(c_30236, plain, (r2_hidden('#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_27534, c_30201])).
% 19.50/9.71  tff(c_14, plain, (![A_7, B_29, D_42]: (~r2_hidden('#skF_1'(A_7, B_29), B_29) | k1_funct_1(A_7, D_42)!='#skF_3'(A_7, B_29) | ~r2_hidden(D_42, k1_relat_1(A_7)) | k2_relat_1(A_7)=B_29 | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_57])).
% 19.50/9.71  tff(c_30261, plain, (![D_42]: (k1_funct_1('#skF_7', D_42)!='#skF_3'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden(D_42, k1_relat_1('#skF_7')) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_30236, c_14])).
% 19.50/9.71  tff(c_30270, plain, (![D_42]: (k1_funct_1('#skF_7', D_42)!='#skF_3'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden(D_42, k1_relat_1('#skF_7')) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_30261])).
% 19.50/9.71  tff(c_30286, plain, (![D_836]: (k1_funct_1('#skF_7', D_836)!='#skF_3'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden(D_836, k1_relat_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_27535, c_30270])).
% 19.50/9.71  tff(c_30307, plain, (![C_43]: (C_43!='#skF_3'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_43), k1_relat_1('#skF_7')) | ~r2_hidden(C_43, k2_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_10, c_30286])).
% 19.50/9.71  tff(c_30484, plain, (![C_843]: (C_843!='#skF_3'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_843), k1_relat_1('#skF_7')) | ~r2_hidden(C_843, k2_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_30307])).
% 19.50/9.71  tff(c_30492, plain, (![C_43]: (C_43!='#skF_3'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden(C_43, k2_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_12, c_30484])).
% 19.50/9.71  tff(c_30518, plain, (~r2_hidden('#skF_3'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_30492])).
% 19.50/9.71  tff(c_20, plain, (![A_7, B_29]: (~r2_hidden('#skF_1'(A_7, B_29), B_29) | r2_hidden('#skF_3'(A_7, B_29), B_29) | k2_relat_1(A_7)=B_29 | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_57])).
% 19.50/9.71  tff(c_3956, plain, (![A_7]: (r2_hidden('#skF_3'(A_7, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7')) | ~r2_hidden('#skF_1'(A_7, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_20, c_3824])).
% 19.50/9.71  tff(c_30256, plain, (r2_hidden('#skF_3'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7')) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_30236, c_3956])).
% 19.50/9.71  tff(c_30264, plain, (r2_hidden('#skF_3'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7')) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_30256])).
% 19.50/9.71  tff(c_30265, plain, (r2_hidden('#skF_3'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_27535, c_30264])).
% 19.50/9.71  tff(c_30520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30518, c_30265])).
% 19.50/9.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.50/9.71  
% 19.50/9.71  Inference rules
% 19.50/9.71  ----------------------
% 19.50/9.71  #Ref     : 16
% 19.50/9.71  #Sup     : 6858
% 19.50/9.71  #Fact    : 0
% 19.50/9.71  #Define  : 0
% 19.50/9.71  #Split   : 78
% 19.50/9.71  #Chain   : 0
% 19.50/9.71  #Close   : 0
% 19.50/9.71  
% 19.50/9.71  Ordering : KBO
% 19.50/9.71  
% 19.50/9.71  Simplification rules
% 19.50/9.71  ----------------------
% 19.50/9.71  #Subsume      : 981
% 19.50/9.71  #Demod        : 13212
% 19.50/9.71  #Tautology    : 1646
% 19.50/9.71  #SimpNegUnit  : 502
% 19.50/9.71  #BackRed      : 91
% 19.50/9.71  
% 19.50/9.71  #Partial instantiations: 0
% 19.50/9.71  #Strategies tried      : 1
% 19.50/9.71  
% 19.50/9.71  Timing (in seconds)
% 19.50/9.71  ----------------------
% 19.50/9.71  Preprocessing        : 0.36
% 19.50/9.71  Parsing              : 0.19
% 19.50/9.71  CNF conversion       : 0.03
% 19.50/9.71  Main loop            : 8.51
% 19.50/9.71  Inferencing          : 2.04
% 19.50/9.71  Reduction            : 2.65
% 19.50/9.71  Demodulation         : 1.95
% 19.50/9.71  BG Simplification    : 0.29
% 19.50/9.71  Subsumption          : 3.14
% 19.50/9.71  Abstraction          : 0.44
% 19.50/9.71  MUC search           : 0.00
% 19.50/9.71  Cooper               : 0.00
% 19.50/9.71  Total                : 8.94
% 19.50/9.71  Index Insertion      : 0.00
% 19.50/9.71  Index Deletion       : 0.00
% 19.50/9.71  Index Matching       : 0.00
% 19.50/9.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
