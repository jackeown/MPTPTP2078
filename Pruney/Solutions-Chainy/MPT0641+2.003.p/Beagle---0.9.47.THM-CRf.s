%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:39 EST 2020

% Result     : Theorem 47.84s
% Output     : CNFRefutation 48.26s
% Verified   : 
% Statistics : Number of formulae       :  320 (16717 expanded)
%              Number of leaves         :   31 (5980 expanded)
%              Depth                    :   36
%              Number of atoms          :  946 (65344 expanded)
%              Number of equality atoms :  240 (13392 expanded)
%              Maximal formula depth    :   15 (   4 average)
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

tff(f_136,negated_conjecture,(
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

tff(f_63,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_118,axiom,(
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

tff(f_78,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

tff(c_62,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_60,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_18,plain,(
    ! [A_9,C_45] :
      ( r2_hidden('#skF_4'(A_9,k2_relat_1(A_9),C_45),k1_relat_1(A_9))
      | ~ r2_hidden(C_45,k2_relat_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16,plain,(
    ! [A_9,C_45] :
      ( k1_funct_1(A_9,'#skF_4'(A_9,k2_relat_1(A_9),C_45)) = C_45
      | ~ r2_hidden(C_45,k2_relat_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_54,plain,(
    v2_funct_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,
    ( ~ v2_funct_1('#skF_7')
    | ~ v2_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_65,plain,(
    ~ v2_funct_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_58,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_56,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_52,plain,(
    k2_relat_1('#skF_8') = k1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_305,plain,(
    ! [B_97,A_98] :
      ( v2_funct_1(B_97)
      | ~ r1_tarski(k2_relat_1(B_97),k1_relat_1(A_98))
      | ~ v2_funct_1(k5_relat_1(B_97,A_98))
      | ~ v1_funct_1(B_97)
      | ~ v1_relat_1(B_97)
      | ~ v1_funct_1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_314,plain,(
    ! [A_98] :
      ( v2_funct_1('#skF_8')
      | ~ r1_tarski(k1_relat_1('#skF_7'),k1_relat_1(A_98))
      | ~ v2_funct_1(k5_relat_1('#skF_8',A_98))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ v1_funct_1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_305])).

tff(c_318,plain,(
    ! [A_98] :
      ( v2_funct_1('#skF_8')
      | ~ r1_tarski(k1_relat_1('#skF_7'),k1_relat_1(A_98))
      | ~ v2_funct_1(k5_relat_1('#skF_8',A_98))
      | ~ v1_funct_1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_314])).

tff(c_320,plain,(
    ! [A_99] :
      ( ~ r1_tarski(k1_relat_1('#skF_7'),k1_relat_1(A_99))
      | ~ v2_funct_1(k5_relat_1('#skF_8',A_99))
      | ~ v1_funct_1(A_99)
      | ~ v1_relat_1(A_99) ) ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_318])).

tff(c_330,plain,
    ( ~ v2_funct_1(k5_relat_1('#skF_8','#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_6,c_320])).

tff(c_336,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_54,c_330])).

tff(c_337,plain,(
    ~ v2_funct_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_40,plain,(
    ! [A_49] :
      ( r2_hidden('#skF_5'(A_49),k1_relat_1(A_49))
      | v2_funct_1(A_49)
      | ~ v1_funct_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_36,plain,(
    ! [A_49] :
      ( k1_funct_1(A_49,'#skF_5'(A_49)) = k1_funct_1(A_49,'#skF_6'(A_49))
      | v2_funct_1(A_49)
      | ~ v1_funct_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_439,plain,(
    ! [A_116,C_117] :
      ( r2_hidden('#skF_4'(A_116,k2_relat_1(A_116),C_117),k1_relat_1(A_116))
      | ~ r2_hidden(C_117,k2_relat_1(A_116))
      | ~ v1_funct_1(A_116)
      | ~ v1_relat_1(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_445,plain,(
    ! [C_117] :
      ( r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_117),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_117,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_439])).

tff(c_447,plain,(
    ! [C_117] :
      ( r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_117),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_117,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_445])).

tff(c_449,plain,(
    ! [A_119,C_120] :
      ( k1_funct_1(A_119,'#skF_4'(A_119,k2_relat_1(A_119),C_120)) = C_120
      | ~ r2_hidden(C_120,k2_relat_1(A_119))
      | ~ v1_funct_1(A_119)
      | ~ v1_relat_1(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_465,plain,(
    ! [C_120] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_120)) = C_120
      | ~ r2_hidden(C_120,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_449])).

tff(c_471,plain,(
    ! [C_120] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_120)) = C_120
      | ~ r2_hidden(C_120,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_465])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( v1_relat_1(k5_relat_1(A_3,B_4))
      | ~ v1_relat_1(B_4)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_379,plain,(
    ! [A_110,B_111] :
      ( k10_relat_1(A_110,k1_relat_1(B_111)) = k1_relat_1(k5_relat_1(A_110,B_111))
      | ~ v1_relat_1(B_111)
      | ~ v1_relat_1(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_343,plain,(
    ! [A_100] :
      ( k10_relat_1(A_100,k2_relat_1(A_100)) = k1_relat_1(A_100)
      | ~ v1_relat_1(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_352,plain,
    ( k10_relat_1('#skF_8',k1_relat_1('#skF_7')) = k1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_343])).

tff(c_356,plain,(
    k10_relat_1('#skF_8',k1_relat_1('#skF_7')) = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_352])).

tff(c_385,plain,
    ( k1_relat_1(k5_relat_1('#skF_8','#skF_7')) = k1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_356])).

tff(c_394,plain,(
    k1_relat_1(k5_relat_1('#skF_8','#skF_7')) = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_385])).

tff(c_12,plain,(
    ! [A_6,B_8] :
      ( k10_relat_1(A_6,k1_relat_1(B_8)) = k1_relat_1(k5_relat_1(A_6,B_8))
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_401,plain,(
    ! [A_6] :
      ( k1_relat_1(k5_relat_1(A_6,k5_relat_1('#skF_8','#skF_7'))) = k10_relat_1(A_6,k1_relat_1('#skF_8'))
      | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1(A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_12])).

tff(c_489,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_401])).

tff(c_492,plain,
    ( ~ v1_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_8,c_489])).

tff(c_496,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_492])).

tff(c_498,plain,(
    v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_401])).

tff(c_42,plain,(
    ! [A_56,B_57] :
      ( v1_funct_1(k5_relat_1(A_56,B_57))
      | ~ v1_funct_1(B_57)
      | ~ v1_relat_1(B_57)
      | ~ v1_funct_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_536,plain,(
    ! [B_127,A_128] :
      ( v2_funct_1(B_127)
      | ~ r1_tarski(k2_relat_1(B_127),k1_relat_1(A_128))
      | ~ v2_funct_1(k5_relat_1(B_127,A_128))
      | ~ v1_funct_1(B_127)
      | ~ v1_relat_1(B_127)
      | ~ v1_funct_1(A_128)
      | ~ v1_relat_1(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_542,plain,(
    ! [B_127] :
      ( v2_funct_1(B_127)
      | ~ r1_tarski(k2_relat_1(B_127),k1_relat_1('#skF_8'))
      | ~ v2_funct_1(k5_relat_1(B_127,k5_relat_1('#skF_8','#skF_7')))
      | ~ v1_funct_1(B_127)
      | ~ v1_relat_1(B_127)
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_536])).

tff(c_547,plain,(
    ! [B_127] :
      ( v2_funct_1(B_127)
      | ~ r1_tarski(k2_relat_1(B_127),k1_relat_1('#skF_8'))
      | ~ v2_funct_1(k5_relat_1(B_127,k5_relat_1('#skF_8','#skF_7')))
      | ~ v1_funct_1(B_127)
      | ~ v1_relat_1(B_127)
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_542])).

tff(c_564,plain,(
    ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_547])).

tff(c_567,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_564])).

tff(c_571,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_62,c_60,c_567])).

tff(c_573,plain,(
    v1_funct_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_547])).

tff(c_626,plain,(
    ! [C_143,B_144,A_145] :
      ( k1_funct_1(k5_relat_1(C_143,B_144),A_145) = k1_funct_1(B_144,k1_funct_1(C_143,A_145))
      | ~ r2_hidden(A_145,k1_relat_1(k5_relat_1(C_143,B_144)))
      | ~ v1_funct_1(C_143)
      | ~ v1_relat_1(C_143)
      | ~ v1_funct_1(B_144)
      | ~ v1_relat_1(B_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_652,plain,(
    ! [A_145] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),A_145) = k1_funct_1('#skF_7',k1_funct_1('#skF_8',A_145))
      | ~ r2_hidden(A_145,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_626])).

tff(c_677,plain,(
    ! [A_148] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),A_148) = k1_funct_1('#skF_7',k1_funct_1('#skF_8',A_148))
      | ~ r2_hidden(A_148,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_652])).

tff(c_765,plain,(
    ! [C_150] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_150)) = k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_150)))
      | ~ r2_hidden(C_150,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_447,c_677])).

tff(c_14,plain,(
    ! [A_9,D_48] :
      ( r2_hidden(k1_funct_1(A_9,D_48),k2_relat_1(A_9))
      | ~ r2_hidden(D_48,k1_relat_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_777,plain,(
    ! [C_150] :
      ( r2_hidden(k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_150))),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_150),k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ r2_hidden(C_150,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_765,c_14])).

tff(c_1014,plain,(
    ! [C_166] :
      ( r2_hidden(k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_166))),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_166),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_166,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_573,c_394,c_777])).

tff(c_1093,plain,(
    ! [C_172] :
      ( r2_hidden(k1_funct_1('#skF_7',C_172),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_172),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_172,k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_172,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_1014])).

tff(c_1098,plain,(
    ! [C_173] :
      ( r2_hidden(k1_funct_1('#skF_7',C_173),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden(C_173,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_447,c_1093])).

tff(c_1108,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_6'('#skF_7')),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7'))
    | v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1098])).

tff(c_1112,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_6'('#skF_7')),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7'))
    | v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1108])).

tff(c_1113,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_6'('#skF_7')),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_337,c_1112])).

tff(c_1114,plain,(
    ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1113])).

tff(c_1117,plain,
    ( v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_1114])).

tff(c_1120,plain,(
    v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1117])).

tff(c_1122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_337,c_1120])).

tff(c_1124,plain,(
    r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1113])).

tff(c_38,plain,(
    ! [A_49] :
      ( r2_hidden('#skF_6'(A_49),k1_relat_1(A_49))
      | v2_funct_1(A_49)
      | ~ v1_funct_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_338,plain,(
    v2_funct_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_369,plain,(
    ! [A_105] :
      ( '#skF_5'(A_105) != '#skF_6'(A_105)
      | v2_funct_1(A_105)
      | ~ v1_funct_1(A_105)
      | ~ v1_relat_1(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_372,plain,
    ( '#skF_5'('#skF_7') != '#skF_6'('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_369,c_337])).

tff(c_375,plain,(
    '#skF_5'('#skF_7') != '#skF_6'('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_372])).

tff(c_30,plain,(
    ! [A_9,B_31] :
      ( r2_hidden('#skF_2'(A_9,B_31),k1_relat_1(A_9))
      | r2_hidden('#skF_3'(A_9,B_31),B_31)
      | k2_relat_1(A_9) = B_31
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_550,plain,(
    ! [A_129,B_130] :
      ( k1_funct_1(A_129,'#skF_2'(A_129,B_130)) = '#skF_1'(A_129,B_130)
      | r2_hidden('#skF_3'(A_129,B_130),B_130)
      | k2_relat_1(A_129) = B_130
      | ~ v1_funct_1(A_129)
      | ~ v1_relat_1(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1018,plain,(
    ! [A_167,B_168] :
      ( r2_hidden('#skF_1'(A_167,B_168),k2_relat_1(A_167))
      | ~ r2_hidden('#skF_2'(A_167,B_168),k1_relat_1(A_167))
      | ~ v1_funct_1(A_167)
      | ~ v1_relat_1(A_167)
      | r2_hidden('#skF_3'(A_167,B_168),B_168)
      | k2_relat_1(A_167) = B_168
      | ~ v1_funct_1(A_167)
      | ~ v1_relat_1(A_167) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_550,c_14])).

tff(c_1030,plain,(
    ! [A_169,B_170] :
      ( r2_hidden('#skF_1'(A_169,B_170),k2_relat_1(A_169))
      | r2_hidden('#skF_3'(A_169,B_170),B_170)
      | k2_relat_1(A_169) = B_170
      | ~ v1_funct_1(A_169)
      | ~ v1_relat_1(A_169) ) ),
    inference(resolution,[status(thm)],[c_30,c_1018])).

tff(c_1054,plain,(
    ! [B_170] :
      ( r2_hidden('#skF_1'('#skF_8',B_170),k1_relat_1('#skF_7'))
      | r2_hidden('#skF_3'('#skF_8',B_170),B_170)
      | k2_relat_1('#skF_8') = B_170
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1030])).

tff(c_1065,plain,(
    ! [B_171] :
      ( r2_hidden('#skF_1'('#skF_8',B_171),k1_relat_1('#skF_7'))
      | r2_hidden('#skF_3'('#skF_8',B_171),B_171)
      | k1_relat_1('#skF_7') = B_171 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_1054])).

tff(c_669,plain,(
    ! [A_145] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),A_145) = k1_funct_1('#skF_7',k1_funct_1('#skF_8',A_145))
      | ~ r2_hidden(A_145,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_652])).

tff(c_1091,plain,
    ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_3'('#skF_8',k1_relat_1('#skF_8'))) = k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_3'('#skF_8',k1_relat_1('#skF_8'))))
    | r2_hidden('#skF_1'('#skF_8',k1_relat_1('#skF_8')),k1_relat_1('#skF_7'))
    | k1_relat_1('#skF_7') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_1065,c_669])).

tff(c_1186,plain,(
    k1_relat_1('#skF_7') = k1_relat_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1091])).

tff(c_1224,plain,
    ( r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_8'))
    | v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1186,c_38])).

tff(c_1242,plain,
    ( r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_8'))
    | v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1224])).

tff(c_1243,plain,(
    r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_337,c_1242])).

tff(c_1296,plain,(
    k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_6'('#skF_7')) = k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_6'('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_1243,c_669])).

tff(c_1221,plain,
    ( r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_8'))
    | v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1186,c_40])).

tff(c_1239,plain,
    ( r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_8'))
    | v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1221])).

tff(c_1240,plain,(
    r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_337,c_1239])).

tff(c_1292,plain,(
    k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_5'('#skF_7')) = k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_5'('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_1240,c_669])).

tff(c_32,plain,(
    ! [C_55,B_54,A_49] :
      ( C_55 = B_54
      | k1_funct_1(A_49,C_55) != k1_funct_1(A_49,B_54)
      | ~ r2_hidden(C_55,k1_relat_1(A_49))
      | ~ r2_hidden(B_54,k1_relat_1(A_49))
      | ~ v2_funct_1(A_49)
      | ~ v1_funct_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1594,plain,(
    ! [B_54] :
      ( B_54 = '#skF_5'('#skF_7')
      | k1_funct_1(k5_relat_1('#skF_8','#skF_7'),B_54) != k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_5'('#skF_7')))
      | ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden(B_54,k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ v2_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1292,c_32])).

tff(c_2077,plain,(
    ! [B_209] :
      ( B_209 = '#skF_5'('#skF_7')
      | k1_funct_1(k5_relat_1('#skF_8','#skF_7'),B_209) != k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_5'('#skF_7')))
      | ~ r2_hidden(B_209,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_573,c_54,c_394,c_1240,c_394,c_1594])).

tff(c_2083,plain,
    ( '#skF_5'('#skF_7') = '#skF_6'('#skF_7')
    | k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_5'('#skF_7'))) != k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_6'('#skF_7')))
    | ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1296,c_2077])).

tff(c_2098,plain,
    ( '#skF_5'('#skF_7') = '#skF_6'('#skF_7')
    | k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_5'('#skF_7'))) != k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_6'('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1243,c_2083])).

tff(c_2099,plain,(
    k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_5'('#skF_7'))) != k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_6'('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_375,c_2098])).

tff(c_1199,plain,(
    ! [C_117] :
      ( r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_8'),C_117),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_117,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1186,c_1186,c_447])).

tff(c_1201,plain,(
    k10_relat_1('#skF_8',k1_relat_1('#skF_8')) = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1186,c_356])).

tff(c_1321,plain,
    ( k1_relat_1(k5_relat_1('#skF_8','#skF_8')) = k1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1201,c_12])).

tff(c_1330,plain,(
    k1_relat_1(k5_relat_1('#skF_8','#skF_8')) = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_58,c_1321])).

tff(c_46,plain,(
    ! [C_61,B_59,A_58] :
      ( k1_funct_1(k5_relat_1(C_61,B_59),A_58) = k1_funct_1(B_59,k1_funct_1(C_61,A_58))
      | ~ r2_hidden(A_58,k1_relat_1(k5_relat_1(C_61,B_59)))
      | ~ v1_funct_1(C_61)
      | ~ v1_relat_1(C_61)
      | ~ v1_funct_1(B_59)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1346,plain,(
    ! [A_58] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_8'),A_58) = k1_funct_1('#skF_8',k1_funct_1('#skF_8',A_58))
      | ~ r2_hidden(A_58,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1330,c_46])).

tff(c_1684,plain,(
    ! [A_200] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_8'),A_200) = k1_funct_1('#skF_8',k1_funct_1('#skF_8',A_200))
      | ~ r2_hidden(A_200,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_58,c_56,c_1346])).

tff(c_1772,plain,(
    k1_funct_1(k5_relat_1('#skF_8','#skF_8'),'#skF_6'('#skF_7')) = k1_funct_1('#skF_8',k1_funct_1('#skF_8','#skF_6'('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_1243,c_1684])).

tff(c_423,plain,(
    ! [A_113,D_114] :
      ( r2_hidden(k1_funct_1(A_113,D_114),k2_relat_1(A_113))
      | ~ r2_hidden(D_114,k1_relat_1(A_113))
      | ~ v1_funct_1(A_113)
      | ~ v1_relat_1(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_429,plain,(
    ! [D_114] :
      ( r2_hidden(k1_funct_1('#skF_8',D_114),k1_relat_1('#skF_7'))
      | ~ r2_hidden(D_114,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_423])).

tff(c_431,plain,(
    ! [D_114] :
      ( r2_hidden(k1_funct_1('#skF_8',D_114),k1_relat_1('#skF_7'))
      | ~ r2_hidden(D_114,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_429])).

tff(c_1200,plain,(
    ! [D_114] :
      ( r2_hidden(k1_funct_1('#skF_8',D_114),k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_114,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1186,c_431])).

tff(c_1198,plain,(
    ! [C_120] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_8'),C_120)) = C_120
      | ~ r2_hidden(C_120,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1186,c_1186,c_471])).

tff(c_2142,plain,(
    ! [D_211] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_8'),k1_funct_1('#skF_8',D_211)) = k1_funct_1('#skF_8',k1_funct_1('#skF_8',k1_funct_1('#skF_8',D_211)))
      | ~ r2_hidden(D_211,k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_1200,c_1684])).

tff(c_4299,plain,(
    ! [C_280] :
      ( k1_funct_1('#skF_8',k1_funct_1('#skF_8',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_8'),C_280)))) = k1_funct_1(k5_relat_1('#skF_8','#skF_8'),C_280)
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_8'),C_280),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_280,k1_relat_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1198,c_2142])).

tff(c_72185,plain,(
    ! [C_1024] :
      ( r2_hidden(k1_funct_1(k5_relat_1('#skF_8','#skF_8'),C_1024),k1_relat_1('#skF_8'))
      | ~ r2_hidden(k1_funct_1('#skF_8',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_8'),C_1024))),k1_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_8'),C_1024),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_1024,k1_relat_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4299,c_1200])).

tff(c_73029,plain,(
    ! [C_1033] :
      ( r2_hidden(k1_funct_1(k5_relat_1('#skF_8','#skF_8'),C_1033),k1_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_8'),C_1033),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_1033,k1_relat_1('#skF_8'))
      | ~ r2_hidden(k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_8'),C_1033)),k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_1200,c_72185])).

tff(c_73040,plain,(
    ! [C_1034] :
      ( r2_hidden(k1_funct_1(k5_relat_1('#skF_8','#skF_8'),C_1034),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_1034,k1_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_8'),C_1034),k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_1200,c_73029])).

tff(c_73122,plain,
    ( r2_hidden(k1_funct_1('#skF_8',k1_funct_1('#skF_8','#skF_6'('#skF_7'))),k1_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_6'('#skF_7')),k1_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1772,c_73040])).

tff(c_73164,plain,
    ( r2_hidden(k1_funct_1('#skF_8',k1_funct_1('#skF_8','#skF_6'('#skF_7'))),k1_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_6'('#skF_7')),k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1243,c_73122])).

tff(c_73197,plain,(
    ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_6'('#skF_7')),k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_73164])).

tff(c_73200,plain,(
    ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_1199,c_73197])).

tff(c_73204,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1243,c_73200])).

tff(c_73206,plain,(
    r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_6'('#skF_7')),k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_73164])).

tff(c_1773,plain,(
    k1_funct_1(k5_relat_1('#skF_8','#skF_8'),'#skF_5'('#skF_7')) = k1_funct_1('#skF_8',k1_funct_1('#skF_8','#skF_5'('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_1240,c_1684])).

tff(c_73119,plain,
    ( r2_hidden(k1_funct_1('#skF_8',k1_funct_1('#skF_8','#skF_5'('#skF_7'))),k1_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_5'('#skF_7')),k1_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1773,c_73040])).

tff(c_73162,plain,
    ( r2_hidden(k1_funct_1('#skF_8',k1_funct_1('#skF_8','#skF_5'('#skF_7'))),k1_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_5'('#skF_7')),k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1240,c_73119])).

tff(c_73171,plain,(
    ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_5'('#skF_7')),k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_73162])).

tff(c_73174,plain,(
    ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_1199,c_73171])).

tff(c_73178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1240,c_73174])).

tff(c_73180,plain,(
    r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_5'('#skF_7')),k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_73162])).

tff(c_73196,plain,(
    k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_5'('#skF_7'))) = k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_5'('#skF_7')))) ),
    inference(resolution,[status(thm)],[c_73180,c_669])).

tff(c_585,plain,(
    ! [C_135,B_136,A_137] :
      ( C_135 = B_136
      | k1_funct_1(A_137,C_135) != k1_funct_1(A_137,B_136)
      | ~ r2_hidden(C_135,k1_relat_1(A_137))
      | ~ r2_hidden(B_136,k1_relat_1(A_137))
      | ~ v2_funct_1(A_137)
      | ~ v1_funct_1(A_137)
      | ~ v1_relat_1(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_597,plain,(
    ! [C_135,A_9,C_45] :
      ( C_135 = '#skF_4'(A_9,k2_relat_1(A_9),C_45)
      | k1_funct_1(A_9,C_135) != C_45
      | ~ r2_hidden(C_135,k1_relat_1(A_9))
      | ~ r2_hidden('#skF_4'(A_9,k2_relat_1(A_9),C_45),k1_relat_1(A_9))
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9)
      | ~ r2_hidden(C_45,k2_relat_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_585])).

tff(c_71044,plain,(
    ! [A_1007,C_1008] :
      ( '#skF_4'(A_1007,k2_relat_1(A_1007),k1_funct_1(A_1007,C_1008)) = C_1008
      | ~ r2_hidden(C_1008,k1_relat_1(A_1007))
      | ~ r2_hidden('#skF_4'(A_1007,k2_relat_1(A_1007),k1_funct_1(A_1007,C_1008)),k1_relat_1(A_1007))
      | ~ v2_funct_1(A_1007)
      | ~ v1_funct_1(A_1007)
      | ~ v1_relat_1(A_1007)
      | ~ r2_hidden(k1_funct_1(A_1007,C_1008),k2_relat_1(A_1007))
      | ~ v1_funct_1(A_1007)
      | ~ v1_relat_1(A_1007) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_597])).

tff(c_71982,plain,(
    ! [A_1022,C_1023] :
      ( '#skF_4'(A_1022,k2_relat_1(A_1022),k1_funct_1(A_1022,C_1023)) = C_1023
      | ~ r2_hidden(C_1023,k1_relat_1(A_1022))
      | ~ v2_funct_1(A_1022)
      | ~ r2_hidden(k1_funct_1(A_1022,C_1023),k2_relat_1(A_1022))
      | ~ v1_funct_1(A_1022)
      | ~ v1_relat_1(A_1022) ) ),
    inference(resolution,[status(thm)],[c_18,c_71044])).

tff(c_72160,plain,(
    ! [A_9,D_48] :
      ( '#skF_4'(A_9,k2_relat_1(A_9),k1_funct_1(A_9,D_48)) = D_48
      | ~ v2_funct_1(A_9)
      | ~ r2_hidden(D_48,k1_relat_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(resolution,[status(thm)],[c_14,c_71982])).

tff(c_73513,plain,
    ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_5'('#skF_7'))))) = '#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_5'('#skF_7'))
    | ~ v2_funct_1(k5_relat_1('#skF_8','#skF_7'))
    | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_5'('#skF_7')),k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
    | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_73196,c_72160])).

tff(c_73546,plain,(
    '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_5'('#skF_7'))))) = '#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_5'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_573,c_73180,c_394,c_54,c_73513])).

tff(c_75342,plain,
    ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),k1_funct_1('#skF_7','#skF_5'('#skF_7'))) = '#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_5'('#skF_7'))
    | ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1198,c_73546])).

tff(c_75357,plain,(
    '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),k1_funct_1('#skF_7','#skF_5'('#skF_7'))) = '#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_5'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1240,c_75342])).

tff(c_75377,plain,
    ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),k1_funct_1('#skF_7','#skF_6'('#skF_7'))) = '#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_5'('#skF_7'))
    | v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_75357])).

tff(c_75391,plain,
    ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),k1_funct_1('#skF_7','#skF_6'('#skF_7'))) = '#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_5'('#skF_7'))
    | v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_75377])).

tff(c_75392,plain,(
    '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),k1_funct_1('#skF_7','#skF_6'('#skF_7'))) = '#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_5'('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_337,c_75391])).

tff(c_73222,plain,(
    k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_6'('#skF_7'))) = k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_6'('#skF_7')))) ),
    inference(resolution,[status(thm)],[c_73206,c_669])).

tff(c_73441,plain,
    ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_6'('#skF_7'))))) = '#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_6'('#skF_7'))
    | ~ v2_funct_1(k5_relat_1('#skF_8','#skF_7'))
    | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_6'('#skF_7')),k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
    | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_73222,c_72160])).

tff(c_73474,plain,(
    '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_6'('#skF_7'))))) = '#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_6'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_573,c_73206,c_394,c_54,c_73441])).

tff(c_76478,plain,
    ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),k1_funct_1('#skF_7','#skF_6'('#skF_7'))) = '#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_6'('#skF_7'))
    | ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1198,c_73474])).

tff(c_76495,plain,(
    '#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_5'('#skF_7')) = '#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_6'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1243,c_75392,c_76478])).

tff(c_76529,plain,
    ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_6'('#skF_7'))) = '#skF_5'('#skF_7')
    | ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_76495,c_1198])).

tff(c_76548,plain,(
    k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_6'('#skF_7'))) = '#skF_5'('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1240,c_76529])).

tff(c_1378,plain,(
    ! [D_184] :
      ( r2_hidden(k1_funct_1('#skF_8',D_184),k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_184,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1186,c_431])).

tff(c_1976,plain,(
    ! [D_207] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),k1_funct_1('#skF_8',D_207)) = k1_funct_1('#skF_7',k1_funct_1('#skF_8',k1_funct_1('#skF_8',D_207)))
      | ~ r2_hidden(D_207,k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_1378,c_669])).

tff(c_1998,plain,(
    ! [C_120] :
      ( k1_funct_1('#skF_7',k1_funct_1('#skF_8',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_8'),C_120)))) = k1_funct_1(k5_relat_1('#skF_8','#skF_7'),C_120)
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_8'),C_120),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_120,k1_relat_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1198,c_1976])).

tff(c_76592,plain,
    ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_6'('#skF_7')) = k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_5'('#skF_7')))
    | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_6'('#skF_7')),k1_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_76548,c_1998])).

tff(c_76650,plain,(
    k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_5'('#skF_7'))) = k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_6'('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1243,c_73206,c_1296,c_76592])).

tff(c_76652,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2099,c_76650])).

tff(c_76654,plain,(
    k1_relat_1('#skF_7') != k1_relat_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_1091])).

tff(c_76653,plain,
    ( r2_hidden('#skF_1'('#skF_8',k1_relat_1('#skF_8')),k1_relat_1('#skF_7'))
    | k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_3'('#skF_8',k1_relat_1('#skF_8'))) = k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_3'('#skF_8',k1_relat_1('#skF_8')))) ),
    inference(splitRight,[status(thm)],[c_1091])).

tff(c_76691,plain,(
    k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_3'('#skF_8',k1_relat_1('#skF_8'))) = k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_3'('#skF_8',k1_relat_1('#skF_8')))) ),
    inference(splitLeft,[status(thm)],[c_76653])).

tff(c_76703,plain,
    ( r2_hidden(k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_3'('#skF_8',k1_relat_1('#skF_8')))),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | ~ r2_hidden('#skF_3'('#skF_8',k1_relat_1('#skF_8')),k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
    | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_76691,c_14])).

tff(c_76715,plain,
    ( r2_hidden(k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_3'('#skF_8',k1_relat_1('#skF_8')))),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | ~ r2_hidden('#skF_3'('#skF_8',k1_relat_1('#skF_8')),k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_573,c_394,c_76703])).

tff(c_76717,plain,(
    ~ r2_hidden('#skF_3'('#skF_8',k1_relat_1('#skF_8')),k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_76715])).

tff(c_76733,plain,
    ( r2_hidden('#skF_2'('#skF_8',k1_relat_1('#skF_8')),k1_relat_1('#skF_8'))
    | k2_relat_1('#skF_8') = k1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_30,c_76717])).

tff(c_76753,plain,
    ( r2_hidden('#skF_2'('#skF_8',k1_relat_1('#skF_8')),k1_relat_1('#skF_8'))
    | k1_relat_1('#skF_7') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_76733])).

tff(c_76754,plain,(
    r2_hidden('#skF_2'('#skF_8',k1_relat_1('#skF_8')),k1_relat_1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_76654,c_76753])).

tff(c_28,plain,(
    ! [A_9,B_31] :
      ( k1_funct_1(A_9,'#skF_2'(A_9,B_31)) = '#skF_1'(A_9,B_31)
      | r2_hidden('#skF_3'(A_9,B_31),B_31)
      | k2_relat_1(A_9) = B_31
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_76730,plain,
    ( k1_funct_1('#skF_8','#skF_2'('#skF_8',k1_relat_1('#skF_8'))) = '#skF_1'('#skF_8',k1_relat_1('#skF_8'))
    | k2_relat_1('#skF_8') = k1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_28,c_76717])).

tff(c_76749,plain,
    ( k1_funct_1('#skF_8','#skF_2'('#skF_8',k1_relat_1('#skF_8'))) = '#skF_1'('#skF_8',k1_relat_1('#skF_8'))
    | k1_relat_1('#skF_7') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_76730])).

tff(c_76750,plain,(
    k1_funct_1('#skF_8','#skF_2'('#skF_8',k1_relat_1('#skF_8'))) = '#skF_1'('#skF_8',k1_relat_1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_76654,c_76749])).

tff(c_76831,plain,(
    ! [C_55] :
      ( C_55 = '#skF_2'('#skF_8',k1_relat_1('#skF_8'))
      | k1_funct_1('#skF_8',C_55) != '#skF_1'('#skF_8',k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_55,k1_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_2'('#skF_8',k1_relat_1('#skF_8')),k1_relat_1('#skF_8'))
      | ~ v2_funct_1('#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76750,c_32])).

tff(c_76898,plain,(
    ! [C_1097] :
      ( C_1097 = '#skF_2'('#skF_8',k1_relat_1('#skF_8'))
      | k1_funct_1('#skF_8',C_1097) != '#skF_1'('#skF_8',k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_1097,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_338,c_76754,c_76831])).

tff(c_76998,plain,(
    ! [C_1098] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_1098) = '#skF_2'('#skF_8',k1_relat_1('#skF_8'))
      | k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_1098)) != '#skF_1'('#skF_8',k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_1098,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_447,c_76898])).

tff(c_77120,plain,(
    ! [C_1106] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_1106) = '#skF_2'('#skF_8',k1_relat_1('#skF_8'))
      | C_1106 != '#skF_1'('#skF_8',k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_1106,k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_1106,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_76998])).

tff(c_77171,plain,
    ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')) = '#skF_2'('#skF_8',k1_relat_1('#skF_8'))
    | '#skF_1'('#skF_8',k1_relat_1('#skF_8')) != '#skF_6'('#skF_7')
    | ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7'))
    | v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_77120])).

tff(c_77207,plain,
    ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')) = '#skF_2'('#skF_8',k1_relat_1('#skF_8'))
    | '#skF_1'('#skF_8',k1_relat_1('#skF_8')) != '#skF_6'('#skF_7')
    | ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7'))
    | v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_77171])).

tff(c_77208,plain,
    ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')) = '#skF_2'('#skF_8',k1_relat_1('#skF_8'))
    | '#skF_1'('#skF_8',k1_relat_1('#skF_8')) != '#skF_6'('#skF_7')
    | ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_337,c_77207])).

tff(c_77239,plain,(
    ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_77208])).

tff(c_77242,plain,
    ( v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_77239])).

tff(c_77245,plain,(
    v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_77242])).

tff(c_77247,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_337,c_77245])).

tff(c_77249,plain,(
    r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_77208])).

tff(c_78360,plain,(
    ! [C_1147,A_1148,B_1149] :
      ( C_1147 = '#skF_2'(A_1148,B_1149)
      | k1_funct_1(A_1148,C_1147) != '#skF_1'(A_1148,B_1149)
      | ~ r2_hidden(C_1147,k1_relat_1(A_1148))
      | ~ r2_hidden('#skF_2'(A_1148,B_1149),k1_relat_1(A_1148))
      | ~ v2_funct_1(A_1148)
      | ~ v1_funct_1(A_1148)
      | ~ v1_relat_1(A_1148)
      | r2_hidden('#skF_3'(A_1148,B_1149),B_1149)
      | k2_relat_1(A_1148) = B_1149
      | ~ v1_funct_1(A_1148)
      | ~ v1_relat_1(A_1148) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_585])).

tff(c_78394,plain,(
    ! [C_120,B_1149] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_120) = '#skF_2'('#skF_8',B_1149)
      | C_120 != '#skF_1'('#skF_8',B_1149)
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_120),k1_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_2'('#skF_8',B_1149),k1_relat_1('#skF_8'))
      | ~ v2_funct_1('#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | r2_hidden('#skF_3'('#skF_8',B_1149),B_1149)
      | k2_relat_1('#skF_8') = B_1149
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(C_120,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_78360])).

tff(c_92604,plain,(
    ! [C_1410,B_1411] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_1410) = '#skF_2'('#skF_8',B_1411)
      | C_1410 != '#skF_1'('#skF_8',B_1411)
      | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_1410),k1_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_2'('#skF_8',B_1411),k1_relat_1('#skF_8'))
      | r2_hidden('#skF_3'('#skF_8',B_1411),B_1411)
      | k1_relat_1('#skF_7') = B_1411
      | ~ r2_hidden(C_1410,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_58,c_56,c_338,c_78394])).

tff(c_92737,plain,(
    ! [C_1414,B_1415] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_1414) = '#skF_2'('#skF_8',B_1415)
      | C_1414 != '#skF_1'('#skF_8',B_1415)
      | ~ r2_hidden('#skF_2'('#skF_8',B_1415),k1_relat_1('#skF_8'))
      | r2_hidden('#skF_3'('#skF_8',B_1415),B_1415)
      | k1_relat_1('#skF_7') = B_1415
      | ~ r2_hidden(C_1414,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_447,c_92604])).

tff(c_92753,plain,(
    ! [C_1414,B_31] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_1414) = '#skF_2'('#skF_8',B_31)
      | C_1414 != '#skF_1'('#skF_8',B_31)
      | k1_relat_1('#skF_7') = B_31
      | ~ r2_hidden(C_1414,k1_relat_1('#skF_7'))
      | r2_hidden('#skF_3'('#skF_8',B_31),B_31)
      | k2_relat_1('#skF_8') = B_31
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_30,c_92737])).

tff(c_92933,plain,(
    ! [C_1417,B_1418] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),C_1417) = '#skF_2'('#skF_8',B_1418)
      | C_1417 != '#skF_1'('#skF_8',B_1418)
      | ~ r2_hidden(C_1417,k1_relat_1('#skF_7'))
      | r2_hidden('#skF_3'('#skF_8',B_1418),B_1418)
      | k1_relat_1('#skF_7') = B_1418 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_92753])).

tff(c_93007,plain,(
    ! [B_1418] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) = '#skF_2'('#skF_8',B_1418)
      | '#skF_5'('#skF_7') != '#skF_1'('#skF_8',B_1418)
      | r2_hidden('#skF_3'('#skF_8',B_1418),B_1418)
      | k1_relat_1('#skF_7') = B_1418
      | v2_funct_1('#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_40,c_92933])).

tff(c_93062,plain,(
    ! [B_1418] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) = '#skF_2'('#skF_8',B_1418)
      | '#skF_5'('#skF_7') != '#skF_1'('#skF_8',B_1418)
      | r2_hidden('#skF_3'('#skF_8',B_1418),B_1418)
      | k1_relat_1('#skF_7') = B_1418
      | v2_funct_1('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_93007])).

tff(c_93069,plain,(
    ! [B_1419] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) = '#skF_2'('#skF_8',B_1419)
      | '#skF_5'('#skF_7') != '#skF_1'('#skF_8',B_1419)
      | r2_hidden('#skF_3'('#skF_8',B_1419),B_1419)
      | k1_relat_1('#skF_7') = B_1419 ) ),
    inference(negUnitSimplification,[status(thm)],[c_337,c_93062])).

tff(c_93116,plain,(
    ! [B_1419] :
      ( r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_relat_1('#skF_8'))
      | r2_hidden('#skF_3'('#skF_8',B_1419),B_1419)
      | k2_relat_1('#skF_8') = B_1419
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | '#skF_5'('#skF_7') != '#skF_1'('#skF_8',B_1419)
      | r2_hidden('#skF_3'('#skF_8',B_1419),B_1419)
      | k1_relat_1('#skF_7') = B_1419 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93069,c_30])).

tff(c_93188,plain,(
    ! [B_1419] :
      ( r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_relat_1('#skF_8'))
      | '#skF_5'('#skF_7') != '#skF_1'('#skF_8',B_1419)
      | r2_hidden('#skF_3'('#skF_8',B_1419),B_1419)
      | k1_relat_1('#skF_7') = B_1419 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_93116])).

tff(c_94014,plain,(
    r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_93188])).

tff(c_94023,plain,(
    k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))) = k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')))) ),
    inference(resolution,[status(thm)],[c_94014,c_669])).

tff(c_442,plain,(
    ! [C_117] :
      ( r2_hidden('#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_117),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_117,k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_439])).

tff(c_499,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_442])).

tff(c_501,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_499])).

tff(c_502,plain,(
    ! [C_117] :
      ( ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | r2_hidden('#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_117),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_117,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(splitRight,[status(thm)],[c_442])).

tff(c_624,plain,(
    ! [C_117] :
      ( r2_hidden('#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_117),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_117,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_502])).

tff(c_79320,plain,(
    ! [C_1188] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_1188)) = k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_1188)))
      | ~ r2_hidden(C_1188,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(resolution,[status(thm)],[c_624,c_677])).

tff(c_79343,plain,(
    ! [C_1188] :
      ( k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_1188))) = C_1188
      | ~ r2_hidden(C_1188,k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ r2_hidden(C_1188,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79320,c_16])).

tff(c_79374,plain,(
    ! [C_1189] :
      ( k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_1189))) = C_1189
      | ~ r2_hidden(C_1189,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_573,c_79343])).

tff(c_79395,plain,(
    ! [C_1189] :
      ( r2_hidden(C_1189,k2_relat_1('#skF_7'))
      | ~ r2_hidden(k1_funct_1('#skF_8','#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_1189)),k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(C_1189,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79374,c_14])).

tff(c_79519,plain,(
    ! [C_1193] :
      ( r2_hidden(C_1193,k2_relat_1('#skF_7'))
      | ~ r2_hidden(k1_funct_1('#skF_8','#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_1193)),k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_1193,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_79395])).

tff(c_79524,plain,(
    ! [C_1194] :
      ( r2_hidden(C_1194,k2_relat_1('#skF_7'))
      | ~ r2_hidden(C_1194,k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden('#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),C_1194),k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_431,c_79519])).

tff(c_79529,plain,(
    ! [C_1195] :
      ( r2_hidden(C_1195,k2_relat_1('#skF_7'))
      | ~ r2_hidden(C_1195,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ) ),
    inference(resolution,[status(thm)],[c_624,c_79524])).

tff(c_79638,plain,(
    ! [D_48] :
      ( r2_hidden(k1_funct_1(k5_relat_1('#skF_8','#skF_7'),D_48),k2_relat_1('#skF_7'))
      | ~ r2_hidden(D_48,k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_14,c_79529])).

tff(c_79683,plain,(
    ! [D_48] :
      ( r2_hidden(k1_funct_1(k5_relat_1('#skF_8','#skF_7'),D_48),k2_relat_1('#skF_7'))
      | ~ r2_hidden(D_48,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_573,c_394,c_79638])).

tff(c_94030,plain,
    ( r2_hidden(k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')))),k2_relat_1('#skF_7'))
    | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_94023,c_79683])).

tff(c_94060,plain,(
    r2_hidden(k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')))),k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94014,c_94030])).

tff(c_79679,plain,(
    ! [A_9] :
      ( r2_hidden('#skF_3'(A_9,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7'))
      | r2_hidden('#skF_2'(A_9,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k1_relat_1(A_9))
      | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(resolution,[status(thm)],[c_30,c_79529])).

tff(c_606,plain,(
    ! [A_138,B_139,D_140] :
      ( r2_hidden('#skF_2'(A_138,B_139),k1_relat_1(A_138))
      | k1_funct_1(A_138,D_140) != '#skF_3'(A_138,B_139)
      | ~ r2_hidden(D_140,k1_relat_1(A_138))
      | k2_relat_1(A_138) = B_139
      | ~ v1_funct_1(A_138)
      | ~ v1_relat_1(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_612,plain,(
    ! [A_9,B_139,C_45] :
      ( r2_hidden('#skF_2'(A_9,B_139),k1_relat_1(A_9))
      | C_45 != '#skF_3'(A_9,B_139)
      | ~ r2_hidden('#skF_4'(A_9,k2_relat_1(A_9),C_45),k1_relat_1(A_9))
      | k2_relat_1(A_9) = B_139
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9)
      | ~ r2_hidden(C_45,k2_relat_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_606])).

tff(c_91984,plain,(
    ! [A_1396,B_1397] :
      ( r2_hidden('#skF_2'(A_1396,B_1397),k1_relat_1(A_1396))
      | ~ r2_hidden('#skF_4'(A_1396,k2_relat_1(A_1396),'#skF_3'(A_1396,B_1397)),k1_relat_1(A_1396))
      | k2_relat_1(A_1396) = B_1397
      | ~ v1_funct_1(A_1396)
      | ~ v1_relat_1(A_1396)
      | ~ r2_hidden('#skF_3'(A_1396,B_1397),k2_relat_1(A_1396))
      | ~ v1_funct_1(A_1396)
      | ~ v1_relat_1(A_1396) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_612])).

tff(c_92006,plain,(
    ! [A_1398,B_1399] :
      ( r2_hidden('#skF_2'(A_1398,B_1399),k1_relat_1(A_1398))
      | k2_relat_1(A_1398) = B_1399
      | ~ r2_hidden('#skF_3'(A_1398,B_1399),k2_relat_1(A_1398))
      | ~ v1_funct_1(A_1398)
      | ~ v1_relat_1(A_1398) ) ),
    inference(resolution,[status(thm)],[c_18,c_91984])).

tff(c_92018,plain,
    ( r2_hidden('#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k1_relat_1('#skF_7'))
    | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_79679,c_92006])).

tff(c_92098,plain,
    ( r2_hidden('#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k1_relat_1('#skF_7'))
    | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_92018])).

tff(c_92149,plain,(
    k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_92098])).

tff(c_595,plain,(
    ! [B_136,A_9,C_45] :
      ( B_136 = '#skF_4'(A_9,k2_relat_1(A_9),C_45)
      | k1_funct_1(A_9,B_136) != C_45
      | ~ r2_hidden('#skF_4'(A_9,k2_relat_1(A_9),C_45),k1_relat_1(A_9))
      | ~ r2_hidden(B_136,k1_relat_1(A_9))
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9)
      | ~ r2_hidden(C_45,k2_relat_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_585])).

tff(c_93385,plain,(
    ! [A_1422,B_1423] :
      ( '#skF_4'(A_1422,k2_relat_1(A_1422),k1_funct_1(A_1422,B_1423)) = B_1423
      | ~ r2_hidden('#skF_4'(A_1422,k2_relat_1(A_1422),k1_funct_1(A_1422,B_1423)),k1_relat_1(A_1422))
      | ~ r2_hidden(B_1423,k1_relat_1(A_1422))
      | ~ v2_funct_1(A_1422)
      | ~ v1_funct_1(A_1422)
      | ~ v1_relat_1(A_1422)
      | ~ r2_hidden(k1_funct_1(A_1422,B_1423),k2_relat_1(A_1422))
      | ~ v1_funct_1(A_1422)
      | ~ v1_relat_1(A_1422) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_595])).

tff(c_94520,plain,(
    ! [A_1435,B_1436] :
      ( '#skF_4'(A_1435,k2_relat_1(A_1435),k1_funct_1(A_1435,B_1436)) = B_1436
      | ~ r2_hidden(B_1436,k1_relat_1(A_1435))
      | ~ v2_funct_1(A_1435)
      | ~ r2_hidden(k1_funct_1(A_1435,B_1436),k2_relat_1(A_1435))
      | ~ v1_funct_1(A_1435)
      | ~ v1_relat_1(A_1435) ) ),
    inference(resolution,[status(thm)],[c_18,c_93385])).

tff(c_94536,plain,
    ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))
    | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | ~ v2_funct_1(k5_relat_1('#skF_8','#skF_7'))
    | ~ r2_hidden(k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')))),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
    | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_94023,c_94520])).

tff(c_94625,plain,(
    '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1('#skF_7'),k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_573,c_94060,c_92149,c_54,c_94014,c_394,c_94023,c_92149,c_94536])).

tff(c_95071,plain,
    ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1('#skF_7'),k1_funct_1('#skF_7','#skF_5'('#skF_7'))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))
    | ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_94625])).

tff(c_95082,plain,(
    '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1('#skF_7'),k1_funct_1('#skF_7','#skF_5'('#skF_7'))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1124,c_95071])).

tff(c_95327,plain,
    ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1('#skF_7'),k1_funct_1('#skF_7','#skF_6'('#skF_7'))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))
    | v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_95082])).

tff(c_95337,plain,
    ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1('#skF_7'),k1_funct_1('#skF_7','#skF_6'('#skF_7'))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7'))
    | v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_95327])).

tff(c_95338,plain,(
    '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1('#skF_7'),k1_funct_1('#skF_7','#skF_6'('#skF_7'))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_337,c_95337])).

tff(c_93010,plain,(
    ! [B_1418] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')) = '#skF_2'('#skF_8',B_1418)
      | '#skF_1'('#skF_8',B_1418) != '#skF_6'('#skF_7')
      | r2_hidden('#skF_3'('#skF_8',B_1418),B_1418)
      | k1_relat_1('#skF_7') = B_1418
      | v2_funct_1('#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_38,c_92933])).

tff(c_93066,plain,(
    ! [B_1418] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')) = '#skF_2'('#skF_8',B_1418)
      | '#skF_1'('#skF_8',B_1418) != '#skF_6'('#skF_7')
      | r2_hidden('#skF_3'('#skF_8',B_1418),B_1418)
      | k1_relat_1('#skF_7') = B_1418
      | v2_funct_1('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_93010])).

tff(c_93514,plain,(
    ! [B_1424] :
      ( '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')) = '#skF_2'('#skF_8',B_1424)
      | '#skF_1'('#skF_8',B_1424) != '#skF_6'('#skF_7')
      | r2_hidden('#skF_3'('#skF_8',B_1424),B_1424)
      | k1_relat_1('#skF_7') = B_1424 ) ),
    inference(negUnitSimplification,[status(thm)],[c_337,c_93066])).

tff(c_93567,plain,(
    ! [B_1424] :
      ( r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')),k1_relat_1('#skF_8'))
      | r2_hidden('#skF_3'('#skF_8',B_1424),B_1424)
      | k2_relat_1('#skF_8') = B_1424
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | '#skF_1'('#skF_8',B_1424) != '#skF_6'('#skF_7')
      | r2_hidden('#skF_3'('#skF_8',B_1424),B_1424)
      | k1_relat_1('#skF_7') = B_1424 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93514,c_30])).

tff(c_93642,plain,(
    ! [B_1424] :
      ( r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')),k1_relat_1('#skF_8'))
      | '#skF_1'('#skF_8',B_1424) != '#skF_6'('#skF_7')
      | r2_hidden('#skF_3'('#skF_8',B_1424),B_1424)
      | k1_relat_1('#skF_7') = B_1424 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_93567])).

tff(c_94144,plain,(
    r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')),k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_93642])).

tff(c_94153,plain,(
    k1_funct_1(k5_relat_1('#skF_8','#skF_7'),'#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))) = k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')))) ),
    inference(resolution,[status(thm)],[c_94144,c_669])).

tff(c_94779,plain,(
    ! [A_1440,D_1441] :
      ( '#skF_4'(A_1440,k2_relat_1(A_1440),k1_funct_1(A_1440,D_1441)) = D_1441
      | ~ v2_funct_1(A_1440)
      | ~ r2_hidden(D_1441,k1_relat_1(A_1440))
      | ~ v1_funct_1(A_1440)
      | ~ v1_relat_1(A_1440) ) ),
    inference(resolution,[status(thm)],[c_14,c_94520])).

tff(c_94805,plain,
    ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1(k5_relat_1('#skF_8','#skF_7')),k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))
    | ~ v2_funct_1(k5_relat_1('#skF_8','#skF_7'))
    | ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')),k1_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_7'))
    | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_94153,c_94779])).

tff(c_94897,plain,(
    '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1('#skF_7'),k1_funct_1('#skF_7',k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_573,c_94144,c_394,c_54,c_92149,c_94805])).

tff(c_96256,plain,
    ( '#skF_4'(k5_relat_1('#skF_8','#skF_7'),k2_relat_1('#skF_7'),k1_funct_1('#skF_7','#skF_6'('#skF_7'))) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))
    | ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_94897])).

tff(c_96267,plain,(
    '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')) = '#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77249,c_95338,c_96256])).

tff(c_96289,plain,
    ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))) = '#skF_5'('#skF_7')
    | ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_96267,c_471])).

tff(c_96302,plain,(
    k1_funct_1('#skF_8','#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7'))) = '#skF_5'('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1124,c_96289])).

tff(c_96372,plain,
    ( '#skF_5'('#skF_7') = '#skF_6'('#skF_7')
    | ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_96302,c_471])).

tff(c_96416,plain,(
    '#skF_5'('#skF_7') = '#skF_6'('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77249,c_96372])).

tff(c_96418,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_375,c_96416])).

tff(c_96420,plain,(
    ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_6'('#skF_7')),k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_93642])).

tff(c_96424,plain,(
    ~ r2_hidden('#skF_6'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_447,c_96420])).

tff(c_96428,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77249,c_96424])).

tff(c_96430,plain,(
    ~ r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_7'),'#skF_5'('#skF_7')),k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_93188])).

tff(c_96434,plain,(
    ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_447,c_96430])).

tff(c_96438,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1124,c_96434])).

tff(c_96440,plain,(
    k2_relat_1(k5_relat_1('#skF_8','#skF_7')) != k2_relat_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_92098])).

tff(c_96439,plain,(
    r2_hidden('#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_92098])).

tff(c_1027,plain,(
    ! [A_9,B_31] :
      ( r2_hidden('#skF_1'(A_9,B_31),k2_relat_1(A_9))
      | r2_hidden('#skF_3'(A_9,B_31),B_31)
      | k2_relat_1(A_9) = B_31
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(resolution,[status(thm)],[c_30,c_1018])).

tff(c_79669,plain,(
    ! [A_9] :
      ( r2_hidden('#skF_3'(A_9,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7'))
      | r2_hidden('#skF_1'(A_9,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1(A_9))
      | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(resolution,[status(thm)],[c_1027,c_79529])).

tff(c_808,plain,(
    ! [A_152,B_153,D_154] :
      ( k1_funct_1(A_152,'#skF_2'(A_152,B_153)) = '#skF_1'(A_152,B_153)
      | k1_funct_1(A_152,D_154) != '#skF_3'(A_152,B_153)
      | ~ r2_hidden(D_154,k1_relat_1(A_152))
      | k2_relat_1(A_152) = B_153
      | ~ v1_funct_1(A_152)
      | ~ v1_relat_1(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_818,plain,(
    ! [A_9,B_153,C_45] :
      ( k1_funct_1(A_9,'#skF_2'(A_9,B_153)) = '#skF_1'(A_9,B_153)
      | C_45 != '#skF_3'(A_9,B_153)
      | ~ r2_hidden('#skF_4'(A_9,k2_relat_1(A_9),C_45),k1_relat_1(A_9))
      | k2_relat_1(A_9) = B_153
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9)
      | ~ r2_hidden(C_45,k2_relat_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_808])).

tff(c_96449,plain,(
    ! [A_1453,B_1454] :
      ( k1_funct_1(A_1453,'#skF_2'(A_1453,B_1454)) = '#skF_1'(A_1453,B_1454)
      | ~ r2_hidden('#skF_4'(A_1453,k2_relat_1(A_1453),'#skF_3'(A_1453,B_1454)),k1_relat_1(A_1453))
      | k2_relat_1(A_1453) = B_1454
      | ~ v1_funct_1(A_1453)
      | ~ v1_relat_1(A_1453)
      | ~ r2_hidden('#skF_3'(A_1453,B_1454),k2_relat_1(A_1453))
      | ~ v1_funct_1(A_1453)
      | ~ v1_relat_1(A_1453) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_818])).

tff(c_96471,plain,(
    ! [A_1455,B_1456] :
      ( k1_funct_1(A_1455,'#skF_2'(A_1455,B_1456)) = '#skF_1'(A_1455,B_1456)
      | k2_relat_1(A_1455) = B_1456
      | ~ r2_hidden('#skF_3'(A_1455,B_1456),k2_relat_1(A_1455))
      | ~ v1_funct_1(A_1455)
      | ~ v1_relat_1(A_1455) ) ),
    inference(resolution,[status(thm)],[c_18,c_96449])).

tff(c_96479,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))) = '#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | r2_hidden('#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7'))
    | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_79669,c_96471])).

tff(c_96561,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))) = '#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | r2_hidden('#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7'))
    | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_96479])).

tff(c_96562,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))) = '#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | r2_hidden('#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_96440,c_96561])).

tff(c_97158,plain,(
    r2_hidden('#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_96562])).

tff(c_1104,plain,(
    ! [C_45] :
      ( r2_hidden(C_45,k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_45),k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_45,k2_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1098])).

tff(c_1125,plain,(
    ! [C_174] :
      ( r2_hidden(C_174,k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_174),k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_174,k2_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1104])).

tff(c_1129,plain,(
    ! [C_45] :
      ( r2_hidden(C_45,k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden(C_45,k2_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_18,c_1125])).

tff(c_1132,plain,(
    ! [C_45] :
      ( r2_hidden(C_45,k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden(C_45,k2_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1129])).

tff(c_26,plain,(
    ! [A_9,B_31] :
      ( ~ r2_hidden('#skF_1'(A_9,B_31),B_31)
      | r2_hidden('#skF_3'(A_9,B_31),B_31)
      | k2_relat_1(A_9) = B_31
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_91895,plain,(
    ! [A_1388] :
      ( r2_hidden('#skF_3'(A_1388,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7'))
      | ~ r2_hidden('#skF_1'(A_1388,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1(A_1388)
      | ~ v1_funct_1(A_1388)
      | ~ v1_relat_1(A_1388) ) ),
    inference(resolution,[status(thm)],[c_26,c_79529])).

tff(c_91926,plain,(
    ! [A_1388] :
      ( r2_hidden('#skF_3'(A_1388,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7'))
      | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1(A_1388)
      | ~ v1_funct_1(A_1388)
      | ~ v1_relat_1(A_1388)
      | ~ r2_hidden('#skF_1'(A_1388,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_1132,c_91895])).

tff(c_96475,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))) = '#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ r2_hidden('#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_91926,c_96471])).

tff(c_96557,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))) = '#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7')
    | ~ r2_hidden('#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_96475])).

tff(c_96558,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))) = '#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | ~ r2_hidden('#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_96440,c_96557])).

tff(c_97160,plain,(
    k1_funct_1('#skF_7','#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))) = '#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97158,c_96558])).

tff(c_1097,plain,(
    ! [C_117] :
      ( r2_hidden(k1_funct_1('#skF_7',C_117),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden(C_117,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_447,c_1093])).

tff(c_97177,plain,
    ( r2_hidden('#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
    | ~ r2_hidden('#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_97160,c_1097])).

tff(c_97212,plain,(
    r2_hidden('#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96439,c_97177])).

tff(c_20,plain,(
    ! [A_9,B_31,D_44] :
      ( ~ r2_hidden('#skF_1'(A_9,B_31),B_31)
      | k1_funct_1(A_9,D_44) != '#skF_3'(A_9,B_31)
      | ~ r2_hidden(D_44,k1_relat_1(A_9))
      | k2_relat_1(A_9) = B_31
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_97237,plain,(
    ! [D_44] :
      ( k1_funct_1('#skF_7',D_44) != '#skF_3'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden(D_44,k1_relat_1('#skF_7'))
      | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_97212,c_20])).

tff(c_97246,plain,(
    ! [D_44] :
      ( k1_funct_1('#skF_7',D_44) != '#skF_3'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden(D_44,k1_relat_1('#skF_7'))
      | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_97237])).

tff(c_97405,plain,(
    ! [D_1467] :
      ( k1_funct_1('#skF_7',D_1467) != '#skF_3'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden(D_1467,k1_relat_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96440,c_97246])).

tff(c_97423,plain,(
    ! [C_45] :
      ( C_45 != '#skF_3'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_45),k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_45,k2_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_97405])).

tff(c_97485,plain,(
    ! [C_1470] :
      ( C_1470 != '#skF_3'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_1470),k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_1470,k2_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_97423])).

tff(c_97489,plain,(
    ! [C_45] :
      ( C_45 != '#skF_3'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | ~ r2_hidden(C_45,k2_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_18,c_97485])).

tff(c_97493,plain,(
    ~ r2_hidden('#skF_3'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_97489])).

tff(c_79680,plain,(
    ! [A_9] :
      ( r2_hidden('#skF_3'(A_9,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7'))
      | ~ r2_hidden('#skF_1'(A_9,k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1(k5_relat_1('#skF_8','#skF_7')))
      | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(resolution,[status(thm)],[c_26,c_79529])).

tff(c_97232,plain,
    ( r2_hidden('#skF_3'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7'))
    | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_97212,c_79680])).

tff(c_97240,plain,
    ( r2_hidden('#skF_3'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7'))
    | k2_relat_1(k5_relat_1('#skF_8','#skF_7')) = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_97232])).

tff(c_97241,plain,(
    r2_hidden('#skF_3'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_96440,c_97240])).

tff(c_97495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_97493,c_97241])).

tff(c_97497,plain,(
    ~ r2_hidden('#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_96562])).

tff(c_97496,plain,(
    k1_funct_1('#skF_7','#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7')))) = '#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_96562])).

tff(c_79664,plain,(
    ! [C_117] :
      ( r2_hidden(k1_funct_1('#skF_7',C_117),k2_relat_1('#skF_7'))
      | ~ r2_hidden(C_117,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_1097,c_79529])).

tff(c_97657,plain,
    ( r2_hidden('#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7'))
    | ~ r2_hidden('#skF_2'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_97496,c_79664])).

tff(c_97695,plain,(
    r2_hidden('#skF_1'('#skF_7',k2_relat_1(k5_relat_1('#skF_8','#skF_7'))),k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96439,c_97657])).

tff(c_97697,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_97497,c_97695])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:00:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 47.84/35.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 48.02/35.66  
% 48.02/35.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 48.02/35.66  %$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_5 > #skF_4 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_1 > #skF_6
% 48.02/35.66  
% 48.02/35.66  %Foreground sorts:
% 48.02/35.66  
% 48.02/35.66  
% 48.02/35.66  %Background operators:
% 48.02/35.66  
% 48.02/35.66  
% 48.02/35.66  %Foreground operators:
% 48.02/35.66  tff('#skF_5', type, '#skF_5': $i > $i).
% 48.02/35.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 48.02/35.66  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 48.02/35.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 48.02/35.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 48.02/35.66  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 48.02/35.66  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 48.02/35.66  tff('#skF_7', type, '#skF_7': $i).
% 48.02/35.66  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 48.02/35.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 48.02/35.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 48.02/35.66  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 48.02/35.66  tff('#skF_8', type, '#skF_8': $i).
% 48.02/35.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 48.02/35.66  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 48.02/35.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 48.02/35.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 48.02/35.66  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 48.02/35.66  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 48.02/35.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 48.02/35.66  tff('#skF_6', type, '#skF_6': $i > $i).
% 48.02/35.66  
% 48.26/35.70  tff(f_136, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 48.26/35.70  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 48.26/35.70  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 48.26/35.70  tff(f_118, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & r1_tarski(k2_relat_1(B), k1_relat_1(A))) => v2_funct_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_funct_1)).
% 48.26/35.70  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 48.26/35.70  tff(f_37, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 48.26/35.70  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 48.26/35.70  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 48.26/35.70  tff(f_90, axiom, (![A, B]: ((((v1_relat_1(A) & v1_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v1_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funct_1)).
% 48.26/35.70  tff(f_103, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 48.26/35.70  tff(c_62, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_136])).
% 48.26/35.70  tff(c_60, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_136])).
% 48.26/35.70  tff(c_18, plain, (![A_9, C_45]: (r2_hidden('#skF_4'(A_9, k2_relat_1(A_9), C_45), k1_relat_1(A_9)) | ~r2_hidden(C_45, k2_relat_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_63])).
% 48.26/35.70  tff(c_16, plain, (![A_9, C_45]: (k1_funct_1(A_9, '#skF_4'(A_9, k2_relat_1(A_9), C_45))=C_45 | ~r2_hidden(C_45, k2_relat_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_63])).
% 48.26/35.70  tff(c_54, plain, (v2_funct_1(k5_relat_1('#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 48.26/35.70  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 48.26/35.70  tff(c_50, plain, (~v2_funct_1('#skF_7') | ~v2_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_136])).
% 48.26/35.70  tff(c_65, plain, (~v2_funct_1('#skF_8')), inference(splitLeft, [status(thm)], [c_50])).
% 48.26/35.70  tff(c_58, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_136])).
% 48.26/35.70  tff(c_56, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_136])).
% 48.26/35.70  tff(c_52, plain, (k2_relat_1('#skF_8')=k1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_136])).
% 48.26/35.70  tff(c_305, plain, (![B_97, A_98]: (v2_funct_1(B_97) | ~r1_tarski(k2_relat_1(B_97), k1_relat_1(A_98)) | ~v2_funct_1(k5_relat_1(B_97, A_98)) | ~v1_funct_1(B_97) | ~v1_relat_1(B_97) | ~v1_funct_1(A_98) | ~v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_118])).
% 48.26/35.70  tff(c_314, plain, (![A_98]: (v2_funct_1('#skF_8') | ~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1(A_98)) | ~v2_funct_1(k5_relat_1('#skF_8', A_98)) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~v1_funct_1(A_98) | ~v1_relat_1(A_98))), inference(superposition, [status(thm), theory('equality')], [c_52, c_305])).
% 48.26/35.70  tff(c_318, plain, (![A_98]: (v2_funct_1('#skF_8') | ~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1(A_98)) | ~v2_funct_1(k5_relat_1('#skF_8', A_98)) | ~v1_funct_1(A_98) | ~v1_relat_1(A_98))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_314])).
% 48.26/35.70  tff(c_320, plain, (![A_99]: (~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1(A_99)) | ~v2_funct_1(k5_relat_1('#skF_8', A_99)) | ~v1_funct_1(A_99) | ~v1_relat_1(A_99))), inference(negUnitSimplification, [status(thm)], [c_65, c_318])).
% 48.26/35.70  tff(c_330, plain, (~v2_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_6, c_320])).
% 48.26/35.70  tff(c_336, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_54, c_330])).
% 48.26/35.70  tff(c_337, plain, (~v2_funct_1('#skF_7')), inference(splitRight, [status(thm)], [c_50])).
% 48.26/35.70  tff(c_40, plain, (![A_49]: (r2_hidden('#skF_5'(A_49), k1_relat_1(A_49)) | v2_funct_1(A_49) | ~v1_funct_1(A_49) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_78])).
% 48.26/35.70  tff(c_36, plain, (![A_49]: (k1_funct_1(A_49, '#skF_5'(A_49))=k1_funct_1(A_49, '#skF_6'(A_49)) | v2_funct_1(A_49) | ~v1_funct_1(A_49) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_78])).
% 48.26/35.70  tff(c_439, plain, (![A_116, C_117]: (r2_hidden('#skF_4'(A_116, k2_relat_1(A_116), C_117), k1_relat_1(A_116)) | ~r2_hidden(C_117, k2_relat_1(A_116)) | ~v1_funct_1(A_116) | ~v1_relat_1(A_116))), inference(cnfTransformation, [status(thm)], [f_63])).
% 48.26/35.70  tff(c_445, plain, (![C_117]: (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_117), k1_relat_1('#skF_8')) | ~r2_hidden(C_117, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_439])).
% 48.26/35.70  tff(c_447, plain, (![C_117]: (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_117), k1_relat_1('#skF_8')) | ~r2_hidden(C_117, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_445])).
% 48.26/35.70  tff(c_449, plain, (![A_119, C_120]: (k1_funct_1(A_119, '#skF_4'(A_119, k2_relat_1(A_119), C_120))=C_120 | ~r2_hidden(C_120, k2_relat_1(A_119)) | ~v1_funct_1(A_119) | ~v1_relat_1(A_119))), inference(cnfTransformation, [status(thm)], [f_63])).
% 48.26/35.70  tff(c_465, plain, (![C_120]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_120))=C_120 | ~r2_hidden(C_120, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_449])).
% 48.26/35.70  tff(c_471, plain, (![C_120]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_120))=C_120 | ~r2_hidden(C_120, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_465])).
% 48.26/35.70  tff(c_8, plain, (![A_3, B_4]: (v1_relat_1(k5_relat_1(A_3, B_4)) | ~v1_relat_1(B_4) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 48.26/35.70  tff(c_379, plain, (![A_110, B_111]: (k10_relat_1(A_110, k1_relat_1(B_111))=k1_relat_1(k5_relat_1(A_110, B_111)) | ~v1_relat_1(B_111) | ~v1_relat_1(A_110))), inference(cnfTransformation, [status(thm)], [f_48])).
% 48.26/35.70  tff(c_343, plain, (![A_100]: (k10_relat_1(A_100, k2_relat_1(A_100))=k1_relat_1(A_100) | ~v1_relat_1(A_100))), inference(cnfTransformation, [status(thm)], [f_41])).
% 48.26/35.70  tff(c_352, plain, (k10_relat_1('#skF_8', k1_relat_1('#skF_7'))=k1_relat_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_52, c_343])).
% 48.26/35.70  tff(c_356, plain, (k10_relat_1('#skF_8', k1_relat_1('#skF_7'))=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_352])).
% 48.26/35.70  tff(c_385, plain, (k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k1_relat_1('#skF_8') | ~v1_relat_1('#skF_7') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_379, c_356])).
% 48.26/35.70  tff(c_394, plain, (k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_385])).
% 48.26/35.70  tff(c_12, plain, (![A_6, B_8]: (k10_relat_1(A_6, k1_relat_1(B_8))=k1_relat_1(k5_relat_1(A_6, B_8)) | ~v1_relat_1(B_8) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 48.26/35.70  tff(c_401, plain, (![A_6]: (k1_relat_1(k5_relat_1(A_6, k5_relat_1('#skF_8', '#skF_7')))=k10_relat_1(A_6, k1_relat_1('#skF_8')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(A_6))), inference(superposition, [status(thm), theory('equality')], [c_394, c_12])).
% 48.26/35.70  tff(c_489, plain, (~v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(splitLeft, [status(thm)], [c_401])).
% 48.26/35.70  tff(c_492, plain, (~v1_relat_1('#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_8, c_489])).
% 48.26/35.70  tff(c_496, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_492])).
% 48.26/35.70  tff(c_498, plain, (v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(splitRight, [status(thm)], [c_401])).
% 48.26/35.70  tff(c_42, plain, (![A_56, B_57]: (v1_funct_1(k5_relat_1(A_56, B_57)) | ~v1_funct_1(B_57) | ~v1_relat_1(B_57) | ~v1_funct_1(A_56) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_90])).
% 48.26/35.70  tff(c_536, plain, (![B_127, A_128]: (v2_funct_1(B_127) | ~r1_tarski(k2_relat_1(B_127), k1_relat_1(A_128)) | ~v2_funct_1(k5_relat_1(B_127, A_128)) | ~v1_funct_1(B_127) | ~v1_relat_1(B_127) | ~v1_funct_1(A_128) | ~v1_relat_1(A_128))), inference(cnfTransformation, [status(thm)], [f_118])).
% 48.26/35.70  tff(c_542, plain, (![B_127]: (v2_funct_1(B_127) | ~r1_tarski(k2_relat_1(B_127), k1_relat_1('#skF_8')) | ~v2_funct_1(k5_relat_1(B_127, k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(B_127) | ~v1_relat_1(B_127) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_394, c_536])).
% 48.26/35.70  tff(c_547, plain, (![B_127]: (v2_funct_1(B_127) | ~r1_tarski(k2_relat_1(B_127), k1_relat_1('#skF_8')) | ~v2_funct_1(k5_relat_1(B_127, k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(B_127) | ~v1_relat_1(B_127) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_498, c_542])).
% 48.26/35.70  tff(c_564, plain, (~v1_funct_1(k5_relat_1('#skF_8', '#skF_7'))), inference(splitLeft, [status(thm)], [c_547])).
% 48.26/35.70  tff(c_567, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_42, c_564])).
% 48.26/35.70  tff(c_571, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_62, c_60, c_567])).
% 48.26/35.70  tff(c_573, plain, (v1_funct_1(k5_relat_1('#skF_8', '#skF_7'))), inference(splitRight, [status(thm)], [c_547])).
% 48.26/35.70  tff(c_626, plain, (![C_143, B_144, A_145]: (k1_funct_1(k5_relat_1(C_143, B_144), A_145)=k1_funct_1(B_144, k1_funct_1(C_143, A_145)) | ~r2_hidden(A_145, k1_relat_1(k5_relat_1(C_143, B_144))) | ~v1_funct_1(C_143) | ~v1_relat_1(C_143) | ~v1_funct_1(B_144) | ~v1_relat_1(B_144))), inference(cnfTransformation, [status(thm)], [f_103])).
% 48.26/35.70  tff(c_652, plain, (![A_145]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), A_145)=k1_funct_1('#skF_7', k1_funct_1('#skF_8', A_145)) | ~r2_hidden(A_145, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_394, c_626])).
% 48.26/35.70  tff(c_677, plain, (![A_148]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), A_148)=k1_funct_1('#skF_7', k1_funct_1('#skF_8', A_148)) | ~r2_hidden(A_148, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_652])).
% 48.26/35.70  tff(c_765, plain, (![C_150]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_150))=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_150))) | ~r2_hidden(C_150, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_447, c_677])).
% 48.26/35.70  tff(c_14, plain, (![A_9, D_48]: (r2_hidden(k1_funct_1(A_9, D_48), k2_relat_1(A_9)) | ~r2_hidden(D_48, k1_relat_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_63])).
% 48.26/35.70  tff(c_777, plain, (![C_150]: (r2_hidden(k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_150))), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_150), k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden(C_150, k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_765, c_14])).
% 48.26/35.70  tff(c_1014, plain, (![C_166]: (r2_hidden(k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_166))), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_166), k1_relat_1('#skF_8')) | ~r2_hidden(C_166, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_498, c_573, c_394, c_777])).
% 48.26/35.70  tff(c_1093, plain, (![C_172]: (r2_hidden(k1_funct_1('#skF_7', C_172), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_172), k1_relat_1('#skF_8')) | ~r2_hidden(C_172, k1_relat_1('#skF_7')) | ~r2_hidden(C_172, k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_471, c_1014])).
% 48.26/35.70  tff(c_1098, plain, (![C_173]: (r2_hidden(k1_funct_1('#skF_7', C_173), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden(C_173, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_447, c_1093])).
% 48.26/35.70  tff(c_1108, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_6'('#skF_7')), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7')) | v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_36, c_1098])).
% 48.26/35.70  tff(c_1112, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_6'('#skF_7')), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7')) | v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1108])).
% 48.26/35.70  tff(c_1113, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_6'('#skF_7')), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_337, c_1112])).
% 48.26/35.70  tff(c_1114, plain, (~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_1113])).
% 48.26/35.70  tff(c_1117, plain, (v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_40, c_1114])).
% 48.26/35.70  tff(c_1120, plain, (v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1117])).
% 48.26/35.70  tff(c_1122, plain, $false, inference(negUnitSimplification, [status(thm)], [c_337, c_1120])).
% 48.26/35.70  tff(c_1124, plain, (r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_1113])).
% 48.26/35.70  tff(c_38, plain, (![A_49]: (r2_hidden('#skF_6'(A_49), k1_relat_1(A_49)) | v2_funct_1(A_49) | ~v1_funct_1(A_49) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_78])).
% 48.26/35.70  tff(c_338, plain, (v2_funct_1('#skF_8')), inference(splitRight, [status(thm)], [c_50])).
% 48.26/35.70  tff(c_369, plain, (![A_105]: ('#skF_5'(A_105)!='#skF_6'(A_105) | v2_funct_1(A_105) | ~v1_funct_1(A_105) | ~v1_relat_1(A_105))), inference(cnfTransformation, [status(thm)], [f_78])).
% 48.26/35.70  tff(c_372, plain, ('#skF_5'('#skF_7')!='#skF_6'('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_369, c_337])).
% 48.26/35.70  tff(c_375, plain, ('#skF_5'('#skF_7')!='#skF_6'('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_372])).
% 48.26/35.70  tff(c_30, plain, (![A_9, B_31]: (r2_hidden('#skF_2'(A_9, B_31), k1_relat_1(A_9)) | r2_hidden('#skF_3'(A_9, B_31), B_31) | k2_relat_1(A_9)=B_31 | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_63])).
% 48.26/35.70  tff(c_550, plain, (![A_129, B_130]: (k1_funct_1(A_129, '#skF_2'(A_129, B_130))='#skF_1'(A_129, B_130) | r2_hidden('#skF_3'(A_129, B_130), B_130) | k2_relat_1(A_129)=B_130 | ~v1_funct_1(A_129) | ~v1_relat_1(A_129))), inference(cnfTransformation, [status(thm)], [f_63])).
% 48.26/35.70  tff(c_1018, plain, (![A_167, B_168]: (r2_hidden('#skF_1'(A_167, B_168), k2_relat_1(A_167)) | ~r2_hidden('#skF_2'(A_167, B_168), k1_relat_1(A_167)) | ~v1_funct_1(A_167) | ~v1_relat_1(A_167) | r2_hidden('#skF_3'(A_167, B_168), B_168) | k2_relat_1(A_167)=B_168 | ~v1_funct_1(A_167) | ~v1_relat_1(A_167))), inference(superposition, [status(thm), theory('equality')], [c_550, c_14])).
% 48.26/35.70  tff(c_1030, plain, (![A_169, B_170]: (r2_hidden('#skF_1'(A_169, B_170), k2_relat_1(A_169)) | r2_hidden('#skF_3'(A_169, B_170), B_170) | k2_relat_1(A_169)=B_170 | ~v1_funct_1(A_169) | ~v1_relat_1(A_169))), inference(resolution, [status(thm)], [c_30, c_1018])).
% 48.26/35.70  tff(c_1054, plain, (![B_170]: (r2_hidden('#skF_1'('#skF_8', B_170), k1_relat_1('#skF_7')) | r2_hidden('#skF_3'('#skF_8', B_170), B_170) | k2_relat_1('#skF_8')=B_170 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_1030])).
% 48.26/35.70  tff(c_1065, plain, (![B_171]: (r2_hidden('#skF_1'('#skF_8', B_171), k1_relat_1('#skF_7')) | r2_hidden('#skF_3'('#skF_8', B_171), B_171) | k1_relat_1('#skF_7')=B_171)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_1054])).
% 48.26/35.70  tff(c_669, plain, (![A_145]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), A_145)=k1_funct_1('#skF_7', k1_funct_1('#skF_8', A_145)) | ~r2_hidden(A_145, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_652])).
% 48.26/35.70  tff(c_1091, plain, (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_3'('#skF_8', k1_relat_1('#skF_8')))=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_3'('#skF_8', k1_relat_1('#skF_8')))) | r2_hidden('#skF_1'('#skF_8', k1_relat_1('#skF_8')), k1_relat_1('#skF_7')) | k1_relat_1('#skF_7')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_1065, c_669])).
% 48.26/35.70  tff(c_1186, plain, (k1_relat_1('#skF_7')=k1_relat_1('#skF_8')), inference(splitLeft, [status(thm)], [c_1091])).
% 48.26/35.70  tff(c_1224, plain, (r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_8')) | v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1186, c_38])).
% 48.26/35.70  tff(c_1242, plain, (r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_8')) | v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1224])).
% 48.26/35.70  tff(c_1243, plain, (r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_337, c_1242])).
% 48.26/35.70  tff(c_1296, plain, (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_6'('#skF_7'))=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_6'('#skF_7')))), inference(resolution, [status(thm)], [c_1243, c_669])).
% 48.26/35.70  tff(c_1221, plain, (r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_8')) | v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1186, c_40])).
% 48.26/35.70  tff(c_1239, plain, (r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_8')) | v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1221])).
% 48.26/35.70  tff(c_1240, plain, (r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_337, c_1239])).
% 48.26/35.70  tff(c_1292, plain, (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_5'('#skF_7'))=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_5'('#skF_7')))), inference(resolution, [status(thm)], [c_1240, c_669])).
% 48.26/35.70  tff(c_32, plain, (![C_55, B_54, A_49]: (C_55=B_54 | k1_funct_1(A_49, C_55)!=k1_funct_1(A_49, B_54) | ~r2_hidden(C_55, k1_relat_1(A_49)) | ~r2_hidden(B_54, k1_relat_1(A_49)) | ~v2_funct_1(A_49) | ~v1_funct_1(A_49) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_78])).
% 48.26/35.70  tff(c_1594, plain, (![B_54]: (B_54='#skF_5'('#skF_7') | k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), B_54)!=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_5'('#skF_7'))) | ~r2_hidden('#skF_5'('#skF_7'), k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden(B_54, k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v2_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_1292, c_32])).
% 48.26/35.70  tff(c_2077, plain, (![B_209]: (B_209='#skF_5'('#skF_7') | k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), B_209)!=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_5'('#skF_7'))) | ~r2_hidden(B_209, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_498, c_573, c_54, c_394, c_1240, c_394, c_1594])).
% 48.26/35.70  tff(c_2083, plain, ('#skF_5'('#skF_7')='#skF_6'('#skF_7') | k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_5'('#skF_7')))!=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_6'('#skF_7'))) | ~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1296, c_2077])).
% 48.26/35.70  tff(c_2098, plain, ('#skF_5'('#skF_7')='#skF_6'('#skF_7') | k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_5'('#skF_7')))!=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_6'('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_1243, c_2083])).
% 48.26/35.70  tff(c_2099, plain, (k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_5'('#skF_7')))!=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_6'('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_375, c_2098])).
% 48.26/35.70  tff(c_1199, plain, (![C_117]: (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_8'), C_117), k1_relat_1('#skF_8')) | ~r2_hidden(C_117, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_1186, c_1186, c_447])).
% 48.26/35.70  tff(c_1201, plain, (k10_relat_1('#skF_8', k1_relat_1('#skF_8'))=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1186, c_356])).
% 48.26/35.70  tff(c_1321, plain, (k1_relat_1(k5_relat_1('#skF_8', '#skF_8'))=k1_relat_1('#skF_8') | ~v1_relat_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1201, c_12])).
% 48.26/35.70  tff(c_1330, plain, (k1_relat_1(k5_relat_1('#skF_8', '#skF_8'))=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_58, c_1321])).
% 48.26/35.70  tff(c_46, plain, (![C_61, B_59, A_58]: (k1_funct_1(k5_relat_1(C_61, B_59), A_58)=k1_funct_1(B_59, k1_funct_1(C_61, A_58)) | ~r2_hidden(A_58, k1_relat_1(k5_relat_1(C_61, B_59))) | ~v1_funct_1(C_61) | ~v1_relat_1(C_61) | ~v1_funct_1(B_59) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_103])).
% 48.26/35.70  tff(c_1346, plain, (![A_58]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_8'), A_58)=k1_funct_1('#skF_8', k1_funct_1('#skF_8', A_58)) | ~r2_hidden(A_58, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1330, c_46])).
% 48.26/35.70  tff(c_1684, plain, (![A_200]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_8'), A_200)=k1_funct_1('#skF_8', k1_funct_1('#skF_8', A_200)) | ~r2_hidden(A_200, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_58, c_56, c_1346])).
% 48.26/35.70  tff(c_1772, plain, (k1_funct_1(k5_relat_1('#skF_8', '#skF_8'), '#skF_6'('#skF_7'))=k1_funct_1('#skF_8', k1_funct_1('#skF_8', '#skF_6'('#skF_7')))), inference(resolution, [status(thm)], [c_1243, c_1684])).
% 48.26/35.70  tff(c_423, plain, (![A_113, D_114]: (r2_hidden(k1_funct_1(A_113, D_114), k2_relat_1(A_113)) | ~r2_hidden(D_114, k1_relat_1(A_113)) | ~v1_funct_1(A_113) | ~v1_relat_1(A_113))), inference(cnfTransformation, [status(thm)], [f_63])).
% 48.26/35.70  tff(c_429, plain, (![D_114]: (r2_hidden(k1_funct_1('#skF_8', D_114), k1_relat_1('#skF_7')) | ~r2_hidden(D_114, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_423])).
% 48.26/35.70  tff(c_431, plain, (![D_114]: (r2_hidden(k1_funct_1('#skF_8', D_114), k1_relat_1('#skF_7')) | ~r2_hidden(D_114, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_429])).
% 48.26/35.70  tff(c_1200, plain, (![D_114]: (r2_hidden(k1_funct_1('#skF_8', D_114), k1_relat_1('#skF_8')) | ~r2_hidden(D_114, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_1186, c_431])).
% 48.26/35.70  tff(c_1198, plain, (![C_120]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_8'), C_120))=C_120 | ~r2_hidden(C_120, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_1186, c_1186, c_471])).
% 48.26/35.70  tff(c_2142, plain, (![D_211]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_8'), k1_funct_1('#skF_8', D_211))=k1_funct_1('#skF_8', k1_funct_1('#skF_8', k1_funct_1('#skF_8', D_211))) | ~r2_hidden(D_211, k1_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_1200, c_1684])).
% 48.26/35.70  tff(c_4299, plain, (![C_280]: (k1_funct_1('#skF_8', k1_funct_1('#skF_8', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_8'), C_280))))=k1_funct_1(k5_relat_1('#skF_8', '#skF_8'), C_280) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_8'), C_280), k1_relat_1('#skF_8')) | ~r2_hidden(C_280, k1_relat_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_1198, c_2142])).
% 48.26/35.70  tff(c_72185, plain, (![C_1024]: (r2_hidden(k1_funct_1(k5_relat_1('#skF_8', '#skF_8'), C_1024), k1_relat_1('#skF_8')) | ~r2_hidden(k1_funct_1('#skF_8', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_8'), C_1024))), k1_relat_1('#skF_8')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_8'), C_1024), k1_relat_1('#skF_8')) | ~r2_hidden(C_1024, k1_relat_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_4299, c_1200])).
% 48.26/35.70  tff(c_73029, plain, (![C_1033]: (r2_hidden(k1_funct_1(k5_relat_1('#skF_8', '#skF_8'), C_1033), k1_relat_1('#skF_8')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_8'), C_1033), k1_relat_1('#skF_8')) | ~r2_hidden(C_1033, k1_relat_1('#skF_8')) | ~r2_hidden(k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_8'), C_1033)), k1_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_1200, c_72185])).
% 48.26/35.70  tff(c_73040, plain, (![C_1034]: (r2_hidden(k1_funct_1(k5_relat_1('#skF_8', '#skF_8'), C_1034), k1_relat_1('#skF_8')) | ~r2_hidden(C_1034, k1_relat_1('#skF_8')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_8'), C_1034), k1_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_1200, c_73029])).
% 48.26/35.70  tff(c_73122, plain, (r2_hidden(k1_funct_1('#skF_8', k1_funct_1('#skF_8', '#skF_6'('#skF_7'))), k1_relat_1('#skF_8')) | ~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_8')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_8'), '#skF_6'('#skF_7')), k1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1772, c_73040])).
% 48.26/35.70  tff(c_73164, plain, (r2_hidden(k1_funct_1('#skF_8', k1_funct_1('#skF_8', '#skF_6'('#skF_7'))), k1_relat_1('#skF_8')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_8'), '#skF_6'('#skF_7')), k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1243, c_73122])).
% 48.26/35.70  tff(c_73197, plain, (~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_8'), '#skF_6'('#skF_7')), k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_73164])).
% 48.26/35.70  tff(c_73200, plain, (~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_1199, c_73197])).
% 48.26/35.70  tff(c_73204, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1243, c_73200])).
% 48.26/35.70  tff(c_73206, plain, (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_8'), '#skF_6'('#skF_7')), k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_73164])).
% 48.26/35.70  tff(c_1773, plain, (k1_funct_1(k5_relat_1('#skF_8', '#skF_8'), '#skF_5'('#skF_7'))=k1_funct_1('#skF_8', k1_funct_1('#skF_8', '#skF_5'('#skF_7')))), inference(resolution, [status(thm)], [c_1240, c_1684])).
% 48.26/35.70  tff(c_73119, plain, (r2_hidden(k1_funct_1('#skF_8', k1_funct_1('#skF_8', '#skF_5'('#skF_7'))), k1_relat_1('#skF_8')) | ~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_8')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_8'), '#skF_5'('#skF_7')), k1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1773, c_73040])).
% 48.26/35.70  tff(c_73162, plain, (r2_hidden(k1_funct_1('#skF_8', k1_funct_1('#skF_8', '#skF_5'('#skF_7'))), k1_relat_1('#skF_8')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_8'), '#skF_5'('#skF_7')), k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1240, c_73119])).
% 48.26/35.70  tff(c_73171, plain, (~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_8'), '#skF_5'('#skF_7')), k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_73162])).
% 48.26/35.70  tff(c_73174, plain, (~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_1199, c_73171])).
% 48.26/35.70  tff(c_73178, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1240, c_73174])).
% 48.26/35.70  tff(c_73180, plain, (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_8'), '#skF_5'('#skF_7')), k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_73162])).
% 48.26/35.70  tff(c_73196, plain, (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_4'('#skF_8', k1_relat_1('#skF_8'), '#skF_5'('#skF_7')))=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_8'), '#skF_5'('#skF_7'))))), inference(resolution, [status(thm)], [c_73180, c_669])).
% 48.26/35.70  tff(c_585, plain, (![C_135, B_136, A_137]: (C_135=B_136 | k1_funct_1(A_137, C_135)!=k1_funct_1(A_137, B_136) | ~r2_hidden(C_135, k1_relat_1(A_137)) | ~r2_hidden(B_136, k1_relat_1(A_137)) | ~v2_funct_1(A_137) | ~v1_funct_1(A_137) | ~v1_relat_1(A_137))), inference(cnfTransformation, [status(thm)], [f_78])).
% 48.26/35.70  tff(c_597, plain, (![C_135, A_9, C_45]: (C_135='#skF_4'(A_9, k2_relat_1(A_9), C_45) | k1_funct_1(A_9, C_135)!=C_45 | ~r2_hidden(C_135, k1_relat_1(A_9)) | ~r2_hidden('#skF_4'(A_9, k2_relat_1(A_9), C_45), k1_relat_1(A_9)) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9) | ~r2_hidden(C_45, k2_relat_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(superposition, [status(thm), theory('equality')], [c_16, c_585])).
% 48.26/35.70  tff(c_71044, plain, (![A_1007, C_1008]: ('#skF_4'(A_1007, k2_relat_1(A_1007), k1_funct_1(A_1007, C_1008))=C_1008 | ~r2_hidden(C_1008, k1_relat_1(A_1007)) | ~r2_hidden('#skF_4'(A_1007, k2_relat_1(A_1007), k1_funct_1(A_1007, C_1008)), k1_relat_1(A_1007)) | ~v2_funct_1(A_1007) | ~v1_funct_1(A_1007) | ~v1_relat_1(A_1007) | ~r2_hidden(k1_funct_1(A_1007, C_1008), k2_relat_1(A_1007)) | ~v1_funct_1(A_1007) | ~v1_relat_1(A_1007))), inference(reflexivity, [status(thm), theory('equality')], [c_597])).
% 48.26/35.70  tff(c_71982, plain, (![A_1022, C_1023]: ('#skF_4'(A_1022, k2_relat_1(A_1022), k1_funct_1(A_1022, C_1023))=C_1023 | ~r2_hidden(C_1023, k1_relat_1(A_1022)) | ~v2_funct_1(A_1022) | ~r2_hidden(k1_funct_1(A_1022, C_1023), k2_relat_1(A_1022)) | ~v1_funct_1(A_1022) | ~v1_relat_1(A_1022))), inference(resolution, [status(thm)], [c_18, c_71044])).
% 48.26/35.70  tff(c_72160, plain, (![A_9, D_48]: ('#skF_4'(A_9, k2_relat_1(A_9), k1_funct_1(A_9, D_48))=D_48 | ~v2_funct_1(A_9) | ~r2_hidden(D_48, k1_relat_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(resolution, [status(thm)], [c_14, c_71982])).
% 48.26/35.70  tff(c_73513, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_8'), '#skF_5'('#skF_7')))))='#skF_4'('#skF_8', k1_relat_1('#skF_8'), '#skF_5'('#skF_7')) | ~v2_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_8'), '#skF_5'('#skF_7')), k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_73196, c_72160])).
% 48.26/35.70  tff(c_73546, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_8'), '#skF_5'('#skF_7')))))='#skF_4'('#skF_8', k1_relat_1('#skF_8'), '#skF_5'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_498, c_573, c_73180, c_394, c_54, c_73513])).
% 48.26/35.70  tff(c_75342, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), k1_funct_1('#skF_7', '#skF_5'('#skF_7')))='#skF_4'('#skF_8', k1_relat_1('#skF_8'), '#skF_5'('#skF_7')) | ~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1198, c_73546])).
% 48.26/35.70  tff(c_75357, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), k1_funct_1('#skF_7', '#skF_5'('#skF_7')))='#skF_4'('#skF_8', k1_relat_1('#skF_8'), '#skF_5'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1240, c_75342])).
% 48.26/35.70  tff(c_75377, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), k1_funct_1('#skF_7', '#skF_6'('#skF_7')))='#skF_4'('#skF_8', k1_relat_1('#skF_8'), '#skF_5'('#skF_7')) | v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_36, c_75357])).
% 48.26/35.70  tff(c_75391, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), k1_funct_1('#skF_7', '#skF_6'('#skF_7')))='#skF_4'('#skF_8', k1_relat_1('#skF_8'), '#skF_5'('#skF_7')) | v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_75377])).
% 48.26/35.70  tff(c_75392, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), k1_funct_1('#skF_7', '#skF_6'('#skF_7')))='#skF_4'('#skF_8', k1_relat_1('#skF_8'), '#skF_5'('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_337, c_75391])).
% 48.26/35.70  tff(c_73222, plain, (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_4'('#skF_8', k1_relat_1('#skF_8'), '#skF_6'('#skF_7')))=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_8'), '#skF_6'('#skF_7'))))), inference(resolution, [status(thm)], [c_73206, c_669])).
% 48.26/35.70  tff(c_73441, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_8'), '#skF_6'('#skF_7')))))='#skF_4'('#skF_8', k1_relat_1('#skF_8'), '#skF_6'('#skF_7')) | ~v2_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_8'), '#skF_6'('#skF_7')), k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_73222, c_72160])).
% 48.26/35.70  tff(c_73474, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_8'), '#skF_6'('#skF_7')))))='#skF_4'('#skF_8', k1_relat_1('#skF_8'), '#skF_6'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_498, c_573, c_73206, c_394, c_54, c_73441])).
% 48.26/35.70  tff(c_76478, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), k1_funct_1('#skF_7', '#skF_6'('#skF_7')))='#skF_4'('#skF_8', k1_relat_1('#skF_8'), '#skF_6'('#skF_7')) | ~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1198, c_73474])).
% 48.26/35.70  tff(c_76495, plain, ('#skF_4'('#skF_8', k1_relat_1('#skF_8'), '#skF_5'('#skF_7'))='#skF_4'('#skF_8', k1_relat_1('#skF_8'), '#skF_6'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1243, c_75392, c_76478])).
% 48.26/35.70  tff(c_76529, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_8'), '#skF_6'('#skF_7')))='#skF_5'('#skF_7') | ~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_76495, c_1198])).
% 48.26/35.70  tff(c_76548, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_8'), '#skF_6'('#skF_7')))='#skF_5'('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1240, c_76529])).
% 48.26/35.70  tff(c_1378, plain, (![D_184]: (r2_hidden(k1_funct_1('#skF_8', D_184), k1_relat_1('#skF_8')) | ~r2_hidden(D_184, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_1186, c_431])).
% 48.26/35.70  tff(c_1976, plain, (![D_207]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), k1_funct_1('#skF_8', D_207))=k1_funct_1('#skF_7', k1_funct_1('#skF_8', k1_funct_1('#skF_8', D_207))) | ~r2_hidden(D_207, k1_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_1378, c_669])).
% 48.26/35.70  tff(c_1998, plain, (![C_120]: (k1_funct_1('#skF_7', k1_funct_1('#skF_8', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_8'), C_120))))=k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), C_120) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_8'), C_120), k1_relat_1('#skF_8')) | ~r2_hidden(C_120, k1_relat_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_1198, c_1976])).
% 48.26/35.70  tff(c_76592, plain, (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_6'('#skF_7'))=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_5'('#skF_7'))) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_8'), '#skF_6'('#skF_7')), k1_relat_1('#skF_8')) | ~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_76548, c_1998])).
% 48.26/35.70  tff(c_76650, plain, (k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_5'('#skF_7')))=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_6'('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_1243, c_73206, c_1296, c_76592])).
% 48.26/35.70  tff(c_76652, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2099, c_76650])).
% 48.26/35.70  tff(c_76654, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_8')), inference(splitRight, [status(thm)], [c_1091])).
% 48.26/35.70  tff(c_76653, plain, (r2_hidden('#skF_1'('#skF_8', k1_relat_1('#skF_8')), k1_relat_1('#skF_7')) | k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_3'('#skF_8', k1_relat_1('#skF_8')))=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_3'('#skF_8', k1_relat_1('#skF_8'))))), inference(splitRight, [status(thm)], [c_1091])).
% 48.26/35.70  tff(c_76691, plain, (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_3'('#skF_8', k1_relat_1('#skF_8')))=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_3'('#skF_8', k1_relat_1('#skF_8'))))), inference(splitLeft, [status(thm)], [c_76653])).
% 48.26/35.70  tff(c_76703, plain, (r2_hidden(k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_3'('#skF_8', k1_relat_1('#skF_8')))), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_3'('#skF_8', k1_relat_1('#skF_8')), k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_76691, c_14])).
% 48.26/35.70  tff(c_76715, plain, (r2_hidden(k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_3'('#skF_8', k1_relat_1('#skF_8')))), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_3'('#skF_8', k1_relat_1('#skF_8')), k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_498, c_573, c_394, c_76703])).
% 48.26/35.70  tff(c_76717, plain, (~r2_hidden('#skF_3'('#skF_8', k1_relat_1('#skF_8')), k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_76715])).
% 48.26/35.70  tff(c_76733, plain, (r2_hidden('#skF_2'('#skF_8', k1_relat_1('#skF_8')), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_30, c_76717])).
% 48.26/35.70  tff(c_76753, plain, (r2_hidden('#skF_2'('#skF_8', k1_relat_1('#skF_8')), k1_relat_1('#skF_8')) | k1_relat_1('#skF_7')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_76733])).
% 48.26/35.70  tff(c_76754, plain, (r2_hidden('#skF_2'('#skF_8', k1_relat_1('#skF_8')), k1_relat_1('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_76654, c_76753])).
% 48.26/35.70  tff(c_28, plain, (![A_9, B_31]: (k1_funct_1(A_9, '#skF_2'(A_9, B_31))='#skF_1'(A_9, B_31) | r2_hidden('#skF_3'(A_9, B_31), B_31) | k2_relat_1(A_9)=B_31 | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_63])).
% 48.26/35.70  tff(c_76730, plain, (k1_funct_1('#skF_8', '#skF_2'('#skF_8', k1_relat_1('#skF_8')))='#skF_1'('#skF_8', k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_28, c_76717])).
% 48.26/35.70  tff(c_76749, plain, (k1_funct_1('#skF_8', '#skF_2'('#skF_8', k1_relat_1('#skF_8')))='#skF_1'('#skF_8', k1_relat_1('#skF_8')) | k1_relat_1('#skF_7')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_76730])).
% 48.26/35.70  tff(c_76750, plain, (k1_funct_1('#skF_8', '#skF_2'('#skF_8', k1_relat_1('#skF_8')))='#skF_1'('#skF_8', k1_relat_1('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_76654, c_76749])).
% 48.26/35.70  tff(c_76831, plain, (![C_55]: (C_55='#skF_2'('#skF_8', k1_relat_1('#skF_8')) | k1_funct_1('#skF_8', C_55)!='#skF_1'('#skF_8', k1_relat_1('#skF_8')) | ~r2_hidden(C_55, k1_relat_1('#skF_8')) | ~r2_hidden('#skF_2'('#skF_8', k1_relat_1('#skF_8')), k1_relat_1('#skF_8')) | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_76750, c_32])).
% 48.26/35.70  tff(c_76898, plain, (![C_1097]: (C_1097='#skF_2'('#skF_8', k1_relat_1('#skF_8')) | k1_funct_1('#skF_8', C_1097)!='#skF_1'('#skF_8', k1_relat_1('#skF_8')) | ~r2_hidden(C_1097, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_338, c_76754, c_76831])).
% 48.26/35.70  tff(c_76998, plain, (![C_1098]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_1098)='#skF_2'('#skF_8', k1_relat_1('#skF_8')) | k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_1098))!='#skF_1'('#skF_8', k1_relat_1('#skF_8')) | ~r2_hidden(C_1098, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_447, c_76898])).
% 48.26/35.70  tff(c_77120, plain, (![C_1106]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_1106)='#skF_2'('#skF_8', k1_relat_1('#skF_8')) | C_1106!='#skF_1'('#skF_8', k1_relat_1('#skF_8')) | ~r2_hidden(C_1106, k1_relat_1('#skF_7')) | ~r2_hidden(C_1106, k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_471, c_76998])).
% 48.26/35.70  tff(c_77171, plain, ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))='#skF_2'('#skF_8', k1_relat_1('#skF_8')) | '#skF_1'('#skF_8', k1_relat_1('#skF_8'))!='#skF_6'('#skF_7') | ~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7')) | v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_38, c_77120])).
% 48.26/35.70  tff(c_77207, plain, ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))='#skF_2'('#skF_8', k1_relat_1('#skF_8')) | '#skF_1'('#skF_8', k1_relat_1('#skF_8'))!='#skF_6'('#skF_7') | ~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7')) | v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_77171])).
% 48.26/35.70  tff(c_77208, plain, ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))='#skF_2'('#skF_8', k1_relat_1('#skF_8')) | '#skF_1'('#skF_8', k1_relat_1('#skF_8'))!='#skF_6'('#skF_7') | ~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_337, c_77207])).
% 48.26/35.70  tff(c_77239, plain, (~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_77208])).
% 48.26/35.70  tff(c_77242, plain, (v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_38, c_77239])).
% 48.26/35.70  tff(c_77245, plain, (v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_77242])).
% 48.26/35.70  tff(c_77247, plain, $false, inference(negUnitSimplification, [status(thm)], [c_337, c_77245])).
% 48.26/35.70  tff(c_77249, plain, (r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_77208])).
% 48.26/35.70  tff(c_78360, plain, (![C_1147, A_1148, B_1149]: (C_1147='#skF_2'(A_1148, B_1149) | k1_funct_1(A_1148, C_1147)!='#skF_1'(A_1148, B_1149) | ~r2_hidden(C_1147, k1_relat_1(A_1148)) | ~r2_hidden('#skF_2'(A_1148, B_1149), k1_relat_1(A_1148)) | ~v2_funct_1(A_1148) | ~v1_funct_1(A_1148) | ~v1_relat_1(A_1148) | r2_hidden('#skF_3'(A_1148, B_1149), B_1149) | k2_relat_1(A_1148)=B_1149 | ~v1_funct_1(A_1148) | ~v1_relat_1(A_1148))), inference(superposition, [status(thm), theory('equality')], [c_28, c_585])).
% 48.26/35.70  tff(c_78394, plain, (![C_120, B_1149]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_120)='#skF_2'('#skF_8', B_1149) | C_120!='#skF_1'('#skF_8', B_1149) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_120), k1_relat_1('#skF_8')) | ~r2_hidden('#skF_2'('#skF_8', B_1149), k1_relat_1('#skF_8')) | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | r2_hidden('#skF_3'('#skF_8', B_1149), B_1149) | k2_relat_1('#skF_8')=B_1149 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(C_120, k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_471, c_78360])).
% 48.26/35.70  tff(c_92604, plain, (![C_1410, B_1411]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_1410)='#skF_2'('#skF_8', B_1411) | C_1410!='#skF_1'('#skF_8', B_1411) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_1410), k1_relat_1('#skF_8')) | ~r2_hidden('#skF_2'('#skF_8', B_1411), k1_relat_1('#skF_8')) | r2_hidden('#skF_3'('#skF_8', B_1411), B_1411) | k1_relat_1('#skF_7')=B_1411 | ~r2_hidden(C_1410, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_58, c_56, c_338, c_78394])).
% 48.26/35.70  tff(c_92737, plain, (![C_1414, B_1415]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_1414)='#skF_2'('#skF_8', B_1415) | C_1414!='#skF_1'('#skF_8', B_1415) | ~r2_hidden('#skF_2'('#skF_8', B_1415), k1_relat_1('#skF_8')) | r2_hidden('#skF_3'('#skF_8', B_1415), B_1415) | k1_relat_1('#skF_7')=B_1415 | ~r2_hidden(C_1414, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_447, c_92604])).
% 48.26/35.70  tff(c_92753, plain, (![C_1414, B_31]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_1414)='#skF_2'('#skF_8', B_31) | C_1414!='#skF_1'('#skF_8', B_31) | k1_relat_1('#skF_7')=B_31 | ~r2_hidden(C_1414, k1_relat_1('#skF_7')) | r2_hidden('#skF_3'('#skF_8', B_31), B_31) | k2_relat_1('#skF_8')=B_31 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_30, c_92737])).
% 48.26/35.70  tff(c_92933, plain, (![C_1417, B_1418]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), C_1417)='#skF_2'('#skF_8', B_1418) | C_1417!='#skF_1'('#skF_8', B_1418) | ~r2_hidden(C_1417, k1_relat_1('#skF_7')) | r2_hidden('#skF_3'('#skF_8', B_1418), B_1418) | k1_relat_1('#skF_7')=B_1418)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_92753])).
% 48.26/35.70  tff(c_93007, plain, (![B_1418]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))='#skF_2'('#skF_8', B_1418) | '#skF_5'('#skF_7')!='#skF_1'('#skF_8', B_1418) | r2_hidden('#skF_3'('#skF_8', B_1418), B_1418) | k1_relat_1('#skF_7')=B_1418 | v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_40, c_92933])).
% 48.26/35.70  tff(c_93062, plain, (![B_1418]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))='#skF_2'('#skF_8', B_1418) | '#skF_5'('#skF_7')!='#skF_1'('#skF_8', B_1418) | r2_hidden('#skF_3'('#skF_8', B_1418), B_1418) | k1_relat_1('#skF_7')=B_1418 | v2_funct_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_93007])).
% 48.26/35.70  tff(c_93069, plain, (![B_1419]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))='#skF_2'('#skF_8', B_1419) | '#skF_5'('#skF_7')!='#skF_1'('#skF_8', B_1419) | r2_hidden('#skF_3'('#skF_8', B_1419), B_1419) | k1_relat_1('#skF_7')=B_1419)), inference(negUnitSimplification, [status(thm)], [c_337, c_93062])).
% 48.26/35.70  tff(c_93116, plain, (![B_1419]: (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_relat_1('#skF_8')) | r2_hidden('#skF_3'('#skF_8', B_1419), B_1419) | k2_relat_1('#skF_8')=B_1419 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | '#skF_5'('#skF_7')!='#skF_1'('#skF_8', B_1419) | r2_hidden('#skF_3'('#skF_8', B_1419), B_1419) | k1_relat_1('#skF_7')=B_1419)), inference(superposition, [status(thm), theory('equality')], [c_93069, c_30])).
% 48.26/35.70  tff(c_93188, plain, (![B_1419]: (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_relat_1('#skF_8')) | '#skF_5'('#skF_7')!='#skF_1'('#skF_8', B_1419) | r2_hidden('#skF_3'('#skF_8', B_1419), B_1419) | k1_relat_1('#skF_7')=B_1419)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_93116])).
% 48.26/35.70  tff(c_94014, plain, (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_93188])).
% 48.26/35.70  tff(c_94023, plain, (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')))=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))))), inference(resolution, [status(thm)], [c_94014, c_669])).
% 48.26/35.70  tff(c_442, plain, (![C_117]: (r2_hidden('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_117), k1_relat_1('#skF_8')) | ~r2_hidden(C_117, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_394, c_439])).
% 48.26/35.70  tff(c_499, plain, (~v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(splitLeft, [status(thm)], [c_442])).
% 48.26/35.70  tff(c_501, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_498, c_499])).
% 48.26/35.70  tff(c_502, plain, (![C_117]: (~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | r2_hidden('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_117), k1_relat_1('#skF_8')) | ~r2_hidden(C_117, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(splitRight, [status(thm)], [c_442])).
% 48.26/35.70  tff(c_624, plain, (![C_117]: (r2_hidden('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_117), k1_relat_1('#skF_8')) | ~r2_hidden(C_117, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_573, c_502])).
% 48.26/35.70  tff(c_79320, plain, (![C_1188]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_1188))=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_1188))) | ~r2_hidden(C_1188, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(resolution, [status(thm)], [c_624, c_677])).
% 48.26/35.70  tff(c_79343, plain, (![C_1188]: (k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_1188)))=C_1188 | ~r2_hidden(C_1188, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden(C_1188, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_79320, c_16])).
% 48.26/35.70  tff(c_79374, plain, (![C_1189]: (k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_1189)))=C_1189 | ~r2_hidden(C_1189, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_498, c_573, c_79343])).
% 48.26/35.70  tff(c_79395, plain, (![C_1189]: (r2_hidden(C_1189, k2_relat_1('#skF_7')) | ~r2_hidden(k1_funct_1('#skF_8', '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_1189)), k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(C_1189, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_79374, c_14])).
% 48.26/35.70  tff(c_79519, plain, (![C_1193]: (r2_hidden(C_1193, k2_relat_1('#skF_7')) | ~r2_hidden(k1_funct_1('#skF_8', '#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_1193)), k1_relat_1('#skF_7')) | ~r2_hidden(C_1193, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_79395])).
% 48.26/35.70  tff(c_79524, plain, (![C_1194]: (r2_hidden(C_1194, k2_relat_1('#skF_7')) | ~r2_hidden(C_1194, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), C_1194), k1_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_431, c_79519])).
% 48.26/35.70  tff(c_79529, plain, (![C_1195]: (r2_hidden(C_1195, k2_relat_1('#skF_7')) | ~r2_hidden(C_1195, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))), inference(resolution, [status(thm)], [c_624, c_79524])).
% 48.26/35.70  tff(c_79638, plain, (![D_48]: (r2_hidden(k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), D_48), k2_relat_1('#skF_7')) | ~r2_hidden(D_48, k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7')))), inference(resolution, [status(thm)], [c_14, c_79529])).
% 48.26/35.70  tff(c_79683, plain, (![D_48]: (r2_hidden(k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), D_48), k2_relat_1('#skF_7')) | ~r2_hidden(D_48, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_498, c_573, c_394, c_79638])).
% 48.26/35.70  tff(c_94030, plain, (r2_hidden(k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')))), k2_relat_1('#skF_7')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_94023, c_79683])).
% 48.26/35.70  tff(c_94060, plain, (r2_hidden(k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')))), k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_94014, c_94030])).
% 48.26/35.70  tff(c_79679, plain, (![A_9]: (r2_hidden('#skF_3'(A_9, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7')) | r2_hidden('#skF_2'(A_9, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k1_relat_1(A_9)) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(resolution, [status(thm)], [c_30, c_79529])).
% 48.26/35.70  tff(c_606, plain, (![A_138, B_139, D_140]: (r2_hidden('#skF_2'(A_138, B_139), k1_relat_1(A_138)) | k1_funct_1(A_138, D_140)!='#skF_3'(A_138, B_139) | ~r2_hidden(D_140, k1_relat_1(A_138)) | k2_relat_1(A_138)=B_139 | ~v1_funct_1(A_138) | ~v1_relat_1(A_138))), inference(cnfTransformation, [status(thm)], [f_63])).
% 48.26/35.70  tff(c_612, plain, (![A_9, B_139, C_45]: (r2_hidden('#skF_2'(A_9, B_139), k1_relat_1(A_9)) | C_45!='#skF_3'(A_9, B_139) | ~r2_hidden('#skF_4'(A_9, k2_relat_1(A_9), C_45), k1_relat_1(A_9)) | k2_relat_1(A_9)=B_139 | ~v1_funct_1(A_9) | ~v1_relat_1(A_9) | ~r2_hidden(C_45, k2_relat_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(superposition, [status(thm), theory('equality')], [c_16, c_606])).
% 48.26/35.70  tff(c_91984, plain, (![A_1396, B_1397]: (r2_hidden('#skF_2'(A_1396, B_1397), k1_relat_1(A_1396)) | ~r2_hidden('#skF_4'(A_1396, k2_relat_1(A_1396), '#skF_3'(A_1396, B_1397)), k1_relat_1(A_1396)) | k2_relat_1(A_1396)=B_1397 | ~v1_funct_1(A_1396) | ~v1_relat_1(A_1396) | ~r2_hidden('#skF_3'(A_1396, B_1397), k2_relat_1(A_1396)) | ~v1_funct_1(A_1396) | ~v1_relat_1(A_1396))), inference(reflexivity, [status(thm), theory('equality')], [c_612])).
% 48.26/35.70  tff(c_92006, plain, (![A_1398, B_1399]: (r2_hidden('#skF_2'(A_1398, B_1399), k1_relat_1(A_1398)) | k2_relat_1(A_1398)=B_1399 | ~r2_hidden('#skF_3'(A_1398, B_1399), k2_relat_1(A_1398)) | ~v1_funct_1(A_1398) | ~v1_relat_1(A_1398))), inference(resolution, [status(thm)], [c_18, c_91984])).
% 48.26/35.70  tff(c_92018, plain, (r2_hidden('#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k1_relat_1('#skF_7')) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_79679, c_92006])).
% 48.26/35.70  tff(c_92098, plain, (r2_hidden('#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k1_relat_1('#skF_7')) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_92018])).
% 48.26/35.70  tff(c_92149, plain, (k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7')), inference(splitLeft, [status(thm)], [c_92098])).
% 48.26/35.70  tff(c_595, plain, (![B_136, A_9, C_45]: (B_136='#skF_4'(A_9, k2_relat_1(A_9), C_45) | k1_funct_1(A_9, B_136)!=C_45 | ~r2_hidden('#skF_4'(A_9, k2_relat_1(A_9), C_45), k1_relat_1(A_9)) | ~r2_hidden(B_136, k1_relat_1(A_9)) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9) | ~r2_hidden(C_45, k2_relat_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(superposition, [status(thm), theory('equality')], [c_16, c_585])).
% 48.26/35.70  tff(c_93385, plain, (![A_1422, B_1423]: ('#skF_4'(A_1422, k2_relat_1(A_1422), k1_funct_1(A_1422, B_1423))=B_1423 | ~r2_hidden('#skF_4'(A_1422, k2_relat_1(A_1422), k1_funct_1(A_1422, B_1423)), k1_relat_1(A_1422)) | ~r2_hidden(B_1423, k1_relat_1(A_1422)) | ~v2_funct_1(A_1422) | ~v1_funct_1(A_1422) | ~v1_relat_1(A_1422) | ~r2_hidden(k1_funct_1(A_1422, B_1423), k2_relat_1(A_1422)) | ~v1_funct_1(A_1422) | ~v1_relat_1(A_1422))), inference(reflexivity, [status(thm), theory('equality')], [c_595])).
% 48.26/35.70  tff(c_94520, plain, (![A_1435, B_1436]: ('#skF_4'(A_1435, k2_relat_1(A_1435), k1_funct_1(A_1435, B_1436))=B_1436 | ~r2_hidden(B_1436, k1_relat_1(A_1435)) | ~v2_funct_1(A_1435) | ~r2_hidden(k1_funct_1(A_1435, B_1436), k2_relat_1(A_1435)) | ~v1_funct_1(A_1435) | ~v1_relat_1(A_1435))), inference(resolution, [status(thm)], [c_18, c_93385])).
% 48.26/35.70  tff(c_94536, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v2_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden(k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')))), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_94023, c_94520])).
% 48.26/35.70  tff(c_94625, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1('#skF_7'), k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')))))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_498, c_573, c_94060, c_92149, c_54, c_94014, c_394, c_94023, c_92149, c_94536])).
% 48.26/35.70  tff(c_95071, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1('#skF_7'), k1_funct_1('#skF_7', '#skF_5'('#skF_7')))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')) | ~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_471, c_94625])).
% 48.26/35.70  tff(c_95082, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1('#skF_7'), k1_funct_1('#skF_7', '#skF_5'('#skF_7')))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1124, c_95071])).
% 48.26/35.70  tff(c_95327, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1('#skF_7'), k1_funct_1('#skF_7', '#skF_6'('#skF_7')))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')) | v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_36, c_95082])).
% 48.26/35.70  tff(c_95337, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1('#skF_7'), k1_funct_1('#skF_7', '#skF_6'('#skF_7')))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')) | v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_95327])).
% 48.26/35.70  tff(c_95338, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1('#skF_7'), k1_funct_1('#skF_7', '#skF_6'('#skF_7')))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_337, c_95337])).
% 48.26/35.70  tff(c_93010, plain, (![B_1418]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))='#skF_2'('#skF_8', B_1418) | '#skF_1'('#skF_8', B_1418)!='#skF_6'('#skF_7') | r2_hidden('#skF_3'('#skF_8', B_1418), B_1418) | k1_relat_1('#skF_7')=B_1418 | v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_38, c_92933])).
% 48.26/35.70  tff(c_93066, plain, (![B_1418]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))='#skF_2'('#skF_8', B_1418) | '#skF_1'('#skF_8', B_1418)!='#skF_6'('#skF_7') | r2_hidden('#skF_3'('#skF_8', B_1418), B_1418) | k1_relat_1('#skF_7')=B_1418 | v2_funct_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_93010])).
% 48.26/35.70  tff(c_93514, plain, (![B_1424]: ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))='#skF_2'('#skF_8', B_1424) | '#skF_1'('#skF_8', B_1424)!='#skF_6'('#skF_7') | r2_hidden('#skF_3'('#skF_8', B_1424), B_1424) | k1_relat_1('#skF_7')=B_1424)), inference(negUnitSimplification, [status(thm)], [c_337, c_93066])).
% 48.26/35.70  tff(c_93567, plain, (![B_1424]: (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')), k1_relat_1('#skF_8')) | r2_hidden('#skF_3'('#skF_8', B_1424), B_1424) | k2_relat_1('#skF_8')=B_1424 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | '#skF_1'('#skF_8', B_1424)!='#skF_6'('#skF_7') | r2_hidden('#skF_3'('#skF_8', B_1424), B_1424) | k1_relat_1('#skF_7')=B_1424)), inference(superposition, [status(thm), theory('equality')], [c_93514, c_30])).
% 48.26/35.70  tff(c_93642, plain, (![B_1424]: (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')), k1_relat_1('#skF_8')) | '#skF_1'('#skF_8', B_1424)!='#skF_6'('#skF_7') | r2_hidden('#skF_3'('#skF_8', B_1424), B_1424) | k1_relat_1('#skF_7')=B_1424)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_93567])).
% 48.26/35.70  tff(c_94144, plain, (r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')), k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_93642])).
% 48.26/35.70  tff(c_94153, plain, (k1_funct_1(k5_relat_1('#skF_8', '#skF_7'), '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')))=k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))))), inference(resolution, [status(thm)], [c_94144, c_669])).
% 48.26/35.70  tff(c_94779, plain, (![A_1440, D_1441]: ('#skF_4'(A_1440, k2_relat_1(A_1440), k1_funct_1(A_1440, D_1441))=D_1441 | ~v2_funct_1(A_1440) | ~r2_hidden(D_1441, k1_relat_1(A_1440)) | ~v1_funct_1(A_1440) | ~v1_relat_1(A_1440))), inference(resolution, [status(thm)], [c_14, c_94520])).
% 48.26/35.70  tff(c_94805, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')), k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')))))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')) | ~v2_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')), k1_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_94153, c_94779])).
% 48.26/35.70  tff(c_94897, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1('#skF_7'), k1_funct_1('#skF_7', k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')))))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_498, c_573, c_94144, c_394, c_54, c_92149, c_94805])).
% 48.26/35.70  tff(c_96256, plain, ('#skF_4'(k5_relat_1('#skF_8', '#skF_7'), k2_relat_1('#skF_7'), k1_funct_1('#skF_7', '#skF_6'('#skF_7')))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')) | ~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_471, c_94897])).
% 48.26/35.70  tff(c_96267, plain, ('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7'))='#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_77249, c_95338, c_96256])).
% 48.26/35.70  tff(c_96289, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')))='#skF_5'('#skF_7') | ~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_96267, c_471])).
% 48.26/35.70  tff(c_96302, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')))='#skF_5'('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1124, c_96289])).
% 48.26/35.70  tff(c_96372, plain, ('#skF_5'('#skF_7')='#skF_6'('#skF_7') | ~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_96302, c_471])).
% 48.26/35.70  tff(c_96416, plain, ('#skF_5'('#skF_7')='#skF_6'('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_77249, c_96372])).
% 48.26/35.70  tff(c_96418, plain, $false, inference(negUnitSimplification, [status(thm)], [c_375, c_96416])).
% 48.26/35.70  tff(c_96420, plain, (~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_6'('#skF_7')), k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_93642])).
% 48.26/35.70  tff(c_96424, plain, (~r2_hidden('#skF_6'('#skF_7'), k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_447, c_96420])).
% 48.26/35.70  tff(c_96428, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77249, c_96424])).
% 48.26/35.70  tff(c_96430, plain, (~r2_hidden('#skF_4'('#skF_8', k1_relat_1('#skF_7'), '#skF_5'('#skF_7')), k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_93188])).
% 48.26/35.70  tff(c_96434, plain, (~r2_hidden('#skF_5'('#skF_7'), k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_447, c_96430])).
% 48.26/35.70  tff(c_96438, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1124, c_96434])).
% 48.26/35.70  tff(c_96440, plain, (k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))!=k2_relat_1('#skF_7')), inference(splitRight, [status(thm)], [c_92098])).
% 48.26/35.70  tff(c_96439, plain, (r2_hidden('#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_92098])).
% 48.26/35.70  tff(c_1027, plain, (![A_9, B_31]: (r2_hidden('#skF_1'(A_9, B_31), k2_relat_1(A_9)) | r2_hidden('#skF_3'(A_9, B_31), B_31) | k2_relat_1(A_9)=B_31 | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(resolution, [status(thm)], [c_30, c_1018])).
% 48.26/35.70  tff(c_79669, plain, (![A_9]: (r2_hidden('#skF_3'(A_9, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7')) | r2_hidden('#skF_1'(A_9, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1(A_9)) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(resolution, [status(thm)], [c_1027, c_79529])).
% 48.26/35.70  tff(c_808, plain, (![A_152, B_153, D_154]: (k1_funct_1(A_152, '#skF_2'(A_152, B_153))='#skF_1'(A_152, B_153) | k1_funct_1(A_152, D_154)!='#skF_3'(A_152, B_153) | ~r2_hidden(D_154, k1_relat_1(A_152)) | k2_relat_1(A_152)=B_153 | ~v1_funct_1(A_152) | ~v1_relat_1(A_152))), inference(cnfTransformation, [status(thm)], [f_63])).
% 48.26/35.70  tff(c_818, plain, (![A_9, B_153, C_45]: (k1_funct_1(A_9, '#skF_2'(A_9, B_153))='#skF_1'(A_9, B_153) | C_45!='#skF_3'(A_9, B_153) | ~r2_hidden('#skF_4'(A_9, k2_relat_1(A_9), C_45), k1_relat_1(A_9)) | k2_relat_1(A_9)=B_153 | ~v1_funct_1(A_9) | ~v1_relat_1(A_9) | ~r2_hidden(C_45, k2_relat_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(superposition, [status(thm), theory('equality')], [c_16, c_808])).
% 48.26/35.70  tff(c_96449, plain, (![A_1453, B_1454]: (k1_funct_1(A_1453, '#skF_2'(A_1453, B_1454))='#skF_1'(A_1453, B_1454) | ~r2_hidden('#skF_4'(A_1453, k2_relat_1(A_1453), '#skF_3'(A_1453, B_1454)), k1_relat_1(A_1453)) | k2_relat_1(A_1453)=B_1454 | ~v1_funct_1(A_1453) | ~v1_relat_1(A_1453) | ~r2_hidden('#skF_3'(A_1453, B_1454), k2_relat_1(A_1453)) | ~v1_funct_1(A_1453) | ~v1_relat_1(A_1453))), inference(reflexivity, [status(thm), theory('equality')], [c_818])).
% 48.26/35.70  tff(c_96471, plain, (![A_1455, B_1456]: (k1_funct_1(A_1455, '#skF_2'(A_1455, B_1456))='#skF_1'(A_1455, B_1456) | k2_relat_1(A_1455)=B_1456 | ~r2_hidden('#skF_3'(A_1455, B_1456), k2_relat_1(A_1455)) | ~v1_funct_1(A_1455) | ~v1_relat_1(A_1455))), inference(resolution, [status(thm)], [c_18, c_96449])).
% 48.26/35.70  tff(c_96479, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))='#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | r2_hidden('#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7')) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_79669, c_96471])).
% 48.26/35.70  tff(c_96561, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))='#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | r2_hidden('#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7')) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_96479])).
% 48.26/35.70  tff(c_96562, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))='#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | r2_hidden('#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_96440, c_96561])).
% 48.26/35.70  tff(c_97158, plain, (r2_hidden('#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_96562])).
% 48.26/35.70  tff(c_1104, plain, (![C_45]: (r2_hidden(C_45, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_45), k1_relat_1('#skF_7')) | ~r2_hidden(C_45, k2_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1098])).
% 48.26/35.70  tff(c_1125, plain, (![C_174]: (r2_hidden(C_174, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_174), k1_relat_1('#skF_7')) | ~r2_hidden(C_174, k2_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1104])).
% 48.26/35.70  tff(c_1129, plain, (![C_45]: (r2_hidden(C_45, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden(C_45, k2_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_18, c_1125])).
% 48.26/35.70  tff(c_1132, plain, (![C_45]: (r2_hidden(C_45, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden(C_45, k2_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1129])).
% 48.26/35.70  tff(c_26, plain, (![A_9, B_31]: (~r2_hidden('#skF_1'(A_9, B_31), B_31) | r2_hidden('#skF_3'(A_9, B_31), B_31) | k2_relat_1(A_9)=B_31 | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_63])).
% 48.26/35.70  tff(c_91895, plain, (![A_1388]: (r2_hidden('#skF_3'(A_1388, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7')) | ~r2_hidden('#skF_1'(A_1388, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1(A_1388) | ~v1_funct_1(A_1388) | ~v1_relat_1(A_1388))), inference(resolution, [status(thm)], [c_26, c_79529])).
% 48.26/35.70  tff(c_91926, plain, (![A_1388]: (r2_hidden('#skF_3'(A_1388, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7')) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1(A_1388) | ~v1_funct_1(A_1388) | ~v1_relat_1(A_1388) | ~r2_hidden('#skF_1'(A_1388, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_1132, c_91895])).
% 48.26/35.70  tff(c_96475, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))='#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden('#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_91926, c_96471])).
% 48.26/35.70  tff(c_96557, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))='#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7') | ~r2_hidden('#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_96475])).
% 48.26/35.70  tff(c_96558, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))='#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_96440, c_96557])).
% 48.26/35.70  tff(c_97160, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))='#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_97158, c_96558])).
% 48.26/35.70  tff(c_1097, plain, (![C_117]: (r2_hidden(k1_funct_1('#skF_7', C_117), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden(C_117, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_447, c_1093])).
% 48.26/35.70  tff(c_97177, plain, (r2_hidden('#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_97160, c_1097])).
% 48.26/35.70  tff(c_97212, plain, (r2_hidden('#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1(k5_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_96439, c_97177])).
% 48.26/35.70  tff(c_20, plain, (![A_9, B_31, D_44]: (~r2_hidden('#skF_1'(A_9, B_31), B_31) | k1_funct_1(A_9, D_44)!='#skF_3'(A_9, B_31) | ~r2_hidden(D_44, k1_relat_1(A_9)) | k2_relat_1(A_9)=B_31 | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_63])).
% 48.26/35.70  tff(c_97237, plain, (![D_44]: (k1_funct_1('#skF_7', D_44)!='#skF_3'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden(D_44, k1_relat_1('#skF_7')) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_97212, c_20])).
% 48.26/35.70  tff(c_97246, plain, (![D_44]: (k1_funct_1('#skF_7', D_44)!='#skF_3'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden(D_44, k1_relat_1('#skF_7')) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_97237])).
% 48.26/35.70  tff(c_97405, plain, (![D_1467]: (k1_funct_1('#skF_7', D_1467)!='#skF_3'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden(D_1467, k1_relat_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_96440, c_97246])).
% 48.26/35.70  tff(c_97423, plain, (![C_45]: (C_45!='#skF_3'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_45), k1_relat_1('#skF_7')) | ~r2_hidden(C_45, k2_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_97405])).
% 48.26/35.70  tff(c_97485, plain, (![C_1470]: (C_1470!='#skF_3'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_1470), k1_relat_1('#skF_7')) | ~r2_hidden(C_1470, k2_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_97423])).
% 48.26/35.70  tff(c_97489, plain, (![C_45]: (C_45!='#skF_3'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | ~r2_hidden(C_45, k2_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_18, c_97485])).
% 48.26/35.70  tff(c_97493, plain, (~r2_hidden('#skF_3'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_97489])).
% 48.26/35.70  tff(c_79680, plain, (![A_9]: (r2_hidden('#skF_3'(A_9, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7')) | ~r2_hidden('#skF_1'(A_9, k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(resolution, [status(thm)], [c_26, c_79529])).
% 48.26/35.70  tff(c_97232, plain, (r2_hidden('#skF_3'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7')) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_97212, c_79680])).
% 48.26/35.70  tff(c_97240, plain, (r2_hidden('#skF_3'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7')) | k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_97232])).
% 48.26/35.70  tff(c_97241, plain, (r2_hidden('#skF_3'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_96440, c_97240])).
% 48.26/35.70  tff(c_97495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_97493, c_97241])).
% 48.26/35.70  tff(c_97497, plain, (~r2_hidden('#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_96562])).
% 48.26/35.70  tff(c_97496, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))))='#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7')))), inference(splitRight, [status(thm)], [c_96562])).
% 48.26/35.70  tff(c_79664, plain, (![C_117]: (r2_hidden(k1_funct_1('#skF_7', C_117), k2_relat_1('#skF_7')) | ~r2_hidden(C_117, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_1097, c_79529])).
% 48.26/35.70  tff(c_97657, plain, (r2_hidden('#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7')) | ~r2_hidden('#skF_2'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_97496, c_79664])).
% 48.26/35.70  tff(c_97695, plain, (r2_hidden('#skF_1'('#skF_7', k2_relat_1(k5_relat_1('#skF_8', '#skF_7'))), k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_96439, c_97657])).
% 48.26/35.70  tff(c_97697, plain, $false, inference(negUnitSimplification, [status(thm)], [c_97497, c_97695])).
% 48.26/35.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 48.26/35.70  
% 48.26/35.70  Inference rules
% 48.26/35.70  ----------------------
% 48.26/35.71  #Ref     : 24
% 48.26/35.71  #Sup     : 21493
% 48.26/35.71  #Fact    : 8
% 48.26/35.71  #Define  : 0
% 48.26/35.71  #Split   : 221
% 48.26/35.71  #Chain   : 0
% 48.26/35.71  #Close   : 0
% 48.26/35.71  
% 48.26/35.71  Ordering : KBO
% 48.26/35.71  
% 48.26/35.71  Simplification rules
% 48.26/35.71  ----------------------
% 48.26/35.71  #Subsume      : 3060
% 48.26/35.71  #Demod        : 62947
% 48.26/35.71  #Tautology    : 5381
% 48.26/35.71  #SimpNegUnit  : 658
% 48.26/35.71  #BackRed      : 317
% 48.26/35.71  
% 48.26/35.71  #Partial instantiations: 0
% 48.26/35.71  #Strategies tried      : 1
% 48.26/35.71  
% 48.26/35.71  Timing (in seconds)
% 48.26/35.71  ----------------------
% 48.26/35.71  Preprocessing        : 0.33
% 48.26/35.71  Parsing              : 0.16
% 48.26/35.71  CNF conversion       : 0.03
% 48.26/35.71  Main loop            : 34.53
% 48.26/35.71  Inferencing          : 5.62
% 48.26/35.71  Reduction            : 16.79
% 48.26/35.71  Demodulation         : 14.55
% 48.26/35.71  BG Simplification    : 0.69
% 48.26/35.71  Subsumption          : 10.06
% 48.26/35.71  Abstraction          : 1.44
% 48.26/35.71  MUC search           : 0.00
% 48.26/35.71  Cooper               : 0.00
% 48.26/35.71  Total                : 34.96
% 48.26/35.71  Index Insertion      : 0.00
% 48.26/35.71  Index Deletion       : 0.00
% 48.26/35.71  Index Matching       : 0.00
% 48.26/35.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
