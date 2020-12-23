%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:44 EST 2020

% Result     : Theorem 21.82s
% Output     : CNFRefutation 21.88s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 463 expanded)
%              Number of leaves         :   37 ( 180 expanded)
%              Depth                    :   15
%              Number of atoms          :  248 (1359 expanded)
%              Number of equality atoms :   42 ( 372 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_159,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( v2_funct_1(B)
            & r2_hidden(A,k2_relat_1(B)) )
         => ( A = k1_funct_1(B,k1_funct_1(k2_funct_1(B),A))
            & A = k1_funct_1(k5_relat_1(k2_funct_1(B),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_146,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( r2_hidden(C,k2_relat_1(B))
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).

tff(f_136,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k1_relat_1(B)) )
       => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
          & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
          <=> ( r2_hidden(A,k1_relat_1(C))
              & r2_hidden(k1_funct_1(C,A),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).

tff(f_124,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

tff(c_64,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_70,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_68,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_12,plain,(
    ! [A_5,C_20] :
      ( r2_hidden(k4_tarski('#skF_4'(A_5,k2_relat_1(A_5),C_20),C_20),A_5)
      | ~ r2_hidden(C_20,k2_relat_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_303,plain,(
    ! [C_84,A_85,B_86] :
      ( k1_funct_1(C_84,A_85) = B_86
      | ~ r2_hidden(k4_tarski(A_85,B_86),C_84)
      | ~ v1_funct_1(C_84)
      | ~ v1_relat_1(C_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_307,plain,(
    ! [A_5,C_20] :
      ( k1_funct_1(A_5,'#skF_4'(A_5,k2_relat_1(A_5),C_20)) = C_20
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5)
      | ~ r2_hidden(C_20,k2_relat_1(A_5)) ) ),
    inference(resolution,[status(thm)],[c_12,c_303])).

tff(c_66,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_127,plain,(
    ! [A_66] :
      ( k4_relat_1(A_66) = k2_funct_1(A_66)
      | ~ v2_funct_1(A_66)
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_130,plain,
    ( k4_relat_1('#skF_6') = k2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_127])).

tff(c_133,plain,(
    k4_relat_1('#skF_6') = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_130])).

tff(c_24,plain,(
    ! [A_24] :
      ( v1_relat_1(k4_relat_1(A_24))
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_143,plain,
    ( v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_24])).

tff(c_151,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_143])).

tff(c_32,plain,(
    ! [A_32] :
      ( k2_relat_1(k4_relat_1(A_32)) = k1_relat_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_140,plain,
    ( k2_relat_1(k2_funct_1('#skF_6')) = k1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_32])).

tff(c_149,plain,(
    k2_relat_1(k2_funct_1('#skF_6')) = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_140])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_102,plain,(
    ! [B_58,A_59] :
      ( v5_relat_1(B_58,A_59)
      | ~ r1_tarski(k2_relat_1(B_58),A_59)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_110,plain,(
    ! [B_58] :
      ( v5_relat_1(B_58,k2_relat_1(B_58))
      | ~ v1_relat_1(B_58) ) ),
    inference(resolution,[status(thm)],[c_6,c_102])).

tff(c_159,plain,
    ( v5_relat_1(k2_funct_1('#skF_6'),k1_relat_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_110])).

tff(c_168,plain,(
    v5_relat_1(k2_funct_1('#skF_6'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_159])).

tff(c_260,plain,(
    ! [A_81,C_82] :
      ( r2_hidden(k4_tarski('#skF_4'(A_81,k2_relat_1(A_81),C_82),C_82),A_81)
      | ~ r2_hidden(C_82,k2_relat_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_30,plain,(
    ! [A_29,C_31,B_30] :
      ( r2_hidden(A_29,k1_relat_1(C_31))
      | ~ r2_hidden(k4_tarski(A_29,B_30),C_31)
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_669,plain,(
    ! [A_108,C_109] :
      ( r2_hidden('#skF_4'(A_108,k2_relat_1(A_108),C_109),k1_relat_1(A_108))
      | ~ v1_relat_1(A_108)
      | ~ r2_hidden(C_109,k2_relat_1(A_108)) ) ),
    inference(resolution,[status(thm)],[c_260,c_30])).

tff(c_219,plain,(
    ! [C_73,A_74,B_75] :
      ( r2_hidden(C_73,A_74)
      | ~ r2_hidden(C_73,k2_relat_1(B_75))
      | ~ v5_relat_1(B_75,A_74)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_221,plain,(
    ! [C_73,A_74] :
      ( r2_hidden(C_73,A_74)
      | ~ r2_hidden(C_73,k1_relat_1('#skF_6'))
      | ~ v5_relat_1(k2_funct_1('#skF_6'),A_74)
      | ~ v1_relat_1(k2_funct_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_219])).

tff(c_227,plain,(
    ! [C_73,A_74] :
      ( r2_hidden(C_73,A_74)
      | ~ r2_hidden(C_73,k1_relat_1('#skF_6'))
      | ~ v5_relat_1(k2_funct_1('#skF_6'),A_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_221])).

tff(c_672,plain,(
    ! [C_109,A_74] :
      ( r2_hidden('#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_109),A_74)
      | ~ v5_relat_1(k2_funct_1('#skF_6'),A_74)
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(C_109,k2_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_669,c_227])).

tff(c_690,plain,(
    ! [C_109,A_74] :
      ( r2_hidden('#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_109),A_74)
      | ~ v5_relat_1(k2_funct_1('#skF_6'),A_74)
      | ~ r2_hidden(C_109,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_672])).

tff(c_2207,plain,(
    ! [A_176,C_177] :
      ( k1_funct_1(A_176,'#skF_4'(A_176,k2_relat_1(A_176),C_177)) = C_177
      | ~ v1_funct_1(A_176)
      | ~ v1_relat_1(A_176)
      | ~ r2_hidden(C_177,k2_relat_1(A_176)) ) ),
    inference(resolution,[status(thm)],[c_12,c_303])).

tff(c_54,plain,(
    ! [B_46,A_45] :
      ( k1_funct_1(k2_funct_1(B_46),k1_funct_1(B_46,A_45)) = A_45
      | ~ r2_hidden(A_45,k1_relat_1(B_46))
      | ~ v2_funct_1(B_46)
      | ~ v1_funct_1(B_46)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_54442,plain,(
    ! [A_1022,C_1023] :
      ( k1_funct_1(k2_funct_1(A_1022),C_1023) = '#skF_4'(A_1022,k2_relat_1(A_1022),C_1023)
      | ~ r2_hidden('#skF_4'(A_1022,k2_relat_1(A_1022),C_1023),k1_relat_1(A_1022))
      | ~ v2_funct_1(A_1022)
      | ~ v1_funct_1(A_1022)
      | ~ v1_relat_1(A_1022)
      | ~ v1_funct_1(A_1022)
      | ~ v1_relat_1(A_1022)
      | ~ r2_hidden(C_1023,k2_relat_1(A_1022)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2207,c_54])).

tff(c_54536,plain,(
    ! [C_109] :
      ( k1_funct_1(k2_funct_1('#skF_6'),C_109) = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_109)
      | ~ v2_funct_1('#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ v5_relat_1(k2_funct_1('#skF_6'),k1_relat_1('#skF_6'))
      | ~ r2_hidden(C_109,k2_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_690,c_54442])).

tff(c_54615,plain,(
    ! [C_1024] :
      ( k1_funct_1(k2_funct_1('#skF_6'),C_1024) = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_1024)
      | ~ r2_hidden(C_1024,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_70,c_68,c_66,c_54536])).

tff(c_55552,plain,(
    k1_funct_1(k2_funct_1('#skF_6'),'#skF_5') = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_54615])).

tff(c_62,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),'#skF_5') != '#skF_5'
    | k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_85,plain,(
    k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_55553,plain,(
    k1_funct_1('#skF_6','#skF_4'('#skF_6',k2_relat_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55552,c_85])).

tff(c_55635,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ r2_hidden('#skF_5',k2_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_55553])).

tff(c_55639,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_70,c_68,c_55635])).

tff(c_55640,plain,(
    k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),'#skF_5') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_55687,plain,(
    ! [A_1036] :
      ( k4_relat_1(A_1036) = k2_funct_1(A_1036)
      | ~ v2_funct_1(A_1036)
      | ~ v1_funct_1(A_1036)
      | ~ v1_relat_1(A_1036) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_55690,plain,
    ( k4_relat_1('#skF_6') = k2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_55687])).

tff(c_55693,plain,(
    k4_relat_1('#skF_6') = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_55690])).

tff(c_55703,plain,
    ( v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_55693,c_24])).

tff(c_55711,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_55703])).

tff(c_38,plain,(
    ! [A_34] :
      ( v1_funct_1(k2_funct_1(A_34))
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_34,plain,(
    ! [A_32] :
      ( k1_relat_1(k4_relat_1(A_32)) = k2_relat_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_55697,plain,
    ( k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_55693,c_34])).

tff(c_55707,plain,(
    k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_55697])).

tff(c_55700,plain,
    ( k2_relat_1(k2_funct_1('#skF_6')) = k1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_55693,c_32])).

tff(c_55709,plain,(
    k2_relat_1(k2_funct_1('#skF_6')) = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_55700])).

tff(c_56017,plain,(
    ! [B_1063,A_1064] :
      ( r2_hidden(k1_funct_1(B_1063,A_1064),k2_relat_1(B_1063))
      | ~ r2_hidden(A_1064,k1_relat_1(B_1063))
      | ~ v1_funct_1(B_1063)
      | ~ v1_relat_1(B_1063) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_56025,plain,(
    ! [A_1064] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),A_1064),k1_relat_1('#skF_6'))
      | ~ r2_hidden(A_1064,k1_relat_1(k2_funct_1('#skF_6')))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55709,c_56017])).

tff(c_56036,plain,(
    ! [A_1064] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),A_1064),k1_relat_1('#skF_6'))
      | ~ r2_hidden(A_1064,k2_relat_1('#skF_6'))
      | ~ v1_funct_1(k2_funct_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55711,c_55707,c_56025])).

tff(c_56253,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_56036])).

tff(c_56256,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_56253])).

tff(c_56260,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_56256])).

tff(c_56262,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_56036])).

tff(c_55641,plain,(
    k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_56264,plain,(
    ! [A_1079] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),A_1079),k1_relat_1('#skF_6'))
      | ~ r2_hidden(A_1079,k2_relat_1('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_56036])).

tff(c_56194,plain,(
    ! [A_1075,C_1076] :
      ( r2_hidden(k4_tarski(A_1075,k1_funct_1(C_1076,A_1075)),C_1076)
      | ~ r2_hidden(A_1075,k1_relat_1(C_1076))
      | ~ v1_funct_1(C_1076)
      | ~ v1_relat_1(C_1076) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_56215,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_6'),'#skF_5'),'#skF_5'),'#skF_6')
    | ~ r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),'#skF_5'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_55641,c_56194])).

tff(c_56224,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_6'),'#skF_5'),'#skF_5'),'#skF_6')
    | ~ r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),'#skF_5'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_56215])).

tff(c_56263,plain,(
    ~ r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),'#skF_5'),k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_56224])).

tff(c_56267,plain,(
    ~ r2_hidden('#skF_5',k2_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_56264,c_56263])).

tff(c_56273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_56267])).

tff(c_56275,plain,(
    r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),'#skF_5'),k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_56224])).

tff(c_57693,plain,(
    ! [A_1143,C_1144,B_1145] :
      ( r2_hidden(A_1143,k1_relat_1(k5_relat_1(C_1144,B_1145)))
      | ~ r2_hidden(k1_funct_1(C_1144,A_1143),k1_relat_1(B_1145))
      | ~ r2_hidden(A_1143,k1_relat_1(C_1144))
      | ~ v1_funct_1(C_1144)
      | ~ v1_relat_1(C_1144)
      | ~ v1_funct_1(B_1145)
      | ~ v1_relat_1(B_1145) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_57734,plain,
    ( r2_hidden('#skF_5',k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6')))
    | ~ r2_hidden('#skF_5',k1_relat_1(k2_funct_1('#skF_6')))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56275,c_57693])).

tff(c_57769,plain,(
    r2_hidden('#skF_5',k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_55711,c_56262,c_64,c_55707,c_57734])).

tff(c_58114,plain,(
    ! [C_1159,B_1160,A_1161] :
      ( k1_funct_1(k5_relat_1(C_1159,B_1160),A_1161) = k1_funct_1(B_1160,k1_funct_1(C_1159,A_1161))
      | ~ r2_hidden(A_1161,k1_relat_1(k5_relat_1(C_1159,B_1160)))
      | ~ v1_funct_1(C_1159)
      | ~ v1_relat_1(C_1159)
      | ~ v1_funct_1(B_1160)
      | ~ v1_relat_1(B_1160) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_58135,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),'#skF_5') = k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_57769,c_58114])).

tff(c_58207,plain,(
    k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_55711,c_56262,c_55641,c_58135])).

tff(c_58209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55640,c_58207])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:54:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.82/11.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.82/11.86  
% 21.82/11.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.82/11.86  %$ v5_relat_1 > r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 21.82/11.86  
% 21.82/11.86  %Foreground sorts:
% 21.82/11.86  
% 21.82/11.86  
% 21.82/11.86  %Background operators:
% 21.82/11.86  
% 21.82/11.86  
% 21.82/11.86  %Foreground operators:
% 21.82/11.86  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 21.82/11.86  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 21.82/11.86  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 21.82/11.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.82/11.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 21.82/11.86  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 21.82/11.86  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 21.82/11.86  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 21.82/11.86  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 21.82/11.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 21.82/11.86  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 21.82/11.86  tff('#skF_5', type, '#skF_5': $i).
% 21.82/11.86  tff('#skF_6', type, '#skF_6': $i).
% 21.82/11.86  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 21.82/11.86  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 21.82/11.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.82/11.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 21.82/11.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.82/11.86  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 21.82/11.86  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 21.82/11.86  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 21.82/11.86  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 21.82/11.86  
% 21.88/11.88  tff(f_159, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k2_relat_1(B))) => ((A = k1_funct_1(B, k1_funct_1(k2_funct_1(B), A))) & (A = k1_funct_1(k5_relat_1(k2_funct_1(B), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_funct_1)).
% 21.88/11.88  tff(f_45, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 21.88/11.88  tff(f_146, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 21.88/11.88  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 21.88/11.88  tff(f_49, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 21.88/11.88  tff(f_72, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 21.88/11.88  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 21.88/11.88  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 21.88/11.88  tff(f_66, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 21.88/11.88  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t202_relat_1)).
% 21.88/11.88  tff(f_136, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_funct_1)).
% 21.88/11.88  tff(f_88, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 21.88/11.88  tff(f_96, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 21.88/11.88  tff(f_111, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), k1_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_funct_1)).
% 21.88/11.88  tff(f_124, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_funct_1)).
% 21.88/11.88  tff(c_64, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 21.88/11.88  tff(c_70, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_159])).
% 21.88/11.88  tff(c_68, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_159])).
% 21.88/11.88  tff(c_12, plain, (![A_5, C_20]: (r2_hidden(k4_tarski('#skF_4'(A_5, k2_relat_1(A_5), C_20), C_20), A_5) | ~r2_hidden(C_20, k2_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 21.88/11.88  tff(c_303, plain, (![C_84, A_85, B_86]: (k1_funct_1(C_84, A_85)=B_86 | ~r2_hidden(k4_tarski(A_85, B_86), C_84) | ~v1_funct_1(C_84) | ~v1_relat_1(C_84))), inference(cnfTransformation, [status(thm)], [f_146])).
% 21.88/11.88  tff(c_307, plain, (![A_5, C_20]: (k1_funct_1(A_5, '#skF_4'(A_5, k2_relat_1(A_5), C_20))=C_20 | ~v1_funct_1(A_5) | ~v1_relat_1(A_5) | ~r2_hidden(C_20, k2_relat_1(A_5)))), inference(resolution, [status(thm)], [c_12, c_303])).
% 21.88/11.88  tff(c_66, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_159])).
% 21.88/11.88  tff(c_127, plain, (![A_66]: (k4_relat_1(A_66)=k2_funct_1(A_66) | ~v2_funct_1(A_66) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_80])).
% 21.88/11.88  tff(c_130, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_127])).
% 21.88/11.88  tff(c_133, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_130])).
% 21.88/11.88  tff(c_24, plain, (![A_24]: (v1_relat_1(k4_relat_1(A_24)) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_49])).
% 21.88/11.88  tff(c_143, plain, (v1_relat_1(k2_funct_1('#skF_6')) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_133, c_24])).
% 21.88/11.88  tff(c_151, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_143])).
% 21.88/11.88  tff(c_32, plain, (![A_32]: (k2_relat_1(k4_relat_1(A_32))=k1_relat_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_72])).
% 21.88/11.88  tff(c_140, plain, (k2_relat_1(k2_funct_1('#skF_6'))=k1_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_133, c_32])).
% 21.88/11.88  tff(c_149, plain, (k2_relat_1(k2_funct_1('#skF_6'))=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_140])).
% 21.88/11.88  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 21.88/11.88  tff(c_102, plain, (![B_58, A_59]: (v5_relat_1(B_58, A_59) | ~r1_tarski(k2_relat_1(B_58), A_59) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_37])).
% 21.88/11.88  tff(c_110, plain, (![B_58]: (v5_relat_1(B_58, k2_relat_1(B_58)) | ~v1_relat_1(B_58))), inference(resolution, [status(thm)], [c_6, c_102])).
% 21.88/11.88  tff(c_159, plain, (v5_relat_1(k2_funct_1('#skF_6'), k1_relat_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_149, c_110])).
% 21.88/11.88  tff(c_168, plain, (v5_relat_1(k2_funct_1('#skF_6'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_159])).
% 21.88/11.88  tff(c_260, plain, (![A_81, C_82]: (r2_hidden(k4_tarski('#skF_4'(A_81, k2_relat_1(A_81), C_82), C_82), A_81) | ~r2_hidden(C_82, k2_relat_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 21.88/11.88  tff(c_30, plain, (![A_29, C_31, B_30]: (r2_hidden(A_29, k1_relat_1(C_31)) | ~r2_hidden(k4_tarski(A_29, B_30), C_31) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_66])).
% 21.88/11.88  tff(c_669, plain, (![A_108, C_109]: (r2_hidden('#skF_4'(A_108, k2_relat_1(A_108), C_109), k1_relat_1(A_108)) | ~v1_relat_1(A_108) | ~r2_hidden(C_109, k2_relat_1(A_108)))), inference(resolution, [status(thm)], [c_260, c_30])).
% 21.88/11.88  tff(c_219, plain, (![C_73, A_74, B_75]: (r2_hidden(C_73, A_74) | ~r2_hidden(C_73, k2_relat_1(B_75)) | ~v5_relat_1(B_75, A_74) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_58])).
% 21.88/11.88  tff(c_221, plain, (![C_73, A_74]: (r2_hidden(C_73, A_74) | ~r2_hidden(C_73, k1_relat_1('#skF_6')) | ~v5_relat_1(k2_funct_1('#skF_6'), A_74) | ~v1_relat_1(k2_funct_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_149, c_219])).
% 21.88/11.88  tff(c_227, plain, (![C_73, A_74]: (r2_hidden(C_73, A_74) | ~r2_hidden(C_73, k1_relat_1('#skF_6')) | ~v5_relat_1(k2_funct_1('#skF_6'), A_74))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_221])).
% 21.88/11.88  tff(c_672, plain, (![C_109, A_74]: (r2_hidden('#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_109), A_74) | ~v5_relat_1(k2_funct_1('#skF_6'), A_74) | ~v1_relat_1('#skF_6') | ~r2_hidden(C_109, k2_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_669, c_227])).
% 21.88/11.88  tff(c_690, plain, (![C_109, A_74]: (r2_hidden('#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_109), A_74) | ~v5_relat_1(k2_funct_1('#skF_6'), A_74) | ~r2_hidden(C_109, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_672])).
% 21.88/11.88  tff(c_2207, plain, (![A_176, C_177]: (k1_funct_1(A_176, '#skF_4'(A_176, k2_relat_1(A_176), C_177))=C_177 | ~v1_funct_1(A_176) | ~v1_relat_1(A_176) | ~r2_hidden(C_177, k2_relat_1(A_176)))), inference(resolution, [status(thm)], [c_12, c_303])).
% 21.88/11.88  tff(c_54, plain, (![B_46, A_45]: (k1_funct_1(k2_funct_1(B_46), k1_funct_1(B_46, A_45))=A_45 | ~r2_hidden(A_45, k1_relat_1(B_46)) | ~v2_funct_1(B_46) | ~v1_funct_1(B_46) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_136])).
% 21.88/11.88  tff(c_54442, plain, (![A_1022, C_1023]: (k1_funct_1(k2_funct_1(A_1022), C_1023)='#skF_4'(A_1022, k2_relat_1(A_1022), C_1023) | ~r2_hidden('#skF_4'(A_1022, k2_relat_1(A_1022), C_1023), k1_relat_1(A_1022)) | ~v2_funct_1(A_1022) | ~v1_funct_1(A_1022) | ~v1_relat_1(A_1022) | ~v1_funct_1(A_1022) | ~v1_relat_1(A_1022) | ~r2_hidden(C_1023, k2_relat_1(A_1022)))), inference(superposition, [status(thm), theory('equality')], [c_2207, c_54])).
% 21.88/11.88  tff(c_54536, plain, (![C_109]: (k1_funct_1(k2_funct_1('#skF_6'), C_109)='#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_109) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v5_relat_1(k2_funct_1('#skF_6'), k1_relat_1('#skF_6')) | ~r2_hidden(C_109, k2_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_690, c_54442])).
% 21.88/11.88  tff(c_54615, plain, (![C_1024]: (k1_funct_1(k2_funct_1('#skF_6'), C_1024)='#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_1024) | ~r2_hidden(C_1024, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_168, c_70, c_68, c_66, c_54536])).
% 21.88/11.88  tff(c_55552, plain, (k1_funct_1(k2_funct_1('#skF_6'), '#skF_5')='#skF_4'('#skF_6', k2_relat_1('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_64, c_54615])).
% 21.88/11.88  tff(c_62, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), '#skF_5')!='#skF_5' | k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_159])).
% 21.88/11.88  tff(c_85, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_62])).
% 21.88/11.88  tff(c_55553, plain, (k1_funct_1('#skF_6', '#skF_4'('#skF_6', k2_relat_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_55552, c_85])).
% 21.88/11.88  tff(c_55635, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~r2_hidden('#skF_5', k2_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_307, c_55553])).
% 21.88/11.88  tff(c_55639, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_70, c_68, c_55635])).
% 21.88/11.88  tff(c_55640, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), '#skF_5')!='#skF_5'), inference(splitRight, [status(thm)], [c_62])).
% 21.88/11.88  tff(c_55687, plain, (![A_1036]: (k4_relat_1(A_1036)=k2_funct_1(A_1036) | ~v2_funct_1(A_1036) | ~v1_funct_1(A_1036) | ~v1_relat_1(A_1036))), inference(cnfTransformation, [status(thm)], [f_80])).
% 21.88/11.88  tff(c_55690, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_55687])).
% 21.88/11.88  tff(c_55693, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_55690])).
% 21.88/11.88  tff(c_55703, plain, (v1_relat_1(k2_funct_1('#skF_6')) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_55693, c_24])).
% 21.88/11.88  tff(c_55711, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_55703])).
% 21.88/11.88  tff(c_38, plain, (![A_34]: (v1_funct_1(k2_funct_1(A_34)) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_88])).
% 21.88/11.88  tff(c_34, plain, (![A_32]: (k1_relat_1(k4_relat_1(A_32))=k2_relat_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_72])).
% 21.88/11.88  tff(c_55697, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_55693, c_34])).
% 21.88/11.88  tff(c_55707, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_55697])).
% 21.88/11.88  tff(c_55700, plain, (k2_relat_1(k2_funct_1('#skF_6'))=k1_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_55693, c_32])).
% 21.88/11.88  tff(c_55709, plain, (k2_relat_1(k2_funct_1('#skF_6'))=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_55700])).
% 21.88/11.88  tff(c_56017, plain, (![B_1063, A_1064]: (r2_hidden(k1_funct_1(B_1063, A_1064), k2_relat_1(B_1063)) | ~r2_hidden(A_1064, k1_relat_1(B_1063)) | ~v1_funct_1(B_1063) | ~v1_relat_1(B_1063))), inference(cnfTransformation, [status(thm)], [f_96])).
% 21.88/11.88  tff(c_56025, plain, (![A_1064]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), A_1064), k1_relat_1('#skF_6')) | ~r2_hidden(A_1064, k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_55709, c_56017])).
% 21.88/11.88  tff(c_56036, plain, (![A_1064]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), A_1064), k1_relat_1('#skF_6')) | ~r2_hidden(A_1064, k2_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_55711, c_55707, c_56025])).
% 21.88/11.88  tff(c_56253, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_56036])).
% 21.88/11.88  tff(c_56256, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_56253])).
% 21.88/11.88  tff(c_56260, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_56256])).
% 21.88/11.88  tff(c_56262, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_56036])).
% 21.88/11.88  tff(c_55641, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_62])).
% 21.88/11.88  tff(c_56264, plain, (![A_1079]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), A_1079), k1_relat_1('#skF_6')) | ~r2_hidden(A_1079, k2_relat_1('#skF_6')))), inference(splitRight, [status(thm)], [c_56036])).
% 21.88/11.88  tff(c_56194, plain, (![A_1075, C_1076]: (r2_hidden(k4_tarski(A_1075, k1_funct_1(C_1076, A_1075)), C_1076) | ~r2_hidden(A_1075, k1_relat_1(C_1076)) | ~v1_funct_1(C_1076) | ~v1_relat_1(C_1076))), inference(cnfTransformation, [status(thm)], [f_146])).
% 21.88/11.88  tff(c_56215, plain, (r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'), '#skF_5'), '#skF_6') | ~r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_55641, c_56194])).
% 21.88/11.88  tff(c_56224, plain, (r2_hidden(k4_tarski(k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'), '#skF_5'), '#skF_6') | ~r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_56215])).
% 21.88/11.88  tff(c_56263, plain, (~r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'), k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_56224])).
% 21.88/11.88  tff(c_56267, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_56264, c_56263])).
% 21.88/11.88  tff(c_56273, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_56267])).
% 21.88/11.88  tff(c_56275, plain, (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'), k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_56224])).
% 21.88/11.88  tff(c_57693, plain, (![A_1143, C_1144, B_1145]: (r2_hidden(A_1143, k1_relat_1(k5_relat_1(C_1144, B_1145))) | ~r2_hidden(k1_funct_1(C_1144, A_1143), k1_relat_1(B_1145)) | ~r2_hidden(A_1143, k1_relat_1(C_1144)) | ~v1_funct_1(C_1144) | ~v1_relat_1(C_1144) | ~v1_funct_1(B_1145) | ~v1_relat_1(B_1145))), inference(cnfTransformation, [status(thm)], [f_111])).
% 21.88/11.88  tff(c_57734, plain, (r2_hidden('#skF_5', k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'))) | ~r2_hidden('#skF_5', k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_56275, c_57693])).
% 21.88/11.88  tff(c_57769, plain, (r2_hidden('#skF_5', k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_55711, c_56262, c_64, c_55707, c_57734])).
% 21.88/11.88  tff(c_58114, plain, (![C_1159, B_1160, A_1161]: (k1_funct_1(k5_relat_1(C_1159, B_1160), A_1161)=k1_funct_1(B_1160, k1_funct_1(C_1159, A_1161)) | ~r2_hidden(A_1161, k1_relat_1(k5_relat_1(C_1159, B_1160))) | ~v1_funct_1(C_1159) | ~v1_relat_1(C_1159) | ~v1_funct_1(B_1160) | ~v1_relat_1(B_1160))), inference(cnfTransformation, [status(thm)], [f_124])).
% 21.88/11.88  tff(c_58135, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), '#skF_5')=k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_57769, c_58114])).
% 21.88/11.88  tff(c_58207, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_55711, c_56262, c_55641, c_58135])).
% 21.88/11.88  tff(c_58209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55640, c_58207])).
% 21.88/11.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.88/11.88  
% 21.88/11.88  Inference rules
% 21.88/11.88  ----------------------
% 21.88/11.88  #Ref     : 0
% 21.88/11.88  #Sup     : 12264
% 21.88/11.88  #Fact    : 0
% 21.88/11.88  #Define  : 0
% 21.88/11.88  #Split   : 63
% 21.88/11.88  #Chain   : 0
% 21.88/11.88  #Close   : 0
% 21.88/11.88  
% 21.88/11.88  Ordering : KBO
% 21.88/11.88  
% 21.88/11.88  Simplification rules
% 21.88/11.88  ----------------------
% 21.88/11.88  #Subsume      : 2481
% 21.88/11.88  #Demod        : 12515
% 21.88/11.88  #Tautology    : 1582
% 21.88/11.88  #SimpNegUnit  : 257
% 21.88/11.88  #BackRed      : 136
% 21.88/11.88  
% 21.88/11.88  #Partial instantiations: 0
% 21.88/11.88  #Strategies tried      : 1
% 21.88/11.88  
% 21.88/11.88  Timing (in seconds)
% 21.88/11.88  ----------------------
% 21.88/11.88  Preprocessing        : 0.35
% 21.88/11.88  Parsing              : 0.19
% 21.88/11.88  CNF conversion       : 0.03
% 21.88/11.88  Main loop            : 10.75
% 21.88/11.88  Inferencing          : 1.91
% 21.88/11.88  Reduction            : 2.90
% 21.88/11.88  Demodulation         : 2.07
% 21.88/11.88  BG Simplification    : 0.24
% 21.88/11.88  Subsumption          : 4.99
% 21.88/11.88  Abstraction          : 0.40
% 21.88/11.88  MUC search           : 0.00
% 21.88/11.88  Cooper               : 0.00
% 21.88/11.88  Total                : 11.14
% 21.88/11.88  Index Insertion      : 0.00
% 21.88/11.88  Index Deletion       : 0.00
% 21.88/11.88  Index Matching       : 0.00
% 21.88/11.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
