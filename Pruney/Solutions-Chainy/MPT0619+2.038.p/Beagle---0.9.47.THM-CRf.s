%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:56 EST 2020

% Result     : Theorem 49.31s
% Output     : CNFRefutation 49.44s
% Verified   : 
% Statistics : Number of formulae       :  144 (1817 expanded)
%              Number of leaves         :   25 ( 624 expanded)
%              Depth                    :   21
%              Number of atoms          :  299 (5043 expanded)
%              Number of equality atoms :  156 (2596 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_9 > #skF_7 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_46,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_61,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_3'(A_6,B_7),A_6)
      | k1_xboole_0 = A_6
      | k1_tarski(B_7) = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_44,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_42,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4642,plain,(
    ! [A_3208,C_3209] :
      ( r2_hidden('#skF_7'(A_3208,k2_relat_1(A_3208),C_3209),k1_relat_1(A_3208))
      | ~ r2_hidden(C_3209,k2_relat_1(A_3208))
      | ~ v1_funct_1(A_3208)
      | ~ v1_relat_1(A_3208) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_40,plain,(
    k1_tarski('#skF_8') = k1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_53,plain,(
    ! [C_52,A_53] :
      ( C_52 = A_53
      | ~ r2_hidden(C_52,k1_tarski(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,(
    ! [C_52] :
      ( C_52 = '#skF_8'
      | ~ r2_hidden(C_52,k1_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_53])).

tff(c_4649,plain,(
    ! [C_3209] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_3209) = '#skF_8'
      | ~ r2_hidden(C_3209,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_4642,c_56])).

tff(c_4692,plain,(
    ! [C_3290] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_3290) = '#skF_8'
      | ~ r2_hidden(C_3290,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_4649])).

tff(c_4714,plain,(
    ! [B_7] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),'#skF_3'(k2_relat_1('#skF_9'),B_7)) = '#skF_8'
      | k2_relat_1('#skF_9') = k1_xboole_0
      | k2_relat_1('#skF_9') = k1_tarski(B_7) ) ),
    inference(resolution,[status(thm)],[c_16,c_4692])).

tff(c_6691,plain,(
    k2_relat_1('#skF_9') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_4714])).

tff(c_38,plain,(
    k1_tarski(k1_funct_1('#skF_9','#skF_8')) != k2_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6776,plain,(
    k1_tarski(k1_funct_1('#skF_9','#skF_8')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6691,c_38])).

tff(c_69,plain,(
    ! [A_57,B_58] :
      ( r2_hidden('#skF_3'(A_57,B_58),A_57)
      | k1_xboole_0 = A_57
      | k1_tarski(B_58) = A_57 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_78,plain,(
    ! [B_58] :
      ( '#skF_3'(k1_relat_1('#skF_9'),B_58) = '#skF_8'
      | k1_relat_1('#skF_9') = k1_xboole_0
      | k1_tarski(B_58) = k1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_69,c_56])).

tff(c_116,plain,(
    k1_relat_1('#skF_9') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_130,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_40])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_49,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_4])).

tff(c_129,plain,(
    r2_hidden('#skF_8',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_49])).

tff(c_12,plain,(
    ! [A_1,B_2] :
      ( '#skF_1'(A_1,B_2) = A_1
      | r2_hidden('#skF_2'(A_1,B_2),B_2)
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_150,plain,(
    ! [C_69] :
      ( C_69 = '#skF_8'
      | ~ r2_hidden(C_69,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_56])).

tff(c_173,plain,(
    ! [A_70] :
      ( '#skF_2'(A_70,k1_xboole_0) = '#skF_8'
      | '#skF_1'(A_70,k1_xboole_0) = A_70
      | k1_tarski(A_70) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_150])).

tff(c_188,plain,
    ( k2_relat_1('#skF_9') != k1_xboole_0
    | '#skF_2'(k1_funct_1('#skF_9','#skF_8'),k1_xboole_0) = '#skF_8'
    | '#skF_1'(k1_funct_1('#skF_9','#skF_8'),k1_xboole_0) = k1_funct_1('#skF_9','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_38])).

tff(c_290,plain,(
    k2_relat_1('#skF_9') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_188])).

tff(c_292,plain,(
    ! [A_80,C_81] :
      ( r2_hidden('#skF_7'(A_80,k2_relat_1(A_80),C_81),k1_relat_1(A_80))
      | ~ r2_hidden(C_81,k2_relat_1(A_80))
      | ~ v1_funct_1(A_80)
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_295,plain,(
    ! [C_81] :
      ( r2_hidden('#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_81),k1_xboole_0)
      | ~ r2_hidden(C_81,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_292])).

tff(c_297,plain,(
    ! [C_81] :
      ( r2_hidden('#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_81),k1_xboole_0)
      | ~ r2_hidden(C_81,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_295])).

tff(c_36,plain,(
    ! [B_50,A_49] :
      ( r2_hidden(k1_funct_1(B_50,A_49),k2_relat_1(B_50))
      | ~ r2_hidden(A_49,k1_relat_1(B_50))
      | ~ v1_funct_1(B_50)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_298,plain,(
    ! [C_82] :
      ( r2_hidden('#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_82),k1_xboole_0)
      | ~ r2_hidden(C_82,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_295])).

tff(c_128,plain,(
    ! [C_52] :
      ( C_52 = '#skF_8'
      | ~ r2_hidden(C_52,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_56])).

tff(c_306,plain,(
    ! [C_83] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_83) = '#skF_8'
      | ~ r2_hidden(C_83,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_298,c_128])).

tff(c_310,plain,(
    ! [A_49] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),k1_funct_1('#skF_9',A_49)) = '#skF_8'
      | ~ r2_hidden(A_49,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_36,c_306])).

tff(c_343,plain,(
    ! [A_86] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),k1_funct_1('#skF_9',A_86)) = '#skF_8'
      | ~ r2_hidden(A_86,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_116,c_310])).

tff(c_20,plain,(
    ! [A_9,C_45] :
      ( k1_funct_1(A_9,'#skF_7'(A_9,k2_relat_1(A_9),C_45)) = C_45
      | ~ r2_hidden(C_45,k2_relat_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_349,plain,(
    ! [A_86] :
      ( k1_funct_1('#skF_9',A_86) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(k1_funct_1('#skF_9',A_86),k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(A_86,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_20])).

tff(c_395,plain,(
    ! [A_88] :
      ( k1_funct_1('#skF_9',A_88) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(k1_funct_1('#skF_9',A_88),k2_relat_1('#skF_9'))
      | ~ r2_hidden(A_88,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_349])).

tff(c_403,plain,(
    ! [A_49] :
      ( k1_funct_1('#skF_9',A_49) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(A_49,k1_xboole_0)
      | ~ r2_hidden(A_49,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_36,c_395])).

tff(c_410,plain,(
    ! [A_89] :
      ( k1_funct_1('#skF_9',A_89) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(A_89,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_116,c_403])).

tff(c_440,plain,(
    ! [C_90] :
      ( k1_funct_1('#skF_9','#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_90)) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(C_90,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_297,c_410])).

tff(c_449,plain,(
    ! [C_90] :
      ( k1_funct_1('#skF_9','#skF_8') = C_90
      | ~ r2_hidden(C_90,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(C_90,k2_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_20])).

tff(c_476,plain,(
    ! [C_91] :
      ( k1_funct_1('#skF_9','#skF_8') = C_91
      | ~ r2_hidden(C_91,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_449])).

tff(c_492,plain,(
    ! [B_7] :
      ( '#skF_3'(k2_relat_1('#skF_9'),B_7) = k1_funct_1('#skF_9','#skF_8')
      | k2_relat_1('#skF_9') = k1_xboole_0
      | k2_relat_1('#skF_9') = k1_tarski(B_7) ) ),
    inference(resolution,[status(thm)],[c_16,c_476])).

tff(c_501,plain,(
    ! [B_92] :
      ( '#skF_3'(k2_relat_1('#skF_9'),B_92) = k1_funct_1('#skF_9','#skF_8')
      | k2_relat_1('#skF_9') = k1_tarski(B_92) ) ),
    inference(negUnitSimplification,[status(thm)],[c_290,c_492])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( '#skF_3'(A_6,B_7) != B_7
      | k1_xboole_0 = A_6
      | k1_tarski(B_7) = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_512,plain,(
    ! [B_92] :
      ( k1_funct_1('#skF_9','#skF_8') != B_92
      | k2_relat_1('#skF_9') = k1_xboole_0
      | k2_relat_1('#skF_9') = k1_tarski(B_92)
      | k2_relat_1('#skF_9') = k1_tarski(B_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_14])).

tff(c_550,plain,(
    k1_tarski(k1_funct_1('#skF_9','#skF_8')) = k2_relat_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_290,c_512])).

tff(c_553,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_550,c_38])).

tff(c_555,plain,(
    k2_relat_1('#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_560,plain,(
    ! [A_49] :
      ( r2_hidden(k1_funct_1('#skF_9',A_49),k1_xboole_0)
      | ~ r2_hidden(A_49,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_555,c_36])).

tff(c_571,plain,(
    ! [A_95] :
      ( r2_hidden(k1_funct_1('#skF_9',A_95),k1_xboole_0)
      | ~ r2_hidden(A_95,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_116,c_560])).

tff(c_579,plain,(
    ! [A_96] :
      ( k1_funct_1('#skF_9',A_96) = '#skF_8'
      | ~ r2_hidden(A_96,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_571,c_128])).

tff(c_603,plain,(
    k1_funct_1('#skF_9','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_129,c_579])).

tff(c_556,plain,(
    k1_tarski(k1_funct_1('#skF_9','#skF_8')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_555,c_38])).

tff(c_608,plain,(
    k1_tarski('#skF_8') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_603,c_556])).

tff(c_611,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_608])).

tff(c_613,plain,(
    k1_relat_1('#skF_9') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_614,plain,(
    ! [B_97] :
      ( '#skF_3'(k1_relat_1('#skF_9'),B_97) = '#skF_8'
      | k1_tarski(B_97) = k1_relat_1('#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_622,plain,(
    ! [B_97] :
      ( B_97 != '#skF_8'
      | k1_relat_1('#skF_9') = k1_xboole_0
      | k1_tarski(B_97) = k1_relat_1('#skF_9')
      | k1_tarski(B_97) = k1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_614,c_14])).

tff(c_629,plain,(
    ! [B_97] :
      ( B_97 != '#skF_8'
      | k1_tarski(B_97) = k1_relat_1('#skF_9')
      | k1_tarski(B_97) = k1_relat_1('#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_613,c_622])).

tff(c_672,plain,(
    ! [B_101] :
      ( B_101 != '#skF_8'
      | k1_tarski(B_101) = k1_relat_1('#skF_9') ) ),
    inference(factorization,[status(thm),theory(equality)],[c_629])).

tff(c_694,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_672,c_4])).

tff(c_687,plain,(
    ! [B_101] :
      ( r2_hidden(B_101,k1_relat_1('#skF_9'))
      | B_101 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_672,c_4])).

tff(c_6786,plain,(
    ! [A_49] :
      ( r2_hidden(k1_funct_1('#skF_9',A_49),k1_xboole_0)
      | ~ r2_hidden(A_49,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6691,c_36])).

tff(c_6794,plain,(
    ! [A_49] :
      ( r2_hidden(k1_funct_1('#skF_9',A_49),k1_xboole_0)
      | ~ r2_hidden(A_49,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_6786])).

tff(c_4696,plain,(
    ! [A_49] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),k1_funct_1('#skF_9',A_49)) = '#skF_8'
      | ~ r2_hidden(A_49,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_36,c_4692])).

tff(c_4711,plain,(
    ! [A_49] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),k1_funct_1('#skF_9',A_49)) = '#skF_8'
      | ~ r2_hidden(A_49,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_4696])).

tff(c_7055,plain,(
    ! [A_6404] :
      ( '#skF_7'('#skF_9',k1_xboole_0,k1_funct_1('#skF_9',A_6404)) = '#skF_8'
      | ~ r2_hidden(A_6404,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6691,c_4711])).

tff(c_7111,plain,(
    ! [B_6505] :
      ( '#skF_7'('#skF_9',k1_xboole_0,k1_funct_1('#skF_9',B_6505)) = '#skF_8'
      | B_6505 != '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_687,c_7055])).

tff(c_6783,plain,(
    ! [C_45] :
      ( k1_funct_1('#skF_9','#skF_7'('#skF_9',k1_xboole_0,C_45)) = C_45
      | ~ r2_hidden(C_45,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6691,c_20])).

tff(c_6792,plain,(
    ! [C_45] :
      ( k1_funct_1('#skF_9','#skF_7'('#skF_9',k1_xboole_0,C_45)) = C_45
      | ~ r2_hidden(C_45,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_6691,c_6783])).

tff(c_7431,plain,(
    ! [B_7112] :
      ( k1_funct_1('#skF_9',B_7112) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(k1_funct_1('#skF_9',B_7112),k1_xboole_0)
      | B_7112 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7111,c_6792])).

tff(c_7472,plain,(
    ! [A_7213] :
      ( k1_funct_1('#skF_9',A_7213) = k1_funct_1('#skF_9','#skF_8')
      | A_7213 != '#skF_8'
      | ~ r2_hidden(A_7213,k1_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_6794,c_7431])).

tff(c_7535,plain,(
    ! [B_7314] :
      ( k1_funct_1('#skF_9',B_7314) = k1_funct_1('#skF_9','#skF_8')
      | B_7314 != '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_687,c_7472])).

tff(c_7555,plain,(
    ! [B_7314] :
      ( r2_hidden(k1_funct_1('#skF_9',B_7314),k1_xboole_0)
      | ~ r2_hidden('#skF_8',k1_relat_1('#skF_9'))
      | B_7314 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7535,c_6794])).

tff(c_7650,plain,(
    r2_hidden(k1_funct_1('#skF_9','#skF_8'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_694,c_7555])).

tff(c_4691,plain,(
    ! [C_3209] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_3209) = '#skF_8'
      | ~ r2_hidden(C_3209,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_4649])).

tff(c_6829,plain,(
    ! [C_5796] :
      ( '#skF_7'('#skF_9',k1_xboole_0,C_5796) = '#skF_8'
      | ~ r2_hidden(C_5796,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6691,c_6691,c_4691])).

tff(c_8980,plain,(
    ! [A_8936] :
      ( '#skF_7'('#skF_9',k1_xboole_0,'#skF_2'(A_8936,k1_xboole_0)) = '#skF_8'
      | '#skF_1'(A_8936,k1_xboole_0) = A_8936
      | k1_tarski(A_8936) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_6829])).

tff(c_252228,plain,(
    ! [A_268576] :
      ( k1_funct_1('#skF_9','#skF_8') = '#skF_2'(A_268576,k1_xboole_0)
      | ~ r2_hidden('#skF_2'(A_268576,k1_xboole_0),k1_xboole_0)
      | '#skF_1'(A_268576,k1_xboole_0) = A_268576
      | k1_tarski(A_268576) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8980,c_6792])).

tff(c_252639,plain,(
    ! [A_269337] :
      ( k1_funct_1('#skF_9','#skF_8') = '#skF_2'(A_269337,k1_xboole_0)
      | '#skF_1'(A_269337,k1_xboole_0) = A_269337
      | k1_tarski(A_269337) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_252228])).

tff(c_253935,plain,
    ( '#skF_2'(k1_funct_1('#skF_9','#skF_8'),k1_xboole_0) = k1_funct_1('#skF_9','#skF_8')
    | '#skF_1'(k1_funct_1('#skF_9','#skF_8'),k1_xboole_0) = k1_funct_1('#skF_9','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_252639,c_6776])).

tff(c_256386,plain,(
    '#skF_1'(k1_funct_1('#skF_9','#skF_8'),k1_xboole_0) = k1_funct_1('#skF_9','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_253935])).

tff(c_10,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r2_hidden('#skF_2'(A_1,B_2),B_2)
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | '#skF_2'(A_1,B_2) != A_1
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_256393,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_9','#skF_8'),k1_xboole_0)
    | '#skF_2'(k1_funct_1('#skF_9','#skF_8'),k1_xboole_0) != k1_funct_1('#skF_9','#skF_8')
    | k1_tarski(k1_funct_1('#skF_9','#skF_8')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_256386,c_6])).

tff(c_256742,plain,
    ( '#skF_2'(k1_funct_1('#skF_9','#skF_8'),k1_xboole_0) != k1_funct_1('#skF_9','#skF_8')
    | k1_tarski(k1_funct_1('#skF_9','#skF_8')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7650,c_256393])).

tff(c_256743,plain,(
    '#skF_2'(k1_funct_1('#skF_9','#skF_8'),k1_xboole_0) != k1_funct_1('#skF_9','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_6776,c_256742])).

tff(c_6857,plain,(
    ! [A_1] :
      ( '#skF_7'('#skF_9',k1_xboole_0,'#skF_2'(A_1,k1_xboole_0)) = '#skF_8'
      | ~ r2_hidden('#skF_1'(A_1,k1_xboole_0),k1_xboole_0)
      | k1_tarski(A_1) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_6829])).

tff(c_256390,plain,
    ( '#skF_7'('#skF_9',k1_xboole_0,'#skF_2'(k1_funct_1('#skF_9','#skF_8'),k1_xboole_0)) = '#skF_8'
    | ~ r2_hidden(k1_funct_1('#skF_9','#skF_8'),k1_xboole_0)
    | k1_tarski(k1_funct_1('#skF_9','#skF_8')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_256386,c_6857])).

tff(c_256739,plain,
    ( '#skF_7'('#skF_9',k1_xboole_0,'#skF_2'(k1_funct_1('#skF_9','#skF_8'),k1_xboole_0)) = '#skF_8'
    | k1_tarski(k1_funct_1('#skF_9','#skF_8')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7650,c_256390])).

tff(c_256740,plain,(
    '#skF_7'('#skF_9',k1_xboole_0,'#skF_2'(k1_funct_1('#skF_9','#skF_8'),k1_xboole_0)) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_6776,c_256739])).

tff(c_256867,plain,
    ( '#skF_2'(k1_funct_1('#skF_9','#skF_8'),k1_xboole_0) = k1_funct_1('#skF_9','#skF_8')
    | ~ r2_hidden('#skF_2'(k1_funct_1('#skF_9','#skF_8'),k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_256740,c_6792])).

tff(c_257473,plain,(
    ~ r2_hidden('#skF_2'(k1_funct_1('#skF_9','#skF_8'),k1_xboole_0),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_256743,c_256867])).

tff(c_257670,plain,
    ( ~ r2_hidden('#skF_1'(k1_funct_1('#skF_9','#skF_8'),k1_xboole_0),k1_xboole_0)
    | k1_tarski(k1_funct_1('#skF_9','#skF_8')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_257473])).

tff(c_257688,plain,(
    k1_tarski(k1_funct_1('#skF_9','#skF_8')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7650,c_256386,c_257670])).

tff(c_257690,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6776,c_257688])).

tff(c_257692,plain,(
    '#skF_1'(k1_funct_1('#skF_9','#skF_8'),k1_xboole_0) != k1_funct_1('#skF_9','#skF_8') ),
    inference(splitRight,[status(thm)],[c_253935])).

tff(c_257691,plain,(
    '#skF_2'(k1_funct_1('#skF_9','#skF_8'),k1_xboole_0) = k1_funct_1('#skF_9','#skF_8') ),
    inference(splitRight,[status(thm)],[c_253935])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( '#skF_1'(A_1,B_2) = A_1
      | '#skF_2'(A_1,B_2) != A_1
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_257730,plain,
    ( '#skF_1'(k1_funct_1('#skF_9','#skF_8'),k1_xboole_0) = k1_funct_1('#skF_9','#skF_8')
    | k1_tarski(k1_funct_1('#skF_9','#skF_8')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_257691,c_8])).

tff(c_258106,plain,(
    '#skF_1'(k1_funct_1('#skF_9','#skF_8'),k1_xboole_0) = k1_funct_1('#skF_9','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_6776,c_257730])).

tff(c_258190,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_257692,c_258106])).

tff(c_258192,plain,(
    k2_relat_1('#skF_9') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_4714])).

tff(c_22,plain,(
    ! [A_9,C_45] :
      ( r2_hidden('#skF_7'(A_9,k2_relat_1(A_9),C_45),k1_relat_1(A_9))
      | ~ r2_hidden(C_45,k2_relat_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4715,plain,(
    ! [A_3371] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),k1_funct_1('#skF_9',A_3371)) = '#skF_8'
      | ~ r2_hidden(A_3371,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_4696])).

tff(c_4724,plain,(
    ! [A_3371] :
      ( k1_funct_1('#skF_9',A_3371) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(k1_funct_1('#skF_9',A_3371),k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(A_3371,k1_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4715,c_20])).

tff(c_258312,plain,(
    ! [A_279425] :
      ( k1_funct_1('#skF_9',A_279425) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(k1_funct_1('#skF_9',A_279425),k2_relat_1('#skF_9'))
      | ~ r2_hidden(A_279425,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_4724])).

tff(c_258335,plain,(
    ! [A_49] :
      ( k1_funct_1('#skF_9',A_49) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(A_49,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_36,c_258312])).

tff(c_258341,plain,(
    ! [A_279526] :
      ( k1_funct_1('#skF_9',A_279526) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(A_279526,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_258335])).

tff(c_258349,plain,(
    ! [C_45] :
      ( k1_funct_1('#skF_9','#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_45)) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(C_45,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_22,c_258341])).

tff(c_260506,plain,(
    ! [C_281850] :
      ( k1_funct_1('#skF_9','#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_281850)) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(C_281850,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_258349])).

tff(c_260539,plain,(
    ! [C_281850] :
      ( k1_funct_1('#skF_9','#skF_8') = C_281850
      | ~ r2_hidden(C_281850,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(C_281850,k2_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_260506,c_20])).

tff(c_260682,plain,(
    ! [C_282054] :
      ( k1_funct_1('#skF_9','#skF_8') = C_282054
      | ~ r2_hidden(C_282054,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_260539])).

tff(c_260717,plain,(
    ! [B_7] :
      ( '#skF_3'(k2_relat_1('#skF_9'),B_7) = k1_funct_1('#skF_9','#skF_8')
      | k2_relat_1('#skF_9') = k1_xboole_0
      | k2_relat_1('#skF_9') = k1_tarski(B_7) ) ),
    inference(resolution,[status(thm)],[c_16,c_260682])).

tff(c_260732,plain,(
    ! [B_282155] :
      ( '#skF_3'(k2_relat_1('#skF_9'),B_282155) = k1_funct_1('#skF_9','#skF_8')
      | k2_relat_1('#skF_9') = k1_tarski(B_282155) ) ),
    inference(negUnitSimplification,[status(thm)],[c_258192,c_260717])).

tff(c_260743,plain,(
    ! [B_282155] :
      ( k1_funct_1('#skF_9','#skF_8') != B_282155
      | k2_relat_1('#skF_9') = k1_xboole_0
      | k2_relat_1('#skF_9') = k1_tarski(B_282155)
      | k2_relat_1('#skF_9') = k1_tarski(B_282155) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_260732,c_14])).

tff(c_260935,plain,(
    k1_tarski(k1_funct_1('#skF_9','#skF_8')) = k2_relat_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_258192,c_260743])).

tff(c_260939,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_260935,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 49.31/36.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 49.40/36.97  
% 49.40/36.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 49.44/36.97  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_9 > #skF_7 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 49.44/36.97  
% 49.44/36.97  %Foreground sorts:
% 49.44/36.97  
% 49.44/36.97  
% 49.44/36.97  %Background operators:
% 49.44/36.97  
% 49.44/36.97  
% 49.44/36.97  %Foreground operators:
% 49.44/36.97  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 49.44/36.97  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 49.44/36.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 49.44/36.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 49.44/36.97  tff(k1_tarski, type, k1_tarski: $i > $i).
% 49.44/36.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 49.44/36.97  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 49.44/36.97  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 49.44/36.97  tff('#skF_9', type, '#skF_9': $i).
% 49.44/36.97  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 49.44/36.97  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 49.44/36.97  tff('#skF_8', type, '#skF_8': $i).
% 49.44/36.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 49.44/36.97  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 49.44/36.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 49.44/36.97  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 49.44/36.97  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 49.44/36.97  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 49.44/36.97  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 49.44/36.97  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 49.44/36.97  
% 49.44/37.00  tff(f_46, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 49.44/37.00  tff(f_78, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 49.44/37.00  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 49.44/37.00  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 49.44/37.00  tff(f_69, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 49.44/37.00  tff(c_16, plain, (![A_6, B_7]: (r2_hidden('#skF_3'(A_6, B_7), A_6) | k1_xboole_0=A_6 | k1_tarski(B_7)=A_6)), inference(cnfTransformation, [status(thm)], [f_46])).
% 49.44/37.00  tff(c_44, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_78])).
% 49.44/37.00  tff(c_42, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_78])).
% 49.44/37.00  tff(c_4642, plain, (![A_3208, C_3209]: (r2_hidden('#skF_7'(A_3208, k2_relat_1(A_3208), C_3209), k1_relat_1(A_3208)) | ~r2_hidden(C_3209, k2_relat_1(A_3208)) | ~v1_funct_1(A_3208) | ~v1_relat_1(A_3208))), inference(cnfTransformation, [status(thm)], [f_61])).
% 49.44/37.00  tff(c_40, plain, (k1_tarski('#skF_8')=k1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_78])).
% 49.44/37.00  tff(c_53, plain, (![C_52, A_53]: (C_52=A_53 | ~r2_hidden(C_52, k1_tarski(A_53)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 49.44/37.00  tff(c_56, plain, (![C_52]: (C_52='#skF_8' | ~r2_hidden(C_52, k1_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_40, c_53])).
% 49.44/37.00  tff(c_4649, plain, (![C_3209]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_3209)='#skF_8' | ~r2_hidden(C_3209, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_4642, c_56])).
% 49.44/37.00  tff(c_4692, plain, (![C_3290]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_3290)='#skF_8' | ~r2_hidden(C_3290, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_4649])).
% 49.44/37.00  tff(c_4714, plain, (![B_7]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), '#skF_3'(k2_relat_1('#skF_9'), B_7))='#skF_8' | k2_relat_1('#skF_9')=k1_xboole_0 | k2_relat_1('#skF_9')=k1_tarski(B_7))), inference(resolution, [status(thm)], [c_16, c_4692])).
% 49.44/37.00  tff(c_6691, plain, (k2_relat_1('#skF_9')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_4714])).
% 49.44/37.00  tff(c_38, plain, (k1_tarski(k1_funct_1('#skF_9', '#skF_8'))!=k2_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_78])).
% 49.44/37.00  tff(c_6776, plain, (k1_tarski(k1_funct_1('#skF_9', '#skF_8'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6691, c_38])).
% 49.44/37.00  tff(c_69, plain, (![A_57, B_58]: (r2_hidden('#skF_3'(A_57, B_58), A_57) | k1_xboole_0=A_57 | k1_tarski(B_58)=A_57)), inference(cnfTransformation, [status(thm)], [f_46])).
% 49.44/37.00  tff(c_78, plain, (![B_58]: ('#skF_3'(k1_relat_1('#skF_9'), B_58)='#skF_8' | k1_relat_1('#skF_9')=k1_xboole_0 | k1_tarski(B_58)=k1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_69, c_56])).
% 49.44/37.00  tff(c_116, plain, (k1_relat_1('#skF_9')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_78])).
% 49.44/37.00  tff(c_130, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_116, c_40])).
% 49.44/37.00  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 49.44/37.00  tff(c_49, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_4])).
% 49.44/37.00  tff(c_129, plain, (r2_hidden('#skF_8', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_116, c_49])).
% 49.44/37.00  tff(c_12, plain, (![A_1, B_2]: ('#skF_1'(A_1, B_2)=A_1 | r2_hidden('#skF_2'(A_1, B_2), B_2) | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 49.44/37.00  tff(c_150, plain, (![C_69]: (C_69='#skF_8' | ~r2_hidden(C_69, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_56])).
% 49.44/37.00  tff(c_173, plain, (![A_70]: ('#skF_2'(A_70, k1_xboole_0)='#skF_8' | '#skF_1'(A_70, k1_xboole_0)=A_70 | k1_tarski(A_70)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_150])).
% 49.44/37.00  tff(c_188, plain, (k2_relat_1('#skF_9')!=k1_xboole_0 | '#skF_2'(k1_funct_1('#skF_9', '#skF_8'), k1_xboole_0)='#skF_8' | '#skF_1'(k1_funct_1('#skF_9', '#skF_8'), k1_xboole_0)=k1_funct_1('#skF_9', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_173, c_38])).
% 49.44/37.00  tff(c_290, plain, (k2_relat_1('#skF_9')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_188])).
% 49.44/37.00  tff(c_292, plain, (![A_80, C_81]: (r2_hidden('#skF_7'(A_80, k2_relat_1(A_80), C_81), k1_relat_1(A_80)) | ~r2_hidden(C_81, k2_relat_1(A_80)) | ~v1_funct_1(A_80) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_61])).
% 49.44/37.00  tff(c_295, plain, (![C_81]: (r2_hidden('#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_81), k1_xboole_0) | ~r2_hidden(C_81, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_292])).
% 49.44/37.00  tff(c_297, plain, (![C_81]: (r2_hidden('#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_81), k1_xboole_0) | ~r2_hidden(C_81, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_295])).
% 49.44/37.00  tff(c_36, plain, (![B_50, A_49]: (r2_hidden(k1_funct_1(B_50, A_49), k2_relat_1(B_50)) | ~r2_hidden(A_49, k1_relat_1(B_50)) | ~v1_funct_1(B_50) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_69])).
% 49.44/37.00  tff(c_298, plain, (![C_82]: (r2_hidden('#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_82), k1_xboole_0) | ~r2_hidden(C_82, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_295])).
% 49.44/37.00  tff(c_128, plain, (![C_52]: (C_52='#skF_8' | ~r2_hidden(C_52, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_56])).
% 49.44/37.00  tff(c_306, plain, (![C_83]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_83)='#skF_8' | ~r2_hidden(C_83, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_298, c_128])).
% 49.44/37.00  tff(c_310, plain, (![A_49]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), k1_funct_1('#skF_9', A_49))='#skF_8' | ~r2_hidden(A_49, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_36, c_306])).
% 49.44/37.00  tff(c_343, plain, (![A_86]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), k1_funct_1('#skF_9', A_86))='#skF_8' | ~r2_hidden(A_86, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_116, c_310])).
% 49.44/37.00  tff(c_20, plain, (![A_9, C_45]: (k1_funct_1(A_9, '#skF_7'(A_9, k2_relat_1(A_9), C_45))=C_45 | ~r2_hidden(C_45, k2_relat_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_61])).
% 49.44/37.00  tff(c_349, plain, (![A_86]: (k1_funct_1('#skF_9', A_86)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(k1_funct_1('#skF_9', A_86), k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(A_86, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_343, c_20])).
% 49.44/37.00  tff(c_395, plain, (![A_88]: (k1_funct_1('#skF_9', A_88)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(k1_funct_1('#skF_9', A_88), k2_relat_1('#skF_9')) | ~r2_hidden(A_88, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_349])).
% 49.44/37.00  tff(c_403, plain, (![A_49]: (k1_funct_1('#skF_9', A_49)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(A_49, k1_xboole_0) | ~r2_hidden(A_49, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_36, c_395])).
% 49.44/37.00  tff(c_410, plain, (![A_89]: (k1_funct_1('#skF_9', A_89)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(A_89, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_116, c_403])).
% 49.44/37.00  tff(c_440, plain, (![C_90]: (k1_funct_1('#skF_9', '#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_90))=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(C_90, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_297, c_410])).
% 49.44/37.00  tff(c_449, plain, (![C_90]: (k1_funct_1('#skF_9', '#skF_8')=C_90 | ~r2_hidden(C_90, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(C_90, k2_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_440, c_20])).
% 49.44/37.00  tff(c_476, plain, (![C_91]: (k1_funct_1('#skF_9', '#skF_8')=C_91 | ~r2_hidden(C_91, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_449])).
% 49.44/37.00  tff(c_492, plain, (![B_7]: ('#skF_3'(k2_relat_1('#skF_9'), B_7)=k1_funct_1('#skF_9', '#skF_8') | k2_relat_1('#skF_9')=k1_xboole_0 | k2_relat_1('#skF_9')=k1_tarski(B_7))), inference(resolution, [status(thm)], [c_16, c_476])).
% 49.44/37.00  tff(c_501, plain, (![B_92]: ('#skF_3'(k2_relat_1('#skF_9'), B_92)=k1_funct_1('#skF_9', '#skF_8') | k2_relat_1('#skF_9')=k1_tarski(B_92))), inference(negUnitSimplification, [status(thm)], [c_290, c_492])).
% 49.44/37.00  tff(c_14, plain, (![A_6, B_7]: ('#skF_3'(A_6, B_7)!=B_7 | k1_xboole_0=A_6 | k1_tarski(B_7)=A_6)), inference(cnfTransformation, [status(thm)], [f_46])).
% 49.44/37.00  tff(c_512, plain, (![B_92]: (k1_funct_1('#skF_9', '#skF_8')!=B_92 | k2_relat_1('#skF_9')=k1_xboole_0 | k2_relat_1('#skF_9')=k1_tarski(B_92) | k2_relat_1('#skF_9')=k1_tarski(B_92))), inference(superposition, [status(thm), theory('equality')], [c_501, c_14])).
% 49.44/37.00  tff(c_550, plain, (k1_tarski(k1_funct_1('#skF_9', '#skF_8'))=k2_relat_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_290, c_512])).
% 49.44/37.00  tff(c_553, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_550, c_38])).
% 49.44/37.00  tff(c_555, plain, (k2_relat_1('#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_188])).
% 49.44/37.00  tff(c_560, plain, (![A_49]: (r2_hidden(k1_funct_1('#skF_9', A_49), k1_xboole_0) | ~r2_hidden(A_49, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_555, c_36])).
% 49.44/37.00  tff(c_571, plain, (![A_95]: (r2_hidden(k1_funct_1('#skF_9', A_95), k1_xboole_0) | ~r2_hidden(A_95, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_116, c_560])).
% 49.44/37.00  tff(c_579, plain, (![A_96]: (k1_funct_1('#skF_9', A_96)='#skF_8' | ~r2_hidden(A_96, k1_xboole_0))), inference(resolution, [status(thm)], [c_571, c_128])).
% 49.44/37.00  tff(c_603, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_129, c_579])).
% 49.44/37.00  tff(c_556, plain, (k1_tarski(k1_funct_1('#skF_9', '#skF_8'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_555, c_38])).
% 49.44/37.00  tff(c_608, plain, (k1_tarski('#skF_8')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_603, c_556])).
% 49.44/37.00  tff(c_611, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_608])).
% 49.44/37.00  tff(c_613, plain, (k1_relat_1('#skF_9')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_78])).
% 49.44/37.00  tff(c_614, plain, (![B_97]: ('#skF_3'(k1_relat_1('#skF_9'), B_97)='#skF_8' | k1_tarski(B_97)=k1_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_78])).
% 49.44/37.00  tff(c_622, plain, (![B_97]: (B_97!='#skF_8' | k1_relat_1('#skF_9')=k1_xboole_0 | k1_tarski(B_97)=k1_relat_1('#skF_9') | k1_tarski(B_97)=k1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_614, c_14])).
% 49.44/37.00  tff(c_629, plain, (![B_97]: (B_97!='#skF_8' | k1_tarski(B_97)=k1_relat_1('#skF_9') | k1_tarski(B_97)=k1_relat_1('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_613, c_622])).
% 49.44/37.00  tff(c_672, plain, (![B_101]: (B_101!='#skF_8' | k1_tarski(B_101)=k1_relat_1('#skF_9'))), inference(factorization, [status(thm), theory('equality')], [c_629])).
% 49.44/37.00  tff(c_694, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_672, c_4])).
% 49.44/37.00  tff(c_687, plain, (![B_101]: (r2_hidden(B_101, k1_relat_1('#skF_9')) | B_101!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_672, c_4])).
% 49.44/37.00  tff(c_6786, plain, (![A_49]: (r2_hidden(k1_funct_1('#skF_9', A_49), k1_xboole_0) | ~r2_hidden(A_49, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_6691, c_36])).
% 49.44/37.00  tff(c_6794, plain, (![A_49]: (r2_hidden(k1_funct_1('#skF_9', A_49), k1_xboole_0) | ~r2_hidden(A_49, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_6786])).
% 49.44/37.00  tff(c_4696, plain, (![A_49]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), k1_funct_1('#skF_9', A_49))='#skF_8' | ~r2_hidden(A_49, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_36, c_4692])).
% 49.44/37.00  tff(c_4711, plain, (![A_49]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), k1_funct_1('#skF_9', A_49))='#skF_8' | ~r2_hidden(A_49, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_4696])).
% 49.44/37.00  tff(c_7055, plain, (![A_6404]: ('#skF_7'('#skF_9', k1_xboole_0, k1_funct_1('#skF_9', A_6404))='#skF_8' | ~r2_hidden(A_6404, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_6691, c_4711])).
% 49.44/37.00  tff(c_7111, plain, (![B_6505]: ('#skF_7'('#skF_9', k1_xboole_0, k1_funct_1('#skF_9', B_6505))='#skF_8' | B_6505!='#skF_8')), inference(resolution, [status(thm)], [c_687, c_7055])).
% 49.44/37.00  tff(c_6783, plain, (![C_45]: (k1_funct_1('#skF_9', '#skF_7'('#skF_9', k1_xboole_0, C_45))=C_45 | ~r2_hidden(C_45, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_6691, c_20])).
% 49.44/37.00  tff(c_6792, plain, (![C_45]: (k1_funct_1('#skF_9', '#skF_7'('#skF_9', k1_xboole_0, C_45))=C_45 | ~r2_hidden(C_45, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_6691, c_6783])).
% 49.44/37.00  tff(c_7431, plain, (![B_7112]: (k1_funct_1('#skF_9', B_7112)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(k1_funct_1('#skF_9', B_7112), k1_xboole_0) | B_7112!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_7111, c_6792])).
% 49.44/37.00  tff(c_7472, plain, (![A_7213]: (k1_funct_1('#skF_9', A_7213)=k1_funct_1('#skF_9', '#skF_8') | A_7213!='#skF_8' | ~r2_hidden(A_7213, k1_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_6794, c_7431])).
% 49.44/37.00  tff(c_7535, plain, (![B_7314]: (k1_funct_1('#skF_9', B_7314)=k1_funct_1('#skF_9', '#skF_8') | B_7314!='#skF_8')), inference(resolution, [status(thm)], [c_687, c_7472])).
% 49.44/37.00  tff(c_7555, plain, (![B_7314]: (r2_hidden(k1_funct_1('#skF_9', B_7314), k1_xboole_0) | ~r2_hidden('#skF_8', k1_relat_1('#skF_9')) | B_7314!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_7535, c_6794])).
% 49.44/37.00  tff(c_7650, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_8'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_694, c_7555])).
% 49.44/37.00  tff(c_4691, plain, (![C_3209]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_3209)='#skF_8' | ~r2_hidden(C_3209, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_4649])).
% 49.44/37.00  tff(c_6829, plain, (![C_5796]: ('#skF_7'('#skF_9', k1_xboole_0, C_5796)='#skF_8' | ~r2_hidden(C_5796, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_6691, c_6691, c_4691])).
% 49.44/37.00  tff(c_8980, plain, (![A_8936]: ('#skF_7'('#skF_9', k1_xboole_0, '#skF_2'(A_8936, k1_xboole_0))='#skF_8' | '#skF_1'(A_8936, k1_xboole_0)=A_8936 | k1_tarski(A_8936)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_6829])).
% 49.44/37.00  tff(c_252228, plain, (![A_268576]: (k1_funct_1('#skF_9', '#skF_8')='#skF_2'(A_268576, k1_xboole_0) | ~r2_hidden('#skF_2'(A_268576, k1_xboole_0), k1_xboole_0) | '#skF_1'(A_268576, k1_xboole_0)=A_268576 | k1_tarski(A_268576)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8980, c_6792])).
% 49.44/37.00  tff(c_252639, plain, (![A_269337]: (k1_funct_1('#skF_9', '#skF_8')='#skF_2'(A_269337, k1_xboole_0) | '#skF_1'(A_269337, k1_xboole_0)=A_269337 | k1_tarski(A_269337)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_252228])).
% 49.44/37.00  tff(c_253935, plain, ('#skF_2'(k1_funct_1('#skF_9', '#skF_8'), k1_xboole_0)=k1_funct_1('#skF_9', '#skF_8') | '#skF_1'(k1_funct_1('#skF_9', '#skF_8'), k1_xboole_0)=k1_funct_1('#skF_9', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_252639, c_6776])).
% 49.44/37.00  tff(c_256386, plain, ('#skF_1'(k1_funct_1('#skF_9', '#skF_8'), k1_xboole_0)=k1_funct_1('#skF_9', '#skF_8')), inference(splitLeft, [status(thm)], [c_253935])).
% 49.44/37.00  tff(c_10, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r2_hidden('#skF_2'(A_1, B_2), B_2) | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 49.44/37.00  tff(c_6, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | '#skF_2'(A_1, B_2)!=A_1 | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 49.44/37.00  tff(c_256393, plain, (~r2_hidden(k1_funct_1('#skF_9', '#skF_8'), k1_xboole_0) | '#skF_2'(k1_funct_1('#skF_9', '#skF_8'), k1_xboole_0)!=k1_funct_1('#skF_9', '#skF_8') | k1_tarski(k1_funct_1('#skF_9', '#skF_8'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_256386, c_6])).
% 49.44/37.00  tff(c_256742, plain, ('#skF_2'(k1_funct_1('#skF_9', '#skF_8'), k1_xboole_0)!=k1_funct_1('#skF_9', '#skF_8') | k1_tarski(k1_funct_1('#skF_9', '#skF_8'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7650, c_256393])).
% 49.44/37.00  tff(c_256743, plain, ('#skF_2'(k1_funct_1('#skF_9', '#skF_8'), k1_xboole_0)!=k1_funct_1('#skF_9', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_6776, c_256742])).
% 49.44/37.00  tff(c_6857, plain, (![A_1]: ('#skF_7'('#skF_9', k1_xboole_0, '#skF_2'(A_1, k1_xboole_0))='#skF_8' | ~r2_hidden('#skF_1'(A_1, k1_xboole_0), k1_xboole_0) | k1_tarski(A_1)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_6829])).
% 49.44/37.00  tff(c_256390, plain, ('#skF_7'('#skF_9', k1_xboole_0, '#skF_2'(k1_funct_1('#skF_9', '#skF_8'), k1_xboole_0))='#skF_8' | ~r2_hidden(k1_funct_1('#skF_9', '#skF_8'), k1_xboole_0) | k1_tarski(k1_funct_1('#skF_9', '#skF_8'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_256386, c_6857])).
% 49.44/37.00  tff(c_256739, plain, ('#skF_7'('#skF_9', k1_xboole_0, '#skF_2'(k1_funct_1('#skF_9', '#skF_8'), k1_xboole_0))='#skF_8' | k1_tarski(k1_funct_1('#skF_9', '#skF_8'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7650, c_256390])).
% 49.44/37.00  tff(c_256740, plain, ('#skF_7'('#skF_9', k1_xboole_0, '#skF_2'(k1_funct_1('#skF_9', '#skF_8'), k1_xboole_0))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_6776, c_256739])).
% 49.44/37.00  tff(c_256867, plain, ('#skF_2'(k1_funct_1('#skF_9', '#skF_8'), k1_xboole_0)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden('#skF_2'(k1_funct_1('#skF_9', '#skF_8'), k1_xboole_0), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_256740, c_6792])).
% 49.44/37.00  tff(c_257473, plain, (~r2_hidden('#skF_2'(k1_funct_1('#skF_9', '#skF_8'), k1_xboole_0), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_256743, c_256867])).
% 49.44/37.00  tff(c_257670, plain, (~r2_hidden('#skF_1'(k1_funct_1('#skF_9', '#skF_8'), k1_xboole_0), k1_xboole_0) | k1_tarski(k1_funct_1('#skF_9', '#skF_8'))=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_257473])).
% 49.44/37.00  tff(c_257688, plain, (k1_tarski(k1_funct_1('#skF_9', '#skF_8'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7650, c_256386, c_257670])).
% 49.44/37.00  tff(c_257690, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6776, c_257688])).
% 49.44/37.00  tff(c_257692, plain, ('#skF_1'(k1_funct_1('#skF_9', '#skF_8'), k1_xboole_0)!=k1_funct_1('#skF_9', '#skF_8')), inference(splitRight, [status(thm)], [c_253935])).
% 49.44/37.00  tff(c_257691, plain, ('#skF_2'(k1_funct_1('#skF_9', '#skF_8'), k1_xboole_0)=k1_funct_1('#skF_9', '#skF_8')), inference(splitRight, [status(thm)], [c_253935])).
% 49.44/37.00  tff(c_8, plain, (![A_1, B_2]: ('#skF_1'(A_1, B_2)=A_1 | '#skF_2'(A_1, B_2)!=A_1 | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 49.44/37.00  tff(c_257730, plain, ('#skF_1'(k1_funct_1('#skF_9', '#skF_8'), k1_xboole_0)=k1_funct_1('#skF_9', '#skF_8') | k1_tarski(k1_funct_1('#skF_9', '#skF_8'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_257691, c_8])).
% 49.44/37.00  tff(c_258106, plain, ('#skF_1'(k1_funct_1('#skF_9', '#skF_8'), k1_xboole_0)=k1_funct_1('#skF_9', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_6776, c_257730])).
% 49.44/37.00  tff(c_258190, plain, $false, inference(negUnitSimplification, [status(thm)], [c_257692, c_258106])).
% 49.44/37.00  tff(c_258192, plain, (k2_relat_1('#skF_9')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_4714])).
% 49.44/37.00  tff(c_22, plain, (![A_9, C_45]: (r2_hidden('#skF_7'(A_9, k2_relat_1(A_9), C_45), k1_relat_1(A_9)) | ~r2_hidden(C_45, k2_relat_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_61])).
% 49.44/37.00  tff(c_4715, plain, (![A_3371]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), k1_funct_1('#skF_9', A_3371))='#skF_8' | ~r2_hidden(A_3371, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_4696])).
% 49.44/37.00  tff(c_4724, plain, (![A_3371]: (k1_funct_1('#skF_9', A_3371)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(k1_funct_1('#skF_9', A_3371), k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(A_3371, k1_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_4715, c_20])).
% 49.44/37.00  tff(c_258312, plain, (![A_279425]: (k1_funct_1('#skF_9', A_279425)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(k1_funct_1('#skF_9', A_279425), k2_relat_1('#skF_9')) | ~r2_hidden(A_279425, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_4724])).
% 49.44/37.00  tff(c_258335, plain, (![A_49]: (k1_funct_1('#skF_9', A_49)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(A_49, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_36, c_258312])).
% 49.44/37.00  tff(c_258341, plain, (![A_279526]: (k1_funct_1('#skF_9', A_279526)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(A_279526, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_258335])).
% 49.44/37.00  tff(c_258349, plain, (![C_45]: (k1_funct_1('#skF_9', '#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_45))=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(C_45, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_22, c_258341])).
% 49.44/37.00  tff(c_260506, plain, (![C_281850]: (k1_funct_1('#skF_9', '#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_281850))=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(C_281850, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_258349])).
% 49.44/37.00  tff(c_260539, plain, (![C_281850]: (k1_funct_1('#skF_9', '#skF_8')=C_281850 | ~r2_hidden(C_281850, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(C_281850, k2_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_260506, c_20])).
% 49.44/37.00  tff(c_260682, plain, (![C_282054]: (k1_funct_1('#skF_9', '#skF_8')=C_282054 | ~r2_hidden(C_282054, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_260539])).
% 49.44/37.00  tff(c_260717, plain, (![B_7]: ('#skF_3'(k2_relat_1('#skF_9'), B_7)=k1_funct_1('#skF_9', '#skF_8') | k2_relat_1('#skF_9')=k1_xboole_0 | k2_relat_1('#skF_9')=k1_tarski(B_7))), inference(resolution, [status(thm)], [c_16, c_260682])).
% 49.44/37.00  tff(c_260732, plain, (![B_282155]: ('#skF_3'(k2_relat_1('#skF_9'), B_282155)=k1_funct_1('#skF_9', '#skF_8') | k2_relat_1('#skF_9')=k1_tarski(B_282155))), inference(negUnitSimplification, [status(thm)], [c_258192, c_260717])).
% 49.44/37.00  tff(c_260743, plain, (![B_282155]: (k1_funct_1('#skF_9', '#skF_8')!=B_282155 | k2_relat_1('#skF_9')=k1_xboole_0 | k2_relat_1('#skF_9')=k1_tarski(B_282155) | k2_relat_1('#skF_9')=k1_tarski(B_282155))), inference(superposition, [status(thm), theory('equality')], [c_260732, c_14])).
% 49.44/37.00  tff(c_260935, plain, (k1_tarski(k1_funct_1('#skF_9', '#skF_8'))=k2_relat_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_258192, c_260743])).
% 49.44/37.00  tff(c_260939, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_260935, c_38])).
% 49.44/37.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 49.44/37.00  
% 49.44/37.00  Inference rules
% 49.44/37.00  ----------------------
% 49.44/37.00  #Ref     : 41
% 49.44/37.00  #Sup     : 41420
% 49.44/37.00  #Fact    : 26
% 49.44/37.00  #Define  : 0
% 49.44/37.00  #Split   : 36
% 49.44/37.00  #Chain   : 0
% 49.44/37.00  #Close   : 0
% 49.44/37.00  
% 49.44/37.00  Ordering : KBO
% 49.44/37.00  
% 49.44/37.00  Simplification rules
% 49.44/37.00  ----------------------
% 49.44/37.00  #Subsume      : 19854
% 49.44/37.00  #Demod        : 4056
% 49.44/37.00  #Tautology    : 4116
% 49.44/37.00  #SimpNegUnit  : 1911
% 49.44/37.00  #BackRed      : 87
% 49.44/37.00  
% 49.44/37.00  #Partial instantiations: 185938
% 49.44/37.00  #Strategies tried      : 1
% 49.44/37.00  
% 49.44/37.00  Timing (in seconds)
% 49.44/37.00  ----------------------
% 49.44/37.00  Preprocessing        : 0.32
% 49.44/37.00  Parsing              : 0.16
% 49.44/37.00  CNF conversion       : 0.03
% 49.44/37.00  Main loop            : 35.91
% 49.44/37.00  Inferencing          : 4.90
% 49.44/37.00  Reduction            : 5.79
% 49.44/37.00  Demodulation         : 3.79
% 49.44/37.00  BG Simplification    : 0.52
% 49.44/37.00  Subsumption          : 23.10
% 49.44/37.00  Abstraction          : 0.72
% 49.44/37.00  MUC search           : 0.00
% 49.44/37.00  Cooper               : 0.00
% 49.44/37.00  Total                : 36.27
% 49.44/37.00  Index Insertion      : 0.00
% 49.44/37.00  Index Deletion       : 0.00
% 49.44/37.00  Index Matching       : 0.00
% 49.44/37.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
