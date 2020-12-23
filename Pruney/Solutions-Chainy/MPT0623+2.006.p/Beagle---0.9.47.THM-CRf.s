%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:07 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 325 expanded)
%              Number of leaves         :   37 ( 118 expanded)
%              Depth                    :   14
%              Number of atoms          :  162 ( 868 expanded)
%              Number of equality atoms :   61 ( 444 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_121,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_103,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_48,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_86,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_46,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_58,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_552,plain,(
    ! [A_142,B_143] :
      ( r2_hidden(k4_tarski('#skF_3'(A_142,B_143),'#skF_4'(A_142,B_143)),A_142)
      | r2_hidden('#skF_5'(A_142,B_143),B_143)
      | k1_relat_1(A_142) = B_143 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_50,plain,(
    ! [A_41,B_45] :
      ( k1_relat_1('#skF_7'(A_41,B_45)) = A_41
      | k1_xboole_0 = A_41 ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_52,plain,(
    ! [A_41,B_45] :
      ( v1_funct_1('#skF_7'(A_41,B_45))
      | k1_xboole_0 = A_41 ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_54,plain,(
    ! [A_41,B_45] :
      ( v1_relat_1('#skF_7'(A_41,B_45))
      | k1_xboole_0 = A_41 ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_22,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(k1_tarski(A_11),B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_129,plain,(
    ! [A_71,B_72] :
      ( k2_relat_1('#skF_7'(A_71,B_72)) = k1_tarski(B_72)
      | k1_xboole_0 = A_71 ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_56,plain,(
    ! [C_48] :
      ( ~ r1_tarski(k2_relat_1(C_48),'#skF_8')
      | k1_relat_1(C_48) != '#skF_9'
      | ~ v1_funct_1(C_48)
      | ~ v1_relat_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_174,plain,(
    ! [B_89,A_90] :
      ( ~ r1_tarski(k1_tarski(B_89),'#skF_8')
      | k1_relat_1('#skF_7'(A_90,B_89)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_90,B_89))
      | ~ v1_relat_1('#skF_7'(A_90,B_89))
      | k1_xboole_0 = A_90 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_56])).

tff(c_291,plain,(
    ! [A_107,A_108] :
      ( k1_relat_1('#skF_7'(A_107,A_108)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_107,A_108))
      | ~ v1_relat_1('#skF_7'(A_107,A_108))
      | k1_xboole_0 = A_107
      | ~ r2_hidden(A_108,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_22,c_174])).

tff(c_345,plain,(
    ! [A_121,B_122] :
      ( k1_relat_1('#skF_7'(A_121,B_122)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_121,B_122))
      | ~ r2_hidden(B_122,'#skF_8')
      | k1_xboole_0 = A_121 ) ),
    inference(resolution,[status(thm)],[c_54,c_291])).

tff(c_377,plain,(
    ! [A_128,B_129] :
      ( k1_relat_1('#skF_7'(A_128,B_129)) != '#skF_9'
      | ~ r2_hidden(B_129,'#skF_8')
      | k1_xboole_0 = A_128 ) ),
    inference(resolution,[status(thm)],[c_52,c_345])).

tff(c_380,plain,(
    ! [A_41,B_45] :
      ( A_41 != '#skF_9'
      | ~ r2_hidden(B_45,'#skF_8')
      | k1_xboole_0 = A_41
      | k1_xboole_0 = A_41 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_377])).

tff(c_381,plain,(
    ! [B_45] : ~ r2_hidden(B_45,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_380])).

tff(c_646,plain,(
    ! [B_147] :
      ( r2_hidden('#skF_5'('#skF_8',B_147),B_147)
      | k1_relat_1('#skF_8') = B_147 ) ),
    inference(resolution,[status(thm)],[c_552,c_381])).

tff(c_673,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_646,c_381])).

tff(c_581,plain,(
    ! [B_143] :
      ( r2_hidden('#skF_5'('#skF_8',B_143),B_143)
      | k1_relat_1('#skF_8') = B_143 ) ),
    inference(resolution,[status(thm)],[c_552,c_381])).

tff(c_678,plain,(
    ! [B_143] :
      ( r2_hidden('#skF_5'('#skF_8',B_143),B_143)
      | B_143 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_673,c_581])).

tff(c_715,plain,(
    ! [B_151] :
      ( r2_hidden('#skF_5'('#skF_8',B_151),B_151)
      | B_151 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_673,c_581])).

tff(c_12,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r1_xboole_0(A_8,B_9)
      | k4_xboole_0(A_8,B_9) != A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_143,plain,(
    ! [A_77,B_78,C_79] :
      ( ~ r1_xboole_0(A_77,B_78)
      | ~ r2_hidden(C_79,B_78)
      | ~ r2_hidden(C_79,A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_148,plain,(
    ! [C_83,B_84,A_85] :
      ( ~ r2_hidden(C_83,B_84)
      | ~ r2_hidden(C_83,A_85)
      | k4_xboole_0(A_85,B_84) != A_85 ) ),
    inference(resolution,[status(thm)],[c_16,c_143])).

tff(c_179,plain,(
    ! [A_91,B_92,A_93] :
      ( ~ r2_hidden('#skF_1'(A_91,B_92),A_93)
      | k4_xboole_0(A_93,B_92) != A_93
      | r1_xboole_0(A_91,B_92) ) ),
    inference(resolution,[status(thm)],[c_6,c_148])).

tff(c_188,plain,(
    ! [B_94,A_95] :
      ( k4_xboole_0(B_94,B_94) != B_94
      | r1_xboole_0(A_95,B_94) ) ),
    inference(resolution,[status(thm)],[c_6,c_179])).

tff(c_193,plain,(
    ! [A_96] : r1_xboole_0(A_96,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_188])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_199,plain,(
    ! [C_5,A_96] :
      ( ~ r2_hidden(C_5,k1_xboole_0)
      | ~ r2_hidden(C_5,A_96) ) ),
    inference(resolution,[status(thm)],[c_193,c_4])).

tff(c_724,plain,(
    ! [A_96] :
      ( ~ r2_hidden('#skF_5'('#skF_8',k1_xboole_0),A_96)
      | k1_xboole_0 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_715,c_199])).

tff(c_739,plain,(
    ! [A_152] : ~ r2_hidden('#skF_5'('#skF_8',k1_xboole_0),A_152) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_724])).

tff(c_743,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_678,c_739])).

tff(c_747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_743])).

tff(c_749,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_380])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_87,plain,(
    ! [A_53] :
      ( v1_relat_1(A_53)
      | ~ v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_91,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_87])).

tff(c_76,plain,(
    ! [A_51] :
      ( v1_funct_1(A_51)
      | ~ v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_80,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_76])).

tff(c_44,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_42,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_81,plain,(
    ! [C_52] :
      ( ~ r1_tarski(k2_relat_1(C_52),'#skF_8')
      | k1_relat_1(C_52) != '#skF_9'
      | ~ v1_funct_1(C_52)
      | ~ v1_relat_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_84,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_8')
    | k1_relat_1(k1_xboole_0) != '#skF_9'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_81])).

tff(c_86,plain,
    ( k1_xboole_0 != '#skF_9'
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_44,c_10,c_84])).

tff(c_93,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_86])).

tff(c_773,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_749,c_93])).

tff(c_775,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_774,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_784,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_775,c_774])).

tff(c_779,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_774,c_2])).

tff(c_789,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_784,c_779])).

tff(c_826,plain,(
    ! [A_157] :
      ( v1_relat_1(A_157)
      | ~ v1_xboole_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_830,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_789,c_826])).

tff(c_806,plain,(
    ! [A_154] :
      ( v1_funct_1(A_154)
      | ~ v1_xboole_0(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_810,plain,(
    v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_789,c_806])).

tff(c_777,plain,(
    k1_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_774,c_774,c_44])).

tff(c_801,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_784,c_784,c_777])).

tff(c_776,plain,(
    ! [A_6] : r1_tarski('#skF_9',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_774,c_10])).

tff(c_799,plain,(
    ! [A_6] : r1_tarski('#skF_8',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_784,c_776])).

tff(c_778,plain,(
    k2_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_774,c_774,c_42])).

tff(c_794,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_784,c_784,c_778])).

tff(c_812,plain,(
    ! [C_155] :
      ( ~ r1_tarski(k2_relat_1(C_155),'#skF_8')
      | k1_relat_1(C_155) != '#skF_8'
      | ~ v1_funct_1(C_155)
      | ~ v1_relat_1(C_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_784,c_56])).

tff(c_815,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | k1_relat_1('#skF_8') != '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_794,c_812])).

tff(c_817,plain,
    ( ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_801,c_799,c_815])).

tff(c_832,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_810,c_817])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:49:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.19/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.40  
% 2.81/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.40  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_5 > #skF_4
% 2.81/1.40  
% 2.81/1.40  %Foreground sorts:
% 2.81/1.40  
% 2.81/1.40  
% 2.81/1.40  %Background operators:
% 2.81/1.40  
% 2.81/1.40  
% 2.81/1.40  %Foreground operators:
% 2.81/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.81/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.81/1.40  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.81/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.81/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.81/1.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.81/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.81/1.40  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.81/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.81/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.81/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.81/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.81/1.40  tff('#skF_9', type, '#skF_9': $i).
% 2.81/1.40  tff('#skF_8', type, '#skF_8': $i).
% 2.81/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.81/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.81/1.40  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.81/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.81/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.81/1.40  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.81/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.81/1.40  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.81/1.40  
% 2.81/1.42  tff(f_121, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 2.81/1.42  tff(f_83, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 2.81/1.42  tff(f_103, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_funct_1)).
% 2.81/1.42  tff(f_58, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.81/1.42  tff(f_48, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.81/1.42  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.81/1.42  tff(f_52, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.81/1.42  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.81/1.42  tff(f_75, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.81/1.42  tff(f_90, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 2.81/1.42  tff(f_86, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.81/1.42  tff(f_46, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.81/1.42  tff(c_58, plain, (k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.81/1.42  tff(c_68, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_58])).
% 2.81/1.42  tff(c_552, plain, (![A_142, B_143]: (r2_hidden(k4_tarski('#skF_3'(A_142, B_143), '#skF_4'(A_142, B_143)), A_142) | r2_hidden('#skF_5'(A_142, B_143), B_143) | k1_relat_1(A_142)=B_143)), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.81/1.42  tff(c_50, plain, (![A_41, B_45]: (k1_relat_1('#skF_7'(A_41, B_45))=A_41 | k1_xboole_0=A_41)), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.81/1.42  tff(c_52, plain, (![A_41, B_45]: (v1_funct_1('#skF_7'(A_41, B_45)) | k1_xboole_0=A_41)), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.81/1.42  tff(c_54, plain, (![A_41, B_45]: (v1_relat_1('#skF_7'(A_41, B_45)) | k1_xboole_0=A_41)), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.81/1.42  tff(c_22, plain, (![A_11, B_12]: (r1_tarski(k1_tarski(A_11), B_12) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.81/1.42  tff(c_129, plain, (![A_71, B_72]: (k2_relat_1('#skF_7'(A_71, B_72))=k1_tarski(B_72) | k1_xboole_0=A_71)), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.81/1.42  tff(c_56, plain, (![C_48]: (~r1_tarski(k2_relat_1(C_48), '#skF_8') | k1_relat_1(C_48)!='#skF_9' | ~v1_funct_1(C_48) | ~v1_relat_1(C_48))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.81/1.42  tff(c_174, plain, (![B_89, A_90]: (~r1_tarski(k1_tarski(B_89), '#skF_8') | k1_relat_1('#skF_7'(A_90, B_89))!='#skF_9' | ~v1_funct_1('#skF_7'(A_90, B_89)) | ~v1_relat_1('#skF_7'(A_90, B_89)) | k1_xboole_0=A_90)), inference(superposition, [status(thm), theory('equality')], [c_129, c_56])).
% 2.81/1.42  tff(c_291, plain, (![A_107, A_108]: (k1_relat_1('#skF_7'(A_107, A_108))!='#skF_9' | ~v1_funct_1('#skF_7'(A_107, A_108)) | ~v1_relat_1('#skF_7'(A_107, A_108)) | k1_xboole_0=A_107 | ~r2_hidden(A_108, '#skF_8'))), inference(resolution, [status(thm)], [c_22, c_174])).
% 2.81/1.42  tff(c_345, plain, (![A_121, B_122]: (k1_relat_1('#skF_7'(A_121, B_122))!='#skF_9' | ~v1_funct_1('#skF_7'(A_121, B_122)) | ~r2_hidden(B_122, '#skF_8') | k1_xboole_0=A_121)), inference(resolution, [status(thm)], [c_54, c_291])).
% 2.81/1.42  tff(c_377, plain, (![A_128, B_129]: (k1_relat_1('#skF_7'(A_128, B_129))!='#skF_9' | ~r2_hidden(B_129, '#skF_8') | k1_xboole_0=A_128)), inference(resolution, [status(thm)], [c_52, c_345])).
% 2.81/1.42  tff(c_380, plain, (![A_41, B_45]: (A_41!='#skF_9' | ~r2_hidden(B_45, '#skF_8') | k1_xboole_0=A_41 | k1_xboole_0=A_41)), inference(superposition, [status(thm), theory('equality')], [c_50, c_377])).
% 2.81/1.42  tff(c_381, plain, (![B_45]: (~r2_hidden(B_45, '#skF_8'))), inference(splitLeft, [status(thm)], [c_380])).
% 2.81/1.42  tff(c_646, plain, (![B_147]: (r2_hidden('#skF_5'('#skF_8', B_147), B_147) | k1_relat_1('#skF_8')=B_147)), inference(resolution, [status(thm)], [c_552, c_381])).
% 2.81/1.42  tff(c_673, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_646, c_381])).
% 2.81/1.42  tff(c_581, plain, (![B_143]: (r2_hidden('#skF_5'('#skF_8', B_143), B_143) | k1_relat_1('#skF_8')=B_143)), inference(resolution, [status(thm)], [c_552, c_381])).
% 2.81/1.42  tff(c_678, plain, (![B_143]: (r2_hidden('#skF_5'('#skF_8', B_143), B_143) | B_143='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_673, c_581])).
% 2.81/1.42  tff(c_715, plain, (![B_151]: (r2_hidden('#skF_5'('#skF_8', B_151), B_151) | B_151='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_673, c_581])).
% 2.81/1.42  tff(c_12, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.81/1.42  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.81/1.42  tff(c_16, plain, (![A_8, B_9]: (r1_xboole_0(A_8, B_9) | k4_xboole_0(A_8, B_9)!=A_8)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.81/1.42  tff(c_143, plain, (![A_77, B_78, C_79]: (~r1_xboole_0(A_77, B_78) | ~r2_hidden(C_79, B_78) | ~r2_hidden(C_79, A_77))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.81/1.42  tff(c_148, plain, (![C_83, B_84, A_85]: (~r2_hidden(C_83, B_84) | ~r2_hidden(C_83, A_85) | k4_xboole_0(A_85, B_84)!=A_85)), inference(resolution, [status(thm)], [c_16, c_143])).
% 2.81/1.42  tff(c_179, plain, (![A_91, B_92, A_93]: (~r2_hidden('#skF_1'(A_91, B_92), A_93) | k4_xboole_0(A_93, B_92)!=A_93 | r1_xboole_0(A_91, B_92))), inference(resolution, [status(thm)], [c_6, c_148])).
% 2.81/1.42  tff(c_188, plain, (![B_94, A_95]: (k4_xboole_0(B_94, B_94)!=B_94 | r1_xboole_0(A_95, B_94))), inference(resolution, [status(thm)], [c_6, c_179])).
% 2.81/1.42  tff(c_193, plain, (![A_96]: (r1_xboole_0(A_96, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_188])).
% 2.81/1.42  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.81/1.42  tff(c_199, plain, (![C_5, A_96]: (~r2_hidden(C_5, k1_xboole_0) | ~r2_hidden(C_5, A_96))), inference(resolution, [status(thm)], [c_193, c_4])).
% 2.81/1.42  tff(c_724, plain, (![A_96]: (~r2_hidden('#skF_5'('#skF_8', k1_xboole_0), A_96) | k1_xboole_0='#skF_8')), inference(resolution, [status(thm)], [c_715, c_199])).
% 2.81/1.42  tff(c_739, plain, (![A_152]: (~r2_hidden('#skF_5'('#skF_8', k1_xboole_0), A_152))), inference(negUnitSimplification, [status(thm)], [c_68, c_724])).
% 2.81/1.42  tff(c_743, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_678, c_739])).
% 2.81/1.42  tff(c_747, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_743])).
% 2.81/1.42  tff(c_749, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_380])).
% 2.81/1.42  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.81/1.42  tff(c_87, plain, (![A_53]: (v1_relat_1(A_53) | ~v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.81/1.42  tff(c_91, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_87])).
% 2.81/1.42  tff(c_76, plain, (![A_51]: (v1_funct_1(A_51) | ~v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.81/1.42  tff(c_80, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_76])).
% 2.81/1.42  tff(c_44, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.81/1.42  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.81/1.42  tff(c_42, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.81/1.42  tff(c_81, plain, (![C_52]: (~r1_tarski(k2_relat_1(C_52), '#skF_8') | k1_relat_1(C_52)!='#skF_9' | ~v1_funct_1(C_52) | ~v1_relat_1(C_52))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.81/1.42  tff(c_84, plain, (~r1_tarski(k1_xboole_0, '#skF_8') | k1_relat_1(k1_xboole_0)!='#skF_9' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_42, c_81])).
% 2.81/1.42  tff(c_86, plain, (k1_xboole_0!='#skF_9' | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_44, c_10, c_84])).
% 2.81/1.42  tff(c_93, plain, (k1_xboole_0!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_91, c_86])).
% 2.81/1.42  tff(c_773, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_749, c_93])).
% 2.81/1.42  tff(c_775, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_58])).
% 2.81/1.42  tff(c_774, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_58])).
% 2.81/1.42  tff(c_784, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_775, c_774])).
% 2.81/1.42  tff(c_779, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_774, c_2])).
% 2.81/1.42  tff(c_789, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_784, c_779])).
% 2.81/1.42  tff(c_826, plain, (![A_157]: (v1_relat_1(A_157) | ~v1_xboole_0(A_157))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.81/1.42  tff(c_830, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_789, c_826])).
% 2.81/1.42  tff(c_806, plain, (![A_154]: (v1_funct_1(A_154) | ~v1_xboole_0(A_154))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.81/1.42  tff(c_810, plain, (v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_789, c_806])).
% 2.81/1.42  tff(c_777, plain, (k1_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_774, c_774, c_44])).
% 2.81/1.42  tff(c_801, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_784, c_784, c_777])).
% 2.81/1.42  tff(c_776, plain, (![A_6]: (r1_tarski('#skF_9', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_774, c_10])).
% 2.81/1.42  tff(c_799, plain, (![A_6]: (r1_tarski('#skF_8', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_784, c_776])).
% 2.81/1.42  tff(c_778, plain, (k2_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_774, c_774, c_42])).
% 2.81/1.42  tff(c_794, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_784, c_784, c_778])).
% 2.81/1.42  tff(c_812, plain, (![C_155]: (~r1_tarski(k2_relat_1(C_155), '#skF_8') | k1_relat_1(C_155)!='#skF_8' | ~v1_funct_1(C_155) | ~v1_relat_1(C_155))), inference(demodulation, [status(thm), theory('equality')], [c_784, c_56])).
% 2.81/1.42  tff(c_815, plain, (~r1_tarski('#skF_8', '#skF_8') | k1_relat_1('#skF_8')!='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_794, c_812])).
% 2.81/1.42  tff(c_817, plain, (~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_801, c_799, c_815])).
% 2.81/1.42  tff(c_832, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_830, c_810, c_817])).
% 2.81/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.42  
% 2.81/1.42  Inference rules
% 2.81/1.42  ----------------------
% 2.81/1.42  #Ref     : 0
% 2.81/1.42  #Sup     : 160
% 2.81/1.42  #Fact    : 0
% 2.81/1.42  #Define  : 0
% 2.81/1.42  #Split   : 2
% 2.81/1.42  #Chain   : 0
% 2.81/1.42  #Close   : 0
% 2.81/1.42  
% 2.81/1.42  Ordering : KBO
% 2.81/1.42  
% 2.81/1.42  Simplification rules
% 2.81/1.42  ----------------------
% 2.81/1.42  #Subsume      : 23
% 2.81/1.42  #Demod        : 110
% 2.81/1.42  #Tautology    : 78
% 2.81/1.42  #SimpNegUnit  : 3
% 2.81/1.42  #BackRed      : 36
% 2.81/1.42  
% 2.81/1.42  #Partial instantiations: 0
% 2.81/1.42  #Strategies tried      : 1
% 2.81/1.42  
% 2.81/1.42  Timing (in seconds)
% 2.81/1.42  ----------------------
% 2.81/1.42  Preprocessing        : 0.32
% 2.81/1.42  Parsing              : 0.16
% 2.81/1.42  CNF conversion       : 0.02
% 2.81/1.42  Main loop            : 0.33
% 2.81/1.42  Inferencing          : 0.12
% 2.81/1.42  Reduction            : 0.09
% 2.81/1.42  Demodulation         : 0.06
% 2.81/1.42  BG Simplification    : 0.02
% 2.81/1.42  Subsumption          : 0.06
% 2.81/1.42  Abstraction          : 0.02
% 2.81/1.42  MUC search           : 0.00
% 2.81/1.42  Cooper               : 0.00
% 2.81/1.42  Total                : 0.69
% 2.81/1.42  Index Insertion      : 0.00
% 2.81/1.43  Index Deletion       : 0.00
% 2.81/1.43  Index Matching       : 0.00
% 2.81/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
