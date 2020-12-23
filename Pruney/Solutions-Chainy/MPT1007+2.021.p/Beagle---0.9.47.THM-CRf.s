%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:13 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 301 expanded)
%              Number of leaves         :   43 ( 120 expanded)
%              Depth                    :   17
%              Number of atoms          :  174 ( 608 expanded)
%              Number of equality atoms :   54 ( 156 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_42,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_130,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_51,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_118,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_92,plain,(
    ! [A_50,B_51] :
      ( r2_hidden(A_50,B_51)
      | ~ r1_tarski(k1_tarski(A_50),B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_101,plain,(
    ! [A_50] : r2_hidden(A_50,k1_tarski(A_50)) ),
    inference(resolution,[status(thm)],[c_14,c_92])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_145,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_149,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_145])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_211,plain,(
    ! [C_78,B_79,A_80] :
      ( v5_relat_1(C_78,B_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_80,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_215,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_211])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_378,plain,(
    ! [B_92,C_93,A_94] :
      ( r2_hidden(k1_funct_1(B_92,C_93),A_94)
      | ~ r2_hidden(C_93,k1_relat_1(B_92))
      | ~ v1_funct_1(B_92)
      | ~ v5_relat_1(B_92,A_94)
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_56,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_388,plain,
    ( ~ r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_378,c_56])).

tff(c_393,plain,(
    ~ r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_215,c_64,c_388])).

tff(c_42,plain,(
    ! [A_22] :
      ( k2_relat_1(A_22) = k1_xboole_0
      | k1_relat_1(A_22) != k1_xboole_0
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_156,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_149,c_42])).

tff(c_162,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_195,plain,(
    ! [C_72,A_73,B_74] :
      ( v4_relat_1(C_72,A_73)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_199,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_195])).

tff(c_36,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k1_relat_1(B_20),A_19)
      | ~ v4_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_164,plain,(
    ! [B_67,A_68] :
      ( k1_tarski(B_67) = A_68
      | k1_xboole_0 = A_68
      | ~ r1_tarski(A_68,k1_tarski(B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_677,plain,(
    ! [B_126,B_127] :
      ( k1_tarski(B_126) = k1_relat_1(B_127)
      | k1_relat_1(B_127) = k1_xboole_0
      | ~ v4_relat_1(B_127,k1_tarski(B_126))
      | ~ v1_relat_1(B_127) ) ),
    inference(resolution,[status(thm)],[c_36,c_164])).

tff(c_683,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_199,c_677])).

tff(c_687,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_683])).

tff(c_688,plain,(
    k1_tarski('#skF_2') = k1_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_687])).

tff(c_739,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_688,c_101])).

tff(c_765,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_393,c_739])).

tff(c_766,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_38,plain,(
    ! [A_21] :
      ( ~ v1_xboole_0(k2_relat_1(A_21))
      | ~ v1_relat_1(A_21)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_771,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_766,c_38])).

tff(c_775,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_6,c_771])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_780,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_775,c_8])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_801,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_780,c_58])).

tff(c_22,plain,(
    ! [A_14] : ~ v1_xboole_0(k1_tarski(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(k1_tarski(A_15),B_16)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    ! [B_18,A_17] :
      ( k1_tarski(B_18) = A_17
      | k1_xboole_0 = A_17
      | ~ r1_tarski(A_17,k1_tarski(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_876,plain,(
    ! [B_138,A_139] :
      ( k1_tarski(B_138) = A_139
      | A_139 = '#skF_4'
      | ~ r1_tarski(A_139,k1_tarski(B_138)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_780,c_28])).

tff(c_984,plain,(
    ! [B_155,A_156] :
      ( k1_tarski(B_155) = k1_tarski(A_156)
      | k1_tarski(A_156) = '#skF_4'
      | ~ r2_hidden(A_156,k1_tarski(B_155)) ) ),
    inference(resolution,[status(thm)],[c_26,c_876])).

tff(c_991,plain,(
    ! [B_155] :
      ( k1_tarski('#skF_1'(k1_tarski(B_155))) = k1_tarski(B_155)
      | k1_tarski('#skF_1'(k1_tarski(B_155))) = '#skF_4'
      | v1_xboole_0(k1_tarski(B_155)) ) ),
    inference(resolution,[status(thm)],[c_4,c_984])).

tff(c_996,plain,(
    ! [B_155] :
      ( k1_tarski('#skF_1'(k1_tarski(B_155))) = k1_tarski(B_155)
      | k1_tarski('#skF_1'(k1_tarski(B_155))) = '#skF_4' ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_991])).

tff(c_1065,plain,(
    ! [B_161] :
      ( k1_tarski('#skF_1'(k1_tarski(B_161))) = '#skF_4'
      | k1_tarski(B_161) != '#skF_4' ) ),
    inference(factorization,[status(thm),theory(equality)],[c_996])).

tff(c_1102,plain,(
    ! [B_161] :
      ( ~ v1_xboole_0('#skF_4')
      | k1_tarski(B_161) != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1065,c_22])).

tff(c_1120,plain,(
    ! [B_161] : k1_tarski(B_161) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_775,c_1102])).

tff(c_32,plain,(
    ! [B_18] : r1_tarski(k1_xboole_0,k1_tarski(B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_119,plain,(
    ! [B_58,A_59] :
      ( B_58 = A_59
      | ~ r1_tarski(B_58,A_59)
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_132,plain,(
    ! [B_60] :
      ( k1_tarski(B_60) = k1_xboole_0
      | ~ r1_tarski(k1_tarski(B_60),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_32,c_119])).

tff(c_137,plain,(
    ! [A_15] :
      ( k1_tarski(A_15) = k1_xboole_0
      | ~ r2_hidden(A_15,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_132])).

tff(c_794,plain,(
    ! [A_15] :
      ( k1_tarski(A_15) = '#skF_4'
      | ~ r2_hidden(A_15,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_780,c_780,c_137])).

tff(c_1126,plain,(
    ! [A_15] : ~ r2_hidden(A_15,'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1120,c_794])).

tff(c_62,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_793,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_780,c_766])).

tff(c_974,plain,(
    ! [A_152,B_153,C_154] :
      ( k2_relset_1(A_152,B_153,C_154) = k2_relat_1(C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_977,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_974])).

tff(c_979,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_793,c_977])).

tff(c_54,plain,(
    ! [D_39,C_38,A_36,B_37] :
      ( r2_hidden(k1_funct_1(D_39,C_38),k2_relset_1(A_36,B_37,D_39))
      | k1_xboole_0 = B_37
      | ~ r2_hidden(C_38,A_36)
      | ~ m1_subset_1(D_39,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_funct_2(D_39,A_36,B_37)
      | ~ v1_funct_1(D_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1147,plain,(
    ! [D_165,C_166,A_167,B_168] :
      ( r2_hidden(k1_funct_1(D_165,C_166),k2_relset_1(A_167,B_168,D_165))
      | B_168 = '#skF_4'
      | ~ r2_hidden(C_166,A_167)
      | ~ m1_subset_1(D_165,k1_zfmisc_1(k2_zfmisc_1(A_167,B_168)))
      | ~ v1_funct_2(D_165,A_167,B_168)
      | ~ v1_funct_1(D_165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_780,c_54])).

tff(c_1153,plain,(
    ! [C_166] :
      ( r2_hidden(k1_funct_1('#skF_4',C_166),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_166,k1_tarski('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3')))
      | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_979,c_1147])).

tff(c_1156,plain,(
    ! [C_166] :
      ( r2_hidden(k1_funct_1('#skF_4',C_166),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_166,k1_tarski('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_1153])).

tff(c_1158,plain,(
    ! [C_169] : ~ r2_hidden(C_169,k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_801,c_1126,c_1156])).

tff(c_1172,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_101,c_1158])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:45:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.49  
% 3.10/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.50  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.10/1.50  
% 3.10/1.50  %Foreground sorts:
% 3.10/1.50  
% 3.10/1.50  
% 3.10/1.50  %Background operators:
% 3.10/1.50  
% 3.10/1.50  
% 3.10/1.50  %Foreground operators:
% 3.10/1.50  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.10/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.10/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.10/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.10/1.50  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.10/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.10/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.10/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.10/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.10/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.10/1.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.10/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.10/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.10/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.10/1.50  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.10/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.10/1.50  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.10/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.10/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.10/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.10/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.50  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.10/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.10/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.10/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.10/1.50  
% 3.10/1.51  tff(f_42, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.10/1.51  tff(f_55, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.10/1.51  tff(f_130, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 3.10/1.51  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.10/1.51  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.10/1.51  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.10/1.51  tff(f_92, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 3.10/1.51  tff(f_81, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 3.10/1.51  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.10/1.51  tff(f_61, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.10/1.51  tff(f_75, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 3.10/1.51  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.10/1.51  tff(f_51, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 3.10/1.51  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.10/1.51  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.10/1.51  tff(f_118, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 3.10/1.51  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.10/1.51  tff(c_92, plain, (![A_50, B_51]: (r2_hidden(A_50, B_51) | ~r1_tarski(k1_tarski(A_50), B_51))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.10/1.51  tff(c_101, plain, (![A_50]: (r2_hidden(A_50, k1_tarski(A_50)))), inference(resolution, [status(thm)], [c_14, c_92])).
% 3.10/1.51  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.10/1.51  tff(c_145, plain, (![C_62, A_63, B_64]: (v1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.10/1.51  tff(c_149, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_145])).
% 3.10/1.51  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.10/1.51  tff(c_211, plain, (![C_78, B_79, A_80]: (v5_relat_1(C_78, B_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_80, B_79))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.10/1.51  tff(c_215, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_211])).
% 3.10/1.51  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.10/1.51  tff(c_378, plain, (![B_92, C_93, A_94]: (r2_hidden(k1_funct_1(B_92, C_93), A_94) | ~r2_hidden(C_93, k1_relat_1(B_92)) | ~v1_funct_1(B_92) | ~v5_relat_1(B_92, A_94) | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.10/1.51  tff(c_56, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.10/1.51  tff(c_388, plain, (~r2_hidden('#skF_2', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_378, c_56])).
% 3.10/1.51  tff(c_393, plain, (~r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_215, c_64, c_388])).
% 3.10/1.51  tff(c_42, plain, (![A_22]: (k2_relat_1(A_22)=k1_xboole_0 | k1_relat_1(A_22)!=k1_xboole_0 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.10/1.51  tff(c_156, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_149, c_42])).
% 3.10/1.51  tff(c_162, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_156])).
% 3.10/1.51  tff(c_195, plain, (![C_72, A_73, B_74]: (v4_relat_1(C_72, A_73) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.10/1.51  tff(c_199, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_60, c_195])).
% 3.10/1.51  tff(c_36, plain, (![B_20, A_19]: (r1_tarski(k1_relat_1(B_20), A_19) | ~v4_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.10/1.51  tff(c_164, plain, (![B_67, A_68]: (k1_tarski(B_67)=A_68 | k1_xboole_0=A_68 | ~r1_tarski(A_68, k1_tarski(B_67)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.10/1.51  tff(c_677, plain, (![B_126, B_127]: (k1_tarski(B_126)=k1_relat_1(B_127) | k1_relat_1(B_127)=k1_xboole_0 | ~v4_relat_1(B_127, k1_tarski(B_126)) | ~v1_relat_1(B_127))), inference(resolution, [status(thm)], [c_36, c_164])).
% 3.10/1.51  tff(c_683, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_199, c_677])).
% 3.10/1.51  tff(c_687, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_149, c_683])).
% 3.10/1.51  tff(c_688, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_162, c_687])).
% 3.10/1.51  tff(c_739, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_688, c_101])).
% 3.10/1.51  tff(c_765, plain, $false, inference(negUnitSimplification, [status(thm)], [c_393, c_739])).
% 3.10/1.51  tff(c_766, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_156])).
% 3.10/1.51  tff(c_38, plain, (![A_21]: (~v1_xboole_0(k2_relat_1(A_21)) | ~v1_relat_1(A_21) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.10/1.51  tff(c_771, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_766, c_38])).
% 3.10/1.51  tff(c_775, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_6, c_771])).
% 3.10/1.51  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.10/1.51  tff(c_780, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_775, c_8])).
% 3.10/1.51  tff(c_58, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.10/1.51  tff(c_801, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_780, c_58])).
% 3.10/1.51  tff(c_22, plain, (![A_14]: (~v1_xboole_0(k1_tarski(A_14)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.10/1.51  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.10/1.51  tff(c_26, plain, (![A_15, B_16]: (r1_tarski(k1_tarski(A_15), B_16) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.10/1.51  tff(c_28, plain, (![B_18, A_17]: (k1_tarski(B_18)=A_17 | k1_xboole_0=A_17 | ~r1_tarski(A_17, k1_tarski(B_18)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.10/1.51  tff(c_876, plain, (![B_138, A_139]: (k1_tarski(B_138)=A_139 | A_139='#skF_4' | ~r1_tarski(A_139, k1_tarski(B_138)))), inference(demodulation, [status(thm), theory('equality')], [c_780, c_28])).
% 3.10/1.51  tff(c_984, plain, (![B_155, A_156]: (k1_tarski(B_155)=k1_tarski(A_156) | k1_tarski(A_156)='#skF_4' | ~r2_hidden(A_156, k1_tarski(B_155)))), inference(resolution, [status(thm)], [c_26, c_876])).
% 3.10/1.51  tff(c_991, plain, (![B_155]: (k1_tarski('#skF_1'(k1_tarski(B_155)))=k1_tarski(B_155) | k1_tarski('#skF_1'(k1_tarski(B_155)))='#skF_4' | v1_xboole_0(k1_tarski(B_155)))), inference(resolution, [status(thm)], [c_4, c_984])).
% 3.10/1.51  tff(c_996, plain, (![B_155]: (k1_tarski('#skF_1'(k1_tarski(B_155)))=k1_tarski(B_155) | k1_tarski('#skF_1'(k1_tarski(B_155)))='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_22, c_991])).
% 3.10/1.51  tff(c_1065, plain, (![B_161]: (k1_tarski('#skF_1'(k1_tarski(B_161)))='#skF_4' | k1_tarski(B_161)!='#skF_4')), inference(factorization, [status(thm), theory('equality')], [c_996])).
% 3.10/1.51  tff(c_1102, plain, (![B_161]: (~v1_xboole_0('#skF_4') | k1_tarski(B_161)!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1065, c_22])).
% 3.10/1.51  tff(c_1120, plain, (![B_161]: (k1_tarski(B_161)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_775, c_1102])).
% 3.10/1.51  tff(c_32, plain, (![B_18]: (r1_tarski(k1_xboole_0, k1_tarski(B_18)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.10/1.51  tff(c_119, plain, (![B_58, A_59]: (B_58=A_59 | ~r1_tarski(B_58, A_59) | ~r1_tarski(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.10/1.51  tff(c_132, plain, (![B_60]: (k1_tarski(B_60)=k1_xboole_0 | ~r1_tarski(k1_tarski(B_60), k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_119])).
% 3.10/1.51  tff(c_137, plain, (![A_15]: (k1_tarski(A_15)=k1_xboole_0 | ~r2_hidden(A_15, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_132])).
% 3.10/1.51  tff(c_794, plain, (![A_15]: (k1_tarski(A_15)='#skF_4' | ~r2_hidden(A_15, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_780, c_780, c_137])).
% 3.10/1.51  tff(c_1126, plain, (![A_15]: (~r2_hidden(A_15, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1120, c_794])).
% 3.10/1.51  tff(c_62, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.10/1.51  tff(c_793, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_780, c_766])).
% 3.10/1.51  tff(c_974, plain, (![A_152, B_153, C_154]: (k2_relset_1(A_152, B_153, C_154)=k2_relat_1(C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.10/1.51  tff(c_977, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_974])).
% 3.10/1.51  tff(c_979, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_793, c_977])).
% 3.10/1.51  tff(c_54, plain, (![D_39, C_38, A_36, B_37]: (r2_hidden(k1_funct_1(D_39, C_38), k2_relset_1(A_36, B_37, D_39)) | k1_xboole_0=B_37 | ~r2_hidden(C_38, A_36) | ~m1_subset_1(D_39, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_2(D_39, A_36, B_37) | ~v1_funct_1(D_39))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.10/1.51  tff(c_1147, plain, (![D_165, C_166, A_167, B_168]: (r2_hidden(k1_funct_1(D_165, C_166), k2_relset_1(A_167, B_168, D_165)) | B_168='#skF_4' | ~r2_hidden(C_166, A_167) | ~m1_subset_1(D_165, k1_zfmisc_1(k2_zfmisc_1(A_167, B_168))) | ~v1_funct_2(D_165, A_167, B_168) | ~v1_funct_1(D_165))), inference(demodulation, [status(thm), theory('equality')], [c_780, c_54])).
% 3.10/1.51  tff(c_1153, plain, (![C_166]: (r2_hidden(k1_funct_1('#skF_4', C_166), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_166, k1_tarski('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_979, c_1147])).
% 3.10/1.51  tff(c_1156, plain, (![C_166]: (r2_hidden(k1_funct_1('#skF_4', C_166), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_166, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_1153])).
% 3.10/1.51  tff(c_1158, plain, (![C_169]: (~r2_hidden(C_169, k1_tarski('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_801, c_1126, c_1156])).
% 3.10/1.51  tff(c_1172, plain, $false, inference(resolution, [status(thm)], [c_101, c_1158])).
% 3.10/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.51  
% 3.10/1.51  Inference rules
% 3.10/1.51  ----------------------
% 3.10/1.51  #Ref     : 0
% 3.10/1.51  #Sup     : 240
% 3.10/1.51  #Fact    : 2
% 3.10/1.51  #Define  : 0
% 3.10/1.51  #Split   : 3
% 3.10/1.51  #Chain   : 0
% 3.10/1.51  #Close   : 0
% 3.10/1.51  
% 3.10/1.51  Ordering : KBO
% 3.10/1.51  
% 3.10/1.51  Simplification rules
% 3.10/1.51  ----------------------
% 3.10/1.51  #Subsume      : 46
% 3.10/1.51  #Demod        : 125
% 3.10/1.51  #Tautology    : 91
% 3.10/1.51  #SimpNegUnit  : 24
% 3.10/1.51  #BackRed      : 23
% 3.10/1.51  
% 3.10/1.51  #Partial instantiations: 0
% 3.10/1.51  #Strategies tried      : 1
% 3.10/1.51  
% 3.10/1.51  Timing (in seconds)
% 3.10/1.51  ----------------------
% 3.10/1.52  Preprocessing        : 0.32
% 3.10/1.52  Parsing              : 0.16
% 3.10/1.52  CNF conversion       : 0.02
% 3.10/1.52  Main loop            : 0.38
% 3.10/1.52  Inferencing          : 0.14
% 3.10/1.52  Reduction            : 0.12
% 3.10/1.52  Demodulation         : 0.09
% 3.10/1.52  BG Simplification    : 0.02
% 3.10/1.52  Subsumption          : 0.07
% 3.10/1.52  Abstraction          : 0.02
% 3.10/1.52  MUC search           : 0.00
% 3.10/1.52  Cooper               : 0.00
% 3.10/1.52  Total                : 0.73
% 3.10/1.52  Index Insertion      : 0.00
% 3.10/1.52  Index Deletion       : 0.00
% 3.10/1.52  Index Matching       : 0.00
% 3.10/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
