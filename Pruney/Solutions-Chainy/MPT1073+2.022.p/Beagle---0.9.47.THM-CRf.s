%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:00 EST 2020

% Result     : Theorem 5.19s
% Output     : CNFRefutation 5.48s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 177 expanded)
%              Number of leaves         :   45 (  80 expanded)
%              Depth                    :   11
%              Number of atoms          :  158 ( 410 expanded)
%              Number of equality atoms :   34 ( 109 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_138,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_122,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(B))
         => v5_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( r2_hidden(C,k2_relat_1(B))
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_72,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_156,plain,(
    ! [C_75,A_76,B_77] :
      ( v1_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_169,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_72,c_156])).

tff(c_76,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_361,plain,(
    ! [A_123,C_124] :
      ( r2_hidden(k4_tarski('#skF_5'(A_123,k2_relat_1(A_123),C_124),C_124),A_123)
      | ~ r2_hidden(C_124,k2_relat_1(A_123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_46,plain,(
    ! [C_44,A_42,B_43] :
      ( k1_funct_1(C_44,A_42) = B_43
      | ~ r2_hidden(k4_tarski(A_42,B_43),C_44)
      | ~ v1_funct_1(C_44)
      | ~ v1_relat_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_377,plain,(
    ! [A_123,C_124] :
      ( k1_funct_1(A_123,'#skF_5'(A_123,k2_relat_1(A_123),C_124)) = C_124
      | ~ v1_funct_1(A_123)
      | ~ v1_relat_1(A_123)
      | ~ r2_hidden(C_124,k2_relat_1(A_123)) ) ),
    inference(resolution,[status(thm)],[c_361,c_46])).

tff(c_74,plain,(
    v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_222,plain,(
    ! [A_95,B_96,C_97] :
      ( k1_relset_1(A_95,B_96,C_97) = k1_relat_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_237,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_72,c_222])).

tff(c_692,plain,(
    ! [B_172,A_173,C_174] :
      ( k1_xboole_0 = B_172
      | k1_relset_1(A_173,B_172,C_174) = A_173
      | ~ v1_funct_2(C_174,A_173,B_172)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_173,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_699,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_9') = '#skF_7'
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_72,c_692])).

tff(c_709,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_9') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_237,c_699])).

tff(c_711,plain,(
    k1_relat_1('#skF_9') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_709])).

tff(c_28,plain,(
    ! [A_17,C_32] :
      ( r2_hidden(k4_tarski('#skF_5'(A_17,k2_relat_1(A_17),C_32),C_32),A_17)
      | ~ r2_hidden(C_32,k2_relat_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_421,plain,(
    ! [A_130,C_131,B_132] :
      ( r2_hidden(A_130,k1_relat_1(C_131))
      | ~ r2_hidden(k4_tarski(A_130,B_132),C_131)
      | ~ v1_funct_1(C_131)
      | ~ v1_relat_1(C_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2920,plain,(
    ! [A_215,C_216] :
      ( r2_hidden('#skF_5'(A_215,k2_relat_1(A_215),C_216),k1_relat_1(A_215))
      | ~ v1_funct_1(A_215)
      | ~ v1_relat_1(A_215)
      | ~ r2_hidden(C_216,k2_relat_1(A_215)) ) ),
    inference(resolution,[status(thm)],[c_28,c_421])).

tff(c_2944,plain,(
    ! [C_216] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_216),'#skF_7')
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(C_216,k2_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_711,c_2920])).

tff(c_3094,plain,(
    ! [C_225] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_225),'#skF_7')
      | ~ r2_hidden(C_225,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_76,c_2944])).

tff(c_20,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_3447,plain,(
    ! [C_243] :
      ( m1_subset_1('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_243),'#skF_7')
      | ~ r2_hidden(C_243,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_3094,c_20])).

tff(c_68,plain,(
    ! [E_58] :
      ( k1_funct_1('#skF_9',E_58) != '#skF_6'
      | ~ m1_subset_1(E_58,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_4488,plain,(
    ! [C_251] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_251)) != '#skF_6'
      | ~ r2_hidden(C_251,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_3447,c_68])).

tff(c_4492,plain,(
    ! [C_124] :
      ( C_124 != '#skF_6'
      | ~ r2_hidden(C_124,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(C_124,k2_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_4488])).

tff(c_4495,plain,(
    ~ r2_hidden('#skF_6',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_76,c_4492])).

tff(c_254,plain,(
    ! [A_102,B_103,C_104] :
      ( k2_relset_1(A_102,B_103,C_104) = k2_relat_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_269,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_72,c_254])).

tff(c_70,plain,(
    r2_hidden('#skF_6',k2_relset_1('#skF_7','#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_272,plain,(
    r2_hidden('#skF_6',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_70])).

tff(c_4497,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4495,c_272])).

tff(c_4498,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_709])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4516,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4498,c_6])).

tff(c_16,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4513,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4498,c_4498,c_16])).

tff(c_40,plain,(
    ! [A_36,B_37] : v1_relat_1(k2_zfmisc_1(A_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_12,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_178,plain,(
    ! [B_82,A_83] :
      ( v5_relat_1(B_82,A_83)
      | ~ r1_tarski(k2_relat_1(B_82),A_83)
      | ~ v1_relat_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_183,plain,(
    ! [B_82] :
      ( v5_relat_1(B_82,k2_relat_1(B_82))
      | ~ v1_relat_1(B_82) ) ),
    inference(resolution,[status(thm)],[c_12,c_178])).

tff(c_204,plain,(
    ! [C_91,A_92,B_93] :
      ( v5_relat_1(C_91,A_92)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(B_93))
      | ~ v5_relat_1(B_93,A_92)
      | ~ v1_relat_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_209,plain,(
    ! [A_92] :
      ( v5_relat_1('#skF_9',A_92)
      | ~ v5_relat_1(k2_zfmisc_1('#skF_7','#skF_8'),A_92)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_72,c_204])).

tff(c_214,plain,(
    ! [A_94] :
      ( v5_relat_1('#skF_9',A_94)
      | ~ v5_relat_1(k2_zfmisc_1('#skF_7','#skF_8'),A_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_209])).

tff(c_218,plain,
    ( v5_relat_1('#skF_9',k2_relat_1(k2_zfmisc_1('#skF_7','#skF_8')))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_183,c_214])).

tff(c_221,plain,(
    v5_relat_1('#skF_9',k2_relat_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_218])).

tff(c_42,plain,(
    ! [C_41,A_38,B_39] :
      ( r2_hidden(C_41,A_38)
      | ~ r2_hidden(C_41,k2_relat_1(B_39))
      | ~ v5_relat_1(B_39,A_38)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_283,plain,(
    ! [A_38] :
      ( r2_hidden('#skF_6',A_38)
      | ~ v5_relat_1('#skF_9',A_38)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_272,c_42])).

tff(c_296,plain,(
    ! [A_108] :
      ( r2_hidden('#skF_6',A_108)
      | ~ v5_relat_1('#skF_9',A_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_283])).

tff(c_304,plain,(
    r2_hidden('#skF_6',k2_relat_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(resolution,[status(thm)],[c_221,c_296])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_382,plain,(
    ! [A_125,C_126] :
      ( ~ v1_xboole_0(A_125)
      | ~ r2_hidden(C_126,k2_relat_1(A_125)) ) ),
    inference(resolution,[status(thm)],[c_361,c_2])).

tff(c_398,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_304,c_382])).

tff(c_4596,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4513,c_398])).

tff(c_4606,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4516,c_4596])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:21:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.19/1.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.48/1.99  
% 5.48/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.48/1.99  %$ v1_funct_2 > v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4
% 5.48/1.99  
% 5.48/1.99  %Foreground sorts:
% 5.48/1.99  
% 5.48/1.99  
% 5.48/1.99  %Background operators:
% 5.48/1.99  
% 5.48/1.99  
% 5.48/1.99  %Foreground operators:
% 5.48/1.99  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.48/1.99  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.48/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.48/1.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.48/1.99  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.48/1.99  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.48/1.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.48/1.99  tff('#skF_7', type, '#skF_7': $i).
% 5.48/1.99  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.48/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.48/1.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.48/1.99  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.48/1.99  tff('#skF_6', type, '#skF_6': $i).
% 5.48/1.99  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.48/1.99  tff('#skF_9', type, '#skF_9': $i).
% 5.48/1.99  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.48/1.99  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.48/1.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.48/1.99  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.48/1.99  tff('#skF_8', type, '#skF_8': $i).
% 5.48/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.48/1.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.48/1.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.48/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.48/1.99  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.48/1.99  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.48/1.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.48/1.99  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.48/1.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.48/1.99  
% 5.48/2.01  tff(f_138, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 5.48/2.01  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.48/2.01  tff(f_71, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 5.48/2.01  tff(f_92, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 5.48/2.01  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.48/2.01  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.48/2.01  tff(f_48, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 5.48/2.01  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.48/2.01  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.48/2.01  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.48/2.01  tff(f_73, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.48/2.01  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.48/2.01  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 5.48/2.01  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(B)) => v5_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_relat_1)).
% 5.48/2.01  tff(f_82, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t202_relat_1)).
% 5.48/2.01  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.48/2.01  tff(c_72, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.48/2.01  tff(c_156, plain, (![C_75, A_76, B_77]: (v1_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.48/2.01  tff(c_169, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_72, c_156])).
% 5.48/2.01  tff(c_76, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.48/2.01  tff(c_361, plain, (![A_123, C_124]: (r2_hidden(k4_tarski('#skF_5'(A_123, k2_relat_1(A_123), C_124), C_124), A_123) | ~r2_hidden(C_124, k2_relat_1(A_123)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.48/2.01  tff(c_46, plain, (![C_44, A_42, B_43]: (k1_funct_1(C_44, A_42)=B_43 | ~r2_hidden(k4_tarski(A_42, B_43), C_44) | ~v1_funct_1(C_44) | ~v1_relat_1(C_44))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.48/2.01  tff(c_377, plain, (![A_123, C_124]: (k1_funct_1(A_123, '#skF_5'(A_123, k2_relat_1(A_123), C_124))=C_124 | ~v1_funct_1(A_123) | ~v1_relat_1(A_123) | ~r2_hidden(C_124, k2_relat_1(A_123)))), inference(resolution, [status(thm)], [c_361, c_46])).
% 5.48/2.01  tff(c_74, plain, (v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.48/2.01  tff(c_222, plain, (![A_95, B_96, C_97]: (k1_relset_1(A_95, B_96, C_97)=k1_relat_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.48/2.01  tff(c_237, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_72, c_222])).
% 5.48/2.01  tff(c_692, plain, (![B_172, A_173, C_174]: (k1_xboole_0=B_172 | k1_relset_1(A_173, B_172, C_174)=A_173 | ~v1_funct_2(C_174, A_173, B_172) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_173, B_172))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.48/2.01  tff(c_699, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_9')='#skF_7' | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_72, c_692])).
% 5.48/2.01  tff(c_709, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_9')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_237, c_699])).
% 5.48/2.01  tff(c_711, plain, (k1_relat_1('#skF_9')='#skF_7'), inference(splitLeft, [status(thm)], [c_709])).
% 5.48/2.01  tff(c_28, plain, (![A_17, C_32]: (r2_hidden(k4_tarski('#skF_5'(A_17, k2_relat_1(A_17), C_32), C_32), A_17) | ~r2_hidden(C_32, k2_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.48/2.01  tff(c_421, plain, (![A_130, C_131, B_132]: (r2_hidden(A_130, k1_relat_1(C_131)) | ~r2_hidden(k4_tarski(A_130, B_132), C_131) | ~v1_funct_1(C_131) | ~v1_relat_1(C_131))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.48/2.01  tff(c_2920, plain, (![A_215, C_216]: (r2_hidden('#skF_5'(A_215, k2_relat_1(A_215), C_216), k1_relat_1(A_215)) | ~v1_funct_1(A_215) | ~v1_relat_1(A_215) | ~r2_hidden(C_216, k2_relat_1(A_215)))), inference(resolution, [status(thm)], [c_28, c_421])).
% 5.48/2.01  tff(c_2944, plain, (![C_216]: (r2_hidden('#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_216), '#skF_7') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(C_216, k2_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_711, c_2920])).
% 5.48/2.01  tff(c_3094, plain, (![C_225]: (r2_hidden('#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_225), '#skF_7') | ~r2_hidden(C_225, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_76, c_2944])).
% 5.48/2.01  tff(c_20, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.48/2.01  tff(c_3447, plain, (![C_243]: (m1_subset_1('#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_243), '#skF_7') | ~r2_hidden(C_243, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_3094, c_20])).
% 5.48/2.01  tff(c_68, plain, (![E_58]: (k1_funct_1('#skF_9', E_58)!='#skF_6' | ~m1_subset_1(E_58, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.48/2.01  tff(c_4488, plain, (![C_251]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_251))!='#skF_6' | ~r2_hidden(C_251, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_3447, c_68])).
% 5.48/2.01  tff(c_4492, plain, (![C_124]: (C_124!='#skF_6' | ~r2_hidden(C_124, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(C_124, k2_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_377, c_4488])).
% 5.48/2.01  tff(c_4495, plain, (~r2_hidden('#skF_6', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_76, c_4492])).
% 5.48/2.01  tff(c_254, plain, (![A_102, B_103, C_104]: (k2_relset_1(A_102, B_103, C_104)=k2_relat_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.48/2.01  tff(c_269, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_72, c_254])).
% 5.48/2.01  tff(c_70, plain, (r2_hidden('#skF_6', k2_relset_1('#skF_7', '#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.48/2.01  tff(c_272, plain, (r2_hidden('#skF_6', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_269, c_70])).
% 5.48/2.01  tff(c_4497, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4495, c_272])).
% 5.48/2.01  tff(c_4498, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_709])).
% 5.48/2.01  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.48/2.01  tff(c_4516, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4498, c_6])).
% 5.48/2.01  tff(c_16, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.48/2.01  tff(c_4513, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4498, c_4498, c_16])).
% 5.48/2.01  tff(c_40, plain, (![A_36, B_37]: (v1_relat_1(k2_zfmisc_1(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.48/2.01  tff(c_12, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.48/2.01  tff(c_178, plain, (![B_82, A_83]: (v5_relat_1(B_82, A_83) | ~r1_tarski(k2_relat_1(B_82), A_83) | ~v1_relat_1(B_82))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.48/2.01  tff(c_183, plain, (![B_82]: (v5_relat_1(B_82, k2_relat_1(B_82)) | ~v1_relat_1(B_82))), inference(resolution, [status(thm)], [c_12, c_178])).
% 5.48/2.01  tff(c_204, plain, (![C_91, A_92, B_93]: (v5_relat_1(C_91, A_92) | ~m1_subset_1(C_91, k1_zfmisc_1(B_93)) | ~v5_relat_1(B_93, A_92) | ~v1_relat_1(B_93))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.48/2.01  tff(c_209, plain, (![A_92]: (v5_relat_1('#skF_9', A_92) | ~v5_relat_1(k2_zfmisc_1('#skF_7', '#skF_8'), A_92) | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(resolution, [status(thm)], [c_72, c_204])).
% 5.48/2.01  tff(c_214, plain, (![A_94]: (v5_relat_1('#skF_9', A_94) | ~v5_relat_1(k2_zfmisc_1('#skF_7', '#skF_8'), A_94))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_209])).
% 5.48/2.01  tff(c_218, plain, (v5_relat_1('#skF_9', k2_relat_1(k2_zfmisc_1('#skF_7', '#skF_8'))) | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_183, c_214])).
% 5.48/2.01  tff(c_221, plain, (v5_relat_1('#skF_9', k2_relat_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_218])).
% 5.48/2.01  tff(c_42, plain, (![C_41, A_38, B_39]: (r2_hidden(C_41, A_38) | ~r2_hidden(C_41, k2_relat_1(B_39)) | ~v5_relat_1(B_39, A_38) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.48/2.01  tff(c_283, plain, (![A_38]: (r2_hidden('#skF_6', A_38) | ~v5_relat_1('#skF_9', A_38) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_272, c_42])).
% 5.48/2.01  tff(c_296, plain, (![A_108]: (r2_hidden('#skF_6', A_108) | ~v5_relat_1('#skF_9', A_108))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_283])).
% 5.48/2.01  tff(c_304, plain, (r2_hidden('#skF_6', k2_relat_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(resolution, [status(thm)], [c_221, c_296])).
% 5.48/2.01  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.48/2.01  tff(c_382, plain, (![A_125, C_126]: (~v1_xboole_0(A_125) | ~r2_hidden(C_126, k2_relat_1(A_125)))), inference(resolution, [status(thm)], [c_361, c_2])).
% 5.48/2.01  tff(c_398, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_304, c_382])).
% 5.48/2.01  tff(c_4596, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4513, c_398])).
% 5.48/2.01  tff(c_4606, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4516, c_4596])).
% 5.48/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.48/2.01  
% 5.48/2.01  Inference rules
% 5.48/2.01  ----------------------
% 5.48/2.01  #Ref     : 0
% 5.48/2.01  #Sup     : 1044
% 5.48/2.01  #Fact    : 0
% 5.48/2.01  #Define  : 0
% 5.48/2.01  #Split   : 8
% 5.48/2.01  #Chain   : 0
% 5.48/2.01  #Close   : 0
% 5.48/2.01  
% 5.48/2.01  Ordering : KBO
% 5.48/2.01  
% 5.48/2.01  Simplification rules
% 5.48/2.01  ----------------------
% 5.48/2.01  #Subsume      : 291
% 5.48/2.01  #Demod        : 1232
% 5.48/2.01  #Tautology    : 357
% 5.48/2.01  #SimpNegUnit  : 18
% 5.48/2.01  #BackRed      : 42
% 5.48/2.01  
% 5.48/2.01  #Partial instantiations: 0
% 5.48/2.01  #Strategies tried      : 1
% 5.48/2.01  
% 5.48/2.01  Timing (in seconds)
% 5.48/2.01  ----------------------
% 5.48/2.01  Preprocessing        : 0.34
% 5.48/2.01  Parsing              : 0.18
% 5.48/2.01  CNF conversion       : 0.03
% 5.48/2.01  Main loop            : 0.89
% 5.48/2.01  Inferencing          : 0.27
% 5.48/2.01  Reduction            : 0.30
% 5.48/2.01  Demodulation         : 0.21
% 5.48/2.01  BG Simplification    : 0.04
% 5.48/2.01  Subsumption          : 0.21
% 5.48/2.01  Abstraction          : 0.05
% 5.48/2.01  MUC search           : 0.00
% 5.48/2.01  Cooper               : 0.00
% 5.48/2.01  Total                : 1.27
% 5.48/2.01  Index Insertion      : 0.00
% 5.48/2.01  Index Deletion       : 0.00
% 5.48/2.01  Index Matching       : 0.00
% 5.48/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
