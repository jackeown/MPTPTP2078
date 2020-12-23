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
% DateTime   : Thu Dec  3 10:14:42 EST 2020

% Result     : Theorem 11.93s
% Output     : CNFRefutation 11.93s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 449 expanded)
%              Number of leaves         :   54 ( 174 expanded)
%              Depth                    :   14
%              Number of atoms          :  218 ( 910 expanded)
%              Number of equality atoms :   59 ( 252 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_3

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_161,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_139,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_58,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_56,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_99,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_96,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_108,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_funct_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_1)).

tff(f_125,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_145,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_149,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_relat_1)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_135,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k1_relat_1(C)) )
       => k9_relat_1(C,k2_tarski(A,B)) = k2_tarski(k1_funct_1(C,A),k1_funct_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).

tff(c_110,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_200,plain,(
    ! [C_113,A_114,B_115] :
      ( v1_relat_1(C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_217,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_110,c_200])).

tff(c_42,plain,(
    ! [A_16] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_184,plain,(
    ! [A_108,B_109] :
      ( r1_tarski(A_108,B_109)
      | ~ m1_subset_1(A_108,k1_zfmisc_1(B_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_192,plain,(
    ! [A_16] : r1_tarski(k1_xboole_0,A_16) ),
    inference(resolution,[status(thm)],[c_42,c_184])).

tff(c_129,plain,(
    ! [A_98] : k2_zfmisc_1(A_98,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_56,plain,(
    ! [A_27,B_28] : v1_relat_1(k2_zfmisc_1(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_133,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_56])).

tff(c_455,plain,(
    ! [A_152,B_153] :
      ( k9_relat_1(A_152,k1_tarski(B_153)) = k11_relat_1(A_152,B_153)
      | ~ v1_relat_1(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_66,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_304,plain,(
    ! [B_126,A_127] :
      ( r1_tarski(k9_relat_1(B_126,A_127),k2_relat_1(B_126))
      | ~ v1_relat_1(B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_309,plain,(
    ! [A_127] :
      ( r1_tarski(k9_relat_1(k1_xboole_0,A_127),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_304])).

tff(c_313,plain,(
    ! [A_128] : r1_tarski(k9_relat_1(k1_xboole_0,A_128),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_309])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_318,plain,(
    ! [A_128] :
      ( k9_relat_1(k1_xboole_0,A_128) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k9_relat_1(k1_xboole_0,A_128)) ) ),
    inference(resolution,[status(thm)],[c_313,c_2])).

tff(c_325,plain,(
    ! [A_128] : k9_relat_1(k1_xboole_0,A_128) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_318])).

tff(c_462,plain,(
    ! [B_153] :
      ( k11_relat_1(k1_xboole_0,B_153) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_325])).

tff(c_475,plain,(
    ! [B_153] : k11_relat_1(k1_xboole_0,B_153) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_462])).

tff(c_68,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_616,plain,(
    ! [B_173,A_174] :
      ( k11_relat_1(B_173,A_174) != k1_xboole_0
      | ~ r2_hidden(A_174,k1_relat_1(B_173))
      | ~ v1_relat_1(B_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_619,plain,(
    ! [A_174] :
      ( k11_relat_1(k1_xboole_0,A_174) != k1_xboole_0
      | ~ r2_hidden(A_174,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_616])).

tff(c_621,plain,(
    ! [A_174] : ~ r2_hidden(A_174,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_475,c_619])).

tff(c_114,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_727,plain,(
    ! [B_191,A_192] :
      ( v1_funct_1(B_191)
      | ~ m1_subset_1(B_191,k1_zfmisc_1(A_192))
      | ~ v1_funct_1(A_192)
      | ~ v1_relat_1(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_741,plain,(
    ! [A_16] :
      ( v1_funct_1(k1_xboole_0)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(resolution,[status(thm)],[c_42,c_727])).

tff(c_744,plain,(
    ! [A_194] :
      ( ~ v1_funct_1(A_194)
      | ~ v1_relat_1(A_194) ) ),
    inference(splitLeft,[status(thm)],[c_741])).

tff(c_750,plain,(
    ~ v1_funct_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_217,c_744])).

tff(c_761,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_750])).

tff(c_762,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_741])).

tff(c_5411,plain,(
    ! [A_19124,B_19125,C_19126] :
      ( r2_hidden('#skF_4'(A_19124,B_19125,C_19126),k1_relat_1(A_19124))
      | r2_hidden('#skF_5'(A_19124,B_19125,C_19126),C_19126)
      | k9_relat_1(A_19124,B_19125) = C_19126
      | ~ v1_funct_1(A_19124)
      | ~ v1_relat_1(A_19124) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_5465,plain,(
    ! [B_19125,C_19126] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_19125,C_19126),k1_xboole_0)
      | r2_hidden('#skF_5'(k1_xboole_0,B_19125,C_19126),C_19126)
      | k9_relat_1(k1_xboole_0,B_19125) = C_19126
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_5411])).

tff(c_5481,plain,(
    ! [B_19125,C_19126] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_19125,C_19126),k1_xboole_0)
      | r2_hidden('#skF_5'(k1_xboole_0,B_19125,C_19126),C_19126)
      | k1_xboole_0 = C_19126 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_762,c_325,c_5465])).

tff(c_5483,plain,(
    ! [B_19247,C_19248] :
      ( r2_hidden('#skF_5'(k1_xboole_0,B_19247,C_19248),C_19248)
      | k1_xboole_0 = C_19248 ) ),
    inference(negUnitSimplification,[status(thm)],[c_621,c_5481])).

tff(c_487,plain,(
    ! [C_155,A_156,B_157] :
      ( v4_relat_1(C_155,A_156)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_506,plain,(
    v4_relat_1('#skF_10',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_110,c_487])).

tff(c_508,plain,(
    ! [B_158,A_159] :
      ( r1_tarski(k1_relat_1(B_158),A_159)
      | ~ v4_relat_1(B_158,A_159)
      | ~ v1_relat_1(B_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_30,plain,(
    ! [B_13,A_12] :
      ( k1_tarski(B_13) = A_12
      | k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_tarski(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4576,plain,(
    ! [B_16209,B_16210] :
      ( k1_tarski(B_16209) = k1_relat_1(B_16210)
      | k1_relat_1(B_16210) = k1_xboole_0
      | ~ v4_relat_1(B_16210,k1_tarski(B_16209))
      | ~ v1_relat_1(B_16210) ) ),
    inference(resolution,[status(thm)],[c_508,c_30])).

tff(c_4631,plain,
    ( k1_tarski('#skF_7') = k1_relat_1('#skF_10')
    | k1_relat_1('#skF_10') = k1_xboole_0
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_506,c_4576])).

tff(c_4650,plain,
    ( k1_tarski('#skF_7') = k1_relat_1('#skF_10')
    | k1_relat_1('#skF_10') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_4631])).

tff(c_4655,plain,(
    k1_relat_1('#skF_10') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_4650])).

tff(c_78,plain,(
    ! [A_38,B_61,D_76] :
      ( r2_hidden('#skF_6'(A_38,B_61,k9_relat_1(A_38,B_61),D_76),k1_relat_1(A_38))
      | ~ r2_hidden(D_76,k9_relat_1(A_38,B_61))
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_4668,plain,(
    ! [B_61,D_76] :
      ( r2_hidden('#skF_6'('#skF_10',B_61,k9_relat_1('#skF_10',B_61),D_76),k1_xboole_0)
      | ~ r2_hidden(D_76,k9_relat_1('#skF_10',B_61))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4655,c_78])).

tff(c_4726,plain,(
    ! [B_61,D_76] :
      ( r2_hidden('#skF_6'('#skF_10',B_61,k9_relat_1('#skF_10',B_61),D_76),k1_xboole_0)
      | ~ r2_hidden(D_76,k9_relat_1('#skF_10',B_61)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_114,c_4668])).

tff(c_4727,plain,(
    ! [D_76,B_61] : ~ r2_hidden(D_76,k9_relat_1('#skF_10',B_61)) ),
    inference(negUnitSimplification,[status(thm)],[c_621,c_4726])).

tff(c_5518,plain,(
    ! [B_61] : k9_relat_1('#skF_10',B_61) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5483,c_4727])).

tff(c_876,plain,(
    ! [A_215,B_216,C_217,D_218] :
      ( k7_relset_1(A_215,B_216,C_217,D_218) = k9_relat_1(C_217,D_218)
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(A_215,B_216))) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_890,plain,(
    ! [D_218] : k7_relset_1(k1_tarski('#skF_7'),'#skF_8','#skF_10',D_218) = k9_relat_1('#skF_10',D_218) ),
    inference(resolution,[status(thm)],[c_110,c_876])).

tff(c_106,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_7'),'#skF_8','#skF_10','#skF_9'),k1_tarski(k1_funct_1('#skF_10','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_917,plain,(
    ~ r1_tarski(k9_relat_1('#skF_10','#skF_9'),k1_tarski(k1_funct_1('#skF_10','#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_890,c_106])).

tff(c_5531,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1('#skF_10','#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5518,c_917])).

tff(c_5538,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_5531])).

tff(c_5539,plain,(
    k1_tarski('#skF_7') = k1_relat_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_4650])).

tff(c_50,plain,(
    ! [A_22,B_24] :
      ( k9_relat_1(A_22,k1_tarski(B_24)) = k11_relat_1(A_22,B_24)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6374,plain,(
    ! [A_22628] :
      ( k9_relat_1(A_22628,k1_relat_1('#skF_10')) = k11_relat_1(A_22628,'#skF_7')
      | ~ v1_relat_1(A_22628) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5539,c_50])).

tff(c_60,plain,(
    ! [B_32,A_31] :
      ( r1_tarski(k9_relat_1(B_32,A_31),k9_relat_1(B_32,k1_relat_1(B_32)))
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6400,plain,(
    ! [A_31] :
      ( r1_tarski(k9_relat_1('#skF_10',A_31),k11_relat_1('#skF_10','#skF_7'))
      | ~ v1_relat_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6374,c_60])).

tff(c_6422,plain,(
    ! [A_31] : r1_tarski(k9_relat_1('#skF_10',A_31),k11_relat_1('#skF_10','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_217,c_6400])).

tff(c_26,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_165,plain,(
    ! [D_101,B_102] : r2_hidden(D_101,k2_tarski(D_101,B_102)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_168,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_165])).

tff(c_5573,plain,(
    r2_hidden('#skF_7',k1_relat_1('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5539,c_168])).

tff(c_638,plain,(
    ! [B_179,A_180] :
      ( r1_tarski(k9_relat_1(B_179,A_180),k9_relat_1(B_179,k1_relat_1(B_179)))
      | ~ v1_relat_1(B_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_643,plain,(
    ! [A_22,B_24] :
      ( r1_tarski(k11_relat_1(A_22,B_24),k9_relat_1(A_22,k1_relat_1(A_22)))
      | ~ v1_relat_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_638])).

tff(c_6387,plain,(
    ! [B_24] :
      ( r1_tarski(k11_relat_1('#skF_10',B_24),k11_relat_1('#skF_10','#skF_7'))
      | ~ v1_relat_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6374,c_643])).

tff(c_6420,plain,(
    ! [B_24] : r1_tarski(k11_relat_1('#skF_10',B_24),k11_relat_1('#skF_10','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_217,c_217,c_6387])).

tff(c_5564,plain,(
    ! [A_22] :
      ( k9_relat_1(A_22,k1_relat_1('#skF_10')) = k11_relat_1(A_22,'#skF_7')
      | ~ v1_relat_1(A_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5539,c_50])).

tff(c_6447,plain,(
    ! [A_22870] : r1_tarski(k9_relat_1('#skF_10',A_22870),k11_relat_1('#skF_10','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_217,c_6400])).

tff(c_14357,plain,(
    ! [A_43791] :
      ( k9_relat_1('#skF_10',A_43791) = k11_relat_1('#skF_10','#skF_7')
      | ~ r1_tarski(k11_relat_1('#skF_10','#skF_7'),k9_relat_1('#skF_10',A_43791)) ) ),
    inference(resolution,[status(thm)],[c_6447,c_2])).

tff(c_14363,plain,
    ( k9_relat_1('#skF_10',k1_relat_1('#skF_10')) = k11_relat_1('#skF_10','#skF_7')
    | ~ r1_tarski(k11_relat_1('#skF_10','#skF_7'),k11_relat_1('#skF_10','#skF_7'))
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_5564,c_14357])).

tff(c_14383,plain,(
    k9_relat_1('#skF_10',k1_relat_1('#skF_10')) = k11_relat_1('#skF_10','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_6420,c_14363])).

tff(c_6136,plain,(
    ! [C_22264,A_22265,B_22266] :
      ( k2_tarski(k1_funct_1(C_22264,A_22265),k1_funct_1(C_22264,B_22266)) = k9_relat_1(C_22264,k2_tarski(A_22265,B_22266))
      | ~ r2_hidden(B_22266,k1_relat_1(C_22264))
      | ~ r2_hidden(A_22265,k1_relat_1(C_22264))
      | ~ v1_funct_1(C_22264)
      | ~ v1_relat_1(C_22264) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_6170,plain,(
    ! [C_22264,B_22266] :
      ( k9_relat_1(C_22264,k2_tarski(B_22266,B_22266)) = k1_tarski(k1_funct_1(C_22264,B_22266))
      | ~ r2_hidden(B_22266,k1_relat_1(C_22264))
      | ~ r2_hidden(B_22266,k1_relat_1(C_22264))
      | ~ v1_funct_1(C_22264)
      | ~ v1_relat_1(C_22264) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6136,c_26])).

tff(c_26040,plain,(
    ! [C_68156,B_68157] :
      ( k9_relat_1(C_68156,k1_tarski(B_68157)) = k1_tarski(k1_funct_1(C_68156,B_68157))
      | ~ r2_hidden(B_68157,k1_relat_1(C_68156))
      | ~ r2_hidden(B_68157,k1_relat_1(C_68156))
      | ~ v1_funct_1(C_68156)
      | ~ v1_relat_1(C_68156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_6170])).

tff(c_26058,plain,
    ( k9_relat_1('#skF_10',k1_tarski('#skF_7')) = k1_tarski(k1_funct_1('#skF_10','#skF_7'))
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_5573,c_26040])).

tff(c_26133,plain,(
    k1_tarski(k1_funct_1('#skF_10','#skF_7')) = k11_relat_1('#skF_10','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_114,c_5573,c_14383,c_5539,c_26058])).

tff(c_26140,plain,(
    ~ r1_tarski(k9_relat_1('#skF_10','#skF_9'),k11_relat_1('#skF_10','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26133,c_917])).

tff(c_26143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6422,c_26140])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:12:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.93/4.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.93/4.29  
% 11.93/4.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.93/4.29  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_3
% 11.93/4.29  
% 11.93/4.29  %Foreground sorts:
% 11.93/4.29  
% 11.93/4.29  
% 11.93/4.29  %Background operators:
% 11.93/4.29  
% 11.93/4.29  
% 11.93/4.29  %Foreground operators:
% 11.93/4.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 11.93/4.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.93/4.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.93/4.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.93/4.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.93/4.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.93/4.29  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 11.93/4.29  tff('#skF_7', type, '#skF_7': $i).
% 11.93/4.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.93/4.29  tff('#skF_10', type, '#skF_10': $i).
% 11.93/4.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.93/4.29  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 11.93/4.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.93/4.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.93/4.29  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 11.93/4.29  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 11.93/4.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.93/4.29  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 11.93/4.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.93/4.29  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 11.93/4.29  tff('#skF_9', type, '#skF_9': $i).
% 11.93/4.29  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 11.93/4.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.93/4.29  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 11.93/4.29  tff('#skF_8', type, '#skF_8': $i).
% 11.93/4.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.93/4.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.93/4.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.93/4.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 11.93/4.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.93/4.29  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 11.93/4.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.93/4.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.93/4.29  
% 11.93/4.31  tff(f_161, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 11.93/4.31  tff(f_139, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.93/4.31  tff(f_58, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 11.93/4.31  tff(f_62, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.93/4.31  tff(f_56, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 11.93/4.31  tff(f_81, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 11.93/4.31  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 11.93/4.31  tff(f_99, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 11.93/4.31  tff(f_85, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 11.93/4.31  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.93/4.31  tff(f_96, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 11.93/4.31  tff(f_108, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_funct_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_funct_1)).
% 11.93/4.31  tff(f_125, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 11.93/4.31  tff(f_145, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 11.93/4.31  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 11.93/4.31  tff(f_50, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 11.93/4.31  tff(f_149, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 11.93/4.31  tff(f_89, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k9_relat_1(B, k1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_relat_1)).
% 11.93/4.31  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 11.93/4.31  tff(f_40, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 11.93/4.31  tff(f_135, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k1_relat_1(C))) => (k9_relat_1(C, k2_tarski(A, B)) = k2_tarski(k1_funct_1(C, A), k1_funct_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_funct_1)).
% 11.93/4.31  tff(c_110, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 11.93/4.31  tff(c_200, plain, (![C_113, A_114, B_115]: (v1_relat_1(C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 11.93/4.31  tff(c_217, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_110, c_200])).
% 11.93/4.31  tff(c_42, plain, (![A_16]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.93/4.31  tff(c_184, plain, (![A_108, B_109]: (r1_tarski(A_108, B_109) | ~m1_subset_1(A_108, k1_zfmisc_1(B_109)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.93/4.31  tff(c_192, plain, (![A_16]: (r1_tarski(k1_xboole_0, A_16))), inference(resolution, [status(thm)], [c_42, c_184])).
% 11.93/4.31  tff(c_129, plain, (![A_98]: (k2_zfmisc_1(A_98, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.93/4.31  tff(c_56, plain, (![A_27, B_28]: (v1_relat_1(k2_zfmisc_1(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.93/4.31  tff(c_133, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_129, c_56])).
% 11.93/4.31  tff(c_455, plain, (![A_152, B_153]: (k9_relat_1(A_152, k1_tarski(B_153))=k11_relat_1(A_152, B_153) | ~v1_relat_1(A_152))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.93/4.31  tff(c_66, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 11.93/4.31  tff(c_304, plain, (![B_126, A_127]: (r1_tarski(k9_relat_1(B_126, A_127), k2_relat_1(B_126)) | ~v1_relat_1(B_126))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.93/4.31  tff(c_309, plain, (![A_127]: (r1_tarski(k9_relat_1(k1_xboole_0, A_127), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_66, c_304])).
% 11.93/4.31  tff(c_313, plain, (![A_128]: (r1_tarski(k9_relat_1(k1_xboole_0, A_128), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_309])).
% 11.93/4.31  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.93/4.31  tff(c_318, plain, (![A_128]: (k9_relat_1(k1_xboole_0, A_128)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k9_relat_1(k1_xboole_0, A_128)))), inference(resolution, [status(thm)], [c_313, c_2])).
% 11.93/4.31  tff(c_325, plain, (![A_128]: (k9_relat_1(k1_xboole_0, A_128)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_192, c_318])).
% 11.93/4.31  tff(c_462, plain, (![B_153]: (k11_relat_1(k1_xboole_0, B_153)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_455, c_325])).
% 11.93/4.31  tff(c_475, plain, (![B_153]: (k11_relat_1(k1_xboole_0, B_153)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_133, c_462])).
% 11.93/4.31  tff(c_68, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 11.93/4.31  tff(c_616, plain, (![B_173, A_174]: (k11_relat_1(B_173, A_174)!=k1_xboole_0 | ~r2_hidden(A_174, k1_relat_1(B_173)) | ~v1_relat_1(B_173))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.93/4.31  tff(c_619, plain, (![A_174]: (k11_relat_1(k1_xboole_0, A_174)!=k1_xboole_0 | ~r2_hidden(A_174, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_68, c_616])).
% 11.93/4.31  tff(c_621, plain, (![A_174]: (~r2_hidden(A_174, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_475, c_619])).
% 11.93/4.31  tff(c_114, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_161])).
% 11.93/4.31  tff(c_727, plain, (![B_191, A_192]: (v1_funct_1(B_191) | ~m1_subset_1(B_191, k1_zfmisc_1(A_192)) | ~v1_funct_1(A_192) | ~v1_relat_1(A_192))), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.93/4.31  tff(c_741, plain, (![A_16]: (v1_funct_1(k1_xboole_0) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(resolution, [status(thm)], [c_42, c_727])).
% 11.93/4.31  tff(c_744, plain, (![A_194]: (~v1_funct_1(A_194) | ~v1_relat_1(A_194))), inference(splitLeft, [status(thm)], [c_741])).
% 11.93/4.31  tff(c_750, plain, (~v1_funct_1('#skF_10')), inference(resolution, [status(thm)], [c_217, c_744])).
% 11.93/4.31  tff(c_761, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_750])).
% 11.93/4.31  tff(c_762, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_741])).
% 11.93/4.31  tff(c_5411, plain, (![A_19124, B_19125, C_19126]: (r2_hidden('#skF_4'(A_19124, B_19125, C_19126), k1_relat_1(A_19124)) | r2_hidden('#skF_5'(A_19124, B_19125, C_19126), C_19126) | k9_relat_1(A_19124, B_19125)=C_19126 | ~v1_funct_1(A_19124) | ~v1_relat_1(A_19124))), inference(cnfTransformation, [status(thm)], [f_125])).
% 11.93/4.31  tff(c_5465, plain, (![B_19125, C_19126]: (r2_hidden('#skF_4'(k1_xboole_0, B_19125, C_19126), k1_xboole_0) | r2_hidden('#skF_5'(k1_xboole_0, B_19125, C_19126), C_19126) | k9_relat_1(k1_xboole_0, B_19125)=C_19126 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_68, c_5411])).
% 11.93/4.31  tff(c_5481, plain, (![B_19125, C_19126]: (r2_hidden('#skF_4'(k1_xboole_0, B_19125, C_19126), k1_xboole_0) | r2_hidden('#skF_5'(k1_xboole_0, B_19125, C_19126), C_19126) | k1_xboole_0=C_19126)), inference(demodulation, [status(thm), theory('equality')], [c_133, c_762, c_325, c_5465])).
% 11.93/4.31  tff(c_5483, plain, (![B_19247, C_19248]: (r2_hidden('#skF_5'(k1_xboole_0, B_19247, C_19248), C_19248) | k1_xboole_0=C_19248)), inference(negUnitSimplification, [status(thm)], [c_621, c_5481])).
% 11.93/4.31  tff(c_487, plain, (![C_155, A_156, B_157]: (v4_relat_1(C_155, A_156) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 11.93/4.31  tff(c_506, plain, (v4_relat_1('#skF_10', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_110, c_487])).
% 11.93/4.31  tff(c_508, plain, (![B_158, A_159]: (r1_tarski(k1_relat_1(B_158), A_159) | ~v4_relat_1(B_158, A_159) | ~v1_relat_1(B_158))), inference(cnfTransformation, [status(thm)], [f_79])).
% 11.93/4.31  tff(c_30, plain, (![B_13, A_12]: (k1_tarski(B_13)=A_12 | k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_tarski(B_13)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.93/4.31  tff(c_4576, plain, (![B_16209, B_16210]: (k1_tarski(B_16209)=k1_relat_1(B_16210) | k1_relat_1(B_16210)=k1_xboole_0 | ~v4_relat_1(B_16210, k1_tarski(B_16209)) | ~v1_relat_1(B_16210))), inference(resolution, [status(thm)], [c_508, c_30])).
% 11.93/4.31  tff(c_4631, plain, (k1_tarski('#skF_7')=k1_relat_1('#skF_10') | k1_relat_1('#skF_10')=k1_xboole_0 | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_506, c_4576])).
% 11.93/4.31  tff(c_4650, plain, (k1_tarski('#skF_7')=k1_relat_1('#skF_10') | k1_relat_1('#skF_10')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_217, c_4631])).
% 11.93/4.31  tff(c_4655, plain, (k1_relat_1('#skF_10')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_4650])).
% 11.93/4.31  tff(c_78, plain, (![A_38, B_61, D_76]: (r2_hidden('#skF_6'(A_38, B_61, k9_relat_1(A_38, B_61), D_76), k1_relat_1(A_38)) | ~r2_hidden(D_76, k9_relat_1(A_38, B_61)) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_125])).
% 11.93/4.31  tff(c_4668, plain, (![B_61, D_76]: (r2_hidden('#skF_6'('#skF_10', B_61, k9_relat_1('#skF_10', B_61), D_76), k1_xboole_0) | ~r2_hidden(D_76, k9_relat_1('#skF_10', B_61)) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_4655, c_78])).
% 11.93/4.31  tff(c_4726, plain, (![B_61, D_76]: (r2_hidden('#skF_6'('#skF_10', B_61, k9_relat_1('#skF_10', B_61), D_76), k1_xboole_0) | ~r2_hidden(D_76, k9_relat_1('#skF_10', B_61)))), inference(demodulation, [status(thm), theory('equality')], [c_217, c_114, c_4668])).
% 11.93/4.31  tff(c_4727, plain, (![D_76, B_61]: (~r2_hidden(D_76, k9_relat_1('#skF_10', B_61)))), inference(negUnitSimplification, [status(thm)], [c_621, c_4726])).
% 11.93/4.31  tff(c_5518, plain, (![B_61]: (k9_relat_1('#skF_10', B_61)=k1_xboole_0)), inference(resolution, [status(thm)], [c_5483, c_4727])).
% 11.93/4.31  tff(c_876, plain, (![A_215, B_216, C_217, D_218]: (k7_relset_1(A_215, B_216, C_217, D_218)=k9_relat_1(C_217, D_218) | ~m1_subset_1(C_217, k1_zfmisc_1(k2_zfmisc_1(A_215, B_216))))), inference(cnfTransformation, [status(thm)], [f_149])).
% 11.93/4.31  tff(c_890, plain, (![D_218]: (k7_relset_1(k1_tarski('#skF_7'), '#skF_8', '#skF_10', D_218)=k9_relat_1('#skF_10', D_218))), inference(resolution, [status(thm)], [c_110, c_876])).
% 11.93/4.31  tff(c_106, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_7'), '#skF_8', '#skF_10', '#skF_9'), k1_tarski(k1_funct_1('#skF_10', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 11.93/4.31  tff(c_917, plain, (~r1_tarski(k9_relat_1('#skF_10', '#skF_9'), k1_tarski(k1_funct_1('#skF_10', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_890, c_106])).
% 11.93/4.31  tff(c_5531, plain, (~r1_tarski(k1_xboole_0, k1_tarski(k1_funct_1('#skF_10', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_5518, c_917])).
% 11.93/4.31  tff(c_5538, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_192, c_5531])).
% 11.93/4.31  tff(c_5539, plain, (k1_tarski('#skF_7')=k1_relat_1('#skF_10')), inference(splitRight, [status(thm)], [c_4650])).
% 11.93/4.31  tff(c_50, plain, (![A_22, B_24]: (k9_relat_1(A_22, k1_tarski(B_24))=k11_relat_1(A_22, B_24) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.93/4.31  tff(c_6374, plain, (![A_22628]: (k9_relat_1(A_22628, k1_relat_1('#skF_10'))=k11_relat_1(A_22628, '#skF_7') | ~v1_relat_1(A_22628))), inference(superposition, [status(thm), theory('equality')], [c_5539, c_50])).
% 11.93/4.31  tff(c_60, plain, (![B_32, A_31]: (r1_tarski(k9_relat_1(B_32, A_31), k9_relat_1(B_32, k1_relat_1(B_32))) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.93/4.31  tff(c_6400, plain, (![A_31]: (r1_tarski(k9_relat_1('#skF_10', A_31), k11_relat_1('#skF_10', '#skF_7')) | ~v1_relat_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_6374, c_60])).
% 11.93/4.31  tff(c_6422, plain, (![A_31]: (r1_tarski(k9_relat_1('#skF_10', A_31), k11_relat_1('#skF_10', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_217, c_217, c_6400])).
% 11.93/4.31  tff(c_26, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.93/4.31  tff(c_165, plain, (![D_101, B_102]: (r2_hidden(D_101, k2_tarski(D_101, B_102)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 11.93/4.31  tff(c_168, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_165])).
% 11.93/4.31  tff(c_5573, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_5539, c_168])).
% 11.93/4.31  tff(c_638, plain, (![B_179, A_180]: (r1_tarski(k9_relat_1(B_179, A_180), k9_relat_1(B_179, k1_relat_1(B_179))) | ~v1_relat_1(B_179))), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.93/4.31  tff(c_643, plain, (![A_22, B_24]: (r1_tarski(k11_relat_1(A_22, B_24), k9_relat_1(A_22, k1_relat_1(A_22))) | ~v1_relat_1(A_22) | ~v1_relat_1(A_22))), inference(superposition, [status(thm), theory('equality')], [c_50, c_638])).
% 11.93/4.31  tff(c_6387, plain, (![B_24]: (r1_tarski(k11_relat_1('#skF_10', B_24), k11_relat_1('#skF_10', '#skF_7')) | ~v1_relat_1('#skF_10') | ~v1_relat_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_6374, c_643])).
% 11.93/4.31  tff(c_6420, plain, (![B_24]: (r1_tarski(k11_relat_1('#skF_10', B_24), k11_relat_1('#skF_10', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_217, c_217, c_217, c_6387])).
% 11.93/4.31  tff(c_5564, plain, (![A_22]: (k9_relat_1(A_22, k1_relat_1('#skF_10'))=k11_relat_1(A_22, '#skF_7') | ~v1_relat_1(A_22))), inference(superposition, [status(thm), theory('equality')], [c_5539, c_50])).
% 11.93/4.31  tff(c_6447, plain, (![A_22870]: (r1_tarski(k9_relat_1('#skF_10', A_22870), k11_relat_1('#skF_10', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_217, c_217, c_6400])).
% 11.93/4.31  tff(c_14357, plain, (![A_43791]: (k9_relat_1('#skF_10', A_43791)=k11_relat_1('#skF_10', '#skF_7') | ~r1_tarski(k11_relat_1('#skF_10', '#skF_7'), k9_relat_1('#skF_10', A_43791)))), inference(resolution, [status(thm)], [c_6447, c_2])).
% 11.93/4.31  tff(c_14363, plain, (k9_relat_1('#skF_10', k1_relat_1('#skF_10'))=k11_relat_1('#skF_10', '#skF_7') | ~r1_tarski(k11_relat_1('#skF_10', '#skF_7'), k11_relat_1('#skF_10', '#skF_7')) | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_5564, c_14357])).
% 11.93/4.31  tff(c_14383, plain, (k9_relat_1('#skF_10', k1_relat_1('#skF_10'))=k11_relat_1('#skF_10', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_217, c_6420, c_14363])).
% 11.93/4.31  tff(c_6136, plain, (![C_22264, A_22265, B_22266]: (k2_tarski(k1_funct_1(C_22264, A_22265), k1_funct_1(C_22264, B_22266))=k9_relat_1(C_22264, k2_tarski(A_22265, B_22266)) | ~r2_hidden(B_22266, k1_relat_1(C_22264)) | ~r2_hidden(A_22265, k1_relat_1(C_22264)) | ~v1_funct_1(C_22264) | ~v1_relat_1(C_22264))), inference(cnfTransformation, [status(thm)], [f_135])).
% 11.93/4.31  tff(c_6170, plain, (![C_22264, B_22266]: (k9_relat_1(C_22264, k2_tarski(B_22266, B_22266))=k1_tarski(k1_funct_1(C_22264, B_22266)) | ~r2_hidden(B_22266, k1_relat_1(C_22264)) | ~r2_hidden(B_22266, k1_relat_1(C_22264)) | ~v1_funct_1(C_22264) | ~v1_relat_1(C_22264))), inference(superposition, [status(thm), theory('equality')], [c_6136, c_26])).
% 11.93/4.31  tff(c_26040, plain, (![C_68156, B_68157]: (k9_relat_1(C_68156, k1_tarski(B_68157))=k1_tarski(k1_funct_1(C_68156, B_68157)) | ~r2_hidden(B_68157, k1_relat_1(C_68156)) | ~r2_hidden(B_68157, k1_relat_1(C_68156)) | ~v1_funct_1(C_68156) | ~v1_relat_1(C_68156))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_6170])).
% 11.93/4.31  tff(c_26058, plain, (k9_relat_1('#skF_10', k1_tarski('#skF_7'))=k1_tarski(k1_funct_1('#skF_10', '#skF_7')) | ~r2_hidden('#skF_7', k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_5573, c_26040])).
% 11.93/4.31  tff(c_26133, plain, (k1_tarski(k1_funct_1('#skF_10', '#skF_7'))=k11_relat_1('#skF_10', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_217, c_114, c_5573, c_14383, c_5539, c_26058])).
% 11.93/4.31  tff(c_26140, plain, (~r1_tarski(k9_relat_1('#skF_10', '#skF_9'), k11_relat_1('#skF_10', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_26133, c_917])).
% 11.93/4.31  tff(c_26143, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6422, c_26140])).
% 11.93/4.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.93/4.31  
% 11.93/4.31  Inference rules
% 11.93/4.31  ----------------------
% 11.93/4.31  #Ref     : 0
% 11.93/4.31  #Sup     : 3905
% 11.93/4.31  #Fact    : 48
% 11.93/4.31  #Define  : 0
% 11.93/4.31  #Split   : 23
% 11.93/4.31  #Chain   : 0
% 11.93/4.31  #Close   : 0
% 11.93/4.31  
% 11.93/4.31  Ordering : KBO
% 11.93/4.31  
% 11.93/4.31  Simplification rules
% 11.93/4.31  ----------------------
% 11.93/4.31  #Subsume      : 1249
% 11.93/4.31  #Demod        : 3257
% 11.93/4.31  #Tautology    : 1346
% 11.93/4.31  #SimpNegUnit  : 194
% 11.93/4.31  #BackRed      : 207
% 11.93/4.31  
% 11.93/4.31  #Partial instantiations: 33224
% 11.93/4.31  #Strategies tried      : 1
% 11.93/4.31  
% 11.93/4.31  Timing (in seconds)
% 11.93/4.31  ----------------------
% 11.93/4.31  Preprocessing        : 0.37
% 11.93/4.31  Parsing              : 0.18
% 11.93/4.31  CNF conversion       : 0.03
% 11.93/4.31  Main loop            : 3.11
% 11.93/4.31  Inferencing          : 1.25
% 11.93/4.31  Reduction            : 0.96
% 11.93/4.31  Demodulation         : 0.71
% 11.93/4.31  BG Simplification    : 0.09
% 11.93/4.31  Subsumption          : 0.62
% 11.93/4.31  Abstraction          : 0.10
% 11.93/4.31  MUC search           : 0.00
% 11.93/4.31  Cooper               : 0.00
% 11.93/4.31  Total                : 3.52
% 11.93/4.31  Index Insertion      : 0.00
% 11.93/4.31  Index Deletion       : 0.00
% 11.93/4.31  Index Matching       : 0.00
% 11.93/4.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
