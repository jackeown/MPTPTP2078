%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:19 EST 2020

% Result     : Theorem 5.13s
% Output     : CNFRefutation 5.51s
% Verified   : 
% Statistics : Number of formulae       :  173 (1200 expanded)
%              Number of leaves         :   32 ( 401 expanded)
%              Depth                    :   17
%              Number of atoms          :  363 (3632 expanded)
%              Number of equality atoms :  155 (1001 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( m1_subset_1(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_funct_2)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_101,axiom,(
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

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_250,plain,(
    ! [A_71,B_72,D_73] :
      ( r2_relset_1(A_71,B_72,D_73,D_73)
      | ~ m1_subset_1(D_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_267,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_250])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_152,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_172,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_152])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_52,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_323,plain,(
    ! [A_89,B_90,C_91] :
      ( k1_relset_1(A_89,B_90,C_91) = k1_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_345,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_323])).

tff(c_593,plain,(
    ! [B_125,A_126,C_127] :
      ( k1_xboole_0 = B_125
      | k1_relset_1(A_126,B_125,C_127) = A_126
      | ~ v1_funct_2(C_127,A_126,B_125)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_126,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_600,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_593])).

tff(c_617,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_345,c_600])).

tff(c_624,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_617])).

tff(c_173,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_152])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_58,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_346,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_323])).

tff(c_603,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_593])).

tff(c_620,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_346,c_603])).

tff(c_630,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_620])).

tff(c_727,plain,(
    ! [A_137,B_138] :
      ( r2_hidden('#skF_1'(A_137,B_138),k1_relat_1(A_137))
      | B_138 = A_137
      | k1_relat_1(B_138) != k1_relat_1(A_137)
      | ~ v1_funct_1(B_138)
      | ~ v1_relat_1(B_138)
      | ~ v1_funct_1(A_137)
      | ~ v1_relat_1(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_732,plain,(
    ! [B_138] :
      ( r2_hidden('#skF_1'('#skF_4',B_138),'#skF_2')
      | B_138 = '#skF_4'
      | k1_relat_1(B_138) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_138)
      | ~ v1_relat_1(B_138)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_630,c_727])).

tff(c_812,plain,(
    ! [B_144] :
      ( r2_hidden('#skF_1'('#skF_4',B_144),'#skF_2')
      | B_144 = '#skF_4'
      | k1_relat_1(B_144) != '#skF_2'
      | ~ v1_funct_1(B_144)
      | ~ v1_relat_1(B_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_60,c_630,c_732])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_175,plain,(
    ! [A_54,C_55,B_56] :
      ( m1_subset_1(A_54,C_55)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(C_55))
      | ~ r2_hidden(A_54,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_184,plain,(
    ! [A_54,B_7,A_6] :
      ( m1_subset_1(A_54,B_7)
      | ~ r2_hidden(A_54,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_18,c_175])).

tff(c_826,plain,(
    ! [B_148,B_149] :
      ( m1_subset_1('#skF_1'('#skF_4',B_148),B_149)
      | ~ r1_tarski('#skF_2',B_149)
      | B_148 = '#skF_4'
      | k1_relat_1(B_148) != '#skF_2'
      | ~ v1_funct_1(B_148)
      | ~ v1_relat_1(B_148) ) ),
    inference(resolution,[status(thm)],[c_812,c_184])).

tff(c_48,plain,(
    ! [E_34] :
      ( k1_funct_1('#skF_5',E_34) = k1_funct_1('#skF_4',E_34)
      | ~ m1_subset_1(E_34,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_871,plain,(
    ! [B_148] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_148)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_148))
      | ~ r1_tarski('#skF_2','#skF_2')
      | B_148 = '#skF_4'
      | k1_relat_1(B_148) != '#skF_2'
      | ~ v1_funct_1(B_148)
      | ~ v1_relat_1(B_148) ) ),
    inference(resolution,[status(thm)],[c_826,c_48])).

tff(c_959,plain,(
    ! [B_152] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_152)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_152))
      | B_152 = '#skF_4'
      | k1_relat_1(B_152) != '#skF_2'
      | ~ v1_funct_1(B_152)
      | ~ v1_relat_1(B_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_871])).

tff(c_22,plain,(
    ! [B_15,A_11] :
      ( k1_funct_1(B_15,'#skF_1'(A_11,B_15)) != k1_funct_1(A_11,'#skF_1'(A_11,B_15))
      | B_15 = A_11
      | k1_relat_1(B_15) != k1_relat_1(A_11)
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_966,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_959,c_22])).

tff(c_973,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_54,c_624,c_173,c_60,c_630,c_624,c_966])).

tff(c_46,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_987,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_973,c_46])).

tff(c_998,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_987])).

tff(c_999,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_620])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_92,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,B_41)
      | ~ m1_subset_1(A_40,k1_zfmisc_1(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_104,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(resolution,[status(thm)],[c_14,c_92])).

tff(c_1027,plain,(
    ! [A_5] : r1_tarski('#skF_3',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_999,c_104])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1030,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_999,c_999,c_10])).

tff(c_103,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_56,c_92])).

tff(c_111,plain,(
    ! [B_45,A_46] :
      ( B_45 = A_46
      | ~ r1_tarski(B_45,A_46)
      | ~ r1_tarski(A_46,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_120,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_103,c_111])).

tff(c_300,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_1096,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1030,c_300])).

tff(c_1106,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1027,c_1096])).

tff(c_1107,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_617])).

tff(c_1136,plain,(
    ! [A_5] : r1_tarski('#skF_3',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1107,c_104])).

tff(c_1139,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1107,c_1107,c_10])).

tff(c_1210,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1139,c_300])).

tff(c_1220,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1136,c_1210])).

tff(c_1221,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_1228,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1221,c_50])).

tff(c_1267,plain,(
    ! [A_165,B_166,C_167] :
      ( k1_relset_1(A_165,B_166,C_167) = k1_relat_1(C_167)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1364,plain,(
    ! [C_178] :
      ( k1_relset_1('#skF_2','#skF_3',C_178) = k1_relat_1(C_178)
      | ~ m1_subset_1(C_178,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1221,c_1267])).

tff(c_1379,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1228,c_1364])).

tff(c_1563,plain,(
    ! [B_203,A_204,C_205] :
      ( k1_xboole_0 = B_203
      | k1_relset_1(A_204,B_203,C_205) = A_204
      | ~ v1_funct_2(C_205,A_204,B_203)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_204,B_203))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1566,plain,(
    ! [C_205] :
      ( k1_xboole_0 = '#skF_3'
      | k1_relset_1('#skF_2','#skF_3',C_205) = '#skF_2'
      | ~ v1_funct_2(C_205,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_205,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1221,c_1563])).

tff(c_1632,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1566])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1242,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1221,c_8])).

tff(c_1336,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1242])).

tff(c_1645,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1632,c_1336])).

tff(c_1795,plain,(
    ! [A_219] : k2_zfmisc_1(A_219,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1632,c_1632,c_10])).

tff(c_1819,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1795,c_1221])).

tff(c_1841,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1645,c_1819])).

tff(c_1918,plain,(
    ! [C_226] :
      ( k1_relset_1('#skF_2','#skF_3',C_226) = '#skF_2'
      | ~ v1_funct_2(C_226,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_226,k1_zfmisc_1('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_1566])).

tff(c_1921,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_1228,c_1918])).

tff(c_1935,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1379,c_1921])).

tff(c_1229,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1221,c_56])).

tff(c_1380,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1229,c_1364])).

tff(c_1924,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_1229,c_1918])).

tff(c_1938,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1380,c_1924])).

tff(c_1972,plain,(
    ! [A_227,B_228] :
      ( r2_hidden('#skF_1'(A_227,B_228),k1_relat_1(A_227))
      | B_228 = A_227
      | k1_relat_1(B_228) != k1_relat_1(A_227)
      | ~ v1_funct_1(B_228)
      | ~ v1_relat_1(B_228)
      | ~ v1_funct_1(A_227)
      | ~ v1_relat_1(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1977,plain,(
    ! [B_228] :
      ( r2_hidden('#skF_1'('#skF_4',B_228),'#skF_2')
      | B_228 = '#skF_4'
      | k1_relat_1(B_228) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_228)
      | ~ v1_relat_1(B_228)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1938,c_1972])).

tff(c_2015,plain,(
    ! [B_231] :
      ( r2_hidden('#skF_1'('#skF_4',B_231),'#skF_2')
      | B_231 = '#skF_4'
      | k1_relat_1(B_231) != '#skF_2'
      | ~ v1_funct_1(B_231)
      | ~ v1_relat_1(B_231) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_60,c_1938,c_1977])).

tff(c_2285,plain,(
    ! [B_249,B_250] :
      ( m1_subset_1('#skF_1'('#skF_4',B_249),B_250)
      | ~ r1_tarski('#skF_2',B_250)
      | B_249 = '#skF_4'
      | k1_relat_1(B_249) != '#skF_2'
      | ~ v1_funct_1(B_249)
      | ~ v1_relat_1(B_249) ) ),
    inference(resolution,[status(thm)],[c_2015,c_184])).

tff(c_2349,plain,(
    ! [B_249] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_249)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_249))
      | ~ r1_tarski('#skF_2','#skF_2')
      | B_249 = '#skF_4'
      | k1_relat_1(B_249) != '#skF_2'
      | ~ v1_funct_1(B_249)
      | ~ v1_relat_1(B_249) ) ),
    inference(resolution,[status(thm)],[c_2285,c_48])).

tff(c_2517,plain,(
    ! [B_259] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_259)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_259))
      | B_259 = '#skF_4'
      | k1_relat_1(B_259) != '#skF_2'
      | ~ v1_funct_1(B_259)
      | ~ v1_relat_1(B_259) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2349])).

tff(c_2524,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2517,c_22])).

tff(c_2531,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_54,c_1935,c_173,c_60,c_1938,c_1935,c_2524])).

tff(c_102,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_92])).

tff(c_121,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_102,c_111])).

tff(c_270,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_1223,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1221,c_270])).

tff(c_2542,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2531,c_1223])).

tff(c_2555,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2542])).

tff(c_2557,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1242])).

tff(c_2571,plain,(
    ! [A_5] : r1_tarski('#skF_4',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2557,c_104])).

tff(c_2583,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2571,c_1223])).

tff(c_2584,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_2590,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2584,c_50])).

tff(c_2679,plain,(
    ! [A_266,B_267,C_268] :
      ( k1_relset_1(A_266,B_267,C_268) = k1_relat_1(C_268)
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k2_zfmisc_1(A_266,B_267))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2757,plain,(
    ! [C_283] :
      ( k1_relset_1('#skF_2','#skF_3',C_283) = k1_relat_1(C_283)
      | ~ m1_subset_1(C_283,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2584,c_2679])).

tff(c_2773,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2590,c_2757])).

tff(c_2946,plain,(
    ! [B_308,C_309,A_310] :
      ( k1_xboole_0 = B_308
      | v1_funct_2(C_309,A_310,B_308)
      | k1_relset_1(A_310,B_308,C_309) != A_310
      | ~ m1_subset_1(C_309,k1_zfmisc_1(k2_zfmisc_1(A_310,B_308))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2949,plain,(
    ! [C_309] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2(C_309,'#skF_2','#skF_3')
      | k1_relset_1('#skF_2','#skF_3',C_309) != '#skF_2'
      | ~ m1_subset_1(C_309,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2584,c_2946])).

tff(c_3025,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2949])).

tff(c_2604,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2584,c_8])).

tff(c_2706,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_2604])).

tff(c_3042,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3025,c_2706])).

tff(c_3055,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3025,c_3025,c_10])).

tff(c_3188,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3055,c_2584])).

tff(c_3190,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3042,c_3188])).

tff(c_3192,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2949])).

tff(c_2865,plain,(
    ! [B_294,A_295,C_296] :
      ( k1_xboole_0 = B_294
      | k1_relset_1(A_295,B_294,C_296) = A_295
      | ~ v1_funct_2(C_296,A_295,B_294)
      | ~ m1_subset_1(C_296,k1_zfmisc_1(k2_zfmisc_1(A_295,B_294))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2868,plain,(
    ! [C_296] :
      ( k1_xboole_0 = '#skF_3'
      | k1_relset_1('#skF_2','#skF_3',C_296) = '#skF_2'
      | ~ v1_funct_2(C_296,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_296,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2584,c_2865])).

tff(c_3193,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2868])).

tff(c_3194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3192,c_3193])).

tff(c_3197,plain,(
    ! [C_324] :
      ( k1_relset_1('#skF_2','#skF_3',C_324) = '#skF_2'
      | ~ v1_funct_2(C_324,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_324,k1_zfmisc_1('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_2868])).

tff(c_3203,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_2590,c_3197])).

tff(c_3217,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2773,c_3203])).

tff(c_2591,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2584,c_56])).

tff(c_2772,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2591,c_2757])).

tff(c_3200,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_2591,c_3197])).

tff(c_3214,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2772,c_3200])).

tff(c_3330,plain,(
    ! [A_331,B_332] :
      ( r2_hidden('#skF_1'(A_331,B_332),k1_relat_1(A_331))
      | B_332 = A_331
      | k1_relat_1(B_332) != k1_relat_1(A_331)
      | ~ v1_funct_1(B_332)
      | ~ v1_relat_1(B_332)
      | ~ v1_funct_1(A_331)
      | ~ v1_relat_1(A_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3338,plain,(
    ! [B_332] :
      ( r2_hidden('#skF_1'('#skF_4',B_332),'#skF_2')
      | B_332 = '#skF_4'
      | k1_relat_1(B_332) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_332)
      | ~ v1_relat_1(B_332)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3214,c_3330])).

tff(c_3363,plain,(
    ! [B_334] :
      ( r2_hidden('#skF_1'('#skF_4',B_334),'#skF_2')
      | B_334 = '#skF_4'
      | k1_relat_1(B_334) != '#skF_2'
      | ~ v1_funct_1(B_334)
      | ~ v1_relat_1(B_334) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_60,c_3214,c_3338])).

tff(c_3371,plain,(
    ! [B_336,B_337] :
      ( m1_subset_1('#skF_1'('#skF_4',B_336),B_337)
      | ~ r1_tarski('#skF_2',B_337)
      | B_336 = '#skF_4'
      | k1_relat_1(B_336) != '#skF_2'
      | ~ v1_funct_1(B_336)
      | ~ v1_relat_1(B_336) ) ),
    inference(resolution,[status(thm)],[c_3363,c_184])).

tff(c_3435,plain,(
    ! [B_336] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_336)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_336))
      | ~ r1_tarski('#skF_2','#skF_2')
      | B_336 = '#skF_4'
      | k1_relat_1(B_336) != '#skF_2'
      | ~ v1_funct_1(B_336)
      | ~ v1_relat_1(B_336) ) ),
    inference(resolution,[status(thm)],[c_3371,c_48])).

tff(c_3869,plain,(
    ! [B_363] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_363)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_363))
      | B_363 = '#skF_4'
      | k1_relat_1(B_363) != '#skF_2'
      | ~ v1_funct_1(B_363)
      | ~ v1_relat_1(B_363) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3435])).

tff(c_3876,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3869,c_22])).

tff(c_3883,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_54,c_3217,c_173,c_60,c_3217,c_3214,c_3876])).

tff(c_2588,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2584,c_103])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2611,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_2588,c_2])).

tff(c_2637,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2611])).

tff(c_3905,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3883,c_2637])).

tff(c_3921,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3905])).

tff(c_3923,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2604])).

tff(c_3933,plain,(
    ! [A_5] : r1_tarski('#skF_5',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3923,c_104])).

tff(c_3945,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3933,c_2637])).

tff(c_3946,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2611])).

tff(c_3956,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3946,c_46])).

tff(c_3964,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_3956])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:25:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.13/2.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.51/2.02  
% 5.51/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.51/2.03  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.51/2.03  
% 5.51/2.03  %Foreground sorts:
% 5.51/2.03  
% 5.51/2.03  
% 5.51/2.03  %Background operators:
% 5.51/2.03  
% 5.51/2.03  
% 5.51/2.03  %Foreground operators:
% 5.51/2.03  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.51/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.51/2.03  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.51/2.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.51/2.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.51/2.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.51/2.03  tff('#skF_5', type, '#skF_5': $i).
% 5.51/2.03  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.51/2.03  tff('#skF_2', type, '#skF_2': $i).
% 5.51/2.03  tff('#skF_3', type, '#skF_3': $i).
% 5.51/2.03  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.51/2.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.51/2.03  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.51/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.51/2.03  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.51/2.03  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.51/2.03  tff('#skF_4', type, '#skF_4': $i).
% 5.51/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.51/2.03  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.51/2.03  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.51/2.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.51/2.03  
% 5.51/2.05  tff(f_122, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_funct_2)).
% 5.51/2.05  tff(f_83, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.51/2.05  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.51/2.05  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.51/2.05  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.51/2.05  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.51/2.05  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 5.51/2.05  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.51/2.05  tff(f_49, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 5.51/2.05  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 5.51/2.05  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.51/2.05  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.51/2.05  tff(c_250, plain, (![A_71, B_72, D_73]: (r2_relset_1(A_71, B_72, D_73, D_73) | ~m1_subset_1(D_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.51/2.05  tff(c_267, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_250])).
% 5.51/2.05  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.51/2.05  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.51/2.05  tff(c_152, plain, (![C_51, A_52, B_53]: (v1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.51/2.05  tff(c_172, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_152])).
% 5.51/2.05  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.51/2.05  tff(c_52, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.51/2.05  tff(c_323, plain, (![A_89, B_90, C_91]: (k1_relset_1(A_89, B_90, C_91)=k1_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.51/2.05  tff(c_345, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_323])).
% 5.51/2.05  tff(c_593, plain, (![B_125, A_126, C_127]: (k1_xboole_0=B_125 | k1_relset_1(A_126, B_125, C_127)=A_126 | ~v1_funct_2(C_127, A_126, B_125) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_126, B_125))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.51/2.05  tff(c_600, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_593])).
% 5.51/2.05  tff(c_617, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_345, c_600])).
% 5.51/2.05  tff(c_624, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_617])).
% 5.51/2.05  tff(c_173, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_152])).
% 5.51/2.05  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.51/2.05  tff(c_58, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.51/2.05  tff(c_346, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_323])).
% 5.51/2.05  tff(c_603, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_593])).
% 5.51/2.05  tff(c_620, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_346, c_603])).
% 5.51/2.05  tff(c_630, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_620])).
% 5.51/2.05  tff(c_727, plain, (![A_137, B_138]: (r2_hidden('#skF_1'(A_137, B_138), k1_relat_1(A_137)) | B_138=A_137 | k1_relat_1(B_138)!=k1_relat_1(A_137) | ~v1_funct_1(B_138) | ~v1_relat_1(B_138) | ~v1_funct_1(A_137) | ~v1_relat_1(A_137))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.51/2.05  tff(c_732, plain, (![B_138]: (r2_hidden('#skF_1'('#skF_4', B_138), '#skF_2') | B_138='#skF_4' | k1_relat_1(B_138)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_138) | ~v1_relat_1(B_138) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_630, c_727])).
% 5.51/2.05  tff(c_812, plain, (![B_144]: (r2_hidden('#skF_1'('#skF_4', B_144), '#skF_2') | B_144='#skF_4' | k1_relat_1(B_144)!='#skF_2' | ~v1_funct_1(B_144) | ~v1_relat_1(B_144))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_60, c_630, c_732])).
% 5.51/2.05  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.51/2.05  tff(c_175, plain, (![A_54, C_55, B_56]: (m1_subset_1(A_54, C_55) | ~m1_subset_1(B_56, k1_zfmisc_1(C_55)) | ~r2_hidden(A_54, B_56))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.51/2.05  tff(c_184, plain, (![A_54, B_7, A_6]: (m1_subset_1(A_54, B_7) | ~r2_hidden(A_54, A_6) | ~r1_tarski(A_6, B_7))), inference(resolution, [status(thm)], [c_18, c_175])).
% 5.51/2.05  tff(c_826, plain, (![B_148, B_149]: (m1_subset_1('#skF_1'('#skF_4', B_148), B_149) | ~r1_tarski('#skF_2', B_149) | B_148='#skF_4' | k1_relat_1(B_148)!='#skF_2' | ~v1_funct_1(B_148) | ~v1_relat_1(B_148))), inference(resolution, [status(thm)], [c_812, c_184])).
% 5.51/2.05  tff(c_48, plain, (![E_34]: (k1_funct_1('#skF_5', E_34)=k1_funct_1('#skF_4', E_34) | ~m1_subset_1(E_34, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.51/2.05  tff(c_871, plain, (![B_148]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_148))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_148)) | ~r1_tarski('#skF_2', '#skF_2') | B_148='#skF_4' | k1_relat_1(B_148)!='#skF_2' | ~v1_funct_1(B_148) | ~v1_relat_1(B_148))), inference(resolution, [status(thm)], [c_826, c_48])).
% 5.51/2.05  tff(c_959, plain, (![B_152]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_152))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_152)) | B_152='#skF_4' | k1_relat_1(B_152)!='#skF_2' | ~v1_funct_1(B_152) | ~v1_relat_1(B_152))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_871])).
% 5.51/2.05  tff(c_22, plain, (![B_15, A_11]: (k1_funct_1(B_15, '#skF_1'(A_11, B_15))!=k1_funct_1(A_11, '#skF_1'(A_11, B_15)) | B_15=A_11 | k1_relat_1(B_15)!=k1_relat_1(A_11) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.51/2.05  tff(c_966, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_5'='#skF_4' | k1_relat_1('#skF_5')!='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_959, c_22])).
% 5.51/2.05  tff(c_973, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_172, c_54, c_624, c_173, c_60, c_630, c_624, c_966])).
% 5.51/2.05  tff(c_46, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.51/2.05  tff(c_987, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_973, c_46])).
% 5.51/2.05  tff(c_998, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_267, c_987])).
% 5.51/2.05  tff(c_999, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_620])).
% 5.51/2.05  tff(c_14, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.51/2.05  tff(c_92, plain, (![A_40, B_41]: (r1_tarski(A_40, B_41) | ~m1_subset_1(A_40, k1_zfmisc_1(B_41)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.51/2.05  tff(c_104, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(resolution, [status(thm)], [c_14, c_92])).
% 5.51/2.05  tff(c_1027, plain, (![A_5]: (r1_tarski('#skF_3', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_999, c_104])).
% 5.51/2.05  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.51/2.05  tff(c_1030, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_999, c_999, c_10])).
% 5.51/2.05  tff(c_103, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_56, c_92])).
% 5.51/2.05  tff(c_111, plain, (![B_45, A_46]: (B_45=A_46 | ~r1_tarski(B_45, A_46) | ~r1_tarski(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.51/2.05  tff(c_120, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_103, c_111])).
% 5.51/2.05  tff(c_300, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_120])).
% 5.51/2.05  tff(c_1096, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1030, c_300])).
% 5.51/2.05  tff(c_1106, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1027, c_1096])).
% 5.51/2.05  tff(c_1107, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_617])).
% 5.51/2.05  tff(c_1136, plain, (![A_5]: (r1_tarski('#skF_3', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_1107, c_104])).
% 5.51/2.05  tff(c_1139, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1107, c_1107, c_10])).
% 5.51/2.05  tff(c_1210, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1139, c_300])).
% 5.51/2.05  tff(c_1220, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1136, c_1210])).
% 5.51/2.05  tff(c_1221, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_120])).
% 5.51/2.05  tff(c_1228, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1221, c_50])).
% 5.51/2.05  tff(c_1267, plain, (![A_165, B_166, C_167]: (k1_relset_1(A_165, B_166, C_167)=k1_relat_1(C_167) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.51/2.05  tff(c_1364, plain, (![C_178]: (k1_relset_1('#skF_2', '#skF_3', C_178)=k1_relat_1(C_178) | ~m1_subset_1(C_178, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1221, c_1267])).
% 5.51/2.05  tff(c_1379, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1228, c_1364])).
% 5.51/2.05  tff(c_1563, plain, (![B_203, A_204, C_205]: (k1_xboole_0=B_203 | k1_relset_1(A_204, B_203, C_205)=A_204 | ~v1_funct_2(C_205, A_204, B_203) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_204, B_203))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.51/2.05  tff(c_1566, plain, (![C_205]: (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', C_205)='#skF_2' | ~v1_funct_2(C_205, '#skF_2', '#skF_3') | ~m1_subset_1(C_205, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1221, c_1563])).
% 5.51/2.05  tff(c_1632, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1566])).
% 5.51/2.05  tff(c_8, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.51/2.05  tff(c_1242, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1221, c_8])).
% 5.51/2.05  tff(c_1336, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_1242])).
% 5.51/2.05  tff(c_1645, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1632, c_1336])).
% 5.51/2.05  tff(c_1795, plain, (![A_219]: (k2_zfmisc_1(A_219, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1632, c_1632, c_10])).
% 5.51/2.05  tff(c_1819, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1795, c_1221])).
% 5.51/2.05  tff(c_1841, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1645, c_1819])).
% 5.51/2.05  tff(c_1918, plain, (![C_226]: (k1_relset_1('#skF_2', '#skF_3', C_226)='#skF_2' | ~v1_funct_2(C_226, '#skF_2', '#skF_3') | ~m1_subset_1(C_226, k1_zfmisc_1('#skF_4')))), inference(splitRight, [status(thm)], [c_1566])).
% 5.51/2.05  tff(c_1921, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_1228, c_1918])).
% 5.51/2.05  tff(c_1935, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1379, c_1921])).
% 5.51/2.05  tff(c_1229, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1221, c_56])).
% 5.51/2.05  tff(c_1380, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1229, c_1364])).
% 5.51/2.05  tff(c_1924, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_1229, c_1918])).
% 5.51/2.05  tff(c_1938, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1380, c_1924])).
% 5.51/2.05  tff(c_1972, plain, (![A_227, B_228]: (r2_hidden('#skF_1'(A_227, B_228), k1_relat_1(A_227)) | B_228=A_227 | k1_relat_1(B_228)!=k1_relat_1(A_227) | ~v1_funct_1(B_228) | ~v1_relat_1(B_228) | ~v1_funct_1(A_227) | ~v1_relat_1(A_227))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.51/2.05  tff(c_1977, plain, (![B_228]: (r2_hidden('#skF_1'('#skF_4', B_228), '#skF_2') | B_228='#skF_4' | k1_relat_1(B_228)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_228) | ~v1_relat_1(B_228) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1938, c_1972])).
% 5.51/2.05  tff(c_2015, plain, (![B_231]: (r2_hidden('#skF_1'('#skF_4', B_231), '#skF_2') | B_231='#skF_4' | k1_relat_1(B_231)!='#skF_2' | ~v1_funct_1(B_231) | ~v1_relat_1(B_231))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_60, c_1938, c_1977])).
% 5.51/2.05  tff(c_2285, plain, (![B_249, B_250]: (m1_subset_1('#skF_1'('#skF_4', B_249), B_250) | ~r1_tarski('#skF_2', B_250) | B_249='#skF_4' | k1_relat_1(B_249)!='#skF_2' | ~v1_funct_1(B_249) | ~v1_relat_1(B_249))), inference(resolution, [status(thm)], [c_2015, c_184])).
% 5.51/2.05  tff(c_2349, plain, (![B_249]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_249))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_249)) | ~r1_tarski('#skF_2', '#skF_2') | B_249='#skF_4' | k1_relat_1(B_249)!='#skF_2' | ~v1_funct_1(B_249) | ~v1_relat_1(B_249))), inference(resolution, [status(thm)], [c_2285, c_48])).
% 5.51/2.05  tff(c_2517, plain, (![B_259]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_259))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_259)) | B_259='#skF_4' | k1_relat_1(B_259)!='#skF_2' | ~v1_funct_1(B_259) | ~v1_relat_1(B_259))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2349])).
% 5.51/2.05  tff(c_2524, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_5'='#skF_4' | k1_relat_1('#skF_5')!='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2517, c_22])).
% 5.51/2.05  tff(c_2531, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_172, c_54, c_1935, c_173, c_60, c_1938, c_1935, c_2524])).
% 5.51/2.05  tff(c_102, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_50, c_92])).
% 5.51/2.05  tff(c_121, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_102, c_111])).
% 5.51/2.05  tff(c_270, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_121])).
% 5.51/2.05  tff(c_1223, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1221, c_270])).
% 5.51/2.05  tff(c_2542, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2531, c_1223])).
% 5.51/2.05  tff(c_2555, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2542])).
% 5.51/2.05  tff(c_2557, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1242])).
% 5.51/2.05  tff(c_2571, plain, (![A_5]: (r1_tarski('#skF_4', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_2557, c_104])).
% 5.51/2.05  tff(c_2583, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2571, c_1223])).
% 5.51/2.05  tff(c_2584, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5'), inference(splitRight, [status(thm)], [c_121])).
% 5.51/2.05  tff(c_2590, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2584, c_50])).
% 5.51/2.05  tff(c_2679, plain, (![A_266, B_267, C_268]: (k1_relset_1(A_266, B_267, C_268)=k1_relat_1(C_268) | ~m1_subset_1(C_268, k1_zfmisc_1(k2_zfmisc_1(A_266, B_267))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.51/2.05  tff(c_2757, plain, (![C_283]: (k1_relset_1('#skF_2', '#skF_3', C_283)=k1_relat_1(C_283) | ~m1_subset_1(C_283, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_2584, c_2679])).
% 5.51/2.05  tff(c_2773, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2590, c_2757])).
% 5.51/2.05  tff(c_2946, plain, (![B_308, C_309, A_310]: (k1_xboole_0=B_308 | v1_funct_2(C_309, A_310, B_308) | k1_relset_1(A_310, B_308, C_309)!=A_310 | ~m1_subset_1(C_309, k1_zfmisc_1(k2_zfmisc_1(A_310, B_308))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.51/2.05  tff(c_2949, plain, (![C_309]: (k1_xboole_0='#skF_3' | v1_funct_2(C_309, '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', C_309)!='#skF_2' | ~m1_subset_1(C_309, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_2584, c_2946])).
% 5.51/2.05  tff(c_3025, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2949])).
% 5.51/2.05  tff(c_2604, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_2584, c_8])).
% 5.51/2.05  tff(c_2706, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_2604])).
% 5.51/2.05  tff(c_3042, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3025, c_2706])).
% 5.51/2.05  tff(c_3055, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3025, c_3025, c_10])).
% 5.51/2.05  tff(c_3188, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3055, c_2584])).
% 5.51/2.05  tff(c_3190, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3042, c_3188])).
% 5.51/2.05  tff(c_3192, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_2949])).
% 5.51/2.05  tff(c_2865, plain, (![B_294, A_295, C_296]: (k1_xboole_0=B_294 | k1_relset_1(A_295, B_294, C_296)=A_295 | ~v1_funct_2(C_296, A_295, B_294) | ~m1_subset_1(C_296, k1_zfmisc_1(k2_zfmisc_1(A_295, B_294))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.51/2.05  tff(c_2868, plain, (![C_296]: (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', C_296)='#skF_2' | ~v1_funct_2(C_296, '#skF_2', '#skF_3') | ~m1_subset_1(C_296, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_2584, c_2865])).
% 5.51/2.05  tff(c_3193, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2868])).
% 5.51/2.05  tff(c_3194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3192, c_3193])).
% 5.51/2.05  tff(c_3197, plain, (![C_324]: (k1_relset_1('#skF_2', '#skF_3', C_324)='#skF_2' | ~v1_funct_2(C_324, '#skF_2', '#skF_3') | ~m1_subset_1(C_324, k1_zfmisc_1('#skF_5')))), inference(splitRight, [status(thm)], [c_2868])).
% 5.51/2.05  tff(c_3203, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_2590, c_3197])).
% 5.51/2.05  tff(c_3217, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2773, c_3203])).
% 5.51/2.05  tff(c_2591, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2584, c_56])).
% 5.51/2.05  tff(c_2772, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2591, c_2757])).
% 5.51/2.05  tff(c_3200, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_2591, c_3197])).
% 5.51/2.05  tff(c_3214, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2772, c_3200])).
% 5.51/2.05  tff(c_3330, plain, (![A_331, B_332]: (r2_hidden('#skF_1'(A_331, B_332), k1_relat_1(A_331)) | B_332=A_331 | k1_relat_1(B_332)!=k1_relat_1(A_331) | ~v1_funct_1(B_332) | ~v1_relat_1(B_332) | ~v1_funct_1(A_331) | ~v1_relat_1(A_331))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.51/2.05  tff(c_3338, plain, (![B_332]: (r2_hidden('#skF_1'('#skF_4', B_332), '#skF_2') | B_332='#skF_4' | k1_relat_1(B_332)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_332) | ~v1_relat_1(B_332) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3214, c_3330])).
% 5.51/2.05  tff(c_3363, plain, (![B_334]: (r2_hidden('#skF_1'('#skF_4', B_334), '#skF_2') | B_334='#skF_4' | k1_relat_1(B_334)!='#skF_2' | ~v1_funct_1(B_334) | ~v1_relat_1(B_334))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_60, c_3214, c_3338])).
% 5.51/2.05  tff(c_3371, plain, (![B_336, B_337]: (m1_subset_1('#skF_1'('#skF_4', B_336), B_337) | ~r1_tarski('#skF_2', B_337) | B_336='#skF_4' | k1_relat_1(B_336)!='#skF_2' | ~v1_funct_1(B_336) | ~v1_relat_1(B_336))), inference(resolution, [status(thm)], [c_3363, c_184])).
% 5.51/2.05  tff(c_3435, plain, (![B_336]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_336))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_336)) | ~r1_tarski('#skF_2', '#skF_2') | B_336='#skF_4' | k1_relat_1(B_336)!='#skF_2' | ~v1_funct_1(B_336) | ~v1_relat_1(B_336))), inference(resolution, [status(thm)], [c_3371, c_48])).
% 5.51/2.05  tff(c_3869, plain, (![B_363]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_363))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_363)) | B_363='#skF_4' | k1_relat_1(B_363)!='#skF_2' | ~v1_funct_1(B_363) | ~v1_relat_1(B_363))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_3435])).
% 5.51/2.05  tff(c_3876, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_5'='#skF_4' | k1_relat_1('#skF_5')!='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3869, c_22])).
% 5.51/2.05  tff(c_3883, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_172, c_54, c_3217, c_173, c_60, c_3217, c_3214, c_3876])).
% 5.51/2.05  tff(c_2588, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2584, c_103])).
% 5.51/2.05  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.51/2.05  tff(c_2611, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_2588, c_2])).
% 5.51/2.05  tff(c_2637, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_2611])).
% 5.51/2.05  tff(c_3905, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3883, c_2637])).
% 5.51/2.05  tff(c_3921, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3905])).
% 5.51/2.05  tff(c_3923, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_2604])).
% 5.51/2.05  tff(c_3933, plain, (![A_5]: (r1_tarski('#skF_5', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_3923, c_104])).
% 5.51/2.05  tff(c_3945, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3933, c_2637])).
% 5.51/2.05  tff(c_3946, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_2611])).
% 5.51/2.05  tff(c_3956, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3946, c_46])).
% 5.51/2.05  tff(c_3964, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_267, c_3956])).
% 5.51/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.51/2.05  
% 5.51/2.05  Inference rules
% 5.51/2.05  ----------------------
% 5.51/2.05  #Ref     : 3
% 5.51/2.05  #Sup     : 759
% 5.51/2.05  #Fact    : 0
% 5.51/2.05  #Define  : 0
% 5.51/2.05  #Split   : 24
% 5.51/2.05  #Chain   : 0
% 5.51/2.05  #Close   : 0
% 5.51/2.05  
% 5.51/2.05  Ordering : KBO
% 5.51/2.05  
% 5.51/2.05  Simplification rules
% 5.51/2.05  ----------------------
% 5.51/2.05  #Subsume      : 139
% 5.51/2.05  #Demod        : 955
% 5.51/2.05  #Tautology    : 343
% 5.51/2.05  #SimpNegUnit  : 49
% 5.51/2.05  #BackRed      : 261
% 5.51/2.05  
% 5.51/2.05  #Partial instantiations: 0
% 5.51/2.05  #Strategies tried      : 1
% 5.51/2.05  
% 5.51/2.05  Timing (in seconds)
% 5.51/2.05  ----------------------
% 5.51/2.06  Preprocessing        : 0.33
% 5.51/2.06  Parsing              : 0.18
% 5.51/2.06  CNF conversion       : 0.02
% 5.51/2.06  Main loop            : 0.92
% 5.51/2.06  Inferencing          : 0.30
% 5.51/2.06  Reduction            : 0.31
% 5.51/2.06  Demodulation         : 0.22
% 5.51/2.06  BG Simplification    : 0.04
% 5.51/2.06  Subsumption          : 0.20
% 5.51/2.06  Abstraction          : 0.05
% 5.51/2.06  MUC search           : 0.00
% 5.51/2.06  Cooper               : 0.00
% 5.51/2.06  Total                : 1.31
% 5.51/2.06  Index Insertion      : 0.00
% 5.51/2.06  Index Deletion       : 0.00
% 5.51/2.06  Index Matching       : 0.00
% 5.51/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
