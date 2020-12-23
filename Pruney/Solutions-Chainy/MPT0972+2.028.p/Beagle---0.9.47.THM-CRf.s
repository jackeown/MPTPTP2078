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
% DateTime   : Thu Dec  3 10:11:38 EST 2020

% Result     : Theorem 4.83s
% Output     : CNFRefutation 4.83s
% Verified   : 
% Statistics : Number of formulae       :  164 (1173 expanded)
%              Number of leaves         :   31 ( 392 expanded)
%              Depth                    :   15
%              Number of atoms          :  323 (3545 expanded)
%              Number of equality atoms :  143 ( 983 expanded)
%              Maximal formula depth    :   11 (   3 average)
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
                  ( r2_hidden(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

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

tff(c_48,plain,(
    ! [E_34] :
      ( k1_funct_1('#skF_5',E_34) = k1_funct_1('#skF_4',E_34)
      | ~ r2_hidden(E_34,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_953,plain,(
    ! [B_152] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_152)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_152))
      | B_152 = '#skF_4'
      | k1_relat_1(B_152) != '#skF_2'
      | ~ v1_funct_1(B_152)
      | ~ v1_relat_1(B_152) ) ),
    inference(resolution,[status(thm)],[c_812,c_48])).

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

tff(c_960,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_953,c_22])).

tff(c_967,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_54,c_624,c_173,c_60,c_630,c_624,c_960])).

tff(c_46,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_981,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_967,c_46])).

tff(c_992,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_981])).

tff(c_993,plain,(
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

tff(c_1021,plain,(
    ! [A_5] : r1_tarski('#skF_3',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_993,c_104])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1024,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_993,c_993,c_10])).

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

tff(c_1090,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1024,c_300])).

tff(c_1100,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1021,c_1090])).

tff(c_1101,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_617])).

tff(c_1130,plain,(
    ! [A_5] : r1_tarski('#skF_3',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1101,c_104])).

tff(c_1133,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1101,c_1101,c_10])).

tff(c_1204,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1133,c_300])).

tff(c_1214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1130,c_1204])).

tff(c_1215,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_1222,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1215,c_50])).

tff(c_1261,plain,(
    ! [A_165,B_166,C_167] :
      ( k1_relset_1(A_165,B_166,C_167) = k1_relat_1(C_167)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1358,plain,(
    ! [C_178] :
      ( k1_relset_1('#skF_2','#skF_3',C_178) = k1_relat_1(C_178)
      | ~ m1_subset_1(C_178,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1215,c_1261])).

tff(c_1373,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1222,c_1358])).

tff(c_1557,plain,(
    ! [B_203,A_204,C_205] :
      ( k1_xboole_0 = B_203
      | k1_relset_1(A_204,B_203,C_205) = A_204
      | ~ v1_funct_2(C_205,A_204,B_203)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_204,B_203))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1560,plain,(
    ! [C_205] :
      ( k1_xboole_0 = '#skF_3'
      | k1_relset_1('#skF_2','#skF_3',C_205) = '#skF_2'
      | ~ v1_funct_2(C_205,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_205,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1215,c_1557])).

tff(c_1626,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1560])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1236,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1215,c_8])).

tff(c_1330,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1236])).

tff(c_1639,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1626,c_1330])).

tff(c_1789,plain,(
    ! [A_219] : k2_zfmisc_1(A_219,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1626,c_1626,c_10])).

tff(c_1813,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1789,c_1215])).

tff(c_1835,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1639,c_1813])).

tff(c_1912,plain,(
    ! [C_226] :
      ( k1_relset_1('#skF_2','#skF_3',C_226) = '#skF_2'
      | ~ v1_funct_2(C_226,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_226,k1_zfmisc_1('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_1560])).

tff(c_1915,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_1222,c_1912])).

tff(c_1929,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1373,c_1915])).

tff(c_1223,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1215,c_56])).

tff(c_1374,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1223,c_1358])).

tff(c_1918,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_1223,c_1912])).

tff(c_1932,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1374,c_1918])).

tff(c_1966,plain,(
    ! [A_227,B_228] :
      ( r2_hidden('#skF_1'(A_227,B_228),k1_relat_1(A_227))
      | B_228 = A_227
      | k1_relat_1(B_228) != k1_relat_1(A_227)
      | ~ v1_funct_1(B_228)
      | ~ v1_relat_1(B_228)
      | ~ v1_funct_1(A_227)
      | ~ v1_relat_1(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1971,plain,(
    ! [B_228] :
      ( r2_hidden('#skF_1'('#skF_4',B_228),'#skF_2')
      | B_228 = '#skF_4'
      | k1_relat_1(B_228) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_228)
      | ~ v1_relat_1(B_228)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1932,c_1966])).

tff(c_2013,plain,(
    ! [B_231] :
      ( r2_hidden('#skF_1'('#skF_4',B_231),'#skF_2')
      | B_231 = '#skF_4'
      | k1_relat_1(B_231) != '#skF_2'
      | ~ v1_funct_1(B_231)
      | ~ v1_relat_1(B_231) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_60,c_1932,c_1971])).

tff(c_2377,plain,(
    ! [B_252] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_252)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_252))
      | B_252 = '#skF_4'
      | k1_relat_1(B_252) != '#skF_2'
      | ~ v1_funct_1(B_252)
      | ~ v1_relat_1(B_252) ) ),
    inference(resolution,[status(thm)],[c_2013,c_48])).

tff(c_2384,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2377,c_22])).

tff(c_2391,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_54,c_1929,c_173,c_60,c_1932,c_1929,c_2384])).

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

tff(c_1217,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1215,c_270])).

tff(c_2401,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2391,c_1217])).

tff(c_2414,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2401])).

tff(c_2416,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1236])).

tff(c_2430,plain,(
    ! [A_5] : r1_tarski('#skF_4',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2416,c_104])).

tff(c_2442,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2430,c_1217])).

tff(c_2443,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_2449,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2443,c_50])).

tff(c_2538,plain,(
    ! [A_259,B_260,C_261] :
      ( k1_relset_1(A_259,B_260,C_261) = k1_relat_1(C_261)
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k2_zfmisc_1(A_259,B_260))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2616,plain,(
    ! [C_276] :
      ( k1_relset_1('#skF_2','#skF_3',C_276) = k1_relat_1(C_276)
      | ~ m1_subset_1(C_276,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2443,c_2538])).

tff(c_2632,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2449,c_2616])).

tff(c_2805,plain,(
    ! [B_301,C_302,A_303] :
      ( k1_xboole_0 = B_301
      | v1_funct_2(C_302,A_303,B_301)
      | k1_relset_1(A_303,B_301,C_302) != A_303
      | ~ m1_subset_1(C_302,k1_zfmisc_1(k2_zfmisc_1(A_303,B_301))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2808,plain,(
    ! [C_302] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2(C_302,'#skF_2','#skF_3')
      | k1_relset_1('#skF_2','#skF_3',C_302) != '#skF_2'
      | ~ m1_subset_1(C_302,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2443,c_2805])).

tff(c_2884,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2808])).

tff(c_2463,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2443,c_8])).

tff(c_2565,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_2463])).

tff(c_2901,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2884,c_2565])).

tff(c_2914,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2884,c_2884,c_10])).

tff(c_3047,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2914,c_2443])).

tff(c_3049,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2901,c_3047])).

tff(c_3051,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2808])).

tff(c_2724,plain,(
    ! [B_287,A_288,C_289] :
      ( k1_xboole_0 = B_287
      | k1_relset_1(A_288,B_287,C_289) = A_288
      | ~ v1_funct_2(C_289,A_288,B_287)
      | ~ m1_subset_1(C_289,k1_zfmisc_1(k2_zfmisc_1(A_288,B_287))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2727,plain,(
    ! [C_289] :
      ( k1_xboole_0 = '#skF_3'
      | k1_relset_1('#skF_2','#skF_3',C_289) = '#skF_2'
      | ~ v1_funct_2(C_289,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_289,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2443,c_2724])).

tff(c_3052,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2727])).

tff(c_3053,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3051,c_3052])).

tff(c_3056,plain,(
    ! [C_317] :
      ( k1_relset_1('#skF_2','#skF_3',C_317) = '#skF_2'
      | ~ v1_funct_2(C_317,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_317,k1_zfmisc_1('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_2727])).

tff(c_3062,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_2449,c_3056])).

tff(c_3076,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2632,c_3062])).

tff(c_2450,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2443,c_56])).

tff(c_2631,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2450,c_2616])).

tff(c_3059,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_2450,c_3056])).

tff(c_3073,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2631,c_3059])).

tff(c_3189,plain,(
    ! [A_324,B_325] :
      ( r2_hidden('#skF_1'(A_324,B_325),k1_relat_1(A_324))
      | B_325 = A_324
      | k1_relat_1(B_325) != k1_relat_1(A_324)
      | ~ v1_funct_1(B_325)
      | ~ v1_relat_1(B_325)
      | ~ v1_funct_1(A_324)
      | ~ v1_relat_1(A_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3197,plain,(
    ! [B_325] :
      ( r2_hidden('#skF_1'('#skF_4',B_325),'#skF_2')
      | B_325 = '#skF_4'
      | k1_relat_1(B_325) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_325)
      | ~ v1_relat_1(B_325)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3073,c_3189])).

tff(c_3222,plain,(
    ! [B_327] :
      ( r2_hidden('#skF_1'('#skF_4',B_327),'#skF_2')
      | B_327 = '#skF_4'
      | k1_relat_1(B_327) != '#skF_2'
      | ~ v1_funct_1(B_327)
      | ~ v1_relat_1(B_327) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_60,c_3073,c_3197])).

tff(c_3229,plain,(
    ! [B_327] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_327)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_327))
      | B_327 = '#skF_4'
      | k1_relat_1(B_327) != '#skF_2'
      | ~ v1_funct_1(B_327)
      | ~ v1_relat_1(B_327) ) ),
    inference(resolution,[status(thm)],[c_3222,c_48])).

tff(c_3373,plain,(
    ! [B_341,A_342] :
      ( k1_funct_1(B_341,'#skF_1'(A_342,B_341)) != k1_funct_1(A_342,'#skF_1'(A_342,B_341))
      | B_341 = A_342
      | k1_relat_1(B_341) != k1_relat_1(A_342)
      | ~ v1_funct_1(B_341)
      | ~ v1_relat_1(B_341)
      | ~ v1_funct_1(A_342)
      | ~ v1_relat_1(A_342) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3377,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3229,c_3373])).

tff(c_3380,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_54,c_3076,c_173,c_60,c_3076,c_3073,c_3377])).

tff(c_2447,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2443,c_103])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2470,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_2447,c_2])).

tff(c_2496,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2470])).

tff(c_3397,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3380,c_2496])).

tff(c_3413,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3397])).

tff(c_3415,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2463])).

tff(c_3425,plain,(
    ! [A_5] : r1_tarski('#skF_5',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3415,c_104])).

tff(c_3437,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3425,c_2496])).

tff(c_3438,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2470])).

tff(c_3450,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3438,c_46])).

tff(c_3458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_3450])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:08:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.83/1.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.83/1.86  
% 4.83/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.83/1.87  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.83/1.87  
% 4.83/1.87  %Foreground sorts:
% 4.83/1.87  
% 4.83/1.87  
% 4.83/1.87  %Background operators:
% 4.83/1.87  
% 4.83/1.87  
% 4.83/1.87  %Foreground operators:
% 4.83/1.87  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.83/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.83/1.87  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.83/1.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.83/1.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.83/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.83/1.87  tff('#skF_5', type, '#skF_5': $i).
% 4.83/1.87  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.83/1.87  tff('#skF_2', type, '#skF_2': $i).
% 4.83/1.87  tff('#skF_3', type, '#skF_3': $i).
% 4.83/1.87  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.83/1.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.83/1.87  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.83/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.83/1.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.83/1.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.83/1.87  tff('#skF_4', type, '#skF_4': $i).
% 4.83/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.83/1.87  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.83/1.87  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.83/1.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.83/1.87  
% 4.83/1.89  tff(f_122, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_2)).
% 4.83/1.89  tff(f_83, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.83/1.89  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.83/1.89  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.83/1.89  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.83/1.89  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.83/1.89  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 4.83/1.89  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.83/1.89  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.83/1.89  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.83/1.89  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.83/1.89  tff(c_250, plain, (![A_71, B_72, D_73]: (r2_relset_1(A_71, B_72, D_73, D_73) | ~m1_subset_1(D_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.83/1.89  tff(c_267, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_250])).
% 4.83/1.89  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.83/1.89  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.83/1.89  tff(c_152, plain, (![C_51, A_52, B_53]: (v1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.83/1.89  tff(c_172, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_152])).
% 4.83/1.89  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.83/1.89  tff(c_52, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.83/1.89  tff(c_323, plain, (![A_89, B_90, C_91]: (k1_relset_1(A_89, B_90, C_91)=k1_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.83/1.89  tff(c_345, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_323])).
% 4.83/1.89  tff(c_593, plain, (![B_125, A_126, C_127]: (k1_xboole_0=B_125 | k1_relset_1(A_126, B_125, C_127)=A_126 | ~v1_funct_2(C_127, A_126, B_125) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_126, B_125))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.83/1.89  tff(c_600, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_593])).
% 4.83/1.89  tff(c_617, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_345, c_600])).
% 4.83/1.89  tff(c_624, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_617])).
% 4.83/1.89  tff(c_173, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_152])).
% 4.83/1.89  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.83/1.89  tff(c_58, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.83/1.89  tff(c_346, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_323])).
% 4.83/1.89  tff(c_603, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_593])).
% 4.83/1.89  tff(c_620, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_346, c_603])).
% 4.83/1.89  tff(c_630, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_620])).
% 4.83/1.89  tff(c_727, plain, (![A_137, B_138]: (r2_hidden('#skF_1'(A_137, B_138), k1_relat_1(A_137)) | B_138=A_137 | k1_relat_1(B_138)!=k1_relat_1(A_137) | ~v1_funct_1(B_138) | ~v1_relat_1(B_138) | ~v1_funct_1(A_137) | ~v1_relat_1(A_137))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.83/1.89  tff(c_732, plain, (![B_138]: (r2_hidden('#skF_1'('#skF_4', B_138), '#skF_2') | B_138='#skF_4' | k1_relat_1(B_138)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_138) | ~v1_relat_1(B_138) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_630, c_727])).
% 4.83/1.89  tff(c_812, plain, (![B_144]: (r2_hidden('#skF_1'('#skF_4', B_144), '#skF_2') | B_144='#skF_4' | k1_relat_1(B_144)!='#skF_2' | ~v1_funct_1(B_144) | ~v1_relat_1(B_144))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_60, c_630, c_732])).
% 4.83/1.89  tff(c_48, plain, (![E_34]: (k1_funct_1('#skF_5', E_34)=k1_funct_1('#skF_4', E_34) | ~r2_hidden(E_34, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.83/1.89  tff(c_953, plain, (![B_152]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_152))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_152)) | B_152='#skF_4' | k1_relat_1(B_152)!='#skF_2' | ~v1_funct_1(B_152) | ~v1_relat_1(B_152))), inference(resolution, [status(thm)], [c_812, c_48])).
% 4.83/1.89  tff(c_22, plain, (![B_15, A_11]: (k1_funct_1(B_15, '#skF_1'(A_11, B_15))!=k1_funct_1(A_11, '#skF_1'(A_11, B_15)) | B_15=A_11 | k1_relat_1(B_15)!=k1_relat_1(A_11) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.83/1.89  tff(c_960, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_5'='#skF_4' | k1_relat_1('#skF_5')!='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_953, c_22])).
% 4.83/1.89  tff(c_967, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_172, c_54, c_624, c_173, c_60, c_630, c_624, c_960])).
% 4.83/1.89  tff(c_46, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.83/1.89  tff(c_981, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_967, c_46])).
% 4.83/1.89  tff(c_992, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_267, c_981])).
% 4.83/1.89  tff(c_993, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_620])).
% 4.83/1.89  tff(c_14, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.83/1.89  tff(c_92, plain, (![A_40, B_41]: (r1_tarski(A_40, B_41) | ~m1_subset_1(A_40, k1_zfmisc_1(B_41)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.83/1.89  tff(c_104, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(resolution, [status(thm)], [c_14, c_92])).
% 4.83/1.89  tff(c_1021, plain, (![A_5]: (r1_tarski('#skF_3', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_993, c_104])).
% 4.83/1.89  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.83/1.89  tff(c_1024, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_993, c_993, c_10])).
% 4.83/1.89  tff(c_103, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_56, c_92])).
% 4.83/1.89  tff(c_111, plain, (![B_45, A_46]: (B_45=A_46 | ~r1_tarski(B_45, A_46) | ~r1_tarski(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.83/1.89  tff(c_120, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_103, c_111])).
% 4.83/1.89  tff(c_300, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_120])).
% 4.83/1.89  tff(c_1090, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1024, c_300])).
% 4.83/1.89  tff(c_1100, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1021, c_1090])).
% 4.83/1.89  tff(c_1101, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_617])).
% 4.83/1.89  tff(c_1130, plain, (![A_5]: (r1_tarski('#skF_3', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_1101, c_104])).
% 4.83/1.89  tff(c_1133, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1101, c_1101, c_10])).
% 4.83/1.89  tff(c_1204, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1133, c_300])).
% 4.83/1.89  tff(c_1214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1130, c_1204])).
% 4.83/1.89  tff(c_1215, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_120])).
% 4.83/1.89  tff(c_1222, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1215, c_50])).
% 4.83/1.89  tff(c_1261, plain, (![A_165, B_166, C_167]: (k1_relset_1(A_165, B_166, C_167)=k1_relat_1(C_167) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.83/1.89  tff(c_1358, plain, (![C_178]: (k1_relset_1('#skF_2', '#skF_3', C_178)=k1_relat_1(C_178) | ~m1_subset_1(C_178, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1215, c_1261])).
% 4.83/1.89  tff(c_1373, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1222, c_1358])).
% 4.83/1.89  tff(c_1557, plain, (![B_203, A_204, C_205]: (k1_xboole_0=B_203 | k1_relset_1(A_204, B_203, C_205)=A_204 | ~v1_funct_2(C_205, A_204, B_203) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_204, B_203))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.83/1.89  tff(c_1560, plain, (![C_205]: (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', C_205)='#skF_2' | ~v1_funct_2(C_205, '#skF_2', '#skF_3') | ~m1_subset_1(C_205, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1215, c_1557])).
% 4.83/1.89  tff(c_1626, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1560])).
% 4.83/1.89  tff(c_8, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.83/1.89  tff(c_1236, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1215, c_8])).
% 4.83/1.89  tff(c_1330, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_1236])).
% 4.83/1.89  tff(c_1639, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1626, c_1330])).
% 4.83/1.89  tff(c_1789, plain, (![A_219]: (k2_zfmisc_1(A_219, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1626, c_1626, c_10])).
% 4.83/1.89  tff(c_1813, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1789, c_1215])).
% 4.83/1.89  tff(c_1835, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1639, c_1813])).
% 4.83/1.89  tff(c_1912, plain, (![C_226]: (k1_relset_1('#skF_2', '#skF_3', C_226)='#skF_2' | ~v1_funct_2(C_226, '#skF_2', '#skF_3') | ~m1_subset_1(C_226, k1_zfmisc_1('#skF_4')))), inference(splitRight, [status(thm)], [c_1560])).
% 4.83/1.89  tff(c_1915, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_1222, c_1912])).
% 4.83/1.89  tff(c_1929, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1373, c_1915])).
% 4.83/1.89  tff(c_1223, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1215, c_56])).
% 4.83/1.89  tff(c_1374, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1223, c_1358])).
% 4.83/1.89  tff(c_1918, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_1223, c_1912])).
% 4.83/1.89  tff(c_1932, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1374, c_1918])).
% 4.83/1.89  tff(c_1966, plain, (![A_227, B_228]: (r2_hidden('#skF_1'(A_227, B_228), k1_relat_1(A_227)) | B_228=A_227 | k1_relat_1(B_228)!=k1_relat_1(A_227) | ~v1_funct_1(B_228) | ~v1_relat_1(B_228) | ~v1_funct_1(A_227) | ~v1_relat_1(A_227))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.83/1.89  tff(c_1971, plain, (![B_228]: (r2_hidden('#skF_1'('#skF_4', B_228), '#skF_2') | B_228='#skF_4' | k1_relat_1(B_228)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_228) | ~v1_relat_1(B_228) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1932, c_1966])).
% 4.83/1.89  tff(c_2013, plain, (![B_231]: (r2_hidden('#skF_1'('#skF_4', B_231), '#skF_2') | B_231='#skF_4' | k1_relat_1(B_231)!='#skF_2' | ~v1_funct_1(B_231) | ~v1_relat_1(B_231))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_60, c_1932, c_1971])).
% 4.83/1.89  tff(c_2377, plain, (![B_252]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_252))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_252)) | B_252='#skF_4' | k1_relat_1(B_252)!='#skF_2' | ~v1_funct_1(B_252) | ~v1_relat_1(B_252))), inference(resolution, [status(thm)], [c_2013, c_48])).
% 4.83/1.89  tff(c_2384, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_5'='#skF_4' | k1_relat_1('#skF_5')!='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2377, c_22])).
% 4.83/1.89  tff(c_2391, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_172, c_54, c_1929, c_173, c_60, c_1932, c_1929, c_2384])).
% 4.83/1.89  tff(c_102, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_50, c_92])).
% 4.83/1.89  tff(c_121, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_102, c_111])).
% 4.83/1.89  tff(c_270, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_121])).
% 4.83/1.89  tff(c_1217, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1215, c_270])).
% 4.83/1.89  tff(c_2401, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2391, c_1217])).
% 4.83/1.89  tff(c_2414, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2401])).
% 4.83/1.89  tff(c_2416, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1236])).
% 4.83/1.89  tff(c_2430, plain, (![A_5]: (r1_tarski('#skF_4', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_2416, c_104])).
% 4.83/1.89  tff(c_2442, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2430, c_1217])).
% 4.83/1.89  tff(c_2443, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5'), inference(splitRight, [status(thm)], [c_121])).
% 4.83/1.89  tff(c_2449, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2443, c_50])).
% 4.83/1.89  tff(c_2538, plain, (![A_259, B_260, C_261]: (k1_relset_1(A_259, B_260, C_261)=k1_relat_1(C_261) | ~m1_subset_1(C_261, k1_zfmisc_1(k2_zfmisc_1(A_259, B_260))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.83/1.89  tff(c_2616, plain, (![C_276]: (k1_relset_1('#skF_2', '#skF_3', C_276)=k1_relat_1(C_276) | ~m1_subset_1(C_276, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_2443, c_2538])).
% 4.83/1.89  tff(c_2632, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2449, c_2616])).
% 4.83/1.89  tff(c_2805, plain, (![B_301, C_302, A_303]: (k1_xboole_0=B_301 | v1_funct_2(C_302, A_303, B_301) | k1_relset_1(A_303, B_301, C_302)!=A_303 | ~m1_subset_1(C_302, k1_zfmisc_1(k2_zfmisc_1(A_303, B_301))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.83/1.89  tff(c_2808, plain, (![C_302]: (k1_xboole_0='#skF_3' | v1_funct_2(C_302, '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', C_302)!='#skF_2' | ~m1_subset_1(C_302, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_2443, c_2805])).
% 4.83/1.89  tff(c_2884, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2808])).
% 4.83/1.89  tff(c_2463, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_2443, c_8])).
% 4.83/1.89  tff(c_2565, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_2463])).
% 4.83/1.89  tff(c_2901, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2884, c_2565])).
% 4.83/1.89  tff(c_2914, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2884, c_2884, c_10])).
% 4.83/1.89  tff(c_3047, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2914, c_2443])).
% 4.83/1.89  tff(c_3049, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2901, c_3047])).
% 4.83/1.89  tff(c_3051, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_2808])).
% 4.83/1.89  tff(c_2724, plain, (![B_287, A_288, C_289]: (k1_xboole_0=B_287 | k1_relset_1(A_288, B_287, C_289)=A_288 | ~v1_funct_2(C_289, A_288, B_287) | ~m1_subset_1(C_289, k1_zfmisc_1(k2_zfmisc_1(A_288, B_287))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.83/1.89  tff(c_2727, plain, (![C_289]: (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', C_289)='#skF_2' | ~v1_funct_2(C_289, '#skF_2', '#skF_3') | ~m1_subset_1(C_289, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_2443, c_2724])).
% 4.83/1.89  tff(c_3052, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2727])).
% 4.83/1.89  tff(c_3053, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3051, c_3052])).
% 4.83/1.89  tff(c_3056, plain, (![C_317]: (k1_relset_1('#skF_2', '#skF_3', C_317)='#skF_2' | ~v1_funct_2(C_317, '#skF_2', '#skF_3') | ~m1_subset_1(C_317, k1_zfmisc_1('#skF_5')))), inference(splitRight, [status(thm)], [c_2727])).
% 4.83/1.89  tff(c_3062, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_2449, c_3056])).
% 4.83/1.89  tff(c_3076, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2632, c_3062])).
% 4.83/1.89  tff(c_2450, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2443, c_56])).
% 4.83/1.89  tff(c_2631, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2450, c_2616])).
% 4.83/1.89  tff(c_3059, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_2450, c_3056])).
% 4.83/1.89  tff(c_3073, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2631, c_3059])).
% 4.83/1.89  tff(c_3189, plain, (![A_324, B_325]: (r2_hidden('#skF_1'(A_324, B_325), k1_relat_1(A_324)) | B_325=A_324 | k1_relat_1(B_325)!=k1_relat_1(A_324) | ~v1_funct_1(B_325) | ~v1_relat_1(B_325) | ~v1_funct_1(A_324) | ~v1_relat_1(A_324))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.83/1.89  tff(c_3197, plain, (![B_325]: (r2_hidden('#skF_1'('#skF_4', B_325), '#skF_2') | B_325='#skF_4' | k1_relat_1(B_325)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_325) | ~v1_relat_1(B_325) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3073, c_3189])).
% 4.83/1.89  tff(c_3222, plain, (![B_327]: (r2_hidden('#skF_1'('#skF_4', B_327), '#skF_2') | B_327='#skF_4' | k1_relat_1(B_327)!='#skF_2' | ~v1_funct_1(B_327) | ~v1_relat_1(B_327))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_60, c_3073, c_3197])).
% 4.83/1.89  tff(c_3229, plain, (![B_327]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_327))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_327)) | B_327='#skF_4' | k1_relat_1(B_327)!='#skF_2' | ~v1_funct_1(B_327) | ~v1_relat_1(B_327))), inference(resolution, [status(thm)], [c_3222, c_48])).
% 4.83/1.89  tff(c_3373, plain, (![B_341, A_342]: (k1_funct_1(B_341, '#skF_1'(A_342, B_341))!=k1_funct_1(A_342, '#skF_1'(A_342, B_341)) | B_341=A_342 | k1_relat_1(B_341)!=k1_relat_1(A_342) | ~v1_funct_1(B_341) | ~v1_relat_1(B_341) | ~v1_funct_1(A_342) | ~v1_relat_1(A_342))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.83/1.89  tff(c_3377, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_5'='#skF_4' | k1_relat_1('#skF_5')!='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3229, c_3373])).
% 4.83/1.89  tff(c_3380, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_172, c_54, c_3076, c_173, c_60, c_3076, c_3073, c_3377])).
% 4.83/1.89  tff(c_2447, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2443, c_103])).
% 4.83/1.89  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.83/1.89  tff(c_2470, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_2447, c_2])).
% 4.83/1.89  tff(c_2496, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_2470])).
% 4.83/1.89  tff(c_3397, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3380, c_2496])).
% 4.83/1.89  tff(c_3413, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3397])).
% 4.83/1.89  tff(c_3415, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_2463])).
% 4.83/1.89  tff(c_3425, plain, (![A_5]: (r1_tarski('#skF_5', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_3415, c_104])).
% 4.83/1.89  tff(c_3437, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3425, c_2496])).
% 4.83/1.89  tff(c_3438, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_2470])).
% 4.83/1.89  tff(c_3450, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3438, c_46])).
% 4.83/1.89  tff(c_3458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_267, c_3450])).
% 4.83/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.83/1.89  
% 4.83/1.89  Inference rules
% 4.83/1.89  ----------------------
% 4.83/1.89  #Ref     : 3
% 4.83/1.89  #Sup     : 658
% 4.83/1.89  #Fact    : 0
% 4.83/1.89  #Define  : 0
% 4.83/1.89  #Split   : 18
% 4.83/1.89  #Chain   : 0
% 4.83/1.89  #Close   : 0
% 4.83/1.89  
% 4.83/1.89  Ordering : KBO
% 4.83/1.89  
% 4.83/1.89  Simplification rules
% 4.83/1.89  ----------------------
% 4.83/1.89  #Subsume      : 100
% 4.83/1.89  #Demod        : 901
% 4.83/1.89  #Tautology    : 336
% 4.83/1.89  #SimpNegUnit  : 45
% 4.83/1.89  #BackRed      : 258
% 4.83/1.89  
% 4.83/1.89  #Partial instantiations: 0
% 4.83/1.89  #Strategies tried      : 1
% 4.83/1.89  
% 4.83/1.89  Timing (in seconds)
% 4.83/1.89  ----------------------
% 4.83/1.89  Preprocessing        : 0.33
% 4.83/1.89  Parsing              : 0.18
% 4.83/1.89  CNF conversion       : 0.02
% 4.83/1.89  Main loop            : 0.78
% 4.83/1.89  Inferencing          : 0.25
% 4.83/1.89  Reduction            : 0.27
% 4.83/1.89  Demodulation         : 0.19
% 4.83/1.89  BG Simplification    : 0.03
% 4.83/1.89  Subsumption          : 0.17
% 4.83/1.89  Abstraction          : 0.04
% 4.83/1.89  MUC search           : 0.00
% 4.83/1.89  Cooper               : 0.00
% 4.83/1.89  Total                : 1.16
% 4.83/1.90  Index Insertion      : 0.00
% 4.83/1.90  Index Deletion       : 0.00
% 4.83/1.90  Index Matching       : 0.00
% 4.83/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
