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
% DateTime   : Thu Dec  3 10:11:35 EST 2020

% Result     : Theorem 4.14s
% Output     : CNFRefutation 4.14s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 287 expanded)
%              Number of leaves         :   37 ( 114 expanded)
%              Depth                    :   11
%              Number of atoms          :  168 ( 853 expanded)
%              Number of equality atoms :   54 ( 203 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_subset_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

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

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_152,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_103,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_113,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_131,axiom,(
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

tff(f_86,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_48,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

tff(c_66,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_292,plain,(
    ! [C_84,B_85,A_86] :
      ( v1_xboole_0(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(B_85,A_86)))
      | ~ v1_xboole_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_313,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_292])).

tff(c_320,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_313])).

tff(c_60,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_962,plain,(
    ! [A_162,B_163,C_164,D_165] :
      ( r2_relset_1(A_162,B_163,C_164,C_164)
      | ~ m1_subset_1(D_165,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163)))
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1010,plain,(
    ! [C_170] :
      ( r2_relset_1('#skF_3','#skF_4',C_170,C_170)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_66,c_962])).

tff(c_1022,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_1010])).

tff(c_112,plain,(
    ! [C_56,A_57,B_58] :
      ( v1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_131,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_112])).

tff(c_70,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_68,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_554,plain,(
    ! [A_125,B_126,C_127] :
      ( k1_relset_1(A_125,B_126,C_127) = k1_relat_1(C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_575,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_554])).

tff(c_912,plain,(
    ! [B_159,A_160,C_161] :
      ( k1_xboole_0 = B_159
      | k1_relset_1(A_160,B_159,C_161) = A_160
      | ~ v1_funct_2(C_161,A_160,B_159)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_160,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_915,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_912])).

tff(c_935,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_575,c_915])).

tff(c_944,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_935])).

tff(c_132,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_112])).

tff(c_64,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_62,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_576,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_554])).

tff(c_918,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_912])).

tff(c_938,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_576,c_918])).

tff(c_951,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_938])).

tff(c_1196,plain,(
    ! [A_189,B_190] :
      ( r2_hidden('#skF_2'(A_189,B_190),k1_relat_1(A_189))
      | B_190 = A_189
      | k1_relat_1(B_190) != k1_relat_1(A_189)
      | ~ v1_funct_1(B_190)
      | ~ v1_relat_1(B_190)
      | ~ v1_funct_1(A_189)
      | ~ v1_relat_1(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1214,plain,(
    ! [B_190] :
      ( r2_hidden('#skF_2'('#skF_6',B_190),'#skF_3')
      | B_190 = '#skF_6'
      | k1_relat_1(B_190) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_190)
      | ~ v1_relat_1(B_190)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_951,c_1196])).

tff(c_1305,plain,(
    ! [B_196] :
      ( r2_hidden('#skF_2'('#skF_6',B_196),'#skF_3')
      | B_196 = '#skF_6'
      | k1_relat_1(B_196) != '#skF_3'
      | ~ v1_funct_1(B_196)
      | ~ v1_relat_1(B_196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_64,c_951,c_1214])).

tff(c_58,plain,(
    ! [E_46] :
      ( k1_funct_1('#skF_5',E_46) = k1_funct_1('#skF_6',E_46)
      | ~ r2_hidden(E_46,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1493,plain,(
    ! [B_215] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_6',B_215)) = k1_funct_1('#skF_6','#skF_2'('#skF_6',B_215))
      | B_215 = '#skF_6'
      | k1_relat_1(B_215) != '#skF_3'
      | ~ v1_funct_1(B_215)
      | ~ v1_relat_1(B_215) ) ),
    inference(resolution,[status(thm)],[c_1305,c_58])).

tff(c_28,plain,(
    ! [B_20,A_16] :
      ( k1_funct_1(B_20,'#skF_2'(A_16,B_20)) != k1_funct_1(A_16,'#skF_2'(A_16,B_20))
      | B_20 = A_16
      | k1_relat_1(B_20) != k1_relat_1(A_16)
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1500,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != '#skF_3'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1493,c_28])).

tff(c_1507,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_70,c_944,c_132,c_64,c_951,c_944,c_1500])).

tff(c_56,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1520,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1507,c_56])).

tff(c_1533,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1022,c_1520])).

tff(c_1534,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_938])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1565,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1534,c_2])).

tff(c_1567,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_320,c_1565])).

tff(c_1568,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_935])).

tff(c_1599,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1568,c_2])).

tff(c_1601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_320,c_1599])).

tff(c_1603,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_313])).

tff(c_102,plain,(
    ! [B_53,A_54] :
      ( ~ v1_xboole_0(B_53)
      | B_53 = A_54
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_105,plain,(
    ! [A_54] :
      ( k1_xboole_0 = A_54
      | ~ v1_xboole_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_2,c_102])).

tff(c_1616,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1603,c_105])).

tff(c_1602,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_313])).

tff(c_1609,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1602,c_105])).

tff(c_1653,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1616,c_1609])).

tff(c_12,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1643,plain,(
    ! [A_5] : m1_subset_1('#skF_5',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1609,c_12])).

tff(c_1831,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1653,c_1643])).

tff(c_16,plain,(
    ! [A_6] : m1_subset_1('#skF_1'(A_6),k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2188,plain,(
    ! [A_276,B_277,C_278,D_279] :
      ( r2_relset_1(A_276,B_277,C_278,C_278)
      | ~ m1_subset_1(D_279,k1_zfmisc_1(k2_zfmisc_1(A_276,B_277)))
      | ~ m1_subset_1(C_278,k1_zfmisc_1(k2_zfmisc_1(A_276,B_277))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2329,plain,(
    ! [A_299,B_300,C_301] :
      ( r2_relset_1(A_299,B_300,C_301,C_301)
      | ~ m1_subset_1(C_301,k1_zfmisc_1(k2_zfmisc_1(A_299,B_300))) ) ),
    inference(resolution,[status(thm)],[c_16,c_2188])).

tff(c_2340,plain,(
    ! [A_299,B_300] : r2_relset_1(A_299,B_300,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_1831,c_2329])).

tff(c_314,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_292])).

tff(c_1699,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1603,c_314])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1739,plain,(
    ! [A_226] :
      ( A_226 = '#skF_4'
      | ~ v1_xboole_0(A_226) ) ),
    inference(resolution,[status(thm)],[c_1603,c_4])).

tff(c_1746,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1699,c_1739])).

tff(c_1665,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1653,c_56])).

tff(c_1828,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1746,c_1665])).

tff(c_2368,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2340,c_1828])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:35:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.14/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.14/1.72  
% 4.14/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.14/1.72  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_subset_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 4.14/1.72  
% 4.14/1.72  %Foreground sorts:
% 4.14/1.72  
% 4.14/1.72  
% 4.14/1.72  %Background operators:
% 4.14/1.72  
% 4.14/1.72  
% 4.14/1.72  %Foreground operators:
% 4.14/1.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.14/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.14/1.72  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.14/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.14/1.72  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.14/1.72  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.14/1.72  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.14/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.14/1.72  tff('#skF_5', type, '#skF_5': $i).
% 4.14/1.72  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.14/1.72  tff('#skF_6', type, '#skF_6': $i).
% 4.14/1.72  tff('#skF_3', type, '#skF_3': $i).
% 4.14/1.72  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.14/1.72  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.14/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.14/1.72  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.14/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.14/1.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.14/1.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.14/1.72  tff('#skF_4', type, '#skF_4': $i).
% 4.14/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.14/1.72  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.14/1.72  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.14/1.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.14/1.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.14/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.14/1.72  
% 4.14/1.74  tff(f_152, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 4.14/1.74  tff(f_103, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 4.14/1.74  tff(f_113, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 4.14/1.74  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.14/1.74  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.14/1.74  tff(f_131, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.14/1.74  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 4.14/1.74  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.14/1.74  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 4.14/1.74  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.14/1.74  tff(f_48, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 4.14/1.74  tff(c_66, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.14/1.74  tff(c_292, plain, (![C_84, B_85, A_86]: (v1_xboole_0(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(B_85, A_86))) | ~v1_xboole_0(A_86))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.14/1.74  tff(c_313, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_66, c_292])).
% 4.14/1.74  tff(c_320, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_313])).
% 4.14/1.74  tff(c_60, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.14/1.74  tff(c_962, plain, (![A_162, B_163, C_164, D_165]: (r2_relset_1(A_162, B_163, C_164, C_164) | ~m1_subset_1(D_165, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.14/1.74  tff(c_1010, plain, (![C_170]: (r2_relset_1('#skF_3', '#skF_4', C_170, C_170) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))))), inference(resolution, [status(thm)], [c_66, c_962])).
% 4.14/1.74  tff(c_1022, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_60, c_1010])).
% 4.14/1.74  tff(c_112, plain, (![C_56, A_57, B_58]: (v1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.14/1.74  tff(c_131, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_112])).
% 4.14/1.74  tff(c_70, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.14/1.74  tff(c_68, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.14/1.74  tff(c_554, plain, (![A_125, B_126, C_127]: (k1_relset_1(A_125, B_126, C_127)=k1_relat_1(C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.14/1.74  tff(c_575, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_554])).
% 4.14/1.74  tff(c_912, plain, (![B_159, A_160, C_161]: (k1_xboole_0=B_159 | k1_relset_1(A_160, B_159, C_161)=A_160 | ~v1_funct_2(C_161, A_160, B_159) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_160, B_159))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.14/1.74  tff(c_915, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_66, c_912])).
% 4.14/1.74  tff(c_935, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_575, c_915])).
% 4.14/1.74  tff(c_944, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_935])).
% 4.14/1.74  tff(c_132, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_112])).
% 4.14/1.74  tff(c_64, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.14/1.74  tff(c_62, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.14/1.74  tff(c_576, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_554])).
% 4.14/1.74  tff(c_918, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_60, c_912])).
% 4.14/1.74  tff(c_938, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_576, c_918])).
% 4.14/1.74  tff(c_951, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_938])).
% 4.14/1.74  tff(c_1196, plain, (![A_189, B_190]: (r2_hidden('#skF_2'(A_189, B_190), k1_relat_1(A_189)) | B_190=A_189 | k1_relat_1(B_190)!=k1_relat_1(A_189) | ~v1_funct_1(B_190) | ~v1_relat_1(B_190) | ~v1_funct_1(A_189) | ~v1_relat_1(A_189))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.14/1.74  tff(c_1214, plain, (![B_190]: (r2_hidden('#skF_2'('#skF_6', B_190), '#skF_3') | B_190='#skF_6' | k1_relat_1(B_190)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_190) | ~v1_relat_1(B_190) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_951, c_1196])).
% 4.14/1.74  tff(c_1305, plain, (![B_196]: (r2_hidden('#skF_2'('#skF_6', B_196), '#skF_3') | B_196='#skF_6' | k1_relat_1(B_196)!='#skF_3' | ~v1_funct_1(B_196) | ~v1_relat_1(B_196))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_64, c_951, c_1214])).
% 4.14/1.74  tff(c_58, plain, (![E_46]: (k1_funct_1('#skF_5', E_46)=k1_funct_1('#skF_6', E_46) | ~r2_hidden(E_46, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.14/1.74  tff(c_1493, plain, (![B_215]: (k1_funct_1('#skF_5', '#skF_2'('#skF_6', B_215))=k1_funct_1('#skF_6', '#skF_2'('#skF_6', B_215)) | B_215='#skF_6' | k1_relat_1(B_215)!='#skF_3' | ~v1_funct_1(B_215) | ~v1_relat_1(B_215))), inference(resolution, [status(thm)], [c_1305, c_58])).
% 4.14/1.74  tff(c_28, plain, (![B_20, A_16]: (k1_funct_1(B_20, '#skF_2'(A_16, B_20))!=k1_funct_1(A_16, '#skF_2'(A_16, B_20)) | B_20=A_16 | k1_relat_1(B_20)!=k1_relat_1(A_16) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.14/1.74  tff(c_1500, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!='#skF_3' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1493, c_28])).
% 4.14/1.74  tff(c_1507, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_131, c_70, c_944, c_132, c_64, c_951, c_944, c_1500])).
% 4.14/1.74  tff(c_56, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.14/1.74  tff(c_1520, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1507, c_56])).
% 4.14/1.74  tff(c_1533, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1022, c_1520])).
% 4.14/1.74  tff(c_1534, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_938])).
% 4.14/1.74  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.14/1.74  tff(c_1565, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1534, c_2])).
% 4.14/1.74  tff(c_1567, plain, $false, inference(negUnitSimplification, [status(thm)], [c_320, c_1565])).
% 4.14/1.74  tff(c_1568, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_935])).
% 4.14/1.74  tff(c_1599, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1568, c_2])).
% 4.14/1.74  tff(c_1601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_320, c_1599])).
% 4.14/1.74  tff(c_1603, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_313])).
% 4.14/1.74  tff(c_102, plain, (![B_53, A_54]: (~v1_xboole_0(B_53) | B_53=A_54 | ~v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.14/1.74  tff(c_105, plain, (![A_54]: (k1_xboole_0=A_54 | ~v1_xboole_0(A_54))), inference(resolution, [status(thm)], [c_2, c_102])).
% 4.14/1.74  tff(c_1616, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1603, c_105])).
% 4.14/1.74  tff(c_1602, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_313])).
% 4.14/1.74  tff(c_1609, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1602, c_105])).
% 4.14/1.74  tff(c_1653, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1616, c_1609])).
% 4.14/1.74  tff(c_12, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.14/1.74  tff(c_1643, plain, (![A_5]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_1609, c_12])).
% 4.14/1.74  tff(c_1831, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_1653, c_1643])).
% 4.14/1.74  tff(c_16, plain, (![A_6]: (m1_subset_1('#skF_1'(A_6), k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.14/1.74  tff(c_2188, plain, (![A_276, B_277, C_278, D_279]: (r2_relset_1(A_276, B_277, C_278, C_278) | ~m1_subset_1(D_279, k1_zfmisc_1(k2_zfmisc_1(A_276, B_277))) | ~m1_subset_1(C_278, k1_zfmisc_1(k2_zfmisc_1(A_276, B_277))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.14/1.74  tff(c_2329, plain, (![A_299, B_300, C_301]: (r2_relset_1(A_299, B_300, C_301, C_301) | ~m1_subset_1(C_301, k1_zfmisc_1(k2_zfmisc_1(A_299, B_300))))), inference(resolution, [status(thm)], [c_16, c_2188])).
% 4.14/1.74  tff(c_2340, plain, (![A_299, B_300]: (r2_relset_1(A_299, B_300, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_1831, c_2329])).
% 4.14/1.74  tff(c_314, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_60, c_292])).
% 4.14/1.74  tff(c_1699, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1603, c_314])).
% 4.14/1.74  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.14/1.74  tff(c_1739, plain, (![A_226]: (A_226='#skF_4' | ~v1_xboole_0(A_226))), inference(resolution, [status(thm)], [c_1603, c_4])).
% 4.14/1.74  tff(c_1746, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_1699, c_1739])).
% 4.14/1.74  tff(c_1665, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1653, c_56])).
% 4.14/1.74  tff(c_1828, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1746, c_1665])).
% 4.14/1.74  tff(c_2368, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2340, c_1828])).
% 4.14/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.14/1.74  
% 4.14/1.74  Inference rules
% 4.14/1.74  ----------------------
% 4.14/1.74  #Ref     : 1
% 4.14/1.74  #Sup     : 495
% 4.14/1.74  #Fact    : 0
% 4.14/1.74  #Define  : 0
% 4.14/1.74  #Split   : 6
% 4.14/1.74  #Chain   : 0
% 4.14/1.74  #Close   : 0
% 4.14/1.74  
% 4.14/1.74  Ordering : KBO
% 4.14/1.74  
% 4.14/1.74  Simplification rules
% 4.14/1.74  ----------------------
% 4.14/1.74  #Subsume      : 147
% 4.14/1.74  #Demod        : 602
% 4.14/1.74  #Tautology    : 259
% 4.14/1.74  #SimpNegUnit  : 8
% 4.14/1.74  #BackRed      : 121
% 4.14/1.74  
% 4.14/1.74  #Partial instantiations: 0
% 4.14/1.74  #Strategies tried      : 1
% 4.14/1.74  
% 4.14/1.74  Timing (in seconds)
% 4.14/1.74  ----------------------
% 4.14/1.74  Preprocessing        : 0.35
% 4.14/1.74  Parsing              : 0.19
% 4.14/1.74  CNF conversion       : 0.02
% 4.14/1.74  Main loop            : 0.61
% 4.14/1.74  Inferencing          : 0.20
% 4.14/1.74  Reduction            : 0.22
% 4.14/1.74  Demodulation         : 0.16
% 4.14/1.74  BG Simplification    : 0.03
% 4.14/1.74  Subsumption          : 0.11
% 4.14/1.74  Abstraction          : 0.03
% 4.14/1.74  MUC search           : 0.00
% 4.14/1.74  Cooper               : 0.00
% 4.14/1.74  Total                : 1.00
% 4.14/1.74  Index Insertion      : 0.00
% 4.14/1.74  Index Deletion       : 0.00
% 4.14/1.74  Index Matching       : 0.00
% 4.14/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
