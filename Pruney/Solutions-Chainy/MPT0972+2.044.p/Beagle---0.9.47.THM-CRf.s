%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:41 EST 2020

% Result     : Theorem 4.24s
% Output     : CNFRefutation 4.37s
% Verified   : 
% Statistics : Number of formulae       :  149 (1202 expanded)
%              Number of leaves         :   37 ( 411 expanded)
%              Depth                    :   13
%              Number of atoms          :  246 (3110 expanded)
%              Number of equality atoms :   88 ( 642 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_133,negated_conjecture,(
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

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_64,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_112,axiom,(
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

tff(f_82,axiom,(
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
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_66,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_657,plain,(
    ! [A_117,B_118,D_119] :
      ( r2_relset_1(A_117,B_118,D_119,D_119)
      | ~ m1_subset_1(D_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_671,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_657])).

tff(c_32,plain,(
    ! [A_19,B_20] : v1_relat_1(k2_zfmisc_1(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_60,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_142,plain,(
    ! [B_57,A_58] :
      ( v1_relat_1(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58))
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_148,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_60,c_142])).

tff(c_155,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_148])).

tff(c_64,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_62,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_699,plain,(
    ! [A_132,B_133,C_134] :
      ( k1_relset_1(A_132,B_133,C_134) = k1_relat_1(C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_717,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_699])).

tff(c_787,plain,(
    ! [B_150,A_151,C_152] :
      ( k1_xboole_0 = B_150
      | k1_relset_1(A_151,B_150,C_152) = A_151
      | ~ v1_funct_2(C_152,A_151,B_150)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_151,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_794,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_787])).

tff(c_807,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_717,c_794])).

tff(c_812,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_807])).

tff(c_151,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_66,c_142])).

tff(c_158,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_151])).

tff(c_70,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_68,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_718,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_699])).

tff(c_797,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_787])).

tff(c_810,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_718,c_797])).

tff(c_818,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_810])).

tff(c_1097,plain,(
    ! [A_192,B_193] :
      ( r2_hidden('#skF_3'(A_192,B_193),k1_relat_1(A_192))
      | B_193 = A_192
      | k1_relat_1(B_193) != k1_relat_1(A_192)
      | ~ v1_funct_1(B_193)
      | ~ v1_relat_1(B_193)
      | ~ v1_funct_1(A_192)
      | ~ v1_relat_1(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1105,plain,(
    ! [B_193] :
      ( r2_hidden('#skF_3'('#skF_6',B_193),'#skF_4')
      | B_193 = '#skF_6'
      | k1_relat_1(B_193) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_193)
      | ~ v1_relat_1(B_193)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_818,c_1097])).

tff(c_1641,plain,(
    ! [B_244] :
      ( r2_hidden('#skF_3'('#skF_6',B_244),'#skF_4')
      | B_244 = '#skF_6'
      | k1_relat_1(B_244) != '#skF_4'
      | ~ v1_funct_1(B_244)
      | ~ v1_relat_1(B_244) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_70,c_818,c_1105])).

tff(c_58,plain,(
    ! [E_41] :
      ( k1_funct_1('#skF_7',E_41) = k1_funct_1('#skF_6',E_41)
      | ~ r2_hidden(E_41,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1761,plain,(
    ! [B_248] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_6',B_248)) = k1_funct_1('#skF_6','#skF_3'('#skF_6',B_248))
      | B_248 = '#skF_6'
      | k1_relat_1(B_248) != '#skF_4'
      | ~ v1_funct_1(B_248)
      | ~ v1_relat_1(B_248) ) ),
    inference(resolution,[status(thm)],[c_1641,c_58])).

tff(c_34,plain,(
    ! [B_25,A_21] :
      ( k1_funct_1(B_25,'#skF_3'(A_21,B_25)) != k1_funct_1(A_21,'#skF_3'(A_21,B_25))
      | B_25 = A_21
      | k1_relat_1(B_25) != k1_relat_1(A_21)
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1768,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_7') != '#skF_4'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1761,c_34])).

tff(c_1775,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_64,c_812,c_158,c_70,c_812,c_818,c_1768])).

tff(c_56,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1800,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1775,c_56])).

tff(c_1811,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_671,c_1800])).

tff(c_1812,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_810])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1834,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1812,c_12])).

tff(c_22,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1833,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1812,c_1812,c_22])).

tff(c_112,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(A_52,B_53)
      | ~ m1_subset_1(A_52,k1_zfmisc_1(B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_124,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_66,c_112])).

tff(c_177,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_2'(A_63,B_64),A_63)
      | r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_192,plain,(
    ! [A_63,B_64] :
      ( ~ v1_xboole_0(A_63)
      | r1_tarski(A_63,B_64) ) ),
    inference(resolution,[status(thm)],[c_177,c_2])).

tff(c_492,plain,(
    ! [B_99,A_100] :
      ( B_99 = A_100
      | ~ r1_tarski(B_99,A_100)
      | ~ r1_tarski(A_100,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_532,plain,(
    ! [B_103,A_104] :
      ( B_103 = A_104
      | ~ r1_tarski(B_103,A_104)
      | ~ v1_xboole_0(A_104) ) ),
    inference(resolution,[status(thm)],[c_192,c_492])).

tff(c_546,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6'
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_124,c_532])).

tff(c_564,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_546])).

tff(c_1886,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1833,c_564])).

tff(c_1893,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1834,c_1886])).

tff(c_1894,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_807])).

tff(c_1917,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1894,c_12])).

tff(c_1916,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1894,c_1894,c_22])).

tff(c_1974,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1916,c_564])).

tff(c_1981,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1917,c_1974])).

tff(c_1982,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_546])).

tff(c_2074,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1982,c_66])).

tff(c_1983,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_546])).

tff(c_2013,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1982,c_1983])).

tff(c_123,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_60,c_112])).

tff(c_547,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = '#skF_7'
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_123,c_532])).

tff(c_1984,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_547])).

tff(c_2068,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2013,c_1982,c_1984])).

tff(c_2070,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_547])).

tff(c_2110,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1982,c_2070])).

tff(c_550,plain,(
    ! [B_105,A_106] :
      ( B_105 = A_106
      | ~ v1_xboole_0(B_105)
      | ~ v1_xboole_0(A_106) ) ),
    inference(resolution,[status(thm)],[c_192,c_532])).

tff(c_553,plain,(
    ! [A_106] :
      ( k1_xboole_0 = A_106
      | ~ v1_xboole_0(A_106) ) ),
    inference(resolution,[status(thm)],[c_12,c_550])).

tff(c_2119,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2110,c_553])).

tff(c_2127,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2119,c_2119,c_22])).

tff(c_2255,plain,(
    ! [A_267,B_268,D_269] :
      ( r2_relset_1(A_267,B_268,D_269,D_269)
      | ~ m1_subset_1(D_269,k1_zfmisc_1(k2_zfmisc_1(A_267,B_268))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2295,plain,(
    ! [A_277,D_278] :
      ( r2_relset_1(A_277,'#skF_6',D_278,D_278)
      | ~ m1_subset_1(D_278,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2127,c_2255])).

tff(c_2301,plain,(
    ! [A_277] : r2_relset_1(A_277,'#skF_6','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_2074,c_2295])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_125,plain,(
    ! [E_54] :
      ( k1_funct_1('#skF_7',E_54) = k1_funct_1('#skF_6',E_54)
      | ~ r2_hidden(E_54,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_130,plain,
    ( k1_funct_1('#skF_7','#skF_1'('#skF_4')) = k1_funct_1('#skF_6','#skF_1'('#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_125])).

tff(c_198,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_218,plain,(
    ! [B_68,A_69] :
      ( B_68 = A_69
      | ~ r1_tarski(B_68,A_69)
      | ~ r1_tarski(A_69,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_234,plain,(
    ! [B_70,A_71] :
      ( B_70 = A_71
      | ~ r1_tarski(B_70,A_71)
      | ~ v1_xboole_0(A_71) ) ),
    inference(resolution,[status(thm)],[c_192,c_218])).

tff(c_252,plain,(
    ! [B_72,A_73] :
      ( B_72 = A_73
      | ~ v1_xboole_0(B_72)
      | ~ v1_xboole_0(A_73) ) ),
    inference(resolution,[status(thm)],[c_192,c_234])).

tff(c_259,plain,(
    ! [A_74] :
      ( k1_xboole_0 = A_74
      | ~ v1_xboole_0(A_74) ) ),
    inference(resolution,[status(thm)],[c_12,c_252])).

tff(c_266,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_198,c_259])).

tff(c_24,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_281,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_4',B_13) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_266,c_24])).

tff(c_296,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_124])).

tff(c_227,plain,(
    ! [B_64,A_63] :
      ( B_64 = A_63
      | ~ r1_tarski(B_64,A_63)
      | ~ v1_xboole_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_192,c_218])).

tff(c_312,plain,
    ( '#skF_6' = '#skF_4'
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_296,c_227])).

tff(c_320,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_312])).

tff(c_299,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_66])).

tff(c_383,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_299])).

tff(c_455,plain,(
    ! [A_89,B_90,D_91] :
      ( r2_relset_1(A_89,B_90,D_91,D_91)
      | ~ m1_subset_1(D_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_479,plain,(
    ! [B_97,D_98] :
      ( r2_relset_1('#skF_4',B_97,D_98,D_98)
      | ~ m1_subset_1(D_98,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_455])).

tff(c_485,plain,(
    ! [B_97] : r2_relset_1('#skF_4',B_97,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_383,c_479])).

tff(c_297,plain,(
    r1_tarski('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_123])).

tff(c_347,plain,
    ( '#skF_7' = '#skF_4'
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_297,c_227])).

tff(c_355,plain,(
    '#skF_7' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_347])).

tff(c_336,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_4','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_56])).

tff(c_422,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_336])).

tff(c_489,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_422])).

tff(c_491,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_20,plain,(
    ! [B_13,A_12] :
      ( k1_xboole_0 = B_13
      | k1_xboole_0 = A_12
      | k2_zfmisc_1(A_12,B_13) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2079,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 != '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_1982,c_20])).

tff(c_2215,plain,
    ( '#skF_5' = '#skF_6'
    | '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2119,c_2119,c_2119,c_2079])).

tff(c_2216,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2215])).

tff(c_2225,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2216,c_2110])).

tff(c_2231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_491,c_2225])).

tff(c_2232,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2215])).

tff(c_2069,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_547])).

tff(c_2135,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1982,c_2069])).

tff(c_2142,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2135,c_56])).

tff(c_2236,plain,(
    ~ r2_relset_1('#skF_4','#skF_6','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2232,c_2142])).

tff(c_2305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2301,c_2236])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:26:29 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.24/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.24/1.79  
% 4.24/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.24/1.79  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 4.24/1.79  
% 4.24/1.79  %Foreground sorts:
% 4.24/1.79  
% 4.24/1.79  
% 4.24/1.79  %Background operators:
% 4.24/1.79  
% 4.24/1.79  
% 4.24/1.79  %Foreground operators:
% 4.24/1.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.24/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.24/1.79  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.24/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.24/1.79  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.24/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.24/1.79  tff('#skF_7', type, '#skF_7': $i).
% 4.24/1.79  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.24/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.24/1.79  tff('#skF_5', type, '#skF_5': $i).
% 4.24/1.79  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.24/1.79  tff('#skF_6', type, '#skF_6': $i).
% 4.24/1.79  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.24/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.24/1.79  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.24/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.24/1.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.24/1.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.24/1.79  tff('#skF_4', type, '#skF_4': $i).
% 4.24/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.24/1.79  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.24/1.79  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.24/1.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.24/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.24/1.79  
% 4.37/1.81  tff(f_133, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_2)).
% 4.37/1.81  tff(f_94, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.37/1.81  tff(f_64, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.37/1.81  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.37/1.81  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.37/1.81  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.37/1.81  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 4.37/1.81  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.37/1.81  tff(f_51, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.37/1.81  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.37/1.81  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.37/1.81  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.37/1.81  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.37/1.81  tff(c_66, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.37/1.81  tff(c_657, plain, (![A_117, B_118, D_119]: (r2_relset_1(A_117, B_118, D_119, D_119) | ~m1_subset_1(D_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.37/1.81  tff(c_671, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_66, c_657])).
% 4.37/1.81  tff(c_32, plain, (![A_19, B_20]: (v1_relat_1(k2_zfmisc_1(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.37/1.81  tff(c_60, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.37/1.81  tff(c_142, plain, (![B_57, A_58]: (v1_relat_1(B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.37/1.81  tff(c_148, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_60, c_142])).
% 4.37/1.81  tff(c_155, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_148])).
% 4.37/1.81  tff(c_64, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.37/1.81  tff(c_62, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.37/1.81  tff(c_699, plain, (![A_132, B_133, C_134]: (k1_relset_1(A_132, B_133, C_134)=k1_relat_1(C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.37/1.81  tff(c_717, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_60, c_699])).
% 4.37/1.81  tff(c_787, plain, (![B_150, A_151, C_152]: (k1_xboole_0=B_150 | k1_relset_1(A_151, B_150, C_152)=A_151 | ~v1_funct_2(C_152, A_151, B_150) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_151, B_150))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.37/1.81  tff(c_794, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_60, c_787])).
% 4.37/1.81  tff(c_807, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_717, c_794])).
% 4.37/1.81  tff(c_812, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_807])).
% 4.37/1.81  tff(c_151, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_66, c_142])).
% 4.37/1.81  tff(c_158, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_151])).
% 4.37/1.81  tff(c_70, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.37/1.81  tff(c_68, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.37/1.81  tff(c_718, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_699])).
% 4.37/1.81  tff(c_797, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_66, c_787])).
% 4.37/1.81  tff(c_810, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_718, c_797])).
% 4.37/1.81  tff(c_818, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_810])).
% 4.37/1.81  tff(c_1097, plain, (![A_192, B_193]: (r2_hidden('#skF_3'(A_192, B_193), k1_relat_1(A_192)) | B_193=A_192 | k1_relat_1(B_193)!=k1_relat_1(A_192) | ~v1_funct_1(B_193) | ~v1_relat_1(B_193) | ~v1_funct_1(A_192) | ~v1_relat_1(A_192))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.37/1.81  tff(c_1105, plain, (![B_193]: (r2_hidden('#skF_3'('#skF_6', B_193), '#skF_4') | B_193='#skF_6' | k1_relat_1(B_193)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_193) | ~v1_relat_1(B_193) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_818, c_1097])).
% 4.37/1.81  tff(c_1641, plain, (![B_244]: (r2_hidden('#skF_3'('#skF_6', B_244), '#skF_4') | B_244='#skF_6' | k1_relat_1(B_244)!='#skF_4' | ~v1_funct_1(B_244) | ~v1_relat_1(B_244))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_70, c_818, c_1105])).
% 4.37/1.81  tff(c_58, plain, (![E_41]: (k1_funct_1('#skF_7', E_41)=k1_funct_1('#skF_6', E_41) | ~r2_hidden(E_41, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.37/1.81  tff(c_1761, plain, (![B_248]: (k1_funct_1('#skF_7', '#skF_3'('#skF_6', B_248))=k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_248)) | B_248='#skF_6' | k1_relat_1(B_248)!='#skF_4' | ~v1_funct_1(B_248) | ~v1_relat_1(B_248))), inference(resolution, [status(thm)], [c_1641, c_58])).
% 4.37/1.81  tff(c_34, plain, (![B_25, A_21]: (k1_funct_1(B_25, '#skF_3'(A_21, B_25))!=k1_funct_1(A_21, '#skF_3'(A_21, B_25)) | B_25=A_21 | k1_relat_1(B_25)!=k1_relat_1(A_21) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.37/1.81  tff(c_1768, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_7'='#skF_6' | k1_relat_1('#skF_7')!='#skF_4' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1761, c_34])).
% 4.37/1.81  tff(c_1775, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_155, c_64, c_812, c_158, c_70, c_812, c_818, c_1768])).
% 4.37/1.81  tff(c_56, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.37/1.81  tff(c_1800, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1775, c_56])).
% 4.37/1.81  tff(c_1811, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_671, c_1800])).
% 4.37/1.81  tff(c_1812, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_810])).
% 4.37/1.81  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.37/1.81  tff(c_1834, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1812, c_12])).
% 4.37/1.81  tff(c_22, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.37/1.81  tff(c_1833, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1812, c_1812, c_22])).
% 4.37/1.81  tff(c_112, plain, (![A_52, B_53]: (r1_tarski(A_52, B_53) | ~m1_subset_1(A_52, k1_zfmisc_1(B_53)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.37/1.81  tff(c_124, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_66, c_112])).
% 4.37/1.81  tff(c_177, plain, (![A_63, B_64]: (r2_hidden('#skF_2'(A_63, B_64), A_63) | r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.37/1.81  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.37/1.81  tff(c_192, plain, (![A_63, B_64]: (~v1_xboole_0(A_63) | r1_tarski(A_63, B_64))), inference(resolution, [status(thm)], [c_177, c_2])).
% 4.37/1.81  tff(c_492, plain, (![B_99, A_100]: (B_99=A_100 | ~r1_tarski(B_99, A_100) | ~r1_tarski(A_100, B_99))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.37/1.81  tff(c_532, plain, (![B_103, A_104]: (B_103=A_104 | ~r1_tarski(B_103, A_104) | ~v1_xboole_0(A_104))), inference(resolution, [status(thm)], [c_192, c_492])).
% 4.37/1.81  tff(c_546, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6' | ~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_124, c_532])).
% 4.37/1.81  tff(c_564, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_546])).
% 4.37/1.81  tff(c_1886, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1833, c_564])).
% 4.37/1.81  tff(c_1893, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1834, c_1886])).
% 4.37/1.81  tff(c_1894, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_807])).
% 4.37/1.81  tff(c_1917, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1894, c_12])).
% 4.37/1.81  tff(c_1916, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1894, c_1894, c_22])).
% 4.37/1.81  tff(c_1974, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1916, c_564])).
% 4.37/1.81  tff(c_1981, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1917, c_1974])).
% 4.37/1.81  tff(c_1982, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_546])).
% 4.37/1.81  tff(c_2074, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1982, c_66])).
% 4.37/1.81  tff(c_1983, plain, (v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_546])).
% 4.37/1.81  tff(c_2013, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1982, c_1983])).
% 4.37/1.81  tff(c_123, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_60, c_112])).
% 4.37/1.81  tff(c_547, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_7' | ~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_123, c_532])).
% 4.37/1.81  tff(c_1984, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_547])).
% 4.37/1.81  tff(c_2068, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2013, c_1982, c_1984])).
% 4.37/1.81  tff(c_2070, plain, (v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_547])).
% 4.37/1.81  tff(c_2110, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1982, c_2070])).
% 4.37/1.81  tff(c_550, plain, (![B_105, A_106]: (B_105=A_106 | ~v1_xboole_0(B_105) | ~v1_xboole_0(A_106))), inference(resolution, [status(thm)], [c_192, c_532])).
% 4.37/1.81  tff(c_553, plain, (![A_106]: (k1_xboole_0=A_106 | ~v1_xboole_0(A_106))), inference(resolution, [status(thm)], [c_12, c_550])).
% 4.37/1.81  tff(c_2119, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_2110, c_553])).
% 4.37/1.81  tff(c_2127, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2119, c_2119, c_22])).
% 4.37/1.81  tff(c_2255, plain, (![A_267, B_268, D_269]: (r2_relset_1(A_267, B_268, D_269, D_269) | ~m1_subset_1(D_269, k1_zfmisc_1(k2_zfmisc_1(A_267, B_268))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.37/1.81  tff(c_2295, plain, (![A_277, D_278]: (r2_relset_1(A_277, '#skF_6', D_278, D_278) | ~m1_subset_1(D_278, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_2127, c_2255])).
% 4.37/1.81  tff(c_2301, plain, (![A_277]: (r2_relset_1(A_277, '#skF_6', '#skF_6', '#skF_6'))), inference(resolution, [status(thm)], [c_2074, c_2295])).
% 4.37/1.81  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.37/1.81  tff(c_125, plain, (![E_54]: (k1_funct_1('#skF_7', E_54)=k1_funct_1('#skF_6', E_54) | ~r2_hidden(E_54, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.37/1.81  tff(c_130, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_4'))=k1_funct_1('#skF_6', '#skF_1'('#skF_4')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_125])).
% 4.37/1.81  tff(c_198, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_130])).
% 4.37/1.81  tff(c_218, plain, (![B_68, A_69]: (B_68=A_69 | ~r1_tarski(B_68, A_69) | ~r1_tarski(A_69, B_68))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.37/1.81  tff(c_234, plain, (![B_70, A_71]: (B_70=A_71 | ~r1_tarski(B_70, A_71) | ~v1_xboole_0(A_71))), inference(resolution, [status(thm)], [c_192, c_218])).
% 4.37/1.81  tff(c_252, plain, (![B_72, A_73]: (B_72=A_73 | ~v1_xboole_0(B_72) | ~v1_xboole_0(A_73))), inference(resolution, [status(thm)], [c_192, c_234])).
% 4.37/1.81  tff(c_259, plain, (![A_74]: (k1_xboole_0=A_74 | ~v1_xboole_0(A_74))), inference(resolution, [status(thm)], [c_12, c_252])).
% 4.37/1.81  tff(c_266, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_198, c_259])).
% 4.37/1.81  tff(c_24, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.37/1.81  tff(c_281, plain, (![B_13]: (k2_zfmisc_1('#skF_4', B_13)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_266, c_266, c_24])).
% 4.37/1.81  tff(c_296, plain, (r1_tarski('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_281, c_124])).
% 4.37/1.81  tff(c_227, plain, (![B_64, A_63]: (B_64=A_63 | ~r1_tarski(B_64, A_63) | ~v1_xboole_0(A_63))), inference(resolution, [status(thm)], [c_192, c_218])).
% 4.37/1.81  tff(c_312, plain, ('#skF_6'='#skF_4' | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_296, c_227])).
% 4.37/1.81  tff(c_320, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_198, c_312])).
% 4.37/1.81  tff(c_299, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_281, c_66])).
% 4.37/1.81  tff(c_383, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_320, c_299])).
% 4.37/1.81  tff(c_455, plain, (![A_89, B_90, D_91]: (r2_relset_1(A_89, B_90, D_91, D_91) | ~m1_subset_1(D_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.37/1.81  tff(c_479, plain, (![B_97, D_98]: (r2_relset_1('#skF_4', B_97, D_98, D_98) | ~m1_subset_1(D_98, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_281, c_455])).
% 4.37/1.81  tff(c_485, plain, (![B_97]: (r2_relset_1('#skF_4', B_97, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_383, c_479])).
% 4.37/1.81  tff(c_297, plain, (r1_tarski('#skF_7', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_281, c_123])).
% 4.37/1.81  tff(c_347, plain, ('#skF_7'='#skF_4' | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_297, c_227])).
% 4.37/1.81  tff(c_355, plain, ('#skF_7'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_198, c_347])).
% 4.37/1.81  tff(c_336, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_4', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_320, c_56])).
% 4.37/1.81  tff(c_422, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_355, c_336])).
% 4.37/1.81  tff(c_489, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_485, c_422])).
% 4.37/1.81  tff(c_491, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_130])).
% 4.37/1.81  tff(c_20, plain, (![B_13, A_12]: (k1_xboole_0=B_13 | k1_xboole_0=A_12 | k2_zfmisc_1(A_12, B_13)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.37/1.81  tff(c_2079, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0!='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_1982, c_20])).
% 4.37/1.81  tff(c_2215, plain, ('#skF_5'='#skF_6' | '#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2119, c_2119, c_2119, c_2079])).
% 4.37/1.81  tff(c_2216, plain, ('#skF_6'='#skF_4'), inference(splitLeft, [status(thm)], [c_2215])).
% 4.37/1.81  tff(c_2225, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2216, c_2110])).
% 4.37/1.81  tff(c_2231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_491, c_2225])).
% 4.37/1.81  tff(c_2232, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_2215])).
% 4.37/1.81  tff(c_2069, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_7'), inference(splitRight, [status(thm)], [c_547])).
% 4.37/1.81  tff(c_2135, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1982, c_2069])).
% 4.37/1.81  tff(c_2142, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2135, c_56])).
% 4.37/1.81  tff(c_2236, plain, (~r2_relset_1('#skF_4', '#skF_6', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2232, c_2142])).
% 4.37/1.81  tff(c_2305, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2301, c_2236])).
% 4.37/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.81  
% 4.37/1.81  Inference rules
% 4.37/1.81  ----------------------
% 4.37/1.81  #Ref     : 1
% 4.37/1.81  #Sup     : 440
% 4.37/1.81  #Fact    : 0
% 4.37/1.81  #Define  : 0
% 4.37/1.81  #Split   : 16
% 4.37/1.81  #Chain   : 0
% 4.37/1.81  #Close   : 0
% 4.37/1.81  
% 4.37/1.81  Ordering : KBO
% 4.37/1.81  
% 4.37/1.81  Simplification rules
% 4.37/1.81  ----------------------
% 4.37/1.81  #Subsume      : 78
% 4.37/1.81  #Demod        : 619
% 4.37/1.81  #Tautology    : 268
% 4.37/1.81  #SimpNegUnit  : 20
% 4.37/1.81  #BackRed      : 206
% 4.37/1.81  
% 4.37/1.81  #Partial instantiations: 0
% 4.37/1.81  #Strategies tried      : 1
% 4.37/1.81  
% 4.37/1.81  Timing (in seconds)
% 4.37/1.81  ----------------------
% 4.37/1.81  Preprocessing        : 0.34
% 4.37/1.81  Parsing              : 0.17
% 4.37/1.81  CNF conversion       : 0.02
% 4.37/1.81  Main loop            : 0.64
% 4.37/1.81  Inferencing          : 0.21
% 4.37/1.81  Reduction            : 0.22
% 4.37/1.81  Demodulation         : 0.15
% 4.37/1.81  BG Simplification    : 0.03
% 4.37/1.81  Subsumption          : 0.12
% 4.37/1.81  Abstraction          : 0.03
% 4.37/1.81  MUC search           : 0.00
% 4.37/1.81  Cooper               : 0.00
% 4.37/1.81  Total                : 1.02
% 4.37/1.81  Index Insertion      : 0.00
% 4.37/1.81  Index Deletion       : 0.00
% 4.37/1.81  Index Matching       : 0.00
% 4.37/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
