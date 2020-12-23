%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:19 EST 2020

% Result     : Theorem 6.27s
% Output     : CNFRefutation 6.62s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 376 expanded)
%              Number of leaves         :   38 ( 144 expanded)
%              Depth                    :   11
%              Number of atoms          :  204 (1144 expanded)
%              Number of equality atoms :   65 ( 287 expanded)
%              Maximal formula depth    :   11 (   4 average)
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_147,negated_conjecture,(
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

tff(f_108,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_126,axiom,(
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

tff(f_88,axiom,(
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

tff(f_57,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_838,plain,(
    ! [A_142,B_143,D_144] :
      ( r2_relset_1(A_142,B_143,D_144,D_144)
      | ~ m1_subset_1(D_144,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_859,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_838])).

tff(c_64,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_164,plain,(
    ! [C_73,A_74,B_75] :
      ( v1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_184,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_164])).

tff(c_68,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_66,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_901,plain,(
    ! [A_154,B_155,C_156] :
      ( k1_relset_1(A_154,B_155,C_156) = k1_relat_1(C_156)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_928,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_901])).

tff(c_1916,plain,(
    ! [B_212,A_213,C_214] :
      ( k1_xboole_0 = B_212
      | k1_relset_1(A_213,B_212,C_214) = A_213
      | ~ v1_funct_2(C_214,A_213,B_212)
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(A_213,B_212))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1931,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_1916])).

tff(c_1950,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_928,c_1931])).

tff(c_1959,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1950])).

tff(c_185,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_164])).

tff(c_74,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_72,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_929,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_901])).

tff(c_1934,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_1916])).

tff(c_1953,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_929,c_1934])).

tff(c_1974,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1953])).

tff(c_2395,plain,(
    ! [A_247,B_248] :
      ( r2_hidden('#skF_3'(A_247,B_248),k1_relat_1(A_247))
      | B_248 = A_247
      | k1_relat_1(B_248) != k1_relat_1(A_247)
      | ~ v1_funct_1(B_248)
      | ~ v1_relat_1(B_248)
      | ~ v1_funct_1(A_247)
      | ~ v1_relat_1(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_28,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,B_16)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3918,plain,(
    ! [A_358,B_359] :
      ( m1_subset_1('#skF_3'(A_358,B_359),k1_relat_1(A_358))
      | B_359 = A_358
      | k1_relat_1(B_359) != k1_relat_1(A_358)
      | ~ v1_funct_1(B_359)
      | ~ v1_relat_1(B_359)
      | ~ v1_funct_1(A_358)
      | ~ v1_relat_1(A_358) ) ),
    inference(resolution,[status(thm)],[c_2395,c_28])).

tff(c_3921,plain,(
    ! [B_359] :
      ( m1_subset_1('#skF_3'('#skF_6',B_359),'#skF_4')
      | B_359 = '#skF_6'
      | k1_relat_1(B_359) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_359)
      | ~ v1_relat_1(B_359)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1974,c_3918])).

tff(c_5636,plain,(
    ! [B_437] :
      ( m1_subset_1('#skF_3'('#skF_6',B_437),'#skF_4')
      | B_437 = '#skF_6'
      | k1_relat_1(B_437) != '#skF_4'
      | ~ v1_funct_1(B_437)
      | ~ v1_relat_1(B_437) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_74,c_1974,c_3921])).

tff(c_62,plain,(
    ! [E_49] :
      ( k1_funct_1('#skF_7',E_49) = k1_funct_1('#skF_6',E_49)
      | ~ m1_subset_1(E_49,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_5657,plain,(
    ! [B_439] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_6',B_439)) = k1_funct_1('#skF_6','#skF_3'('#skF_6',B_439))
      | B_439 = '#skF_6'
      | k1_relat_1(B_439) != '#skF_4'
      | ~ v1_funct_1(B_439)
      | ~ v1_relat_1(B_439) ) ),
    inference(resolution,[status(thm)],[c_5636,c_62])).

tff(c_34,plain,(
    ! [B_27,A_23] :
      ( k1_funct_1(B_27,'#skF_3'(A_23,B_27)) != k1_funct_1(A_23,'#skF_3'(A_23,B_27))
      | B_27 = A_23
      | k1_relat_1(B_27) != k1_relat_1(A_23)
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_5664,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_7') != '#skF_4'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_5657,c_34])).

tff(c_5671,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_68,c_1959,c_185,c_74,c_1974,c_1959,c_5664])).

tff(c_60,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_5688,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5671,c_60])).

tff(c_5698,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_859,c_5688])).

tff(c_5699,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1953])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5731,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5699,c_12])).

tff(c_22,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_5729,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5699,c_5699,c_22])).

tff(c_728,plain,(
    ! [C_130,B_131,A_132] :
      ( ~ v1_xboole_0(C_130)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(C_130))
      | ~ r2_hidden(A_132,B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_748,plain,(
    ! [A_132] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(A_132,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_70,c_728])).

tff(c_792,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_748])).

tff(c_5891,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5729,c_792])).

tff(c_5896,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5731,c_5891])).

tff(c_5897,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1950])).

tff(c_5929,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5897,c_12])).

tff(c_5927,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5897,c_5897,c_22])).

tff(c_6087,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5927,c_792])).

tff(c_6092,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5929,c_6087])).

tff(c_6095,plain,(
    ! [A_459] : ~ r2_hidden(A_459,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_748])).

tff(c_6105,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_6095])).

tff(c_125,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_2'(A_63,B_64),A_63)
      | r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_133,plain,(
    ! [A_63,B_64] :
      ( ~ v1_xboole_0(A_63)
      | r1_tarski(A_63,B_64) ) ),
    inference(resolution,[status(thm)],[c_125,c_2])).

tff(c_140,plain,(
    ! [A_66,B_67] :
      ( ~ v1_xboole_0(A_66)
      | r1_tarski(A_66,B_67) ) ),
    inference(resolution,[status(thm)],[c_125,c_2])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_144,plain,(
    ! [B_68,A_69] :
      ( B_68 = A_69
      | ~ r1_tarski(B_68,A_69)
      | ~ v1_xboole_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_140,c_14])).

tff(c_154,plain,(
    ! [B_70,A_71] :
      ( B_70 = A_71
      | ~ v1_xboole_0(B_70)
      | ~ v1_xboole_0(A_71) ) ),
    inference(resolution,[status(thm)],[c_133,c_144])).

tff(c_157,plain,(
    ! [A_71] :
      ( k1_xboole_0 = A_71
      | ~ v1_xboole_0(A_71) ) ),
    inference(resolution,[status(thm)],[c_12,c_154])).

tff(c_6111,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_6105,c_157])).

tff(c_26,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6113,plain,(
    ! [A_460,B_461,D_462] :
      ( r2_relset_1(A_460,B_461,D_462,D_462)
      | ~ m1_subset_1(D_462,k1_zfmisc_1(k2_zfmisc_1(A_460,B_461))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_6137,plain,(
    ! [A_460,B_461] : r2_relset_1(A_460,B_461,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_6113])).

tff(c_6261,plain,(
    ! [A_460,B_461] : r2_relset_1(A_460,B_461,'#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6111,c_6111,c_6137])).

tff(c_6094,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_748])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6157,plain,(
    ! [B_463] : r1_tarski('#skF_6',B_463) ),
    inference(resolution,[status(thm)],[c_10,c_6095])).

tff(c_143,plain,(
    ! [B_67,A_66] :
      ( B_67 = A_66
      | ~ r1_tarski(B_67,A_66)
      | ~ v1_xboole_0(A_66) ) ),
    inference(resolution,[status(thm)],[c_140,c_14])).

tff(c_6179,plain,(
    ! [B_464] :
      ( B_464 = '#skF_6'
      | ~ v1_xboole_0(B_464) ) ),
    inference(resolution,[status(thm)],[c_6157,c_143])).

tff(c_6186,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_6094,c_6179])).

tff(c_747,plain,(
    ! [A_132] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(A_132,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_64,c_728])).

tff(c_6336,plain,(
    ! [A_477] : ~ r2_hidden(A_477,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6105,c_6186,c_747])).

tff(c_6346,plain,(
    v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_4,c_6336])).

tff(c_6163,plain,(
    ! [B_463] :
      ( B_463 = '#skF_6'
      | ~ v1_xboole_0(B_463) ) ),
    inference(resolution,[status(thm)],[c_6157,c_143])).

tff(c_6352,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_6346,c_6163])).

tff(c_6361,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6352,c_60])).

tff(c_6370,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6261,c_6361])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:09:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.27/2.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.62/2.51  
% 6.62/2.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.62/2.51  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 6.62/2.51  
% 6.62/2.51  %Foreground sorts:
% 6.62/2.51  
% 6.62/2.51  
% 6.62/2.51  %Background operators:
% 6.62/2.51  
% 6.62/2.51  
% 6.62/2.51  %Foreground operators:
% 6.62/2.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.62/2.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.62/2.51  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.62/2.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.62/2.51  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.62/2.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.62/2.51  tff('#skF_7', type, '#skF_7': $i).
% 6.62/2.51  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.62/2.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.62/2.51  tff('#skF_5', type, '#skF_5': $i).
% 6.62/2.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.62/2.51  tff('#skF_6', type, '#skF_6': $i).
% 6.62/2.51  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.62/2.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.62/2.51  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.62/2.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.62/2.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.62/2.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.62/2.51  tff('#skF_4', type, '#skF_4': $i).
% 6.62/2.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.62/2.51  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.62/2.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.62/2.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.62/2.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.62/2.51  
% 6.62/2.53  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.62/2.53  tff(f_147, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_funct_2)).
% 6.62/2.53  tff(f_108, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.62/2.53  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.62/2.53  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.62/2.53  tff(f_126, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.62/2.53  tff(f_88, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 6.62/2.53  tff(f_57, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 6.62/2.53  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.62/2.53  tff(f_51, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.62/2.53  tff(f_70, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 6.62/2.53  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.62/2.53  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.62/2.53  tff(f_53, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 6.62/2.53  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.62/2.53  tff(c_70, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 6.62/2.53  tff(c_838, plain, (![A_142, B_143, D_144]: (r2_relset_1(A_142, B_143, D_144, D_144) | ~m1_subset_1(D_144, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.62/2.53  tff(c_859, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_70, c_838])).
% 6.62/2.53  tff(c_64, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 6.62/2.53  tff(c_164, plain, (![C_73, A_74, B_75]: (v1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.62/2.53  tff(c_184, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_64, c_164])).
% 6.62/2.53  tff(c_68, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_147])).
% 6.62/2.53  tff(c_66, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_147])).
% 6.62/2.53  tff(c_901, plain, (![A_154, B_155, C_156]: (k1_relset_1(A_154, B_155, C_156)=k1_relat_1(C_156) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.62/2.53  tff(c_928, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_64, c_901])).
% 6.62/2.53  tff(c_1916, plain, (![B_212, A_213, C_214]: (k1_xboole_0=B_212 | k1_relset_1(A_213, B_212, C_214)=A_213 | ~v1_funct_2(C_214, A_213, B_212) | ~m1_subset_1(C_214, k1_zfmisc_1(k2_zfmisc_1(A_213, B_212))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.62/2.53  tff(c_1931, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_64, c_1916])).
% 6.62/2.53  tff(c_1950, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_928, c_1931])).
% 6.62/2.53  tff(c_1959, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_1950])).
% 6.62/2.53  tff(c_185, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_70, c_164])).
% 6.62/2.53  tff(c_74, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_147])).
% 6.62/2.53  tff(c_72, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_147])).
% 6.62/2.53  tff(c_929, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_70, c_901])).
% 6.62/2.53  tff(c_1934, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_70, c_1916])).
% 6.62/2.53  tff(c_1953, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_929, c_1934])).
% 6.62/2.53  tff(c_1974, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_1953])).
% 6.62/2.53  tff(c_2395, plain, (![A_247, B_248]: (r2_hidden('#skF_3'(A_247, B_248), k1_relat_1(A_247)) | B_248=A_247 | k1_relat_1(B_248)!=k1_relat_1(A_247) | ~v1_funct_1(B_248) | ~v1_relat_1(B_248) | ~v1_funct_1(A_247) | ~v1_relat_1(A_247))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.62/2.53  tff(c_28, plain, (![A_15, B_16]: (m1_subset_1(A_15, B_16) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.62/2.53  tff(c_3918, plain, (![A_358, B_359]: (m1_subset_1('#skF_3'(A_358, B_359), k1_relat_1(A_358)) | B_359=A_358 | k1_relat_1(B_359)!=k1_relat_1(A_358) | ~v1_funct_1(B_359) | ~v1_relat_1(B_359) | ~v1_funct_1(A_358) | ~v1_relat_1(A_358))), inference(resolution, [status(thm)], [c_2395, c_28])).
% 6.62/2.53  tff(c_3921, plain, (![B_359]: (m1_subset_1('#skF_3'('#skF_6', B_359), '#skF_4') | B_359='#skF_6' | k1_relat_1(B_359)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_359) | ~v1_relat_1(B_359) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1974, c_3918])).
% 6.62/2.53  tff(c_5636, plain, (![B_437]: (m1_subset_1('#skF_3'('#skF_6', B_437), '#skF_4') | B_437='#skF_6' | k1_relat_1(B_437)!='#skF_4' | ~v1_funct_1(B_437) | ~v1_relat_1(B_437))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_74, c_1974, c_3921])).
% 6.62/2.53  tff(c_62, plain, (![E_49]: (k1_funct_1('#skF_7', E_49)=k1_funct_1('#skF_6', E_49) | ~m1_subset_1(E_49, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_147])).
% 6.62/2.53  tff(c_5657, plain, (![B_439]: (k1_funct_1('#skF_7', '#skF_3'('#skF_6', B_439))=k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_439)) | B_439='#skF_6' | k1_relat_1(B_439)!='#skF_4' | ~v1_funct_1(B_439) | ~v1_relat_1(B_439))), inference(resolution, [status(thm)], [c_5636, c_62])).
% 6.62/2.53  tff(c_34, plain, (![B_27, A_23]: (k1_funct_1(B_27, '#skF_3'(A_23, B_27))!=k1_funct_1(A_23, '#skF_3'(A_23, B_27)) | B_27=A_23 | k1_relat_1(B_27)!=k1_relat_1(A_23) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.62/2.53  tff(c_5664, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_7'='#skF_6' | k1_relat_1('#skF_7')!='#skF_4' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_5657, c_34])).
% 6.62/2.53  tff(c_5671, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_184, c_68, c_1959, c_185, c_74, c_1974, c_1959, c_5664])).
% 6.62/2.53  tff(c_60, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_147])).
% 6.62/2.53  tff(c_5688, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5671, c_60])).
% 6.62/2.53  tff(c_5698, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_859, c_5688])).
% 6.62/2.53  tff(c_5699, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1953])).
% 6.62/2.53  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.62/2.53  tff(c_5731, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5699, c_12])).
% 6.62/2.53  tff(c_22, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.62/2.53  tff(c_5729, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5699, c_5699, c_22])).
% 6.62/2.53  tff(c_728, plain, (![C_130, B_131, A_132]: (~v1_xboole_0(C_130) | ~m1_subset_1(B_131, k1_zfmisc_1(C_130)) | ~r2_hidden(A_132, B_131))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.62/2.53  tff(c_748, plain, (![A_132]: (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(A_132, '#skF_6'))), inference(resolution, [status(thm)], [c_70, c_728])).
% 6.62/2.53  tff(c_792, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_748])).
% 6.62/2.53  tff(c_5891, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5729, c_792])).
% 6.62/2.53  tff(c_5896, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5731, c_5891])).
% 6.62/2.53  tff(c_5897, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1950])).
% 6.62/2.53  tff(c_5929, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5897, c_12])).
% 6.62/2.53  tff(c_5927, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5897, c_5897, c_22])).
% 6.62/2.53  tff(c_6087, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5927, c_792])).
% 6.62/2.53  tff(c_6092, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5929, c_6087])).
% 6.62/2.53  tff(c_6095, plain, (![A_459]: (~r2_hidden(A_459, '#skF_6'))), inference(splitRight, [status(thm)], [c_748])).
% 6.62/2.53  tff(c_6105, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_4, c_6095])).
% 6.62/2.53  tff(c_125, plain, (![A_63, B_64]: (r2_hidden('#skF_2'(A_63, B_64), A_63) | r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.62/2.53  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.62/2.53  tff(c_133, plain, (![A_63, B_64]: (~v1_xboole_0(A_63) | r1_tarski(A_63, B_64))), inference(resolution, [status(thm)], [c_125, c_2])).
% 6.62/2.53  tff(c_140, plain, (![A_66, B_67]: (~v1_xboole_0(A_66) | r1_tarski(A_66, B_67))), inference(resolution, [status(thm)], [c_125, c_2])).
% 6.62/2.53  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.62/2.53  tff(c_144, plain, (![B_68, A_69]: (B_68=A_69 | ~r1_tarski(B_68, A_69) | ~v1_xboole_0(A_69))), inference(resolution, [status(thm)], [c_140, c_14])).
% 6.62/2.53  tff(c_154, plain, (![B_70, A_71]: (B_70=A_71 | ~v1_xboole_0(B_70) | ~v1_xboole_0(A_71))), inference(resolution, [status(thm)], [c_133, c_144])).
% 6.62/2.53  tff(c_157, plain, (![A_71]: (k1_xboole_0=A_71 | ~v1_xboole_0(A_71))), inference(resolution, [status(thm)], [c_12, c_154])).
% 6.62/2.53  tff(c_6111, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_6105, c_157])).
% 6.62/2.53  tff(c_26, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.62/2.53  tff(c_6113, plain, (![A_460, B_461, D_462]: (r2_relset_1(A_460, B_461, D_462, D_462) | ~m1_subset_1(D_462, k1_zfmisc_1(k2_zfmisc_1(A_460, B_461))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.62/2.53  tff(c_6137, plain, (![A_460, B_461]: (r2_relset_1(A_460, B_461, k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_6113])).
% 6.62/2.53  tff(c_6261, plain, (![A_460, B_461]: (r2_relset_1(A_460, B_461, '#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6111, c_6111, c_6137])).
% 6.62/2.53  tff(c_6094, plain, (v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_748])).
% 6.62/2.53  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.62/2.53  tff(c_6157, plain, (![B_463]: (r1_tarski('#skF_6', B_463))), inference(resolution, [status(thm)], [c_10, c_6095])).
% 6.62/2.53  tff(c_143, plain, (![B_67, A_66]: (B_67=A_66 | ~r1_tarski(B_67, A_66) | ~v1_xboole_0(A_66))), inference(resolution, [status(thm)], [c_140, c_14])).
% 6.62/2.53  tff(c_6179, plain, (![B_464]: (B_464='#skF_6' | ~v1_xboole_0(B_464))), inference(resolution, [status(thm)], [c_6157, c_143])).
% 6.62/2.53  tff(c_6186, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_6094, c_6179])).
% 6.62/2.53  tff(c_747, plain, (![A_132]: (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(A_132, '#skF_7'))), inference(resolution, [status(thm)], [c_64, c_728])).
% 6.62/2.53  tff(c_6336, plain, (![A_477]: (~r2_hidden(A_477, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_6105, c_6186, c_747])).
% 6.62/2.53  tff(c_6346, plain, (v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_4, c_6336])).
% 6.62/2.53  tff(c_6163, plain, (![B_463]: (B_463='#skF_6' | ~v1_xboole_0(B_463))), inference(resolution, [status(thm)], [c_6157, c_143])).
% 6.62/2.53  tff(c_6352, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_6346, c_6163])).
% 6.62/2.53  tff(c_6361, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6352, c_60])).
% 6.62/2.53  tff(c_6370, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6261, c_6361])).
% 6.62/2.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.62/2.53  
% 6.62/2.53  Inference rules
% 6.62/2.53  ----------------------
% 6.62/2.53  #Ref     : 1
% 6.62/2.53  #Sup     : 1389
% 6.62/2.53  #Fact    : 0
% 6.62/2.53  #Define  : 0
% 6.62/2.53  #Split   : 19
% 6.62/2.53  #Chain   : 0
% 6.62/2.53  #Close   : 0
% 6.62/2.53  
% 6.62/2.53  Ordering : KBO
% 6.62/2.53  
% 6.62/2.53  Simplification rules
% 6.62/2.53  ----------------------
% 6.62/2.53  #Subsume      : 361
% 6.62/2.53  #Demod        : 1260
% 6.62/2.53  #Tautology    : 566
% 6.62/2.53  #SimpNegUnit  : 12
% 6.62/2.53  #BackRed      : 327
% 6.62/2.53  
% 6.62/2.53  #Partial instantiations: 0
% 6.62/2.53  #Strategies tried      : 1
% 6.62/2.53  
% 6.62/2.53  Timing (in seconds)
% 6.62/2.53  ----------------------
% 6.62/2.53  Preprocessing        : 0.36
% 6.62/2.53  Parsing              : 0.20
% 6.62/2.53  CNF conversion       : 0.03
% 6.62/2.53  Main loop            : 1.30
% 6.62/2.53  Inferencing          : 0.39
% 6.62/2.53  Reduction            : 0.42
% 6.62/2.53  Demodulation         : 0.28
% 6.62/2.53  BG Simplification    : 0.05
% 6.62/2.53  Subsumption          : 0.32
% 6.62/2.53  Abstraction          : 0.06
% 6.62/2.53  MUC search           : 0.00
% 6.62/2.53  Cooper               : 0.00
% 6.62/2.53  Total                : 1.70
% 6.62/2.53  Index Insertion      : 0.00
% 6.62/2.53  Index Deletion       : 0.00
% 6.62/2.53  Index Matching       : 0.00
% 6.62/2.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
