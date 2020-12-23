%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:37 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 446 expanded)
%              Number of leaves         :   36 ( 165 expanded)
%              Depth                    :   13
%              Number of atoms          :  184 (1344 expanded)
%              Number of equality atoms :   59 ( 302 expanded)
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

tff(f_131,negated_conjecture,(
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

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_110,axiom,(
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

tff(f_76,axiom,(
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

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_58,axiom,(
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

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_274,plain,(
    ! [A_80,B_81,D_82] :
      ( r2_relset_1(A_80,B_81,D_82,D_82)
      | ~ m1_subset_1(D_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_283,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_274])).

tff(c_56,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_101,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_113,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_101])).

tff(c_60,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_58,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_322,plain,(
    ! [A_96,B_97,C_98] :
      ( k1_relset_1(A_96,B_97,C_98) = k1_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_336,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_322])).

tff(c_408,plain,(
    ! [B_117,A_118,C_119] :
      ( k1_xboole_0 = B_117
      | k1_relset_1(A_118,B_117,C_119) = A_118
      | ~ v1_funct_2(C_119,A_118,B_117)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_118,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_414,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_408])).

tff(c_426,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_336,c_414])).

tff(c_434,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_426])).

tff(c_112,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_101])).

tff(c_66,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_64,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_335,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_322])).

tff(c_411,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_408])).

tff(c_423,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_335,c_411])).

tff(c_428,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_423])).

tff(c_481,plain,(
    ! [A_127,B_128] :
      ( r2_hidden('#skF_3'(A_127,B_128),k1_relat_1(A_127))
      | B_128 = A_127
      | k1_relat_1(B_128) != k1_relat_1(A_127)
      | ~ v1_funct_1(B_128)
      | ~ v1_relat_1(B_128)
      | ~ v1_funct_1(A_127)
      | ~ v1_relat_1(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_492,plain,(
    ! [B_128] :
      ( r2_hidden('#skF_3'('#skF_6',B_128),'#skF_4')
      | B_128 = '#skF_6'
      | k1_relat_1(B_128) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_128)
      | ~ v1_relat_1(B_128)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_428,c_481])).

tff(c_517,plain,(
    ! [B_132] :
      ( r2_hidden('#skF_3'('#skF_6',B_132),'#skF_4')
      | B_132 = '#skF_6'
      | k1_relat_1(B_132) != '#skF_4'
      | ~ v1_funct_1(B_132)
      | ~ v1_relat_1(B_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_66,c_428,c_492])).

tff(c_54,plain,(
    ! [E_40] :
      ( k1_funct_1('#skF_7',E_40) = k1_funct_1('#skF_6',E_40)
      | ~ r2_hidden(E_40,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_538,plain,(
    ! [B_135] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_6',B_135)) = k1_funct_1('#skF_6','#skF_3'('#skF_6',B_135))
      | B_135 = '#skF_6'
      | k1_relat_1(B_135) != '#skF_4'
      | ~ v1_funct_1(B_135)
      | ~ v1_relat_1(B_135) ) ),
    inference(resolution,[status(thm)],[c_517,c_54])).

tff(c_28,plain,(
    ! [B_21,A_17] :
      ( k1_funct_1(B_21,'#skF_3'(A_17,B_21)) != k1_funct_1(A_17,'#skF_3'(A_17,B_21))
      | B_21 = A_17
      | k1_relat_1(B_21) != k1_relat_1(A_17)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_545,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_7') != '#skF_4'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_538,c_28])).

tff(c_552,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_60,c_434,c_112,c_66,c_434,c_428,c_545])).

tff(c_52,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_566,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_52])).

tff(c_576,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_566])).

tff(c_577,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_426])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_593,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_577,c_12])).

tff(c_22,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_592,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_577,c_577,c_22])).

tff(c_187,plain,(
    ! [C_70,B_71,A_72] :
      ( ~ v1_xboole_0(C_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(C_70))
      | ~ r2_hidden(A_72,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_192,plain,(
    ! [A_72] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(A_72,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_62,c_187])).

tff(c_194,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_192])).

tff(c_631,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_592,c_194])).

tff(c_636,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_631])).

tff(c_637,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_423])).

tff(c_653,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_637,c_12])).

tff(c_652,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_637,c_637,c_22])).

tff(c_662,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_194])).

tff(c_667,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_662])).

tff(c_670,plain,(
    ! [A_140] : ~ r2_hidden(A_140,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_680,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_670])).

tff(c_669,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_812,plain,(
    ! [B_149] : r1_tarski('#skF_6',B_149) ),
    inference(resolution,[status(thm)],[c_10,c_670])).

tff(c_129,plain,(
    ! [A_56,B_57] :
      ( r2_hidden('#skF_2'(A_56,B_57),A_56)
      | r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_145,plain,(
    ! [A_58,B_59] :
      ( ~ v1_xboole_0(A_58)
      | r1_tarski(A_58,B_59) ) ),
    inference(resolution,[status(thm)],[c_129,c_2])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_148,plain,(
    ! [B_59,A_58] :
      ( B_59 = A_58
      | ~ r1_tarski(B_59,A_58)
      | ~ v1_xboole_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_145,c_14])).

tff(c_830,plain,(
    ! [B_153] :
      ( B_153 = '#skF_6'
      | ~ v1_xboole_0(B_153) ) ),
    inference(resolution,[status(thm)],[c_812,c_148])).

tff(c_837,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_669,c_830])).

tff(c_842,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_837,c_56])).

tff(c_26,plain,(
    ! [C_16,B_15,A_14] :
      ( ~ v1_xboole_0(C_16)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(C_16))
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_858,plain,(
    ! [A_14] :
      ( ~ v1_xboole_0('#skF_6')
      | ~ r2_hidden(A_14,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_842,c_26])).

tff(c_862,plain,(
    ! [A_154] : ~ r2_hidden(A_154,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_680,c_858])).

tff(c_872,plain,(
    v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_4,c_862])).

tff(c_818,plain,(
    ! [B_149] :
      ( B_149 = '#skF_6'
      | ~ v1_xboole_0(B_149) ) ),
    inference(resolution,[status(thm)],[c_812,c_148])).

tff(c_878,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_872,c_818])).

tff(c_823,plain,(
    ! [A_150,B_151,D_152] :
      ( r2_relset_1(A_150,B_151,D_152,D_152)
      | ~ m1_subset_1(D_152,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_829,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_823])).

tff(c_931,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_878,c_878,c_829])).

tff(c_885,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_878,c_52])).

tff(c_953,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_931,c_885])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:00:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.24/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.50  
% 3.24/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.50  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 3.24/1.50  
% 3.24/1.50  %Foreground sorts:
% 3.24/1.50  
% 3.24/1.50  
% 3.24/1.50  %Background operators:
% 3.24/1.50  
% 3.24/1.50  
% 3.24/1.50  %Foreground operators:
% 3.24/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.24/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.24/1.50  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.24/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.24/1.50  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.24/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.24/1.50  tff('#skF_7', type, '#skF_7': $i).
% 3.24/1.50  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.24/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.24/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.24/1.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.24/1.50  tff('#skF_6', type, '#skF_6': $i).
% 3.24/1.50  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.24/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.24/1.50  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.24/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.24/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.24/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.24/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.24/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.24/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.24/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.24/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.24/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.24/1.50  
% 3.24/1.52  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.24/1.52  tff(f_131, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 3.24/1.52  tff(f_92, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.24/1.52  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.24/1.52  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.24/1.52  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.24/1.52  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 3.24/1.52  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.24/1.52  tff(f_51, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.24/1.52  tff(f_58, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.24/1.52  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.24/1.52  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.24/1.52  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.24/1.52  tff(c_62, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.24/1.52  tff(c_274, plain, (![A_80, B_81, D_82]: (r2_relset_1(A_80, B_81, D_82, D_82) | ~m1_subset_1(D_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.24/1.52  tff(c_283, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_62, c_274])).
% 3.24/1.52  tff(c_56, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.24/1.52  tff(c_101, plain, (![C_47, A_48, B_49]: (v1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.24/1.52  tff(c_113, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_56, c_101])).
% 3.24/1.52  tff(c_60, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.24/1.52  tff(c_58, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.24/1.52  tff(c_322, plain, (![A_96, B_97, C_98]: (k1_relset_1(A_96, B_97, C_98)=k1_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.24/1.52  tff(c_336, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_56, c_322])).
% 3.24/1.52  tff(c_408, plain, (![B_117, A_118, C_119]: (k1_xboole_0=B_117 | k1_relset_1(A_118, B_117, C_119)=A_118 | ~v1_funct_2(C_119, A_118, B_117) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_118, B_117))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.24/1.52  tff(c_414, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_408])).
% 3.24/1.52  tff(c_426, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_336, c_414])).
% 3.24/1.52  tff(c_434, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_426])).
% 3.24/1.52  tff(c_112, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_62, c_101])).
% 3.24/1.52  tff(c_66, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.24/1.52  tff(c_64, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.24/1.52  tff(c_335, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_62, c_322])).
% 3.24/1.52  tff(c_411, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_62, c_408])).
% 3.24/1.52  tff(c_423, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_335, c_411])).
% 3.24/1.52  tff(c_428, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_423])).
% 3.24/1.52  tff(c_481, plain, (![A_127, B_128]: (r2_hidden('#skF_3'(A_127, B_128), k1_relat_1(A_127)) | B_128=A_127 | k1_relat_1(B_128)!=k1_relat_1(A_127) | ~v1_funct_1(B_128) | ~v1_relat_1(B_128) | ~v1_funct_1(A_127) | ~v1_relat_1(A_127))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.24/1.52  tff(c_492, plain, (![B_128]: (r2_hidden('#skF_3'('#skF_6', B_128), '#skF_4') | B_128='#skF_6' | k1_relat_1(B_128)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_128) | ~v1_relat_1(B_128) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_428, c_481])).
% 3.24/1.52  tff(c_517, plain, (![B_132]: (r2_hidden('#skF_3'('#skF_6', B_132), '#skF_4') | B_132='#skF_6' | k1_relat_1(B_132)!='#skF_4' | ~v1_funct_1(B_132) | ~v1_relat_1(B_132))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_66, c_428, c_492])).
% 3.24/1.52  tff(c_54, plain, (![E_40]: (k1_funct_1('#skF_7', E_40)=k1_funct_1('#skF_6', E_40) | ~r2_hidden(E_40, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.24/1.52  tff(c_538, plain, (![B_135]: (k1_funct_1('#skF_7', '#skF_3'('#skF_6', B_135))=k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_135)) | B_135='#skF_6' | k1_relat_1(B_135)!='#skF_4' | ~v1_funct_1(B_135) | ~v1_relat_1(B_135))), inference(resolution, [status(thm)], [c_517, c_54])).
% 3.24/1.52  tff(c_28, plain, (![B_21, A_17]: (k1_funct_1(B_21, '#skF_3'(A_17, B_21))!=k1_funct_1(A_17, '#skF_3'(A_17, B_21)) | B_21=A_17 | k1_relat_1(B_21)!=k1_relat_1(A_17) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.24/1.52  tff(c_545, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_7'='#skF_6' | k1_relat_1('#skF_7')!='#skF_4' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_538, c_28])).
% 3.24/1.52  tff(c_552, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_113, c_60, c_434, c_112, c_66, c_434, c_428, c_545])).
% 3.24/1.52  tff(c_52, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.24/1.52  tff(c_566, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_552, c_52])).
% 3.24/1.52  tff(c_576, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_283, c_566])).
% 3.24/1.52  tff(c_577, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_426])).
% 3.24/1.52  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.24/1.52  tff(c_593, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_577, c_12])).
% 3.24/1.52  tff(c_22, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.24/1.52  tff(c_592, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_577, c_577, c_22])).
% 3.24/1.52  tff(c_187, plain, (![C_70, B_71, A_72]: (~v1_xboole_0(C_70) | ~m1_subset_1(B_71, k1_zfmisc_1(C_70)) | ~r2_hidden(A_72, B_71))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.24/1.52  tff(c_192, plain, (![A_72]: (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(A_72, '#skF_6'))), inference(resolution, [status(thm)], [c_62, c_187])).
% 3.24/1.52  tff(c_194, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_192])).
% 3.24/1.52  tff(c_631, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_592, c_194])).
% 3.24/1.52  tff(c_636, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_593, c_631])).
% 3.24/1.52  tff(c_637, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_423])).
% 3.24/1.52  tff(c_653, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_637, c_12])).
% 3.24/1.52  tff(c_652, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_637, c_637, c_22])).
% 3.24/1.52  tff(c_662, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_652, c_194])).
% 3.24/1.52  tff(c_667, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_653, c_662])).
% 3.24/1.52  tff(c_670, plain, (![A_140]: (~r2_hidden(A_140, '#skF_6'))), inference(splitRight, [status(thm)], [c_192])).
% 3.24/1.52  tff(c_680, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_4, c_670])).
% 3.24/1.52  tff(c_669, plain, (v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_192])).
% 3.24/1.52  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.24/1.52  tff(c_812, plain, (![B_149]: (r1_tarski('#skF_6', B_149))), inference(resolution, [status(thm)], [c_10, c_670])).
% 3.24/1.52  tff(c_129, plain, (![A_56, B_57]: (r2_hidden('#skF_2'(A_56, B_57), A_56) | r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.24/1.52  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.24/1.52  tff(c_145, plain, (![A_58, B_59]: (~v1_xboole_0(A_58) | r1_tarski(A_58, B_59))), inference(resolution, [status(thm)], [c_129, c_2])).
% 3.24/1.52  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.24/1.52  tff(c_148, plain, (![B_59, A_58]: (B_59=A_58 | ~r1_tarski(B_59, A_58) | ~v1_xboole_0(A_58))), inference(resolution, [status(thm)], [c_145, c_14])).
% 3.24/1.52  tff(c_830, plain, (![B_153]: (B_153='#skF_6' | ~v1_xboole_0(B_153))), inference(resolution, [status(thm)], [c_812, c_148])).
% 3.24/1.52  tff(c_837, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_669, c_830])).
% 3.24/1.52  tff(c_842, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_837, c_56])).
% 3.24/1.52  tff(c_26, plain, (![C_16, B_15, A_14]: (~v1_xboole_0(C_16) | ~m1_subset_1(B_15, k1_zfmisc_1(C_16)) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.24/1.52  tff(c_858, plain, (![A_14]: (~v1_xboole_0('#skF_6') | ~r2_hidden(A_14, '#skF_7'))), inference(resolution, [status(thm)], [c_842, c_26])).
% 3.24/1.52  tff(c_862, plain, (![A_154]: (~r2_hidden(A_154, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_680, c_858])).
% 3.24/1.52  tff(c_872, plain, (v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_4, c_862])).
% 3.24/1.52  tff(c_818, plain, (![B_149]: (B_149='#skF_6' | ~v1_xboole_0(B_149))), inference(resolution, [status(thm)], [c_812, c_148])).
% 3.24/1.52  tff(c_878, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_872, c_818])).
% 3.24/1.52  tff(c_823, plain, (![A_150, B_151, D_152]: (r2_relset_1(A_150, B_151, D_152, D_152) | ~m1_subset_1(D_152, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.24/1.52  tff(c_829, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_56, c_823])).
% 3.24/1.52  tff(c_931, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_878, c_878, c_829])).
% 3.24/1.52  tff(c_885, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_878, c_52])).
% 3.24/1.52  tff(c_953, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_931, c_885])).
% 3.24/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.52  
% 3.24/1.52  Inference rules
% 3.24/1.52  ----------------------
% 3.24/1.52  #Ref     : 1
% 3.24/1.52  #Sup     : 187
% 3.24/1.52  #Fact    : 0
% 3.24/1.52  #Define  : 0
% 3.24/1.52  #Split   : 6
% 3.24/1.52  #Chain   : 0
% 3.24/1.52  #Close   : 0
% 3.24/1.52  
% 3.24/1.52  Ordering : KBO
% 3.24/1.52  
% 3.24/1.52  Simplification rules
% 3.24/1.52  ----------------------
% 3.24/1.52  #Subsume      : 27
% 3.24/1.52  #Demod        : 230
% 3.24/1.52  #Tautology    : 122
% 3.24/1.52  #SimpNegUnit  : 2
% 3.24/1.52  #BackRed      : 82
% 3.24/1.52  
% 3.24/1.52  #Partial instantiations: 0
% 3.24/1.52  #Strategies tried      : 1
% 3.24/1.52  
% 3.24/1.52  Timing (in seconds)
% 3.24/1.52  ----------------------
% 3.24/1.52  Preprocessing        : 0.33
% 3.24/1.52  Parsing              : 0.18
% 3.24/1.52  CNF conversion       : 0.02
% 3.24/1.52  Main loop            : 0.39
% 3.24/1.52  Inferencing          : 0.13
% 3.24/1.52  Reduction            : 0.13
% 3.24/1.52  Demodulation         : 0.09
% 3.24/1.52  BG Simplification    : 0.02
% 3.24/1.52  Subsumption          : 0.08
% 3.24/1.52  Abstraction          : 0.02
% 3.24/1.52  MUC search           : 0.00
% 3.24/1.52  Cooper               : 0.00
% 3.24/1.52  Total                : 0.76
% 3.24/1.52  Index Insertion      : 0.00
% 3.24/1.52  Index Deletion       : 0.00
% 3.24/1.52  Index Matching       : 0.00
% 3.24/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
