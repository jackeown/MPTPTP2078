%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:52 EST 2020

% Result     : Timeout 59.04s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  210 ( 736 expanded)
%              Number of leaves         :   56 ( 273 expanded)
%              Depth                    :   16
%              Number of atoms          :  440 (2286 expanded)
%              Number of equality atoms :   88 ( 472 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(f_222,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ! [E] :
                ( ( v1_funct_1(E)
                  & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                     => ( B = k1_xboole_0
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k7_partfun1(A,E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).

tff(f_133,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_91,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_50,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_120,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_126,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_137,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_176,axiom,(
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

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_115,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(f_141,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_187,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_197,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_158,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( r1_tarski(k2_relset_1(A,B,D),k1_relset_1(B,C,E))
           => ( B = k1_xboole_0
              | k8_funct_2(A,B,C,D,E) = k1_partfun1(A,B,B,C,D,E) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_2)).

tff(f_66,axiom,(
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

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_84,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_100,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_94,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_277925,plain,(
    ! [C_3615,A_3616,B_3617] :
      ( v1_xboole_0(C_3615)
      | ~ m1_subset_1(C_3615,k1_zfmisc_1(k2_zfmisc_1(A_3616,B_3617)))
      | ~ v1_xboole_0(A_3616) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_277943,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_94,c_277925])).

tff(c_277947,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_277943])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ! [A_28,B_29] : v1_relat_1(k2_zfmisc_1(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_231,plain,(
    ! [B_105,A_106] :
      ( v1_relat_1(B_105)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(A_106))
      | ~ v1_relat_1(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_237,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_94,c_231])).

tff(c_244,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_237])).

tff(c_20,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_153,plain,(
    ! [B_95,A_96] :
      ( ~ r1_tarski(B_95,A_96)
      | ~ r2_hidden(A_96,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_158,plain,(
    ! [A_97] :
      ( ~ r1_tarski(A_97,'#skF_1'(A_97))
      | v1_xboole_0(A_97) ) ),
    inference(resolution,[status(thm)],[c_4,c_153])).

tff(c_163,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_158])).

tff(c_90,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_140031,plain,(
    ! [C_1874,A_1875,B_1876] :
      ( v4_relat_1(C_1874,A_1875)
      | ~ m1_subset_1(C_1874,k1_zfmisc_1(k2_zfmisc_1(A_1875,B_1876))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_140050,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_140031])).

tff(c_140161,plain,(
    ! [C_1889,A_1890,B_1891] :
      ( v1_xboole_0(C_1889)
      | ~ m1_subset_1(C_1889,k1_zfmisc_1(k2_zfmisc_1(A_1890,B_1891)))
      | ~ v1_xboole_0(A_1890) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_140179,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_94,c_140161])).

tff(c_140183,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_140179])).

tff(c_88,plain,(
    m1_subset_1('#skF_8','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_240,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_90,c_231])).

tff(c_247,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_240])).

tff(c_92,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_96,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_140697,plain,(
    ! [A_1919,B_1920,C_1921] :
      ( k1_relset_1(A_1919,B_1920,C_1921) = k1_relat_1(C_1921)
      | ~ m1_subset_1(C_1921,k1_zfmisc_1(k2_zfmisc_1(A_1919,B_1920))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_140718,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_94,c_140697])).

tff(c_141208,plain,(
    ! [B_1955,A_1956,C_1957] :
      ( k1_xboole_0 = B_1955
      | k1_relset_1(A_1956,B_1955,C_1957) = A_1956
      | ~ v1_funct_2(C_1957,A_1956,B_1955)
      | ~ m1_subset_1(C_1957,k1_zfmisc_1(k2_zfmisc_1(A_1956,B_1955))) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_141221,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_94,c_141208])).

tff(c_141234,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_140718,c_141221])).

tff(c_141238,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_141234])).

tff(c_98,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_28,plain,(
    ! [A_16,B_17] :
      ( r2_hidden(A_16,B_17)
      | v1_xboole_0(B_17)
      | ~ m1_subset_1(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_141701,plain,(
    ! [B_1974,C_1975,A_1976] :
      ( k1_funct_1(k5_relat_1(B_1974,C_1975),A_1976) = k1_funct_1(C_1975,k1_funct_1(B_1974,A_1976))
      | ~ r2_hidden(A_1976,k1_relat_1(B_1974))
      | ~ v1_funct_1(C_1975)
      | ~ v1_relat_1(C_1975)
      | ~ v1_funct_1(B_1974)
      | ~ v1_relat_1(B_1974) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_152953,plain,(
    ! [B_2303,C_2304,A_2305] :
      ( k1_funct_1(k5_relat_1(B_2303,C_2304),A_2305) = k1_funct_1(C_2304,k1_funct_1(B_2303,A_2305))
      | ~ v1_funct_1(C_2304)
      | ~ v1_relat_1(C_2304)
      | ~ v1_funct_1(B_2303)
      | ~ v1_relat_1(B_2303)
      | v1_xboole_0(k1_relat_1(B_2303))
      | ~ m1_subset_1(A_2305,k1_relat_1(B_2303)) ) ),
    inference(resolution,[status(thm)],[c_28,c_141701])).

tff(c_152981,plain,(
    ! [C_2304,A_2305] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_2304),A_2305) = k1_funct_1(C_2304,k1_funct_1('#skF_6',A_2305))
      | ~ v1_funct_1(C_2304)
      | ~ v1_relat_1(C_2304)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | v1_xboole_0(k1_relat_1('#skF_6'))
      | ~ m1_subset_1(A_2305,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141238,c_152953])).

tff(c_152995,plain,(
    ! [C_2304,A_2305] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_2304),A_2305) = k1_funct_1(C_2304,k1_funct_1('#skF_6',A_2305))
      | ~ v1_funct_1(C_2304)
      | ~ v1_relat_1(C_2304)
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_2305,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141238,c_244,c_98,c_152981])).

tff(c_152996,plain,(
    ! [C_2304,A_2305] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_2304),A_2305) = k1_funct_1(C_2304,k1_funct_1('#skF_6',A_2305))
      | ~ v1_funct_1(C_2304)
      | ~ v1_relat_1(C_2304)
      | ~ m1_subset_1(A_2305,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_140183,c_152995])).

tff(c_139765,plain,(
    ! [C_1846,B_1847,A_1848] :
      ( v5_relat_1(C_1846,B_1847)
      | ~ m1_subset_1(C_1846,k1_zfmisc_1(k2_zfmisc_1(A_1848,B_1847))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_139784,plain,(
    v5_relat_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_139765])).

tff(c_140719,plain,(
    k1_relset_1('#skF_5','#skF_3','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_90,c_140697])).

tff(c_140489,plain,(
    ! [A_1910,B_1911,C_1912] :
      ( k2_relset_1(A_1910,B_1911,C_1912) = k2_relat_1(C_1912)
      | ~ m1_subset_1(C_1912,k1_zfmisc_1(k2_zfmisc_1(A_1910,B_1911))) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_140507,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_94,c_140489])).

tff(c_86,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_140511,plain,(
    r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140507,c_86])).

tff(c_40,plain,(
    ! [B_26,A_25] :
      ( v5_relat_1(B_26,A_25)
      | ~ r1_tarski(k2_relat_1(B_26),A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_140522,plain,
    ( v5_relat_1('#skF_6',k1_relset_1('#skF_5','#skF_3','#skF_7'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_140511,c_40])).

tff(c_140536,plain,(
    v5_relat_1('#skF_6',k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_140522])).

tff(c_140725,plain,(
    v5_relat_1('#skF_6',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140719,c_140536])).

tff(c_48,plain,(
    ! [B_31,C_33,A_30] :
      ( r2_hidden(k1_funct_1(B_31,C_33),A_30)
      | ~ r2_hidden(C_33,k1_relat_1(B_31))
      | ~ v1_funct_1(B_31)
      | ~ v5_relat_1(B_31,A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_141441,plain,(
    ! [A_1964,B_1965,C_1966] :
      ( k7_partfun1(A_1964,B_1965,C_1966) = k1_funct_1(B_1965,C_1966)
      | ~ r2_hidden(C_1966,k1_relat_1(B_1965))
      | ~ v1_funct_1(B_1965)
      | ~ v5_relat_1(B_1965,A_1964)
      | ~ v1_relat_1(B_1965) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_158054,plain,(
    ! [A_2380,B_2381,B_2382,C_2383] :
      ( k7_partfun1(A_2380,B_2381,k1_funct_1(B_2382,C_2383)) = k1_funct_1(B_2381,k1_funct_1(B_2382,C_2383))
      | ~ v1_funct_1(B_2381)
      | ~ v5_relat_1(B_2381,A_2380)
      | ~ v1_relat_1(B_2381)
      | ~ r2_hidden(C_2383,k1_relat_1(B_2382))
      | ~ v1_funct_1(B_2382)
      | ~ v5_relat_1(B_2382,k1_relat_1(B_2381))
      | ~ v1_relat_1(B_2382) ) ),
    inference(resolution,[status(thm)],[c_48,c_141441])).

tff(c_268343,plain,(
    ! [A_3499,B_3500,B_3501,A_3502] :
      ( k7_partfun1(A_3499,B_3500,k1_funct_1(B_3501,A_3502)) = k1_funct_1(B_3500,k1_funct_1(B_3501,A_3502))
      | ~ v1_funct_1(B_3500)
      | ~ v5_relat_1(B_3500,A_3499)
      | ~ v1_relat_1(B_3500)
      | ~ v1_funct_1(B_3501)
      | ~ v5_relat_1(B_3501,k1_relat_1(B_3500))
      | ~ v1_relat_1(B_3501)
      | v1_xboole_0(k1_relat_1(B_3501))
      | ~ m1_subset_1(A_3502,k1_relat_1(B_3501)) ) ),
    inference(resolution,[status(thm)],[c_28,c_158054])).

tff(c_268546,plain,(
    ! [A_3499,A_3502] :
      ( k7_partfun1(A_3499,'#skF_7',k1_funct_1('#skF_6',A_3502)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',A_3502))
      | ~ v1_funct_1('#skF_7')
      | ~ v5_relat_1('#skF_7',A_3499)
      | ~ v1_relat_1('#skF_7')
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | v1_xboole_0(k1_relat_1('#skF_6'))
      | ~ m1_subset_1(A_3502,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_140725,c_268343])).

tff(c_268665,plain,(
    ! [A_3499,A_3502] :
      ( k7_partfun1(A_3499,'#skF_7',k1_funct_1('#skF_6',A_3502)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',A_3502))
      | ~ v5_relat_1('#skF_7',A_3499)
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_3502,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141238,c_141238,c_244,c_98,c_247,c_92,c_268546])).

tff(c_275789,plain,(
    ! [A_3539,A_3540] :
      ( k7_partfun1(A_3539,'#skF_7',k1_funct_1('#skF_6',A_3540)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',A_3540))
      | ~ v5_relat_1('#skF_7',A_3539)
      | ~ m1_subset_1(A_3540,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_140183,c_268665])).

tff(c_140726,plain,(
    r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140719,c_140511])).

tff(c_141842,plain,(
    ! [F_1990,B_1992,E_1991,C_1993,A_1989,D_1994] :
      ( k1_partfun1(A_1989,B_1992,C_1993,D_1994,E_1991,F_1990) = k5_relat_1(E_1991,F_1990)
      | ~ m1_subset_1(F_1990,k1_zfmisc_1(k2_zfmisc_1(C_1993,D_1994)))
      | ~ v1_funct_1(F_1990)
      | ~ m1_subset_1(E_1991,k1_zfmisc_1(k2_zfmisc_1(A_1989,B_1992)))
      | ~ v1_funct_1(E_1991) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_141853,plain,(
    ! [A_1989,B_1992,E_1991] :
      ( k1_partfun1(A_1989,B_1992,'#skF_5','#skF_3',E_1991,'#skF_7') = k5_relat_1(E_1991,'#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_1991,k1_zfmisc_1(k2_zfmisc_1(A_1989,B_1992)))
      | ~ v1_funct_1(E_1991) ) ),
    inference(resolution,[status(thm)],[c_90,c_141842])).

tff(c_141898,plain,(
    ! [A_2000,B_2001,E_2002] :
      ( k1_partfun1(A_2000,B_2001,'#skF_5','#skF_3',E_2002,'#skF_7') = k5_relat_1(E_2002,'#skF_7')
      | ~ m1_subset_1(E_2002,k1_zfmisc_1(k2_zfmisc_1(A_2000,B_2001)))
      | ~ v1_funct_1(E_2002) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_141853])).

tff(c_141911,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_3','#skF_6','#skF_7') = k5_relat_1('#skF_6','#skF_7')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_94,c_141898])).

tff(c_141924,plain,(
    k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_3','#skF_6','#skF_7') = k5_relat_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_141911])).

tff(c_139783,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_94,c_139765])).

tff(c_142015,plain,(
    ! [D_2015,E_2012,A_2014,B_2016,C_2013] :
      ( k1_partfun1(A_2014,B_2016,B_2016,C_2013,D_2015,E_2012) = k8_funct_2(A_2014,B_2016,C_2013,D_2015,E_2012)
      | k1_xboole_0 = B_2016
      | ~ r1_tarski(k2_relset_1(A_2014,B_2016,D_2015),k1_relset_1(B_2016,C_2013,E_2012))
      | ~ m1_subset_1(E_2012,k1_zfmisc_1(k2_zfmisc_1(B_2016,C_2013)))
      | ~ v1_funct_1(E_2012)
      | ~ m1_subset_1(D_2015,k1_zfmisc_1(k2_zfmisc_1(A_2014,B_2016)))
      | ~ v1_funct_2(D_2015,A_2014,B_2016)
      | ~ v1_funct_1(D_2015) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_142036,plain,(
    ! [C_2013,E_2012] :
      ( k1_partfun1('#skF_4','#skF_5','#skF_5',C_2013,'#skF_6',E_2012) = k8_funct_2('#skF_4','#skF_5',C_2013,'#skF_6',E_2012)
      | k1_xboole_0 = '#skF_5'
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_5',C_2013,E_2012))
      | ~ m1_subset_1(E_2012,k1_zfmisc_1(k2_zfmisc_1('#skF_5',C_2013)))
      | ~ v1_funct_1(E_2012)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140507,c_142015])).

tff(c_142056,plain,(
    ! [C_2013,E_2012] :
      ( k1_partfun1('#skF_4','#skF_5','#skF_5',C_2013,'#skF_6',E_2012) = k8_funct_2('#skF_4','#skF_5',C_2013,'#skF_6',E_2012)
      | k1_xboole_0 = '#skF_5'
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_5',C_2013,E_2012))
      | ~ m1_subset_1(E_2012,k1_zfmisc_1(k2_zfmisc_1('#skF_5',C_2013)))
      | ~ v1_funct_1(E_2012) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_94,c_142036])).

tff(c_257702,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_142056])).

tff(c_42,plain,(
    ! [B_26,A_25] :
      ( r1_tarski(k2_relat_1(B_26),A_25)
      | ~ v5_relat_1(B_26,A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_32,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_26,plain,(
    ! [B_15] : k2_zfmisc_1(k1_xboole_0,B_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_140177,plain,(
    ! [C_1889] :
      ( v1_xboole_0(C_1889)
      | ~ m1_subset_1(C_1889,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_140161])).

tff(c_140184,plain,(
    ! [C_1892] :
      ( v1_xboole_0(C_1892)
      | ~ m1_subset_1(C_1892,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_140177])).

tff(c_140200,plain,(
    ! [A_1893] :
      ( v1_xboole_0(A_1893)
      | ~ r1_tarski(A_1893,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_32,c_140184])).

tff(c_140221,plain,(
    ! [B_26] :
      ( v1_xboole_0(k2_relat_1(B_26))
      | ~ v5_relat_1(B_26,k1_xboole_0)
      | ~ v1_relat_1(B_26) ) ),
    inference(resolution,[status(thm)],[c_42,c_140200])).

tff(c_18,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_139701,plain,(
    ! [B_1836,A_1837] :
      ( v5_relat_1(B_1836,A_1837)
      | ~ r1_tarski(k2_relat_1(B_1836),A_1837)
      | ~ v1_relat_1(B_1836) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_139711,plain,(
    ! [B_1836] :
      ( v5_relat_1(B_1836,k2_relat_1(B_1836))
      | ~ v1_relat_1(B_1836) ) ),
    inference(resolution,[status(thm)],[c_18,c_139701])).

tff(c_141071,plain,(
    ! [B_1943,C_1944,A_1945] :
      ( r2_hidden(k1_funct_1(B_1943,C_1944),A_1945)
      | ~ r2_hidden(C_1944,k1_relat_1(B_1943))
      | ~ v1_funct_1(B_1943)
      | ~ v5_relat_1(B_1943,A_1945)
      | ~ v1_relat_1(B_1943) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_146050,plain,(
    ! [A_2149,C_2150,B_2151] :
      ( ~ v1_xboole_0(A_2149)
      | ~ r2_hidden(C_2150,k1_relat_1(B_2151))
      | ~ v1_funct_1(B_2151)
      | ~ v5_relat_1(B_2151,A_2149)
      | ~ v1_relat_1(B_2151) ) ),
    inference(resolution,[status(thm)],[c_141071,c_2])).

tff(c_146071,plain,(
    ! [A_2149,C_2150] :
      ( ~ v1_xboole_0(A_2149)
      | ~ r2_hidden(C_2150,'#skF_4')
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',A_2149)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141238,c_146050])).

tff(c_146095,plain,(
    ! [A_2149,C_2150] :
      ( ~ v1_xboole_0(A_2149)
      | ~ r2_hidden(C_2150,'#skF_4')
      | ~ v5_relat_1('#skF_6',A_2149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_98,c_146071])).

tff(c_146154,plain,(
    ! [A_2155] :
      ( ~ v1_xboole_0(A_2155)
      | ~ v5_relat_1('#skF_6',A_2155) ) ),
    inference(splitLeft,[status(thm)],[c_146095])).

tff(c_146172,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_139711,c_146154])).

tff(c_146179,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_146172])).

tff(c_146188,plain,
    ( ~ v5_relat_1('#skF_6',k1_xboole_0)
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_140221,c_146179])).

tff(c_146197,plain,(
    ~ v5_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_146188])).

tff(c_257878,plain,(
    ~ v5_relat_1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_257702,c_146197])).

tff(c_257966,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139783,c_257878])).

tff(c_261269,plain,(
    ! [C_3472,E_3473] :
      ( k1_partfun1('#skF_4','#skF_5','#skF_5',C_3472,'#skF_6',E_3473) = k8_funct_2('#skF_4','#skF_5',C_3472,'#skF_6',E_3473)
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_5',C_3472,E_3473))
      | ~ m1_subset_1(E_3473,k1_zfmisc_1(k2_zfmisc_1('#skF_5',C_3472)))
      | ~ v1_funct_1(E_3473) ) ),
    inference(splitRight,[status(thm)],[c_142056])).

tff(c_261293,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_3','#skF_6','#skF_7') = k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7')
    | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_7'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
    | ~ v1_funct_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_140719,c_261269])).

tff(c_261310,plain,(
    k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7') = k5_relat_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_140726,c_141924,c_261293])).

tff(c_82,plain,(
    k7_partfun1('#skF_3','#skF_7',k1_funct_1('#skF_6','#skF_8')) != k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_264666,plain,(
    k7_partfun1('#skF_3','#skF_7',k1_funct_1('#skF_6','#skF_8')) != k1_funct_1(k5_relat_1('#skF_6','#skF_7'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_261310,c_82])).

tff(c_275799,plain,
    ( k1_funct_1(k5_relat_1('#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | ~ v5_relat_1('#skF_7','#skF_3')
    | ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_275789,c_264666])).

tff(c_275820,plain,(
    k1_funct_1(k5_relat_1('#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_139784,c_275799])).

tff(c_277193,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_152996,c_275820])).

tff(c_277200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_247,c_92,c_277193])).

tff(c_277202,plain,(
    ! [C_3558] : ~ r2_hidden(C_3558,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_146095])).

tff(c_277226,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_277202])).

tff(c_277237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_140183,c_277226])).

tff(c_277238,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_141234])).

tff(c_38,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k1_relat_1(B_24),A_23)
      | ~ v4_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_140222,plain,(
    ! [B_24] :
      ( v1_xboole_0(k1_relat_1(B_24))
      | ~ v4_relat_1(B_24,k1_xboole_0)
      | ~ v1_relat_1(B_24) ) ),
    inference(resolution,[status(thm)],[c_38,c_140200])).

tff(c_293,plain,(
    ! [A_111,B_112] :
      ( r2_hidden('#skF_2'(A_111,B_112),A_111)
      | r1_tarski(A_111,B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_315,plain,(
    ! [A_114,B_115] :
      ( ~ v1_xboole_0(A_114)
      | r1_tarski(A_114,B_115) ) ),
    inference(resolution,[status(thm)],[c_293,c_2])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( B_12 = A_11
      | ~ r1_tarski(B_12,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_362,plain,(
    ! [B_118,A_119] :
      ( B_118 = A_119
      | ~ r1_tarski(B_118,A_119)
      | ~ v1_xboole_0(A_119) ) ),
    inference(resolution,[status(thm)],[c_315,c_14])).

tff(c_382,plain,
    ( k2_relset_1('#skF_4','#skF_5','#skF_6') = k1_relset_1('#skF_5','#skF_3','#skF_7')
    | ~ v1_xboole_0(k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(resolution,[status(thm)],[c_86,c_362])).

tff(c_139712,plain,(
    ~ v1_xboole_0(k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_382])).

tff(c_140727,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140719,c_139712])).

tff(c_140758,plain,
    ( ~ v4_relat_1('#skF_7',k1_xboole_0)
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_140222,c_140727])).

tff(c_140764,plain,(
    ~ v4_relat_1('#skF_7',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_140758])).

tff(c_277248,plain,(
    ~ v4_relat_1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_277238,c_140764])).

tff(c_277289,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140050,c_277248])).

tff(c_277291,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_140179])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_277337,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_277291,c_12])).

tff(c_277347,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_277337])).

tff(c_277349,plain,(
    v1_xboole_0(k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_382])).

tff(c_277368,plain,(
    k1_relset_1('#skF_5','#skF_3','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_277349,c_12])).

tff(c_277406,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_277368,c_86])).

tff(c_330,plain,(
    ! [B_115,A_114] :
      ( B_115 = A_114
      | ~ r1_tarski(B_115,A_114)
      | ~ v1_xboole_0(A_114) ) ),
    inference(resolution,[status(thm)],[c_315,c_14])).

tff(c_277420,plain,
    ( k2_relset_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_277406,c_330])).

tff(c_277432,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_277420])).

tff(c_278095,plain,(
    ! [A_3628,B_3629,C_3630] :
      ( k2_relset_1(A_3628,B_3629,C_3630) = k2_relat_1(C_3630)
      | ~ m1_subset_1(C_3630,k1_zfmisc_1(k2_zfmisc_1(A_3628,B_3629))) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_278102,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_94,c_278095])).

tff(c_278114,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_277432,c_278102])).

tff(c_301,plain,(
    ! [A_111,B_112] :
      ( ~ v1_xboole_0(A_111)
      | r1_tarski(A_111,B_112) ) ),
    inference(resolution,[status(thm)],[c_293,c_2])).

tff(c_139710,plain,(
    ! [B_1836,B_112] :
      ( v5_relat_1(B_1836,B_112)
      | ~ v1_relat_1(B_1836)
      | ~ v1_xboole_0(k2_relat_1(B_1836)) ) ),
    inference(resolution,[status(thm)],[c_301,c_139701])).

tff(c_278118,plain,(
    ! [B_112] :
      ( v5_relat_1('#skF_6',B_112)
      | ~ v1_relat_1('#skF_6')
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_278114,c_139710])).

tff(c_278131,plain,(
    ! [B_112] : v5_relat_1('#skF_6',B_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_244,c_278118])).

tff(c_277959,plain,(
    ! [A_3619,B_3620,C_3621] :
      ( k1_relset_1(A_3619,B_3620,C_3621) = k1_relat_1(C_3621)
      | ~ m1_subset_1(C_3621,k1_zfmisc_1(k2_zfmisc_1(A_3619,B_3620))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_277977,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_94,c_277959])).

tff(c_278556,plain,(
    ! [B_3658,A_3659,C_3660] :
      ( k1_xboole_0 = B_3658
      | k1_relset_1(A_3659,B_3658,C_3660) = A_3659
      | ~ v1_funct_2(C_3660,A_3659,B_3658)
      | ~ m1_subset_1(C_3660,k1_zfmisc_1(k2_zfmisc_1(A_3659,B_3658))) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_278563,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_94,c_278556])).

tff(c_278576,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_277977,c_278563])).

tff(c_278580,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_278576])).

tff(c_278271,plain,(
    ! [B_3638,C_3639,A_3640] :
      ( r2_hidden(k1_funct_1(B_3638,C_3639),A_3640)
      | ~ r2_hidden(C_3639,k1_relat_1(B_3638))
      | ~ v1_funct_1(B_3638)
      | ~ v5_relat_1(B_3638,A_3640)
      | ~ v1_relat_1(B_3638) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_285657,plain,(
    ! [A_3925,C_3926,B_3927] :
      ( ~ v1_xboole_0(A_3925)
      | ~ r2_hidden(C_3926,k1_relat_1(B_3927))
      | ~ v1_funct_1(B_3927)
      | ~ v5_relat_1(B_3927,A_3925)
      | ~ v1_relat_1(B_3927) ) ),
    inference(resolution,[status(thm)],[c_278271,c_2])).

tff(c_285682,plain,(
    ! [A_3925,C_3926] :
      ( ~ v1_xboole_0(A_3925)
      | ~ r2_hidden(C_3926,'#skF_4')
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',A_3925)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_278580,c_285657])).

tff(c_285712,plain,(
    ! [A_3925,C_3926] :
      ( ~ v1_xboole_0(A_3925)
      | ~ r2_hidden(C_3926,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_278131,c_98,c_285682])).

tff(c_285725,plain,(
    ! [C_3928] : ~ r2_hidden(C_3928,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_285712])).

tff(c_285749,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_285725])).

tff(c_285760,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_277947,c_285749])).

tff(c_285761,plain,(
    ! [A_3925] : ~ v1_xboole_0(A_3925) ),
    inference(splitRight,[status(thm)],[c_285712])).

tff(c_285793,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_285761,c_163])).

tff(c_285794,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_278576])).

tff(c_285834,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_285794,c_163])).

tff(c_285843,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_285834])).

tff(c_285845,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_277943])).

tff(c_285891,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_285845,c_12])).

tff(c_285901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_285891])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:50:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 59.04/47.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 59.04/47.18  
% 59.04/47.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 59.15/47.19  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2
% 59.15/47.19  
% 59.15/47.19  %Foreground sorts:
% 59.15/47.19  
% 59.15/47.19  
% 59.15/47.19  %Background operators:
% 59.15/47.19  
% 59.15/47.19  
% 59.15/47.19  %Foreground operators:
% 59.15/47.19  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 59.15/47.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 59.15/47.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 59.15/47.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 59.15/47.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 59.15/47.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 59.15/47.19  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 59.15/47.19  tff('#skF_7', type, '#skF_7': $i).
% 59.15/47.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 59.15/47.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 59.15/47.19  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 59.15/47.19  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 59.15/47.19  tff('#skF_5', type, '#skF_5': $i).
% 59.15/47.19  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 59.15/47.19  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 59.15/47.19  tff('#skF_6', type, '#skF_6': $i).
% 59.15/47.19  tff('#skF_3', type, '#skF_3': $i).
% 59.15/47.19  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 59.15/47.19  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 59.15/47.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 59.15/47.19  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 59.15/47.19  tff('#skF_8', type, '#skF_8': $i).
% 59.15/47.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 59.15/47.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 59.15/47.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 59.15/47.19  tff('#skF_4', type, '#skF_4': $i).
% 59.15/47.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 59.15/47.19  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 59.15/47.19  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 59.15/47.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 59.15/47.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 59.15/47.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 59.15/47.19  
% 59.15/47.22  tff(f_222, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_funct_2)).
% 59.15/47.22  tff(f_133, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 59.15/47.22  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 59.15/47.22  tff(f_91, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 59.15/47.22  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 59.15/47.22  tff(f_50, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 59.15/47.22  tff(f_120, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 59.15/47.22  tff(f_126, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 59.15/47.22  tff(f_137, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 59.15/47.22  tff(f_176, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 59.15/47.22  tff(f_62, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 59.15/47.22  tff(f_115, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 59.15/47.22  tff(f_141, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 59.15/47.22  tff(f_85, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 59.15/47.22  tff(f_102, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 59.15/47.22  tff(f_187, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 59.15/47.22  tff(f_197, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 59.15/47.22  tff(f_158, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (r1_tarski(k2_relset_1(A, B, D), k1_relset_1(B, C, E)) => ((B = k1_xboole_0) | (k8_funct_2(A, B, C, D, E) = k1_partfun1(A, B, B, C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_2)).
% 59.15/47.22  tff(f_66, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 59.15/47.22  tff(f_56, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 59.15/47.22  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 59.15/47.22  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 59.15/47.22  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 59.15/47.22  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 59.15/47.22  tff(c_84, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_222])).
% 59.15/47.22  tff(c_100, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_222])).
% 59.15/47.22  tff(c_94, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_222])).
% 59.15/47.22  tff(c_277925, plain, (![C_3615, A_3616, B_3617]: (v1_xboole_0(C_3615) | ~m1_subset_1(C_3615, k1_zfmisc_1(k2_zfmisc_1(A_3616, B_3617))) | ~v1_xboole_0(A_3616))), inference(cnfTransformation, [status(thm)], [f_133])).
% 59.15/47.22  tff(c_277943, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_94, c_277925])).
% 59.15/47.22  tff(c_277947, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_277943])).
% 59.15/47.22  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 59.15/47.22  tff(c_46, plain, (![A_28, B_29]: (v1_relat_1(k2_zfmisc_1(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 59.15/47.22  tff(c_231, plain, (![B_105, A_106]: (v1_relat_1(B_105) | ~m1_subset_1(B_105, k1_zfmisc_1(A_106)) | ~v1_relat_1(A_106))), inference(cnfTransformation, [status(thm)], [f_73])).
% 59.15/47.22  tff(c_237, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_94, c_231])).
% 59.15/47.22  tff(c_244, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_237])).
% 59.15/47.22  tff(c_20, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 59.15/47.22  tff(c_153, plain, (![B_95, A_96]: (~r1_tarski(B_95, A_96) | ~r2_hidden(A_96, B_95))), inference(cnfTransformation, [status(thm)], [f_120])).
% 59.15/47.22  tff(c_158, plain, (![A_97]: (~r1_tarski(A_97, '#skF_1'(A_97)) | v1_xboole_0(A_97))), inference(resolution, [status(thm)], [c_4, c_153])).
% 59.15/47.22  tff(c_163, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_158])).
% 59.15/47.22  tff(c_90, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_222])).
% 59.15/47.22  tff(c_140031, plain, (![C_1874, A_1875, B_1876]: (v4_relat_1(C_1874, A_1875) | ~m1_subset_1(C_1874, k1_zfmisc_1(k2_zfmisc_1(A_1875, B_1876))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 59.15/47.22  tff(c_140050, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_90, c_140031])).
% 59.15/47.22  tff(c_140161, plain, (![C_1889, A_1890, B_1891]: (v1_xboole_0(C_1889) | ~m1_subset_1(C_1889, k1_zfmisc_1(k2_zfmisc_1(A_1890, B_1891))) | ~v1_xboole_0(A_1890))), inference(cnfTransformation, [status(thm)], [f_133])).
% 59.15/47.22  tff(c_140179, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_94, c_140161])).
% 59.15/47.22  tff(c_140183, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_140179])).
% 59.15/47.22  tff(c_88, plain, (m1_subset_1('#skF_8', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_222])).
% 59.15/47.22  tff(c_240, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_90, c_231])).
% 59.15/47.22  tff(c_247, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_240])).
% 59.15/47.22  tff(c_92, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_222])).
% 59.15/47.22  tff(c_96, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_222])).
% 59.15/47.22  tff(c_140697, plain, (![A_1919, B_1920, C_1921]: (k1_relset_1(A_1919, B_1920, C_1921)=k1_relat_1(C_1921) | ~m1_subset_1(C_1921, k1_zfmisc_1(k2_zfmisc_1(A_1919, B_1920))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 59.15/47.22  tff(c_140718, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_94, c_140697])).
% 59.15/47.22  tff(c_141208, plain, (![B_1955, A_1956, C_1957]: (k1_xboole_0=B_1955 | k1_relset_1(A_1956, B_1955, C_1957)=A_1956 | ~v1_funct_2(C_1957, A_1956, B_1955) | ~m1_subset_1(C_1957, k1_zfmisc_1(k2_zfmisc_1(A_1956, B_1955))))), inference(cnfTransformation, [status(thm)], [f_176])).
% 59.15/47.22  tff(c_141221, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_94, c_141208])).
% 59.15/47.22  tff(c_141234, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_140718, c_141221])).
% 59.15/47.22  tff(c_141238, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_141234])).
% 59.15/47.22  tff(c_98, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_222])).
% 59.15/47.22  tff(c_28, plain, (![A_16, B_17]: (r2_hidden(A_16, B_17) | v1_xboole_0(B_17) | ~m1_subset_1(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 59.15/47.22  tff(c_141701, plain, (![B_1974, C_1975, A_1976]: (k1_funct_1(k5_relat_1(B_1974, C_1975), A_1976)=k1_funct_1(C_1975, k1_funct_1(B_1974, A_1976)) | ~r2_hidden(A_1976, k1_relat_1(B_1974)) | ~v1_funct_1(C_1975) | ~v1_relat_1(C_1975) | ~v1_funct_1(B_1974) | ~v1_relat_1(B_1974))), inference(cnfTransformation, [status(thm)], [f_115])).
% 59.15/47.22  tff(c_152953, plain, (![B_2303, C_2304, A_2305]: (k1_funct_1(k5_relat_1(B_2303, C_2304), A_2305)=k1_funct_1(C_2304, k1_funct_1(B_2303, A_2305)) | ~v1_funct_1(C_2304) | ~v1_relat_1(C_2304) | ~v1_funct_1(B_2303) | ~v1_relat_1(B_2303) | v1_xboole_0(k1_relat_1(B_2303)) | ~m1_subset_1(A_2305, k1_relat_1(B_2303)))), inference(resolution, [status(thm)], [c_28, c_141701])).
% 59.15/47.22  tff(c_152981, plain, (![C_2304, A_2305]: (k1_funct_1(k5_relat_1('#skF_6', C_2304), A_2305)=k1_funct_1(C_2304, k1_funct_1('#skF_6', A_2305)) | ~v1_funct_1(C_2304) | ~v1_relat_1(C_2304) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | v1_xboole_0(k1_relat_1('#skF_6')) | ~m1_subset_1(A_2305, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_141238, c_152953])).
% 59.15/47.22  tff(c_152995, plain, (![C_2304, A_2305]: (k1_funct_1(k5_relat_1('#skF_6', C_2304), A_2305)=k1_funct_1(C_2304, k1_funct_1('#skF_6', A_2305)) | ~v1_funct_1(C_2304) | ~v1_relat_1(C_2304) | v1_xboole_0('#skF_4') | ~m1_subset_1(A_2305, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_141238, c_244, c_98, c_152981])).
% 59.15/47.22  tff(c_152996, plain, (![C_2304, A_2305]: (k1_funct_1(k5_relat_1('#skF_6', C_2304), A_2305)=k1_funct_1(C_2304, k1_funct_1('#skF_6', A_2305)) | ~v1_funct_1(C_2304) | ~v1_relat_1(C_2304) | ~m1_subset_1(A_2305, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_140183, c_152995])).
% 59.15/47.22  tff(c_139765, plain, (![C_1846, B_1847, A_1848]: (v5_relat_1(C_1846, B_1847) | ~m1_subset_1(C_1846, k1_zfmisc_1(k2_zfmisc_1(A_1848, B_1847))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 59.15/47.22  tff(c_139784, plain, (v5_relat_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_90, c_139765])).
% 59.15/47.22  tff(c_140719, plain, (k1_relset_1('#skF_5', '#skF_3', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_90, c_140697])).
% 59.15/47.22  tff(c_140489, plain, (![A_1910, B_1911, C_1912]: (k2_relset_1(A_1910, B_1911, C_1912)=k2_relat_1(C_1912) | ~m1_subset_1(C_1912, k1_zfmisc_1(k2_zfmisc_1(A_1910, B_1911))))), inference(cnfTransformation, [status(thm)], [f_141])).
% 59.15/47.22  tff(c_140507, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_94, c_140489])).
% 59.15/47.22  tff(c_86, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_222])).
% 59.15/47.22  tff(c_140511, plain, (r1_tarski(k2_relat_1('#skF_6'), k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_140507, c_86])).
% 59.15/47.22  tff(c_40, plain, (![B_26, A_25]: (v5_relat_1(B_26, A_25) | ~r1_tarski(k2_relat_1(B_26), A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_85])).
% 59.15/47.22  tff(c_140522, plain, (v5_relat_1('#skF_6', k1_relset_1('#skF_5', '#skF_3', '#skF_7')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_140511, c_40])).
% 59.15/47.22  tff(c_140536, plain, (v5_relat_1('#skF_6', k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_244, c_140522])).
% 59.15/47.22  tff(c_140725, plain, (v5_relat_1('#skF_6', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_140719, c_140536])).
% 59.15/47.22  tff(c_48, plain, (![B_31, C_33, A_30]: (r2_hidden(k1_funct_1(B_31, C_33), A_30) | ~r2_hidden(C_33, k1_relat_1(B_31)) | ~v1_funct_1(B_31) | ~v5_relat_1(B_31, A_30) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_102])).
% 59.15/47.22  tff(c_141441, plain, (![A_1964, B_1965, C_1966]: (k7_partfun1(A_1964, B_1965, C_1966)=k1_funct_1(B_1965, C_1966) | ~r2_hidden(C_1966, k1_relat_1(B_1965)) | ~v1_funct_1(B_1965) | ~v5_relat_1(B_1965, A_1964) | ~v1_relat_1(B_1965))), inference(cnfTransformation, [status(thm)], [f_187])).
% 59.15/47.22  tff(c_158054, plain, (![A_2380, B_2381, B_2382, C_2383]: (k7_partfun1(A_2380, B_2381, k1_funct_1(B_2382, C_2383))=k1_funct_1(B_2381, k1_funct_1(B_2382, C_2383)) | ~v1_funct_1(B_2381) | ~v5_relat_1(B_2381, A_2380) | ~v1_relat_1(B_2381) | ~r2_hidden(C_2383, k1_relat_1(B_2382)) | ~v1_funct_1(B_2382) | ~v5_relat_1(B_2382, k1_relat_1(B_2381)) | ~v1_relat_1(B_2382))), inference(resolution, [status(thm)], [c_48, c_141441])).
% 59.15/47.22  tff(c_268343, plain, (![A_3499, B_3500, B_3501, A_3502]: (k7_partfun1(A_3499, B_3500, k1_funct_1(B_3501, A_3502))=k1_funct_1(B_3500, k1_funct_1(B_3501, A_3502)) | ~v1_funct_1(B_3500) | ~v5_relat_1(B_3500, A_3499) | ~v1_relat_1(B_3500) | ~v1_funct_1(B_3501) | ~v5_relat_1(B_3501, k1_relat_1(B_3500)) | ~v1_relat_1(B_3501) | v1_xboole_0(k1_relat_1(B_3501)) | ~m1_subset_1(A_3502, k1_relat_1(B_3501)))), inference(resolution, [status(thm)], [c_28, c_158054])).
% 59.15/47.22  tff(c_268546, plain, (![A_3499, A_3502]: (k7_partfun1(A_3499, '#skF_7', k1_funct_1('#skF_6', A_3502))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', A_3502)) | ~v1_funct_1('#skF_7') | ~v5_relat_1('#skF_7', A_3499) | ~v1_relat_1('#skF_7') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | v1_xboole_0(k1_relat_1('#skF_6')) | ~m1_subset_1(A_3502, k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_140725, c_268343])).
% 59.15/47.22  tff(c_268665, plain, (![A_3499, A_3502]: (k7_partfun1(A_3499, '#skF_7', k1_funct_1('#skF_6', A_3502))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', A_3502)) | ~v5_relat_1('#skF_7', A_3499) | v1_xboole_0('#skF_4') | ~m1_subset_1(A_3502, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_141238, c_141238, c_244, c_98, c_247, c_92, c_268546])).
% 59.15/47.22  tff(c_275789, plain, (![A_3539, A_3540]: (k7_partfun1(A_3539, '#skF_7', k1_funct_1('#skF_6', A_3540))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', A_3540)) | ~v5_relat_1('#skF_7', A_3539) | ~m1_subset_1(A_3540, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_140183, c_268665])).
% 59.15/47.22  tff(c_140726, plain, (r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_140719, c_140511])).
% 59.15/47.22  tff(c_141842, plain, (![F_1990, B_1992, E_1991, C_1993, A_1989, D_1994]: (k1_partfun1(A_1989, B_1992, C_1993, D_1994, E_1991, F_1990)=k5_relat_1(E_1991, F_1990) | ~m1_subset_1(F_1990, k1_zfmisc_1(k2_zfmisc_1(C_1993, D_1994))) | ~v1_funct_1(F_1990) | ~m1_subset_1(E_1991, k1_zfmisc_1(k2_zfmisc_1(A_1989, B_1992))) | ~v1_funct_1(E_1991))), inference(cnfTransformation, [status(thm)], [f_197])).
% 59.15/47.22  tff(c_141853, plain, (![A_1989, B_1992, E_1991]: (k1_partfun1(A_1989, B_1992, '#skF_5', '#skF_3', E_1991, '#skF_7')=k5_relat_1(E_1991, '#skF_7') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_1991, k1_zfmisc_1(k2_zfmisc_1(A_1989, B_1992))) | ~v1_funct_1(E_1991))), inference(resolution, [status(thm)], [c_90, c_141842])).
% 59.15/47.22  tff(c_141898, plain, (![A_2000, B_2001, E_2002]: (k1_partfun1(A_2000, B_2001, '#skF_5', '#skF_3', E_2002, '#skF_7')=k5_relat_1(E_2002, '#skF_7') | ~m1_subset_1(E_2002, k1_zfmisc_1(k2_zfmisc_1(A_2000, B_2001))) | ~v1_funct_1(E_2002))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_141853])).
% 59.15/47.22  tff(c_141911, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_3', '#skF_6', '#skF_7')=k5_relat_1('#skF_6', '#skF_7') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_94, c_141898])).
% 59.15/47.22  tff(c_141924, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_3', '#skF_6', '#skF_7')=k5_relat_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_141911])).
% 59.15/47.22  tff(c_139783, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_94, c_139765])).
% 59.15/47.22  tff(c_142015, plain, (![D_2015, E_2012, A_2014, B_2016, C_2013]: (k1_partfun1(A_2014, B_2016, B_2016, C_2013, D_2015, E_2012)=k8_funct_2(A_2014, B_2016, C_2013, D_2015, E_2012) | k1_xboole_0=B_2016 | ~r1_tarski(k2_relset_1(A_2014, B_2016, D_2015), k1_relset_1(B_2016, C_2013, E_2012)) | ~m1_subset_1(E_2012, k1_zfmisc_1(k2_zfmisc_1(B_2016, C_2013))) | ~v1_funct_1(E_2012) | ~m1_subset_1(D_2015, k1_zfmisc_1(k2_zfmisc_1(A_2014, B_2016))) | ~v1_funct_2(D_2015, A_2014, B_2016) | ~v1_funct_1(D_2015))), inference(cnfTransformation, [status(thm)], [f_158])).
% 59.15/47.22  tff(c_142036, plain, (![C_2013, E_2012]: (k1_partfun1('#skF_4', '#skF_5', '#skF_5', C_2013, '#skF_6', E_2012)=k8_funct_2('#skF_4', '#skF_5', C_2013, '#skF_6', E_2012) | k1_xboole_0='#skF_5' | ~r1_tarski(k2_relat_1('#skF_6'), k1_relset_1('#skF_5', C_2013, E_2012)) | ~m1_subset_1(E_2012, k1_zfmisc_1(k2_zfmisc_1('#skF_5', C_2013))) | ~v1_funct_1(E_2012) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_140507, c_142015])).
% 59.15/47.22  tff(c_142056, plain, (![C_2013, E_2012]: (k1_partfun1('#skF_4', '#skF_5', '#skF_5', C_2013, '#skF_6', E_2012)=k8_funct_2('#skF_4', '#skF_5', C_2013, '#skF_6', E_2012) | k1_xboole_0='#skF_5' | ~r1_tarski(k2_relat_1('#skF_6'), k1_relset_1('#skF_5', C_2013, E_2012)) | ~m1_subset_1(E_2012, k1_zfmisc_1(k2_zfmisc_1('#skF_5', C_2013))) | ~v1_funct_1(E_2012))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_94, c_142036])).
% 59.15/47.22  tff(c_257702, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_142056])).
% 59.15/47.22  tff(c_42, plain, (![B_26, A_25]: (r1_tarski(k2_relat_1(B_26), A_25) | ~v5_relat_1(B_26, A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_85])).
% 59.15/47.22  tff(c_32, plain, (![A_18, B_19]: (m1_subset_1(A_18, k1_zfmisc_1(B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 59.15/47.22  tff(c_26, plain, (![B_15]: (k2_zfmisc_1(k1_xboole_0, B_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 59.15/47.22  tff(c_140177, plain, (![C_1889]: (v1_xboole_0(C_1889) | ~m1_subset_1(C_1889, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_140161])).
% 59.15/47.22  tff(c_140184, plain, (![C_1892]: (v1_xboole_0(C_1892) | ~m1_subset_1(C_1892, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_140177])).
% 59.15/47.22  tff(c_140200, plain, (![A_1893]: (v1_xboole_0(A_1893) | ~r1_tarski(A_1893, k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_140184])).
% 59.15/47.22  tff(c_140221, plain, (![B_26]: (v1_xboole_0(k2_relat_1(B_26)) | ~v5_relat_1(B_26, k1_xboole_0) | ~v1_relat_1(B_26))), inference(resolution, [status(thm)], [c_42, c_140200])).
% 59.15/47.22  tff(c_18, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 59.15/47.22  tff(c_139701, plain, (![B_1836, A_1837]: (v5_relat_1(B_1836, A_1837) | ~r1_tarski(k2_relat_1(B_1836), A_1837) | ~v1_relat_1(B_1836))), inference(cnfTransformation, [status(thm)], [f_85])).
% 59.15/47.22  tff(c_139711, plain, (![B_1836]: (v5_relat_1(B_1836, k2_relat_1(B_1836)) | ~v1_relat_1(B_1836))), inference(resolution, [status(thm)], [c_18, c_139701])).
% 59.15/47.22  tff(c_141071, plain, (![B_1943, C_1944, A_1945]: (r2_hidden(k1_funct_1(B_1943, C_1944), A_1945) | ~r2_hidden(C_1944, k1_relat_1(B_1943)) | ~v1_funct_1(B_1943) | ~v5_relat_1(B_1943, A_1945) | ~v1_relat_1(B_1943))), inference(cnfTransformation, [status(thm)], [f_102])).
% 59.15/47.22  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 59.15/47.22  tff(c_146050, plain, (![A_2149, C_2150, B_2151]: (~v1_xboole_0(A_2149) | ~r2_hidden(C_2150, k1_relat_1(B_2151)) | ~v1_funct_1(B_2151) | ~v5_relat_1(B_2151, A_2149) | ~v1_relat_1(B_2151))), inference(resolution, [status(thm)], [c_141071, c_2])).
% 59.15/47.22  tff(c_146071, plain, (![A_2149, C_2150]: (~v1_xboole_0(A_2149) | ~r2_hidden(C_2150, '#skF_4') | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', A_2149) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_141238, c_146050])).
% 59.15/47.22  tff(c_146095, plain, (![A_2149, C_2150]: (~v1_xboole_0(A_2149) | ~r2_hidden(C_2150, '#skF_4') | ~v5_relat_1('#skF_6', A_2149))), inference(demodulation, [status(thm), theory('equality')], [c_244, c_98, c_146071])).
% 59.15/47.22  tff(c_146154, plain, (![A_2155]: (~v1_xboole_0(A_2155) | ~v5_relat_1('#skF_6', A_2155))), inference(splitLeft, [status(thm)], [c_146095])).
% 59.15/47.22  tff(c_146172, plain, (~v1_xboole_0(k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_139711, c_146154])).
% 59.15/47.22  tff(c_146179, plain, (~v1_xboole_0(k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_244, c_146172])).
% 59.15/47.22  tff(c_146188, plain, (~v5_relat_1('#skF_6', k1_xboole_0) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_140221, c_146179])).
% 59.15/47.22  tff(c_146197, plain, (~v5_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_244, c_146188])).
% 59.15/47.22  tff(c_257878, plain, (~v5_relat_1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_257702, c_146197])).
% 59.15/47.22  tff(c_257966, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139783, c_257878])).
% 59.15/47.22  tff(c_261269, plain, (![C_3472, E_3473]: (k1_partfun1('#skF_4', '#skF_5', '#skF_5', C_3472, '#skF_6', E_3473)=k8_funct_2('#skF_4', '#skF_5', C_3472, '#skF_6', E_3473) | ~r1_tarski(k2_relat_1('#skF_6'), k1_relset_1('#skF_5', C_3472, E_3473)) | ~m1_subset_1(E_3473, k1_zfmisc_1(k2_zfmisc_1('#skF_5', C_3472))) | ~v1_funct_1(E_3473))), inference(splitRight, [status(thm)], [c_142056])).
% 59.15/47.22  tff(c_261293, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_3', '#skF_6', '#skF_7')=k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7') | ~r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_7')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_140719, c_261269])).
% 59.15/47.22  tff(c_261310, plain, (k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7')=k5_relat_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_140726, c_141924, c_261293])).
% 59.15/47.22  tff(c_82, plain, (k7_partfun1('#skF_3', '#skF_7', k1_funct_1('#skF_6', '#skF_8'))!=k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_222])).
% 59.15/47.22  tff(c_264666, plain, (k7_partfun1('#skF_3', '#skF_7', k1_funct_1('#skF_6', '#skF_8'))!=k1_funct_1(k5_relat_1('#skF_6', '#skF_7'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_261310, c_82])).
% 59.15/47.22  tff(c_275799, plain, (k1_funct_1(k5_relat_1('#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~v5_relat_1('#skF_7', '#skF_3') | ~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_275789, c_264666])).
% 59.15/47.22  tff(c_275820, plain, (k1_funct_1(k5_relat_1('#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_139784, c_275799])).
% 59.15/47.22  tff(c_277193, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_152996, c_275820])).
% 59.15/47.22  tff(c_277200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_247, c_92, c_277193])).
% 59.15/47.22  tff(c_277202, plain, (![C_3558]: (~r2_hidden(C_3558, '#skF_4'))), inference(splitRight, [status(thm)], [c_146095])).
% 59.15/47.22  tff(c_277226, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_277202])).
% 59.15/47.22  tff(c_277237, plain, $false, inference(negUnitSimplification, [status(thm)], [c_140183, c_277226])).
% 59.15/47.22  tff(c_277238, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_141234])).
% 59.15/47.22  tff(c_38, plain, (![B_24, A_23]: (r1_tarski(k1_relat_1(B_24), A_23) | ~v4_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_79])).
% 59.15/47.22  tff(c_140222, plain, (![B_24]: (v1_xboole_0(k1_relat_1(B_24)) | ~v4_relat_1(B_24, k1_xboole_0) | ~v1_relat_1(B_24))), inference(resolution, [status(thm)], [c_38, c_140200])).
% 59.15/47.22  tff(c_293, plain, (![A_111, B_112]: (r2_hidden('#skF_2'(A_111, B_112), A_111) | r1_tarski(A_111, B_112))), inference(cnfTransformation, [status(thm)], [f_38])).
% 59.15/47.22  tff(c_315, plain, (![A_114, B_115]: (~v1_xboole_0(A_114) | r1_tarski(A_114, B_115))), inference(resolution, [status(thm)], [c_293, c_2])).
% 59.15/47.22  tff(c_14, plain, (![B_12, A_11]: (B_12=A_11 | ~r1_tarski(B_12, A_11) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 59.15/47.22  tff(c_362, plain, (![B_118, A_119]: (B_118=A_119 | ~r1_tarski(B_118, A_119) | ~v1_xboole_0(A_119))), inference(resolution, [status(thm)], [c_315, c_14])).
% 59.15/47.22  tff(c_382, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relset_1('#skF_5', '#skF_3', '#skF_7') | ~v1_xboole_0(k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(resolution, [status(thm)], [c_86, c_362])).
% 59.15/47.22  tff(c_139712, plain, (~v1_xboole_0(k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(splitLeft, [status(thm)], [c_382])).
% 59.15/47.22  tff(c_140727, plain, (~v1_xboole_0(k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_140719, c_139712])).
% 59.15/47.22  tff(c_140758, plain, (~v4_relat_1('#skF_7', k1_xboole_0) | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_140222, c_140727])).
% 59.15/47.22  tff(c_140764, plain, (~v4_relat_1('#skF_7', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_247, c_140758])).
% 59.15/47.22  tff(c_277248, plain, (~v4_relat_1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_277238, c_140764])).
% 59.15/47.22  tff(c_277289, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140050, c_277248])).
% 59.15/47.22  tff(c_277291, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_140179])).
% 59.15/47.22  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 59.15/47.22  tff(c_277337, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_277291, c_12])).
% 59.15/47.22  tff(c_277347, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_277337])).
% 59.15/47.22  tff(c_277349, plain, (v1_xboole_0(k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(splitRight, [status(thm)], [c_382])).
% 59.15/47.22  tff(c_277368, plain, (k1_relset_1('#skF_5', '#skF_3', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_277349, c_12])).
% 59.15/47.22  tff(c_277406, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_277368, c_86])).
% 59.15/47.22  tff(c_330, plain, (![B_115, A_114]: (B_115=A_114 | ~r1_tarski(B_115, A_114) | ~v1_xboole_0(A_114))), inference(resolution, [status(thm)], [c_315, c_14])).
% 59.15/47.22  tff(c_277420, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_277406, c_330])).
% 59.15/47.22  tff(c_277432, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_163, c_277420])).
% 59.15/47.22  tff(c_278095, plain, (![A_3628, B_3629, C_3630]: (k2_relset_1(A_3628, B_3629, C_3630)=k2_relat_1(C_3630) | ~m1_subset_1(C_3630, k1_zfmisc_1(k2_zfmisc_1(A_3628, B_3629))))), inference(cnfTransformation, [status(thm)], [f_141])).
% 59.15/47.22  tff(c_278102, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_94, c_278095])).
% 59.15/47.22  tff(c_278114, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_277432, c_278102])).
% 59.15/47.22  tff(c_301, plain, (![A_111, B_112]: (~v1_xboole_0(A_111) | r1_tarski(A_111, B_112))), inference(resolution, [status(thm)], [c_293, c_2])).
% 59.15/47.22  tff(c_139710, plain, (![B_1836, B_112]: (v5_relat_1(B_1836, B_112) | ~v1_relat_1(B_1836) | ~v1_xboole_0(k2_relat_1(B_1836)))), inference(resolution, [status(thm)], [c_301, c_139701])).
% 59.15/47.22  tff(c_278118, plain, (![B_112]: (v5_relat_1('#skF_6', B_112) | ~v1_relat_1('#skF_6') | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_278114, c_139710])).
% 59.15/47.22  tff(c_278131, plain, (![B_112]: (v5_relat_1('#skF_6', B_112))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_244, c_278118])).
% 59.15/47.22  tff(c_277959, plain, (![A_3619, B_3620, C_3621]: (k1_relset_1(A_3619, B_3620, C_3621)=k1_relat_1(C_3621) | ~m1_subset_1(C_3621, k1_zfmisc_1(k2_zfmisc_1(A_3619, B_3620))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 59.15/47.22  tff(c_277977, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_94, c_277959])).
% 59.15/47.22  tff(c_278556, plain, (![B_3658, A_3659, C_3660]: (k1_xboole_0=B_3658 | k1_relset_1(A_3659, B_3658, C_3660)=A_3659 | ~v1_funct_2(C_3660, A_3659, B_3658) | ~m1_subset_1(C_3660, k1_zfmisc_1(k2_zfmisc_1(A_3659, B_3658))))), inference(cnfTransformation, [status(thm)], [f_176])).
% 59.15/47.22  tff(c_278563, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_94, c_278556])).
% 59.15/47.22  tff(c_278576, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_277977, c_278563])).
% 59.15/47.22  tff(c_278580, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_278576])).
% 59.15/47.22  tff(c_278271, plain, (![B_3638, C_3639, A_3640]: (r2_hidden(k1_funct_1(B_3638, C_3639), A_3640) | ~r2_hidden(C_3639, k1_relat_1(B_3638)) | ~v1_funct_1(B_3638) | ~v5_relat_1(B_3638, A_3640) | ~v1_relat_1(B_3638))), inference(cnfTransformation, [status(thm)], [f_102])).
% 59.15/47.22  tff(c_285657, plain, (![A_3925, C_3926, B_3927]: (~v1_xboole_0(A_3925) | ~r2_hidden(C_3926, k1_relat_1(B_3927)) | ~v1_funct_1(B_3927) | ~v5_relat_1(B_3927, A_3925) | ~v1_relat_1(B_3927))), inference(resolution, [status(thm)], [c_278271, c_2])).
% 59.15/47.22  tff(c_285682, plain, (![A_3925, C_3926]: (~v1_xboole_0(A_3925) | ~r2_hidden(C_3926, '#skF_4') | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', A_3925) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_278580, c_285657])).
% 59.15/47.22  tff(c_285712, plain, (![A_3925, C_3926]: (~v1_xboole_0(A_3925) | ~r2_hidden(C_3926, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_244, c_278131, c_98, c_285682])).
% 59.15/47.22  tff(c_285725, plain, (![C_3928]: (~r2_hidden(C_3928, '#skF_4'))), inference(splitLeft, [status(thm)], [c_285712])).
% 59.15/47.22  tff(c_285749, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_285725])).
% 59.15/47.22  tff(c_285760, plain, $false, inference(negUnitSimplification, [status(thm)], [c_277947, c_285749])).
% 59.15/47.22  tff(c_285761, plain, (![A_3925]: (~v1_xboole_0(A_3925))), inference(splitRight, [status(thm)], [c_285712])).
% 59.15/47.22  tff(c_285793, plain, $false, inference(negUnitSimplification, [status(thm)], [c_285761, c_163])).
% 59.15/47.22  tff(c_285794, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_278576])).
% 59.15/47.22  tff(c_285834, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_285794, c_163])).
% 59.15/47.22  tff(c_285843, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_285834])).
% 59.15/47.22  tff(c_285845, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_277943])).
% 59.15/47.22  tff(c_285891, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_285845, c_12])).
% 59.15/47.22  tff(c_285901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_285891])).
% 59.15/47.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 59.15/47.22  
% 59.15/47.22  Inference rules
% 59.15/47.22  ----------------------
% 59.15/47.22  #Ref     : 0
% 59.15/47.22  #Sup     : 71111
% 59.15/47.22  #Fact    : 0
% 59.15/47.22  #Define  : 0
% 59.15/47.22  #Split   : 141
% 59.15/47.22  #Chain   : 0
% 59.15/47.22  #Close   : 0
% 59.15/47.22  
% 59.15/47.22  Ordering : KBO
% 59.15/47.22  
% 59.15/47.22  Simplification rules
% 59.15/47.22  ----------------------
% 59.15/47.22  #Subsume      : 20912
% 59.15/47.22  #Demod        : 79663
% 59.15/47.22  #Tautology    : 32749
% 59.15/47.22  #SimpNegUnit  : 1656
% 59.15/47.22  #BackRed      : 1574
% 59.15/47.22  
% 59.15/47.22  #Partial instantiations: 0
% 59.15/47.22  #Strategies tried      : 1
% 59.15/47.22  
% 59.15/47.22  Timing (in seconds)
% 59.15/47.22  ----------------------
% 59.15/47.22  Preprocessing        : 0.37
% 59.15/47.22  Parsing              : 0.19
% 59.15/47.22  CNF conversion       : 0.03
% 59.15/47.22  Main loop            : 46.04
% 59.15/47.22  Inferencing          : 5.59
% 59.15/47.22  Reduction            : 13.74
% 59.15/47.22  Demodulation         : 10.12
% 59.15/47.22  BG Simplification    : 0.75
% 59.15/47.22  Subsumption          : 24.07
% 59.15/47.22  Abstraction          : 1.22
% 59.15/47.22  MUC search           : 0.00
% 59.15/47.22  Cooper               : 0.00
% 59.15/47.22  Total                : 46.48
% 59.15/47.22  Index Insertion      : 0.00
% 59.15/47.22  Index Deletion       : 0.00
% 59.15/47.22  Index Matching       : 0.00
% 59.15/47.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
