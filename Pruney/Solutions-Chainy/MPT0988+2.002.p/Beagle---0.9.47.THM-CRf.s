%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:54 EST 2020

% Result     : Theorem 8.01s
% Output     : CNFRefutation 8.01s
% Verified   : 
% Statistics : Number of formulae       :  208 (12028 expanded)
%              Number of leaves         :   42 (4444 expanded)
%              Depth                    :   30
%              Number of atoms          :  567 (70069 expanded)
%              Number of equality atoms :  182 (24925 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_210,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( ( k2_relset_1(A,B,C) = B
                & v2_funct_1(C)
                & ! [E,F] :
                    ( ( ( r2_hidden(E,B)
                        & k1_funct_1(D,E) = F )
                     => ( r2_hidden(F,A)
                        & k1_funct_1(C,F) = E ) )
                    & ( ( r2_hidden(F,A)
                        & k1_funct_1(C,F) = E )
                     => ( r2_hidden(E,B)
                        & k1_funct_1(D,E) = F ) ) ) )
             => ( A = k1_xboole_0
                | B = k1_xboole_0
                | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_2)).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_104,axiom,(
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

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_52,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_142,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_152,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_169,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( k1_relat_1(C) = A
          & ! [D] :
              ( r2_hidden(D,A)
             => r2_hidden(k1_funct_1(C,D),B) ) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k1_relat_1(A) = k2_relat_1(B)
              & k2_relat_1(A) = k1_relat_1(B)
              & ! [C,D] :
                  ( ( r2_hidden(C,k1_relat_1(A))
                    & r2_hidden(D,k1_relat_1(B)) )
                 => ( k1_funct_1(A,C) = D
                  <=> k1_funct_1(B,D) = C ) ) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_1)).

tff(c_80,plain,(
    k2_funct_1('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_96,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_134,plain,(
    ! [B_63,A_64] :
      ( v1_relat_1(B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_64))
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_140,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_96,c_134])).

tff(c_147,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_140])).

tff(c_100,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_86,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_82,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_98,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_346,plain,(
    ! [A_81,B_82,C_83] :
      ( k1_relset_1(A_81,B_82,C_83) = k1_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_366,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_96,c_346])).

tff(c_4362,plain,(
    ! [B_334,A_335,C_336] :
      ( k1_xboole_0 = B_334
      | k1_relset_1(A_335,B_334,C_336) = A_335
      | ~ v1_funct_2(C_336,A_335,B_334)
      | ~ m1_subset_1(C_336,k1_zfmisc_1(k2_zfmisc_1(A_335,B_334))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_4382,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_96,c_4362])).

tff(c_4399,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_366,c_4382])).

tff(c_4400,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_4399])).

tff(c_88,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_279,plain,(
    ! [A_78,B_79,C_80] :
      ( k2_relset_1(A_78,B_79,C_80) = k2_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_289,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_96,c_279])).

tff(c_296,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_289])).

tff(c_90,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_143,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_90,c_134])).

tff(c_150,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_143])).

tff(c_94,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_297,plain,(
    k2_relset_1('#skF_5','#skF_4','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_90,c_279])).

tff(c_453,plain,(
    ! [A_94,B_95,C_96] :
      ( m1_subset_1(k2_relset_1(A_94,B_95,C_96),k1_zfmisc_1(B_95))
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_476,plain,
    ( m1_subset_1(k2_relat_1('#skF_7'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_453])).

tff(c_487,plain,(
    m1_subset_1(k2_relat_1('#skF_7'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_476])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_507,plain,(
    r1_tarski(k2_relat_1('#skF_7'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_487,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_513,plain,
    ( k2_relat_1('#skF_7') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_507,c_2])).

tff(c_516,plain,(
    ~ r1_tarski('#skF_4',k2_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_513])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1168,plain,(
    ! [B_168,A_169,C_170] :
      ( k1_xboole_0 = B_168
      | k1_relset_1(A_169,B_168,C_170) = A_169
      | ~ v1_funct_2(C_170,A_169,B_168)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(A_169,B_168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1189,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_96,c_1168])).

tff(c_1203,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_366,c_1189])).

tff(c_1204,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1203])).

tff(c_22,plain,(
    ! [A_13] :
      ( k2_relat_1(k2_funct_1(A_13)) = k1_relat_1(A_13)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_18,plain,(
    ! [A_10] :
      ( v1_relat_1(k2_funct_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1714,plain,(
    ! [C_194,A_195,B_196] :
      ( v1_funct_1(k2_funct_1(C_194))
      | k2_relset_1(A_195,B_196,C_194) != B_196
      | ~ v2_funct_1(C_194)
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(A_195,B_196)))
      | ~ v1_funct_2(C_194,A_195,B_196)
      | ~ v1_funct_1(C_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_1745,plain,
    ( v1_funct_1(k2_funct_1('#skF_6'))
    | k2_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_5'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_96,c_1714])).

tff(c_1766,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_86,c_88,c_1745])).

tff(c_62,plain,(
    ! [A_38] :
      ( m1_subset_1(A_38,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_38),k2_relat_1(A_38))))
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_657,plain,(
    ! [A_116] :
      ( k2_relset_1(k1_relat_1(A_116),k2_relat_1(A_116),A_116) = k2_relat_1(A_116)
      | ~ v1_funct_1(A_116)
      | ~ v1_relat_1(A_116) ) ),
    inference(resolution,[status(thm)],[c_62,c_279])).

tff(c_38,plain,(
    ! [A_23,B_24,C_25] :
      ( m1_subset_1(k2_relset_1(A_23,B_24,C_25),k1_zfmisc_1(B_24))
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2284,plain,(
    ! [A_243] :
      ( m1_subset_1(k2_relat_1(A_243),k1_zfmisc_1(k2_relat_1(A_243)))
      | ~ m1_subset_1(A_243,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_243),k2_relat_1(A_243))))
      | ~ v1_funct_1(A_243)
      | ~ v1_relat_1(A_243) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_657,c_38])).

tff(c_2341,plain,(
    ! [A_245] :
      ( m1_subset_1(k2_relat_1(A_245),k1_zfmisc_1(k2_relat_1(A_245)))
      | ~ v1_funct_1(A_245)
      | ~ v1_relat_1(A_245) ) ),
    inference(resolution,[status(thm)],[c_62,c_2284])).

tff(c_2503,plain,(
    ! [A_255] :
      ( m1_subset_1(k1_relat_1(A_255),k1_zfmisc_1(k2_relat_1(k2_funct_1(A_255))))
      | ~ v1_funct_1(k2_funct_1(A_255))
      | ~ v1_relat_1(k2_funct_1(A_255))
      | ~ v2_funct_1(A_255)
      | ~ v1_funct_1(A_255)
      | ~ v1_relat_1(A_255) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2341])).

tff(c_2515,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_relat_1(k2_funct_1('#skF_6'))))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1204,c_2503])).

tff(c_2527,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_relat_1(k2_funct_1('#skF_6'))))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_100,c_86,c_1766,c_2515])).

tff(c_2566,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_2527])).

tff(c_2569,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_18,c_2566])).

tff(c_2573,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_100,c_2569])).

tff(c_2574,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_relat_1(k2_funct_1('#skF_6')))) ),
    inference(splitRight,[status(thm)],[c_2527])).

tff(c_2588,plain,(
    r1_tarski('#skF_4',k2_relat_1(k2_funct_1('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_2574,c_8])).

tff(c_2631,plain,
    ( k2_relat_1(k2_funct_1('#skF_6')) = '#skF_4'
    | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_6')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_2588,c_2])).

tff(c_2642,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_6')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2631])).

tff(c_2645,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_4')
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2642])).

tff(c_2648,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_100,c_86,c_6,c_1204,c_2645])).

tff(c_2649,plain,(
    k2_relat_1(k2_funct_1('#skF_6')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2631])).

tff(c_2575,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_2527])).

tff(c_84,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_1794,plain,(
    ! [C_200,B_201,A_202] :
      ( v1_funct_2(k2_funct_1(C_200),B_201,A_202)
      | k2_relset_1(A_202,B_201,C_200) != B_201
      | ~ v2_funct_1(C_200)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_202,B_201)))
      | ~ v1_funct_2(C_200,A_202,B_201)
      | ~ v1_funct_1(C_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_1825,plain,
    ( v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | k2_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_5'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_96,c_1794])).

tff(c_1846,plain,(
    v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_86,c_88,c_1825])).

tff(c_24,plain,(
    ! [A_13] :
      ( k1_relat_1(k2_funct_1(A_13)) = k2_relat_1(A_13)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_240,plain,(
    ! [A_74] :
      ( m1_subset_1(A_74,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_74),k2_relat_1(A_74))))
      | ~ v1_funct_1(A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_256,plain,(
    ! [A_74] :
      ( r1_tarski(A_74,k2_zfmisc_1(k1_relat_1(A_74),k2_relat_1(A_74)))
      | ~ v1_funct_1(A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(resolution,[status(thm)],[c_240,c_8])).

tff(c_2689,plain,
    ( r1_tarski(k2_funct_1('#skF_6'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_6')),'#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2649,c_256])).

tff(c_2725,plain,(
    r1_tarski(k2_funct_1('#skF_6'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_6')),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2575,c_1766,c_2689])).

tff(c_2817,plain,
    ( r1_tarski(k2_funct_1('#skF_6'),k2_zfmisc_1(k2_relat_1('#skF_6'),'#skF_4'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2725])).

tff(c_2836,plain,(
    r1_tarski(k2_funct_1('#skF_6'),k2_zfmisc_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_100,c_86,c_296,c_2817])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1200,plain,(
    ! [B_168,A_169,A_3] :
      ( k1_xboole_0 = B_168
      | k1_relset_1(A_169,B_168,A_3) = A_169
      | ~ v1_funct_2(A_3,A_169,B_168)
      | ~ r1_tarski(A_3,k2_zfmisc_1(A_169,B_168)) ) ),
    inference(resolution,[status(thm)],[c_10,c_1168])).

tff(c_2839,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_5','#skF_4',k2_funct_1('#skF_6')) = '#skF_5'
    | ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_2836,c_1200])).

tff(c_2859,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_5','#skF_4',k2_funct_1('#skF_6')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1846,c_2839])).

tff(c_2860,plain,(
    k1_relset_1('#skF_5','#skF_4',k2_funct_1('#skF_6')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2859])).

tff(c_365,plain,(
    ! [A_81,B_82,A_3] :
      ( k1_relset_1(A_81,B_82,A_3) = k1_relat_1(A_3)
      | ~ r1_tarski(A_3,k2_zfmisc_1(A_81,B_82)) ) ),
    inference(resolution,[status(thm)],[c_10,c_346])).

tff(c_2867,plain,(
    k1_relset_1('#skF_5','#skF_4',k2_funct_1('#skF_6')) = k1_relat_1(k2_funct_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_2836,c_365])).

tff(c_2878,plain,(
    k1_relat_1(k2_funct_1('#skF_6')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2860,c_2867])).

tff(c_70,plain,(
    ! [C_41,B_40] :
      ( r2_hidden('#skF_3'(k1_relat_1(C_41),B_40,C_41),k1_relat_1(C_41))
      | m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_41),B_40)))
      | ~ v1_funct_1(C_41)
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_2915,plain,(
    ! [B_40] :
      ( r2_hidden('#skF_3'('#skF_5',B_40,k2_funct_1('#skF_6')),k1_relat_1(k2_funct_1('#skF_6')))
      | m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_6')),B_40)))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2878,c_70])).

tff(c_3267,plain,(
    ! [B_267] :
      ( r2_hidden('#skF_3'('#skF_5',B_267,k2_funct_1('#skF_6')),'#skF_5')
      | m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_267))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2575,c_1766,c_2878,c_2878,c_2915])).

tff(c_42,plain,(
    ! [A_29,B_30,C_31] :
      ( k2_relset_1(A_29,B_30,C_31) = k2_relat_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_3294,plain,(
    ! [B_267] :
      ( k2_relset_1('#skF_5',B_267,k2_funct_1('#skF_6')) = k2_relat_1(k2_funct_1('#skF_6'))
      | r2_hidden('#skF_3'('#skF_5',B_267,k2_funct_1('#skF_6')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3267,c_42])).

tff(c_3407,plain,(
    ! [B_272] :
      ( k2_relset_1('#skF_5',B_272,k2_funct_1('#skF_6')) = '#skF_4'
      | r2_hidden('#skF_3'('#skF_5',B_272,k2_funct_1('#skF_6')),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2649,c_3294])).

tff(c_20,plain,(
    ! [B_12,A_11] :
      ( r2_hidden(k1_funct_1(B_12,A_11),k2_relat_1(B_12))
      | ~ r2_hidden(A_11,k1_relat_1(B_12))
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2686,plain,(
    ! [A_11] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),A_11),'#skF_4')
      | ~ r2_hidden(A_11,k1_relat_1(k2_funct_1('#skF_6')))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2649,c_20])).

tff(c_2723,plain,(
    ! [A_11] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),A_11),'#skF_4')
      | ~ r2_hidden(A_11,k1_relat_1(k2_funct_1('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2575,c_1766,c_2686])).

tff(c_3141,plain,(
    ! [A_263] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),A_263),'#skF_4')
      | ~ r2_hidden(A_263,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2878,c_2723])).

tff(c_108,plain,(
    ! [F_51] :
      ( r2_hidden(k1_funct_1('#skF_6',F_51),'#skF_5')
      | ~ r2_hidden(F_51,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_92,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_367,plain,(
    k1_relset_1('#skF_5','#skF_4','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_90,c_346])).

tff(c_1192,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_5','#skF_4','#skF_7') = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_1168])).

tff(c_1207,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_367,c_1192])).

tff(c_1208,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1207])).

tff(c_106,plain,(
    ! [F_51] :
      ( k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_51)) = F_51
      | ~ r2_hidden(F_51,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_517,plain,(
    ! [B_97,A_98] :
      ( r2_hidden(k1_funct_1(B_97,A_98),k2_relat_1(B_97))
      | ~ r2_hidden(A_98,k1_relat_1(B_97))
      | ~ v1_funct_1(B_97)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_526,plain,(
    ! [F_51] :
      ( r2_hidden(F_51,k2_relat_1('#skF_7'))
      | ~ r2_hidden(k1_funct_1('#skF_6',F_51),k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(F_51,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_517])).

tff(c_533,plain,(
    ! [F_51] :
      ( r2_hidden(F_51,k2_relat_1('#skF_7'))
      | ~ r2_hidden(k1_funct_1('#skF_6',F_51),k1_relat_1('#skF_7'))
      | ~ r2_hidden(F_51,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_94,c_526])).

tff(c_1607,plain,(
    ! [F_187] :
      ( r2_hidden(F_187,k2_relat_1('#skF_7'))
      | ~ r2_hidden(k1_funct_1('#skF_6',F_187),'#skF_5')
      | ~ r2_hidden(F_187,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1208,c_533])).

tff(c_1615,plain,(
    ! [F_188] :
      ( r2_hidden(F_188,k2_relat_1('#skF_7'))
      | ~ r2_hidden(F_188,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_108,c_1607])).

tff(c_72,plain,(
    ! [C_41,B_40] :
      ( ~ r2_hidden(k1_funct_1(C_41,'#skF_3'(k1_relat_1(C_41),B_40,C_41)),B_40)
      | v1_funct_2(C_41,k1_relat_1(C_41),B_40)
      | ~ v1_funct_1(C_41)
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_1625,plain,(
    ! [C_41] :
      ( v1_funct_2(C_41,k1_relat_1(C_41),k2_relat_1('#skF_7'))
      | ~ v1_funct_1(C_41)
      | ~ v1_relat_1(C_41)
      | ~ r2_hidden(k1_funct_1(C_41,'#skF_3'(k1_relat_1(C_41),k2_relat_1('#skF_7'),C_41)),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1615,c_72])).

tff(c_3149,plain,
    ( v1_funct_2(k2_funct_1('#skF_6'),k1_relat_1(k2_funct_1('#skF_6')),k2_relat_1('#skF_7'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ r2_hidden('#skF_3'(k1_relat_1(k2_funct_1('#skF_6')),k2_relat_1('#skF_7'),k2_funct_1('#skF_6')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_3141,c_1625])).

tff(c_3175,plain,
    ( v1_funct_2(k2_funct_1('#skF_6'),'#skF_5',k2_relat_1('#skF_7'))
    | ~ r2_hidden('#skF_3'('#skF_5',k2_relat_1('#skF_7'),k2_funct_1('#skF_6')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2878,c_2575,c_1766,c_2878,c_3149])).

tff(c_3262,plain,(
    ~ r2_hidden('#skF_3'('#skF_5',k2_relat_1('#skF_7'),k2_funct_1('#skF_6')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3175])).

tff(c_3411,plain,(
    k2_relset_1('#skF_5',k2_relat_1('#skF_7'),k2_funct_1('#skF_6')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3407,c_3262])).

tff(c_564,plain,(
    ! [A_102,B_103,C_104] :
      ( r1_tarski(k2_relset_1(A_102,B_103,C_104),B_103)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(resolution,[status(thm)],[c_453,c_8])).

tff(c_583,plain,(
    ! [A_102,B_103,A_3] :
      ( r1_tarski(k2_relset_1(A_102,B_103,A_3),B_103)
      | ~ r1_tarski(A_3,k2_zfmisc_1(A_102,B_103)) ) ),
    inference(resolution,[status(thm)],[c_10,c_564])).

tff(c_3417,plain,
    ( r1_tarski('#skF_4',k2_relat_1('#skF_7'))
    | ~ r1_tarski(k2_funct_1('#skF_6'),k2_zfmisc_1('#skF_5',k2_relat_1('#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3411,c_583])).

tff(c_3425,plain,(
    ~ r1_tarski(k2_funct_1('#skF_6'),k2_zfmisc_1('#skF_5',k2_relat_1('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_516,c_3417])).

tff(c_3428,plain,(
    ! [B_273] :
      ( r1_tarski(k2_funct_1('#skF_6'),k2_zfmisc_1('#skF_5',B_273))
      | r2_hidden('#skF_3'('#skF_5',B_273,k2_funct_1('#skF_6')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3267,c_8])).

tff(c_3431,plain,(
    r1_tarski(k2_funct_1('#skF_6'),k2_zfmisc_1('#skF_5',k2_relat_1('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_3428,c_3262])).

tff(c_3435,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3425,c_3431])).

tff(c_3437,plain,(
    r2_hidden('#skF_3'('#skF_5',k2_relat_1('#skF_7'),k2_funct_1('#skF_6')),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_3175])).

tff(c_68,plain,(
    ! [C_41,B_40] :
      ( ~ r2_hidden(k1_funct_1(C_41,'#skF_3'(k1_relat_1(C_41),B_40,C_41)),B_40)
      | m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_41),B_40)))
      | ~ v1_funct_1(C_41)
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_1624,plain,(
    ! [C_41] :
      ( m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_41),k2_relat_1('#skF_7'))))
      | ~ v1_funct_1(C_41)
      | ~ v1_relat_1(C_41)
      | ~ r2_hidden(k1_funct_1(C_41,'#skF_3'(k1_relat_1(C_41),k2_relat_1('#skF_7'),C_41)),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1615,c_68])).

tff(c_3145,plain,
    ( m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_6')),k2_relat_1('#skF_7'))))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ r2_hidden('#skF_3'(k1_relat_1(k2_funct_1('#skF_6')),k2_relat_1('#skF_7'),k2_funct_1('#skF_6')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_3141,c_1624])).

tff(c_3172,plain,
    ( m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k2_relat_1('#skF_7'))))
    | ~ r2_hidden('#skF_3'('#skF_5',k2_relat_1('#skF_7'),k2_funct_1('#skF_6')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2878,c_2575,c_1766,c_2878,c_3145])).

tff(c_3727,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k2_relat_1('#skF_7')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3437,c_3172])).

tff(c_3753,plain,(
    k2_relset_1('#skF_5',k2_relat_1('#skF_7'),k2_funct_1('#skF_6')) = k2_relat_1(k2_funct_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_3727,c_42])).

tff(c_3779,plain,(
    k2_relset_1('#skF_5',k2_relat_1('#skF_7'),k2_funct_1('#skF_6')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2649,c_3753])).

tff(c_3799,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_relat_1('#skF_7')))
    | ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k2_relat_1('#skF_7')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3779,c_38])).

tff(c_3808,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_relat_1('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3727,c_3799])).

tff(c_3822,plain,(
    r1_tarski('#skF_4',k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_3808,c_8])).

tff(c_3829,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_516,c_3822])).

tff(c_3830,plain,(
    k2_relat_1('#skF_7') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_513])).

tff(c_4385,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_5','#skF_4','#skF_7') = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_4362])).

tff(c_4403,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_367,c_4385])).

tff(c_4404,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_4403])).

tff(c_5533,plain,(
    ! [A_423,B_424] :
      ( r2_hidden('#skF_2'(A_423,B_424),k1_relat_1(B_424))
      | k2_funct_1(A_423) = B_424
      | k2_relat_1(A_423) != k1_relat_1(B_424)
      | k2_relat_1(B_424) != k1_relat_1(A_423)
      | ~ v2_funct_1(A_423)
      | ~ v1_funct_1(B_424)
      | ~ v1_relat_1(B_424)
      | ~ v1_funct_1(A_423)
      | ~ v1_relat_1(A_423) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_5536,plain,(
    ! [A_423] :
      ( r2_hidden('#skF_2'(A_423,'#skF_7'),'#skF_5')
      | k2_funct_1(A_423) = '#skF_7'
      | k2_relat_1(A_423) != k1_relat_1('#skF_7')
      | k2_relat_1('#skF_7') != k1_relat_1(A_423)
      | ~ v2_funct_1(A_423)
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ v1_funct_1(A_423)
      | ~ v1_relat_1(A_423) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4404,c_5533])).

tff(c_5544,plain,(
    ! [A_423] :
      ( r2_hidden('#skF_2'(A_423,'#skF_7'),'#skF_5')
      | k2_funct_1(A_423) = '#skF_7'
      | k2_relat_1(A_423) != '#skF_5'
      | k1_relat_1(A_423) != '#skF_4'
      | ~ v2_funct_1(A_423)
      | ~ v1_funct_1(A_423)
      | ~ v1_relat_1(A_423) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_94,c_3830,c_4404,c_5536])).

tff(c_5478,plain,(
    ! [A_413,B_414] :
      ( r2_hidden('#skF_1'(A_413,B_414),k1_relat_1(A_413))
      | k2_funct_1(A_413) = B_414
      | k2_relat_1(A_413) != k1_relat_1(B_414)
      | k2_relat_1(B_414) != k1_relat_1(A_413)
      | ~ v2_funct_1(A_413)
      | ~ v1_funct_1(B_414)
      | ~ v1_relat_1(B_414)
      | ~ v1_funct_1(A_413)
      | ~ v1_relat_1(A_413) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_5484,plain,(
    ! [B_414] :
      ( r2_hidden('#skF_1'('#skF_6',B_414),'#skF_4')
      | k2_funct_1('#skF_6') = B_414
      | k2_relat_1('#skF_6') != k1_relat_1(B_414)
      | k2_relat_1(B_414) != k1_relat_1('#skF_6')
      | ~ v2_funct_1('#skF_6')
      | ~ v1_funct_1(B_414)
      | ~ v1_relat_1(B_414)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4400,c_5478])).

tff(c_5491,plain,(
    ! [B_414] :
      ( r2_hidden('#skF_1'('#skF_6',B_414),'#skF_4')
      | k2_funct_1('#skF_6') = B_414
      | k1_relat_1(B_414) != '#skF_5'
      | k2_relat_1(B_414) != '#skF_4'
      | ~ v1_funct_1(B_414)
      | ~ v1_relat_1(B_414) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_100,c_86,c_4400,c_296,c_5484])).

tff(c_5628,plain,(
    ! [A_433,B_434] :
      ( k1_funct_1(A_433,'#skF_1'(A_433,B_434)) = '#skF_2'(A_433,B_434)
      | k1_funct_1(B_434,'#skF_2'(A_433,B_434)) = '#skF_1'(A_433,B_434)
      | k2_funct_1(A_433) = B_434
      | k2_relat_1(A_433) != k1_relat_1(B_434)
      | k2_relat_1(B_434) != k1_relat_1(A_433)
      | ~ v2_funct_1(A_433)
      | ~ v1_funct_1(B_434)
      | ~ v1_relat_1(B_434)
      | ~ v1_funct_1(A_433)
      | ~ v1_relat_1(A_433) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_5646,plain,(
    ! [B_434] :
      ( r2_hidden('#skF_2'('#skF_6',B_434),'#skF_5')
      | ~ r2_hidden('#skF_1'('#skF_6',B_434),'#skF_4')
      | k1_funct_1(B_434,'#skF_2'('#skF_6',B_434)) = '#skF_1'('#skF_6',B_434)
      | k2_funct_1('#skF_6') = B_434
      | k2_relat_1('#skF_6') != k1_relat_1(B_434)
      | k2_relat_1(B_434) != k1_relat_1('#skF_6')
      | ~ v2_funct_1('#skF_6')
      | ~ v1_funct_1(B_434)
      | ~ v1_relat_1(B_434)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5628,c_108])).

tff(c_5685,plain,(
    ! [B_434] :
      ( r2_hidden('#skF_2'('#skF_6',B_434),'#skF_5')
      | ~ r2_hidden('#skF_1'('#skF_6',B_434),'#skF_4')
      | k1_funct_1(B_434,'#skF_2'('#skF_6',B_434)) = '#skF_1'('#skF_6',B_434)
      | k2_funct_1('#skF_6') = B_434
      | k1_relat_1(B_434) != '#skF_5'
      | k2_relat_1(B_434) != '#skF_4'
      | ~ v1_funct_1(B_434)
      | ~ v1_relat_1(B_434) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_100,c_86,c_4400,c_296,c_5646])).

tff(c_102,plain,(
    ! [E_50] :
      ( k1_funct_1('#skF_6',k1_funct_1('#skF_7',E_50)) = E_50
      | ~ r2_hidden(E_50,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_5664,plain,(
    ! [A_433] :
      ( k1_funct_1('#skF_6','#skF_1'(A_433,'#skF_7')) = '#skF_2'(A_433,'#skF_7')
      | ~ r2_hidden('#skF_2'(A_433,'#skF_7'),'#skF_5')
      | k1_funct_1(A_433,'#skF_1'(A_433,'#skF_7')) = '#skF_2'(A_433,'#skF_7')
      | k2_funct_1(A_433) = '#skF_7'
      | k2_relat_1(A_433) != k1_relat_1('#skF_7')
      | k2_relat_1('#skF_7') != k1_relat_1(A_433)
      | ~ v2_funct_1(A_433)
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ v1_funct_1(A_433)
      | ~ v1_relat_1(A_433) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5628,c_102])).

tff(c_7031,plain,(
    ! [A_488] :
      ( k1_funct_1('#skF_6','#skF_1'(A_488,'#skF_7')) = '#skF_2'(A_488,'#skF_7')
      | ~ r2_hidden('#skF_2'(A_488,'#skF_7'),'#skF_5')
      | k1_funct_1(A_488,'#skF_1'(A_488,'#skF_7')) = '#skF_2'(A_488,'#skF_7')
      | k2_funct_1(A_488) = '#skF_7'
      | k2_relat_1(A_488) != '#skF_5'
      | k1_relat_1(A_488) != '#skF_4'
      | ~ v2_funct_1(A_488)
      | ~ v1_funct_1(A_488)
      | ~ v1_relat_1(A_488) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_94,c_3830,c_4404,c_5664])).

tff(c_7034,plain,
    ( k1_funct_1('#skF_6','#skF_1'('#skF_6','#skF_7')) = '#skF_2'('#skF_6','#skF_7')
    | k2_relat_1('#skF_6') != '#skF_5'
    | k1_relat_1('#skF_6') != '#skF_4'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_7'),'#skF_4')
    | k1_funct_1('#skF_7','#skF_2'('#skF_6','#skF_7')) = '#skF_1'('#skF_6','#skF_7')
    | k2_funct_1('#skF_6') = '#skF_7'
    | k1_relat_1('#skF_7') != '#skF_5'
    | k2_relat_1('#skF_7') != '#skF_4'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_5685,c_7031])).

tff(c_7037,plain,
    ( k1_funct_1('#skF_6','#skF_1'('#skF_6','#skF_7')) = '#skF_2'('#skF_6','#skF_7')
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_7'),'#skF_4')
    | k1_funct_1('#skF_7','#skF_2'('#skF_6','#skF_7')) = '#skF_1'('#skF_6','#skF_7')
    | k2_funct_1('#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_94,c_3830,c_4404,c_147,c_100,c_86,c_4400,c_296,c_7034])).

tff(c_7038,plain,
    ( k1_funct_1('#skF_6','#skF_1'('#skF_6','#skF_7')) = '#skF_2'('#skF_6','#skF_7')
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_7'),'#skF_4')
    | k1_funct_1('#skF_7','#skF_2'('#skF_6','#skF_7')) = '#skF_1'('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_7037])).

tff(c_7083,plain,(
    ~ r2_hidden('#skF_1'('#skF_6','#skF_7'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_7038])).

tff(c_7086,plain,
    ( k2_funct_1('#skF_6') = '#skF_7'
    | k1_relat_1('#skF_7') != '#skF_5'
    | k2_relat_1('#skF_7') != '#skF_4'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_5491,c_7083])).

tff(c_7089,plain,(
    k2_funct_1('#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_94,c_3830,c_4404,c_7086])).

tff(c_7091,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_7089])).

tff(c_7093,plain,(
    r2_hidden('#skF_1'('#skF_6','#skF_7'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_7038])).

tff(c_5638,plain,(
    ! [B_434] :
      ( k1_funct_1('#skF_7','#skF_2'('#skF_6',B_434)) = '#skF_1'('#skF_6',B_434)
      | ~ r2_hidden('#skF_1'('#skF_6',B_434),'#skF_4')
      | k1_funct_1(B_434,'#skF_2'('#skF_6',B_434)) = '#skF_1'('#skF_6',B_434)
      | k2_funct_1('#skF_6') = B_434
      | k2_relat_1('#skF_6') != k1_relat_1(B_434)
      | k2_relat_1(B_434) != k1_relat_1('#skF_6')
      | ~ v2_funct_1('#skF_6')
      | ~ v1_funct_1(B_434)
      | ~ v1_relat_1(B_434)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5628,c_106])).

tff(c_5681,plain,(
    ! [B_434] :
      ( k1_funct_1('#skF_7','#skF_2'('#skF_6',B_434)) = '#skF_1'('#skF_6',B_434)
      | ~ r2_hidden('#skF_1'('#skF_6',B_434),'#skF_4')
      | k1_funct_1(B_434,'#skF_2'('#skF_6',B_434)) = '#skF_1'('#skF_6',B_434)
      | k2_funct_1('#skF_6') = B_434
      | k1_relat_1(B_434) != '#skF_5'
      | k2_relat_1(B_434) != '#skF_4'
      | ~ v1_funct_1(B_434)
      | ~ v1_relat_1(B_434) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_100,c_86,c_4400,c_296,c_5638])).

tff(c_7095,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_6','#skF_7')) = '#skF_1'('#skF_6','#skF_7')
    | k2_funct_1('#skF_6') = '#skF_7'
    | k1_relat_1('#skF_7') != '#skF_5'
    | k2_relat_1('#skF_7') != '#skF_4'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_7093,c_5681])).

tff(c_7098,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_6','#skF_7')) = '#skF_1'('#skF_6','#skF_7')
    | k2_funct_1('#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_94,c_3830,c_4404,c_7095])).

tff(c_7099,plain,(
    k1_funct_1('#skF_7','#skF_2'('#skF_6','#skF_7')) = '#skF_1'('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_7098])).

tff(c_30,plain,(
    ! [B_20,A_14] :
      ( k1_funct_1(B_20,'#skF_2'(A_14,B_20)) != '#skF_1'(A_14,B_20)
      | k1_funct_1(A_14,'#skF_1'(A_14,B_20)) != '#skF_2'(A_14,B_20)
      | k2_funct_1(A_14) = B_20
      | k2_relat_1(A_14) != k1_relat_1(B_20)
      | k2_relat_1(B_20) != k1_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_7103,plain,
    ( k1_funct_1('#skF_6','#skF_1'('#skF_6','#skF_7')) != '#skF_2'('#skF_6','#skF_7')
    | k2_funct_1('#skF_6') = '#skF_7'
    | k2_relat_1('#skF_6') != k1_relat_1('#skF_7')
    | k2_relat_1('#skF_7') != k1_relat_1('#skF_6')
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_7099,c_30])).

tff(c_7124,plain,
    ( k1_funct_1('#skF_6','#skF_1'('#skF_6','#skF_7')) != '#skF_2'('#skF_6','#skF_7')
    | k2_funct_1('#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_100,c_150,c_94,c_86,c_3830,c_4400,c_296,c_4404,c_7103])).

tff(c_7125,plain,(
    k1_funct_1('#skF_6','#skF_1'('#skF_6','#skF_7')) != '#skF_2'('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_7124])).

tff(c_7112,plain,
    ( k1_funct_1('#skF_6','#skF_1'('#skF_6','#skF_7')) = '#skF_2'('#skF_6','#skF_7')
    | ~ r2_hidden('#skF_2'('#skF_6','#skF_7'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7099,c_102])).

tff(c_7139,plain,(
    ~ r2_hidden('#skF_2'('#skF_6','#skF_7'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_7125,c_7112])).

tff(c_7142,plain,
    ( k2_funct_1('#skF_6') = '#skF_7'
    | k2_relat_1('#skF_6') != '#skF_5'
    | k1_relat_1('#skF_6') != '#skF_4'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_5544,c_7139])).

tff(c_7148,plain,(
    k2_funct_1('#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_100,c_86,c_4400,c_296,c_7142])).

tff(c_7150,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_7148])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:52:46 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.01/2.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.01/2.74  
% 8.01/2.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.01/2.74  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 8.01/2.74  
% 8.01/2.74  %Foreground sorts:
% 8.01/2.74  
% 8.01/2.74  
% 8.01/2.74  %Background operators:
% 8.01/2.74  
% 8.01/2.74  
% 8.01/2.74  %Foreground operators:
% 8.01/2.74  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.01/2.74  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.01/2.74  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.01/2.74  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.01/2.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.01/2.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.01/2.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.01/2.74  tff('#skF_7', type, '#skF_7': $i).
% 8.01/2.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.01/2.74  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.01/2.74  tff('#skF_5', type, '#skF_5': $i).
% 8.01/2.74  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.01/2.74  tff('#skF_6', type, '#skF_6': $i).
% 8.01/2.74  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.01/2.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.01/2.74  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.01/2.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.01/2.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.01/2.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.01/2.74  tff('#skF_4', type, '#skF_4': $i).
% 8.01/2.74  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.01/2.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.01/2.74  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.01/2.74  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.01/2.74  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.01/2.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.01/2.74  
% 8.01/2.77  tff(f_210, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) & (![E, F]: (((r2_hidden(E, B) & (k1_funct_1(D, E) = F)) => (r2_hidden(F, A) & (k1_funct_1(C, F) = E))) & ((r2_hidden(F, A) & (k1_funct_1(C, F) = E)) => (r2_hidden(E, B) & (k1_funct_1(D, E) = F)))))) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_2)).
% 8.01/2.77  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.01/2.77  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.01/2.77  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.01/2.77  tff(f_126, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 8.01/2.77  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.01/2.77  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 8.01/2.77  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.01/2.77  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.01/2.77  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 8.01/2.77  tff(f_52, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 8.01/2.77  tff(f_142, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 8.01/2.77  tff(f_152, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 8.01/2.77  tff(f_169, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 8.01/2.77  tff(f_60, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 8.01/2.77  tff(f_96, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((((v2_funct_1(A) & (k1_relat_1(A) = k2_relat_1(B))) & (k2_relat_1(A) = k1_relat_1(B))) & (![C, D]: ((r2_hidden(C, k1_relat_1(A)) & r2_hidden(D, k1_relat_1(B))) => ((k1_funct_1(A, C) = D) <=> (k1_funct_1(B, D) = C))))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_1)).
% 8.01/2.77  tff(c_80, plain, (k2_funct_1('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_210])).
% 8.01/2.77  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.01/2.77  tff(c_96, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_210])).
% 8.01/2.77  tff(c_134, plain, (![B_63, A_64]: (v1_relat_1(B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(A_64)) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.01/2.77  tff(c_140, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_96, c_134])).
% 8.01/2.77  tff(c_147, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_140])).
% 8.01/2.77  tff(c_100, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_210])).
% 8.01/2.77  tff(c_86, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_210])).
% 8.01/2.77  tff(c_82, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_210])).
% 8.01/2.77  tff(c_98, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_210])).
% 8.01/2.77  tff(c_346, plain, (![A_81, B_82, C_83]: (k1_relset_1(A_81, B_82, C_83)=k1_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.01/2.77  tff(c_366, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_96, c_346])).
% 8.01/2.77  tff(c_4362, plain, (![B_334, A_335, C_336]: (k1_xboole_0=B_334 | k1_relset_1(A_335, B_334, C_336)=A_335 | ~v1_funct_2(C_336, A_335, B_334) | ~m1_subset_1(C_336, k1_zfmisc_1(k2_zfmisc_1(A_335, B_334))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.01/2.77  tff(c_4382, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_96, c_4362])).
% 8.01/2.77  tff(c_4399, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_366, c_4382])).
% 8.01/2.77  tff(c_4400, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_82, c_4399])).
% 8.01/2.77  tff(c_88, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_210])).
% 8.01/2.77  tff(c_279, plain, (![A_78, B_79, C_80]: (k2_relset_1(A_78, B_79, C_80)=k2_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.01/2.77  tff(c_289, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_96, c_279])).
% 8.01/2.77  tff(c_296, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_289])).
% 8.01/2.77  tff(c_90, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_210])).
% 8.01/2.77  tff(c_143, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_90, c_134])).
% 8.01/2.77  tff(c_150, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_143])).
% 8.01/2.77  tff(c_94, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_210])).
% 8.01/2.77  tff(c_297, plain, (k2_relset_1('#skF_5', '#skF_4', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_90, c_279])).
% 8.01/2.77  tff(c_453, plain, (![A_94, B_95, C_96]: (m1_subset_1(k2_relset_1(A_94, B_95, C_96), k1_zfmisc_1(B_95)) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.01/2.77  tff(c_476, plain, (m1_subset_1(k2_relat_1('#skF_7'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_297, c_453])).
% 8.01/2.77  tff(c_487, plain, (m1_subset_1(k2_relat_1('#skF_7'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_476])).
% 8.01/2.77  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.01/2.77  tff(c_507, plain, (r1_tarski(k2_relat_1('#skF_7'), '#skF_4')), inference(resolution, [status(thm)], [c_487, c_8])).
% 8.01/2.77  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.01/2.77  tff(c_513, plain, (k2_relat_1('#skF_7')='#skF_4' | ~r1_tarski('#skF_4', k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_507, c_2])).
% 8.01/2.77  tff(c_516, plain, (~r1_tarski('#skF_4', k2_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_513])).
% 8.01/2.77  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.01/2.77  tff(c_1168, plain, (![B_168, A_169, C_170]: (k1_xboole_0=B_168 | k1_relset_1(A_169, B_168, C_170)=A_169 | ~v1_funct_2(C_170, A_169, B_168) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(A_169, B_168))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.01/2.77  tff(c_1189, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_96, c_1168])).
% 8.01/2.77  tff(c_1203, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_366, c_1189])).
% 8.01/2.77  tff(c_1204, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_82, c_1203])).
% 8.01/2.77  tff(c_22, plain, (![A_13]: (k2_relat_1(k2_funct_1(A_13))=k1_relat_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.01/2.77  tff(c_18, plain, (![A_10]: (v1_relat_1(k2_funct_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.01/2.77  tff(c_1714, plain, (![C_194, A_195, B_196]: (v1_funct_1(k2_funct_1(C_194)) | k2_relset_1(A_195, B_196, C_194)!=B_196 | ~v2_funct_1(C_194) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(A_195, B_196))) | ~v1_funct_2(C_194, A_195, B_196) | ~v1_funct_1(C_194))), inference(cnfTransformation, [status(thm)], [f_142])).
% 8.01/2.77  tff(c_1745, plain, (v1_funct_1(k2_funct_1('#skF_6')) | k2_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5' | ~v2_funct_1('#skF_6') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_96, c_1714])).
% 8.01/2.77  tff(c_1766, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_86, c_88, c_1745])).
% 8.01/2.77  tff(c_62, plain, (![A_38]: (m1_subset_1(A_38, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_38), k2_relat_1(A_38)))) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_152])).
% 8.01/2.77  tff(c_657, plain, (![A_116]: (k2_relset_1(k1_relat_1(A_116), k2_relat_1(A_116), A_116)=k2_relat_1(A_116) | ~v1_funct_1(A_116) | ~v1_relat_1(A_116))), inference(resolution, [status(thm)], [c_62, c_279])).
% 8.01/2.77  tff(c_38, plain, (![A_23, B_24, C_25]: (m1_subset_1(k2_relset_1(A_23, B_24, C_25), k1_zfmisc_1(B_24)) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.01/2.77  tff(c_2284, plain, (![A_243]: (m1_subset_1(k2_relat_1(A_243), k1_zfmisc_1(k2_relat_1(A_243))) | ~m1_subset_1(A_243, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_243), k2_relat_1(A_243)))) | ~v1_funct_1(A_243) | ~v1_relat_1(A_243))), inference(superposition, [status(thm), theory('equality')], [c_657, c_38])).
% 8.01/2.77  tff(c_2341, plain, (![A_245]: (m1_subset_1(k2_relat_1(A_245), k1_zfmisc_1(k2_relat_1(A_245))) | ~v1_funct_1(A_245) | ~v1_relat_1(A_245))), inference(resolution, [status(thm)], [c_62, c_2284])).
% 8.01/2.77  tff(c_2503, plain, (![A_255]: (m1_subset_1(k1_relat_1(A_255), k1_zfmisc_1(k2_relat_1(k2_funct_1(A_255)))) | ~v1_funct_1(k2_funct_1(A_255)) | ~v1_relat_1(k2_funct_1(A_255)) | ~v2_funct_1(A_255) | ~v1_funct_1(A_255) | ~v1_relat_1(A_255))), inference(superposition, [status(thm), theory('equality')], [c_22, c_2341])).
% 8.01/2.77  tff(c_2515, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_relat_1(k2_funct_1('#skF_6')))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1204, c_2503])).
% 8.01/2.77  tff(c_2527, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_relat_1(k2_funct_1('#skF_6')))) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_100, c_86, c_1766, c_2515])).
% 8.01/2.77  tff(c_2566, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_2527])).
% 8.01/2.77  tff(c_2569, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_18, c_2566])).
% 8.01/2.77  tff(c_2573, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_147, c_100, c_2569])).
% 8.01/2.77  tff(c_2574, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_relat_1(k2_funct_1('#skF_6'))))), inference(splitRight, [status(thm)], [c_2527])).
% 8.01/2.77  tff(c_2588, plain, (r1_tarski('#skF_4', k2_relat_1(k2_funct_1('#skF_6')))), inference(resolution, [status(thm)], [c_2574, c_8])).
% 8.01/2.77  tff(c_2631, plain, (k2_relat_1(k2_funct_1('#skF_6'))='#skF_4' | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_6')), '#skF_4')), inference(resolution, [status(thm)], [c_2588, c_2])).
% 8.01/2.77  tff(c_2642, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_6')), '#skF_4')), inference(splitLeft, [status(thm)], [c_2631])).
% 8.01/2.77  tff(c_2645, plain, (~r1_tarski(k1_relat_1('#skF_6'), '#skF_4') | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_22, c_2642])).
% 8.01/2.77  tff(c_2648, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_147, c_100, c_86, c_6, c_1204, c_2645])).
% 8.01/2.77  tff(c_2649, plain, (k2_relat_1(k2_funct_1('#skF_6'))='#skF_4'), inference(splitRight, [status(thm)], [c_2631])).
% 8.01/2.77  tff(c_2575, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_2527])).
% 8.01/2.77  tff(c_84, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_210])).
% 8.01/2.77  tff(c_1794, plain, (![C_200, B_201, A_202]: (v1_funct_2(k2_funct_1(C_200), B_201, A_202) | k2_relset_1(A_202, B_201, C_200)!=B_201 | ~v2_funct_1(C_200) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_202, B_201))) | ~v1_funct_2(C_200, A_202, B_201) | ~v1_funct_1(C_200))), inference(cnfTransformation, [status(thm)], [f_142])).
% 8.01/2.77  tff(c_1825, plain, (v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | k2_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5' | ~v2_funct_1('#skF_6') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_96, c_1794])).
% 8.01/2.77  tff(c_1846, plain, (v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_86, c_88, c_1825])).
% 8.01/2.77  tff(c_24, plain, (![A_13]: (k1_relat_1(k2_funct_1(A_13))=k2_relat_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.01/2.77  tff(c_240, plain, (![A_74]: (m1_subset_1(A_74, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_74), k2_relat_1(A_74)))) | ~v1_funct_1(A_74) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_152])).
% 8.01/2.77  tff(c_256, plain, (![A_74]: (r1_tarski(A_74, k2_zfmisc_1(k1_relat_1(A_74), k2_relat_1(A_74))) | ~v1_funct_1(A_74) | ~v1_relat_1(A_74))), inference(resolution, [status(thm)], [c_240, c_8])).
% 8.01/2.77  tff(c_2689, plain, (r1_tarski(k2_funct_1('#skF_6'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_6')), '#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2649, c_256])).
% 8.01/2.77  tff(c_2725, plain, (r1_tarski(k2_funct_1('#skF_6'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_6')), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2575, c_1766, c_2689])).
% 8.01/2.77  tff(c_2817, plain, (r1_tarski(k2_funct_1('#skF_6'), k2_zfmisc_1(k2_relat_1('#skF_6'), '#skF_4')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_24, c_2725])).
% 8.01/2.77  tff(c_2836, plain, (r1_tarski(k2_funct_1('#skF_6'), k2_zfmisc_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_100, c_86, c_296, c_2817])).
% 8.01/2.77  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.01/2.77  tff(c_1200, plain, (![B_168, A_169, A_3]: (k1_xboole_0=B_168 | k1_relset_1(A_169, B_168, A_3)=A_169 | ~v1_funct_2(A_3, A_169, B_168) | ~r1_tarski(A_3, k2_zfmisc_1(A_169, B_168)))), inference(resolution, [status(thm)], [c_10, c_1168])).
% 8.01/2.77  tff(c_2839, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_5', '#skF_4', k2_funct_1('#skF_6'))='#skF_5' | ~v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_2836, c_1200])).
% 8.01/2.77  tff(c_2859, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_5', '#skF_4', k2_funct_1('#skF_6'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1846, c_2839])).
% 8.01/2.77  tff(c_2860, plain, (k1_relset_1('#skF_5', '#skF_4', k2_funct_1('#skF_6'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_84, c_2859])).
% 8.01/2.77  tff(c_365, plain, (![A_81, B_82, A_3]: (k1_relset_1(A_81, B_82, A_3)=k1_relat_1(A_3) | ~r1_tarski(A_3, k2_zfmisc_1(A_81, B_82)))), inference(resolution, [status(thm)], [c_10, c_346])).
% 8.01/2.77  tff(c_2867, plain, (k1_relset_1('#skF_5', '#skF_4', k2_funct_1('#skF_6'))=k1_relat_1(k2_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_2836, c_365])).
% 8.01/2.77  tff(c_2878, plain, (k1_relat_1(k2_funct_1('#skF_6'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2860, c_2867])).
% 8.01/2.77  tff(c_70, plain, (![C_41, B_40]: (r2_hidden('#skF_3'(k1_relat_1(C_41), B_40, C_41), k1_relat_1(C_41)) | m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_41), B_40))) | ~v1_funct_1(C_41) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_169])).
% 8.01/2.77  tff(c_2915, plain, (![B_40]: (r2_hidden('#skF_3'('#skF_5', B_40, k2_funct_1('#skF_6')), k1_relat_1(k2_funct_1('#skF_6'))) | m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_6')), B_40))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_2878, c_70])).
% 8.01/2.77  tff(c_3267, plain, (![B_267]: (r2_hidden('#skF_3'('#skF_5', B_267, k2_funct_1('#skF_6')), '#skF_5') | m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_267))))), inference(demodulation, [status(thm), theory('equality')], [c_2575, c_1766, c_2878, c_2878, c_2915])).
% 8.01/2.77  tff(c_42, plain, (![A_29, B_30, C_31]: (k2_relset_1(A_29, B_30, C_31)=k2_relat_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.01/2.77  tff(c_3294, plain, (![B_267]: (k2_relset_1('#skF_5', B_267, k2_funct_1('#skF_6'))=k2_relat_1(k2_funct_1('#skF_6')) | r2_hidden('#skF_3'('#skF_5', B_267, k2_funct_1('#skF_6')), '#skF_5'))), inference(resolution, [status(thm)], [c_3267, c_42])).
% 8.01/2.77  tff(c_3407, plain, (![B_272]: (k2_relset_1('#skF_5', B_272, k2_funct_1('#skF_6'))='#skF_4' | r2_hidden('#skF_3'('#skF_5', B_272, k2_funct_1('#skF_6')), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2649, c_3294])).
% 8.01/2.77  tff(c_20, plain, (![B_12, A_11]: (r2_hidden(k1_funct_1(B_12, A_11), k2_relat_1(B_12)) | ~r2_hidden(A_11, k1_relat_1(B_12)) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.01/2.77  tff(c_2686, plain, (![A_11]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), A_11), '#skF_4') | ~r2_hidden(A_11, k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_2649, c_20])).
% 8.01/2.77  tff(c_2723, plain, (![A_11]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), A_11), '#skF_4') | ~r2_hidden(A_11, k1_relat_1(k2_funct_1('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_2575, c_1766, c_2686])).
% 8.01/2.77  tff(c_3141, plain, (![A_263]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), A_263), '#skF_4') | ~r2_hidden(A_263, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2878, c_2723])).
% 8.01/2.77  tff(c_108, plain, (![F_51]: (r2_hidden(k1_funct_1('#skF_6', F_51), '#skF_5') | ~r2_hidden(F_51, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_210])).
% 8.01/2.77  tff(c_92, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_210])).
% 8.01/2.77  tff(c_367, plain, (k1_relset_1('#skF_5', '#skF_4', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_90, c_346])).
% 8.01/2.77  tff(c_1192, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_5', '#skF_4', '#skF_7')='#skF_5' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_90, c_1168])).
% 8.01/2.77  tff(c_1207, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_367, c_1192])).
% 8.01/2.77  tff(c_1208, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_84, c_1207])).
% 8.01/2.77  tff(c_106, plain, (![F_51]: (k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_51))=F_51 | ~r2_hidden(F_51, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_210])).
% 8.01/2.77  tff(c_517, plain, (![B_97, A_98]: (r2_hidden(k1_funct_1(B_97, A_98), k2_relat_1(B_97)) | ~r2_hidden(A_98, k1_relat_1(B_97)) | ~v1_funct_1(B_97) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.01/2.77  tff(c_526, plain, (![F_51]: (r2_hidden(F_51, k2_relat_1('#skF_7')) | ~r2_hidden(k1_funct_1('#skF_6', F_51), k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(F_51, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_106, c_517])).
% 8.01/2.77  tff(c_533, plain, (![F_51]: (r2_hidden(F_51, k2_relat_1('#skF_7')) | ~r2_hidden(k1_funct_1('#skF_6', F_51), k1_relat_1('#skF_7')) | ~r2_hidden(F_51, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_94, c_526])).
% 8.01/2.77  tff(c_1607, plain, (![F_187]: (r2_hidden(F_187, k2_relat_1('#skF_7')) | ~r2_hidden(k1_funct_1('#skF_6', F_187), '#skF_5') | ~r2_hidden(F_187, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1208, c_533])).
% 8.01/2.77  tff(c_1615, plain, (![F_188]: (r2_hidden(F_188, k2_relat_1('#skF_7')) | ~r2_hidden(F_188, '#skF_4'))), inference(resolution, [status(thm)], [c_108, c_1607])).
% 8.01/2.77  tff(c_72, plain, (![C_41, B_40]: (~r2_hidden(k1_funct_1(C_41, '#skF_3'(k1_relat_1(C_41), B_40, C_41)), B_40) | v1_funct_2(C_41, k1_relat_1(C_41), B_40) | ~v1_funct_1(C_41) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_169])).
% 8.01/2.77  tff(c_1625, plain, (![C_41]: (v1_funct_2(C_41, k1_relat_1(C_41), k2_relat_1('#skF_7')) | ~v1_funct_1(C_41) | ~v1_relat_1(C_41) | ~r2_hidden(k1_funct_1(C_41, '#skF_3'(k1_relat_1(C_41), k2_relat_1('#skF_7'), C_41)), '#skF_4'))), inference(resolution, [status(thm)], [c_1615, c_72])).
% 8.01/2.77  tff(c_3149, plain, (v1_funct_2(k2_funct_1('#skF_6'), k1_relat_1(k2_funct_1('#skF_6')), k2_relat_1('#skF_7')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~r2_hidden('#skF_3'(k1_relat_1(k2_funct_1('#skF_6')), k2_relat_1('#skF_7'), k2_funct_1('#skF_6')), '#skF_5')), inference(resolution, [status(thm)], [c_3141, c_1625])).
% 8.01/2.77  tff(c_3175, plain, (v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', k2_relat_1('#skF_7')) | ~r2_hidden('#skF_3'('#skF_5', k2_relat_1('#skF_7'), k2_funct_1('#skF_6')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2878, c_2575, c_1766, c_2878, c_3149])).
% 8.01/2.77  tff(c_3262, plain, (~r2_hidden('#skF_3'('#skF_5', k2_relat_1('#skF_7'), k2_funct_1('#skF_6')), '#skF_5')), inference(splitLeft, [status(thm)], [c_3175])).
% 8.01/2.77  tff(c_3411, plain, (k2_relset_1('#skF_5', k2_relat_1('#skF_7'), k2_funct_1('#skF_6'))='#skF_4'), inference(resolution, [status(thm)], [c_3407, c_3262])).
% 8.01/2.77  tff(c_564, plain, (![A_102, B_103, C_104]: (r1_tarski(k2_relset_1(A_102, B_103, C_104), B_103) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(resolution, [status(thm)], [c_453, c_8])).
% 8.01/2.77  tff(c_583, plain, (![A_102, B_103, A_3]: (r1_tarski(k2_relset_1(A_102, B_103, A_3), B_103) | ~r1_tarski(A_3, k2_zfmisc_1(A_102, B_103)))), inference(resolution, [status(thm)], [c_10, c_564])).
% 8.01/2.77  tff(c_3417, plain, (r1_tarski('#skF_4', k2_relat_1('#skF_7')) | ~r1_tarski(k2_funct_1('#skF_6'), k2_zfmisc_1('#skF_5', k2_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_3411, c_583])).
% 8.01/2.77  tff(c_3425, plain, (~r1_tarski(k2_funct_1('#skF_6'), k2_zfmisc_1('#skF_5', k2_relat_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_516, c_3417])).
% 8.01/2.77  tff(c_3428, plain, (![B_273]: (r1_tarski(k2_funct_1('#skF_6'), k2_zfmisc_1('#skF_5', B_273)) | r2_hidden('#skF_3'('#skF_5', B_273, k2_funct_1('#skF_6')), '#skF_5'))), inference(resolution, [status(thm)], [c_3267, c_8])).
% 8.01/2.77  tff(c_3431, plain, (r1_tarski(k2_funct_1('#skF_6'), k2_zfmisc_1('#skF_5', k2_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_3428, c_3262])).
% 8.01/2.77  tff(c_3435, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3425, c_3431])).
% 8.01/2.77  tff(c_3437, plain, (r2_hidden('#skF_3'('#skF_5', k2_relat_1('#skF_7'), k2_funct_1('#skF_6')), '#skF_5')), inference(splitRight, [status(thm)], [c_3175])).
% 8.01/2.77  tff(c_68, plain, (![C_41, B_40]: (~r2_hidden(k1_funct_1(C_41, '#skF_3'(k1_relat_1(C_41), B_40, C_41)), B_40) | m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_41), B_40))) | ~v1_funct_1(C_41) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_169])).
% 8.01/2.77  tff(c_1624, plain, (![C_41]: (m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_41), k2_relat_1('#skF_7')))) | ~v1_funct_1(C_41) | ~v1_relat_1(C_41) | ~r2_hidden(k1_funct_1(C_41, '#skF_3'(k1_relat_1(C_41), k2_relat_1('#skF_7'), C_41)), '#skF_4'))), inference(resolution, [status(thm)], [c_1615, c_68])).
% 8.01/2.77  tff(c_3145, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_6')), k2_relat_1('#skF_7')))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~r2_hidden('#skF_3'(k1_relat_1(k2_funct_1('#skF_6')), k2_relat_1('#skF_7'), k2_funct_1('#skF_6')), '#skF_5')), inference(resolution, [status(thm)], [c_3141, c_1624])).
% 8.01/2.77  tff(c_3172, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k2_relat_1('#skF_7')))) | ~r2_hidden('#skF_3'('#skF_5', k2_relat_1('#skF_7'), k2_funct_1('#skF_6')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2878, c_2575, c_1766, c_2878, c_3145])).
% 8.01/2.77  tff(c_3727, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k2_relat_1('#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_3437, c_3172])).
% 8.01/2.77  tff(c_3753, plain, (k2_relset_1('#skF_5', k2_relat_1('#skF_7'), k2_funct_1('#skF_6'))=k2_relat_1(k2_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_3727, c_42])).
% 8.01/2.77  tff(c_3779, plain, (k2_relset_1('#skF_5', k2_relat_1('#skF_7'), k2_funct_1('#skF_6'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2649, c_3753])).
% 8.01/2.77  tff(c_3799, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_relat_1('#skF_7'))) | ~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k2_relat_1('#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_3779, c_38])).
% 8.01/2.77  tff(c_3808, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_3727, c_3799])).
% 8.01/2.77  tff(c_3822, plain, (r1_tarski('#skF_4', k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_3808, c_8])).
% 8.01/2.77  tff(c_3829, plain, $false, inference(negUnitSimplification, [status(thm)], [c_516, c_3822])).
% 8.01/2.77  tff(c_3830, plain, (k2_relat_1('#skF_7')='#skF_4'), inference(splitRight, [status(thm)], [c_513])).
% 8.01/2.77  tff(c_4385, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_5', '#skF_4', '#skF_7')='#skF_5' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_90, c_4362])).
% 8.01/2.77  tff(c_4403, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_367, c_4385])).
% 8.01/2.77  tff(c_4404, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_84, c_4403])).
% 8.01/2.77  tff(c_5533, plain, (![A_423, B_424]: (r2_hidden('#skF_2'(A_423, B_424), k1_relat_1(B_424)) | k2_funct_1(A_423)=B_424 | k2_relat_1(A_423)!=k1_relat_1(B_424) | k2_relat_1(B_424)!=k1_relat_1(A_423) | ~v2_funct_1(A_423) | ~v1_funct_1(B_424) | ~v1_relat_1(B_424) | ~v1_funct_1(A_423) | ~v1_relat_1(A_423))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.01/2.77  tff(c_5536, plain, (![A_423]: (r2_hidden('#skF_2'(A_423, '#skF_7'), '#skF_5') | k2_funct_1(A_423)='#skF_7' | k2_relat_1(A_423)!=k1_relat_1('#skF_7') | k2_relat_1('#skF_7')!=k1_relat_1(A_423) | ~v2_funct_1(A_423) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~v1_funct_1(A_423) | ~v1_relat_1(A_423))), inference(superposition, [status(thm), theory('equality')], [c_4404, c_5533])).
% 8.01/2.77  tff(c_5544, plain, (![A_423]: (r2_hidden('#skF_2'(A_423, '#skF_7'), '#skF_5') | k2_funct_1(A_423)='#skF_7' | k2_relat_1(A_423)!='#skF_5' | k1_relat_1(A_423)!='#skF_4' | ~v2_funct_1(A_423) | ~v1_funct_1(A_423) | ~v1_relat_1(A_423))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_94, c_3830, c_4404, c_5536])).
% 8.01/2.77  tff(c_5478, plain, (![A_413, B_414]: (r2_hidden('#skF_1'(A_413, B_414), k1_relat_1(A_413)) | k2_funct_1(A_413)=B_414 | k2_relat_1(A_413)!=k1_relat_1(B_414) | k2_relat_1(B_414)!=k1_relat_1(A_413) | ~v2_funct_1(A_413) | ~v1_funct_1(B_414) | ~v1_relat_1(B_414) | ~v1_funct_1(A_413) | ~v1_relat_1(A_413))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.01/2.77  tff(c_5484, plain, (![B_414]: (r2_hidden('#skF_1'('#skF_6', B_414), '#skF_4') | k2_funct_1('#skF_6')=B_414 | k2_relat_1('#skF_6')!=k1_relat_1(B_414) | k2_relat_1(B_414)!=k1_relat_1('#skF_6') | ~v2_funct_1('#skF_6') | ~v1_funct_1(B_414) | ~v1_relat_1(B_414) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_4400, c_5478])).
% 8.01/2.77  tff(c_5491, plain, (![B_414]: (r2_hidden('#skF_1'('#skF_6', B_414), '#skF_4') | k2_funct_1('#skF_6')=B_414 | k1_relat_1(B_414)!='#skF_5' | k2_relat_1(B_414)!='#skF_4' | ~v1_funct_1(B_414) | ~v1_relat_1(B_414))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_100, c_86, c_4400, c_296, c_5484])).
% 8.01/2.77  tff(c_5628, plain, (![A_433, B_434]: (k1_funct_1(A_433, '#skF_1'(A_433, B_434))='#skF_2'(A_433, B_434) | k1_funct_1(B_434, '#skF_2'(A_433, B_434))='#skF_1'(A_433, B_434) | k2_funct_1(A_433)=B_434 | k2_relat_1(A_433)!=k1_relat_1(B_434) | k2_relat_1(B_434)!=k1_relat_1(A_433) | ~v2_funct_1(A_433) | ~v1_funct_1(B_434) | ~v1_relat_1(B_434) | ~v1_funct_1(A_433) | ~v1_relat_1(A_433))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.01/2.77  tff(c_5646, plain, (![B_434]: (r2_hidden('#skF_2'('#skF_6', B_434), '#skF_5') | ~r2_hidden('#skF_1'('#skF_6', B_434), '#skF_4') | k1_funct_1(B_434, '#skF_2'('#skF_6', B_434))='#skF_1'('#skF_6', B_434) | k2_funct_1('#skF_6')=B_434 | k2_relat_1('#skF_6')!=k1_relat_1(B_434) | k2_relat_1(B_434)!=k1_relat_1('#skF_6') | ~v2_funct_1('#skF_6') | ~v1_funct_1(B_434) | ~v1_relat_1(B_434) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_5628, c_108])).
% 8.01/2.77  tff(c_5685, plain, (![B_434]: (r2_hidden('#skF_2'('#skF_6', B_434), '#skF_5') | ~r2_hidden('#skF_1'('#skF_6', B_434), '#skF_4') | k1_funct_1(B_434, '#skF_2'('#skF_6', B_434))='#skF_1'('#skF_6', B_434) | k2_funct_1('#skF_6')=B_434 | k1_relat_1(B_434)!='#skF_5' | k2_relat_1(B_434)!='#skF_4' | ~v1_funct_1(B_434) | ~v1_relat_1(B_434))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_100, c_86, c_4400, c_296, c_5646])).
% 8.01/2.77  tff(c_102, plain, (![E_50]: (k1_funct_1('#skF_6', k1_funct_1('#skF_7', E_50))=E_50 | ~r2_hidden(E_50, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_210])).
% 8.01/2.77  tff(c_5664, plain, (![A_433]: (k1_funct_1('#skF_6', '#skF_1'(A_433, '#skF_7'))='#skF_2'(A_433, '#skF_7') | ~r2_hidden('#skF_2'(A_433, '#skF_7'), '#skF_5') | k1_funct_1(A_433, '#skF_1'(A_433, '#skF_7'))='#skF_2'(A_433, '#skF_7') | k2_funct_1(A_433)='#skF_7' | k2_relat_1(A_433)!=k1_relat_1('#skF_7') | k2_relat_1('#skF_7')!=k1_relat_1(A_433) | ~v2_funct_1(A_433) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~v1_funct_1(A_433) | ~v1_relat_1(A_433))), inference(superposition, [status(thm), theory('equality')], [c_5628, c_102])).
% 8.01/2.77  tff(c_7031, plain, (![A_488]: (k1_funct_1('#skF_6', '#skF_1'(A_488, '#skF_7'))='#skF_2'(A_488, '#skF_7') | ~r2_hidden('#skF_2'(A_488, '#skF_7'), '#skF_5') | k1_funct_1(A_488, '#skF_1'(A_488, '#skF_7'))='#skF_2'(A_488, '#skF_7') | k2_funct_1(A_488)='#skF_7' | k2_relat_1(A_488)!='#skF_5' | k1_relat_1(A_488)!='#skF_4' | ~v2_funct_1(A_488) | ~v1_funct_1(A_488) | ~v1_relat_1(A_488))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_94, c_3830, c_4404, c_5664])).
% 8.01/2.77  tff(c_7034, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_6', '#skF_7'))='#skF_2'('#skF_6', '#skF_7') | k2_relat_1('#skF_6')!='#skF_5' | k1_relat_1('#skF_6')!='#skF_4' | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~r2_hidden('#skF_1'('#skF_6', '#skF_7'), '#skF_4') | k1_funct_1('#skF_7', '#skF_2'('#skF_6', '#skF_7'))='#skF_1'('#skF_6', '#skF_7') | k2_funct_1('#skF_6')='#skF_7' | k1_relat_1('#skF_7')!='#skF_5' | k2_relat_1('#skF_7')!='#skF_4' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_5685, c_7031])).
% 8.01/2.77  tff(c_7037, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_6', '#skF_7'))='#skF_2'('#skF_6', '#skF_7') | ~r2_hidden('#skF_1'('#skF_6', '#skF_7'), '#skF_4') | k1_funct_1('#skF_7', '#skF_2'('#skF_6', '#skF_7'))='#skF_1'('#skF_6', '#skF_7') | k2_funct_1('#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_150, c_94, c_3830, c_4404, c_147, c_100, c_86, c_4400, c_296, c_7034])).
% 8.01/2.77  tff(c_7038, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_6', '#skF_7'))='#skF_2'('#skF_6', '#skF_7') | ~r2_hidden('#skF_1'('#skF_6', '#skF_7'), '#skF_4') | k1_funct_1('#skF_7', '#skF_2'('#skF_6', '#skF_7'))='#skF_1'('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_80, c_7037])).
% 8.01/2.77  tff(c_7083, plain, (~r2_hidden('#skF_1'('#skF_6', '#skF_7'), '#skF_4')), inference(splitLeft, [status(thm)], [c_7038])).
% 8.01/2.77  tff(c_7086, plain, (k2_funct_1('#skF_6')='#skF_7' | k1_relat_1('#skF_7')!='#skF_5' | k2_relat_1('#skF_7')!='#skF_4' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_5491, c_7083])).
% 8.01/2.77  tff(c_7089, plain, (k2_funct_1('#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_150, c_94, c_3830, c_4404, c_7086])).
% 8.01/2.77  tff(c_7091, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_7089])).
% 8.01/2.77  tff(c_7093, plain, (r2_hidden('#skF_1'('#skF_6', '#skF_7'), '#skF_4')), inference(splitRight, [status(thm)], [c_7038])).
% 8.01/2.77  tff(c_5638, plain, (![B_434]: (k1_funct_1('#skF_7', '#skF_2'('#skF_6', B_434))='#skF_1'('#skF_6', B_434) | ~r2_hidden('#skF_1'('#skF_6', B_434), '#skF_4') | k1_funct_1(B_434, '#skF_2'('#skF_6', B_434))='#skF_1'('#skF_6', B_434) | k2_funct_1('#skF_6')=B_434 | k2_relat_1('#skF_6')!=k1_relat_1(B_434) | k2_relat_1(B_434)!=k1_relat_1('#skF_6') | ~v2_funct_1('#skF_6') | ~v1_funct_1(B_434) | ~v1_relat_1(B_434) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_5628, c_106])).
% 8.01/2.77  tff(c_5681, plain, (![B_434]: (k1_funct_1('#skF_7', '#skF_2'('#skF_6', B_434))='#skF_1'('#skF_6', B_434) | ~r2_hidden('#skF_1'('#skF_6', B_434), '#skF_4') | k1_funct_1(B_434, '#skF_2'('#skF_6', B_434))='#skF_1'('#skF_6', B_434) | k2_funct_1('#skF_6')=B_434 | k1_relat_1(B_434)!='#skF_5' | k2_relat_1(B_434)!='#skF_4' | ~v1_funct_1(B_434) | ~v1_relat_1(B_434))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_100, c_86, c_4400, c_296, c_5638])).
% 8.01/2.77  tff(c_7095, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_6', '#skF_7'))='#skF_1'('#skF_6', '#skF_7') | k2_funct_1('#skF_6')='#skF_7' | k1_relat_1('#skF_7')!='#skF_5' | k2_relat_1('#skF_7')!='#skF_4' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_7093, c_5681])).
% 8.01/2.77  tff(c_7098, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_6', '#skF_7'))='#skF_1'('#skF_6', '#skF_7') | k2_funct_1('#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_150, c_94, c_3830, c_4404, c_7095])).
% 8.01/2.77  tff(c_7099, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_6', '#skF_7'))='#skF_1'('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_80, c_7098])).
% 8.01/2.77  tff(c_30, plain, (![B_20, A_14]: (k1_funct_1(B_20, '#skF_2'(A_14, B_20))!='#skF_1'(A_14, B_20) | k1_funct_1(A_14, '#skF_1'(A_14, B_20))!='#skF_2'(A_14, B_20) | k2_funct_1(A_14)=B_20 | k2_relat_1(A_14)!=k1_relat_1(B_20) | k2_relat_1(B_20)!=k1_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.01/2.77  tff(c_7103, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_6', '#skF_7'))!='#skF_2'('#skF_6', '#skF_7') | k2_funct_1('#skF_6')='#skF_7' | k2_relat_1('#skF_6')!=k1_relat_1('#skF_7') | k2_relat_1('#skF_7')!=k1_relat_1('#skF_6') | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_7099, c_30])).
% 8.01/2.77  tff(c_7124, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_6', '#skF_7'))!='#skF_2'('#skF_6', '#skF_7') | k2_funct_1('#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_147, c_100, c_150, c_94, c_86, c_3830, c_4400, c_296, c_4404, c_7103])).
% 8.01/2.77  tff(c_7125, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_6', '#skF_7'))!='#skF_2'('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_80, c_7124])).
% 8.01/2.77  tff(c_7112, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_6', '#skF_7'))='#skF_2'('#skF_6', '#skF_7') | ~r2_hidden('#skF_2'('#skF_6', '#skF_7'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7099, c_102])).
% 8.01/2.77  tff(c_7139, plain, (~r2_hidden('#skF_2'('#skF_6', '#skF_7'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_7125, c_7112])).
% 8.01/2.77  tff(c_7142, plain, (k2_funct_1('#skF_6')='#skF_7' | k2_relat_1('#skF_6')!='#skF_5' | k1_relat_1('#skF_6')!='#skF_4' | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_5544, c_7139])).
% 8.01/2.77  tff(c_7148, plain, (k2_funct_1('#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_147, c_100, c_86, c_4400, c_296, c_7142])).
% 8.01/2.77  tff(c_7150, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_7148])).
% 8.01/2.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.01/2.77  
% 8.01/2.77  Inference rules
% 8.01/2.77  ----------------------
% 8.01/2.77  #Ref     : 0
% 8.01/2.77  #Sup     : 1419
% 8.01/2.77  #Fact    : 0
% 8.01/2.77  #Define  : 0
% 8.01/2.77  #Split   : 28
% 8.01/2.78  #Chain   : 0
% 8.01/2.78  #Close   : 0
% 8.01/2.78  
% 8.01/2.78  Ordering : KBO
% 8.01/2.78  
% 8.01/2.78  Simplification rules
% 8.01/2.78  ----------------------
% 8.01/2.78  #Subsume      : 251
% 8.01/2.78  #Demod        : 2023
% 8.01/2.78  #Tautology    : 532
% 8.01/2.78  #SimpNegUnit  : 78
% 8.01/2.78  #BackRed      : 47
% 8.01/2.78  
% 8.01/2.78  #Partial instantiations: 0
% 8.01/2.78  #Strategies tried      : 1
% 8.01/2.78  
% 8.01/2.78  Timing (in seconds)
% 8.01/2.78  ----------------------
% 8.01/2.78  Preprocessing        : 0.38
% 8.01/2.78  Parsing              : 0.20
% 8.01/2.78  CNF conversion       : 0.03
% 8.01/2.78  Main loop            : 1.59
% 8.01/2.78  Inferencing          : 0.57
% 8.01/2.78  Reduction            : 0.57
% 8.01/2.78  Demodulation         : 0.42
% 8.01/2.78  BG Simplification    : 0.06
% 8.01/2.78  Subsumption          : 0.27
% 8.01/2.78  Abstraction          : 0.07
% 8.01/2.78  MUC search           : 0.00
% 8.01/2.78  Cooper               : 0.00
% 8.01/2.78  Total                : 2.04
% 8.01/2.78  Index Insertion      : 0.00
% 8.01/2.78  Index Deletion       : 0.00
% 8.01/2.78  Index Matching       : 0.00
% 8.01/2.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
