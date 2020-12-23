%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:51 EST 2020

% Result     : Theorem 4.63s
% Output     : CNFRefutation 4.84s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 591 expanded)
%              Number of leaves         :   39 ( 195 expanded)
%              Depth                    :   13
%              Number of atoms          :  222 (1972 expanded)
%              Number of equality atoms :   47 ( 630 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_150,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_relset_1(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_96,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_127,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( v1_partfun1(C,A)
              & v1_partfun1(D,A)
              & r1_partfun1(C,D) )
           => C = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_710,plain,(
    ! [A_142,B_143,C_144,D_145] :
      ( r2_relset_1(A_142,B_143,C_144,C_144)
      | ~ m1_subset_1(D_145,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143)))
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_752,plain,(
    ! [C_146] :
      ( r2_relset_1('#skF_2','#skF_3',C_146,C_146)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_58,c_710])).

tff(c_769,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_752])).

tff(c_48,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_65,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_54,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_616,plain,(
    ! [C_134,A_135,B_136] :
      ( v1_partfun1(C_134,A_135)
      | ~ v1_funct_2(C_134,A_135,B_136)
      | ~ v1_funct_1(C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136)))
      | v1_xboole_0(B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_630,plain,
    ( v1_partfun1('#skF_5','#skF_2')
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_616])).

tff(c_642,plain,
    ( v1_partfun1('#skF_5','#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_630])).

tff(c_647,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_642])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    ! [A_25] :
      ( r2_hidden('#skF_1'(A_25),A_25)
      | k1_xboole_0 = A_25 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_189,plain,(
    ! [C_64,B_65,A_66] :
      ( ~ v1_xboole_0(C_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(C_64))
      | ~ r2_hidden(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_220,plain,(
    ! [B_70,A_71,A_72] :
      ( ~ v1_xboole_0(B_70)
      | ~ r2_hidden(A_71,A_72)
      | ~ r1_tarski(A_72,B_70) ) ),
    inference(resolution,[status(thm)],[c_12,c_189])).

tff(c_224,plain,(
    ! [B_73,A_74] :
      ( ~ v1_xboole_0(B_73)
      | ~ r1_tarski(A_74,B_73)
      | k1_xboole_0 = A_74 ) ),
    inference(resolution,[status(thm)],[c_34,c_220])).

tff(c_241,plain,(
    ! [B_2] :
      ( ~ v1_xboole_0(B_2)
      | k1_xboole_0 = B_2 ) ),
    inference(resolution,[status(thm)],[c_6,c_224])).

tff(c_650,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_647,c_241])).

tff(c_654,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_650])).

tff(c_656,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_642])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_60,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_633,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_616])).

tff(c_645,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_633])).

tff(c_657,plain,(
    v1_partfun1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_656,c_645])).

tff(c_655,plain,(
    v1_partfun1('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_642])).

tff(c_50,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_787,plain,(
    ! [D_149,C_150,A_151,B_152] :
      ( D_149 = C_150
      | ~ r1_partfun1(C_150,D_149)
      | ~ v1_partfun1(D_149,A_151)
      | ~ v1_partfun1(C_150,A_151)
      | ~ m1_subset_1(D_149,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152)))
      | ~ v1_funct_1(D_149)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152)))
      | ~ v1_funct_1(C_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_789,plain,(
    ! [A_151,B_152] :
      ( '#skF_5' = '#skF_4'
      | ~ v1_partfun1('#skF_5',A_151)
      | ~ v1_partfun1('#skF_4',A_151)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_151,B_152)))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_151,B_152)))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_787])).

tff(c_792,plain,(
    ! [A_151,B_152] :
      ( '#skF_5' = '#skF_4'
      | ~ v1_partfun1('#skF_5',A_151)
      | ~ v1_partfun1('#skF_4',A_151)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_151,B_152)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_151,B_152))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_56,c_789])).

tff(c_1582,plain,(
    ! [A_235,B_236] :
      ( ~ v1_partfun1('#skF_5',A_235)
      | ~ v1_partfun1('#skF_4',A_235)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_235,B_236)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_235,B_236))) ) ),
    inference(splitLeft,[status(thm)],[c_792])).

tff(c_1591,plain,
    ( ~ v1_partfun1('#skF_5','#skF_2')
    | ~ v1_partfun1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_52,c_1582])).

tff(c_1597,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_657,c_655,c_1591])).

tff(c_1598,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_792])).

tff(c_46,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_1610,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1598,c_46])).

tff(c_1623,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_769,c_1610])).

tff(c_1625,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1624,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1630,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1625,c_1624])).

tff(c_1647,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1630,c_58])).

tff(c_1671,plain,(
    ! [C_246,A_247,B_248] :
      ( v1_relat_1(C_246)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(A_247,B_248))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1687,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1647,c_1671])).

tff(c_22,plain,(
    ! [A_14] :
      ( k2_relat_1(A_14) != k1_xboole_0
      | k1_xboole_0 = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1669,plain,(
    ! [A_14] :
      ( k2_relat_1(A_14) != '#skF_3'
      | A_14 = '#skF_3'
      | ~ v1_relat_1(A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1625,c_1625,c_22])).

tff(c_1696,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1687,c_1669])).

tff(c_1716,plain,(
    k2_relat_1('#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1696])).

tff(c_2016,plain,(
    ! [C_291,B_292,A_293] :
      ( v5_relat_1(C_291,B_292)
      | ~ m1_subset_1(C_291,k1_zfmisc_1(k2_zfmisc_1(A_293,B_292))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2029,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1647,c_2016])).

tff(c_1976,plain,(
    ! [B_286,A_287] :
      ( r1_tarski(k2_relat_1(B_286),A_287)
      | ~ v5_relat_1(B_286,A_287)
      | ~ v1_relat_1(B_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1641,plain,(
    ! [A_3] : m1_subset_1('#skF_3',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1625,c_8])).

tff(c_1651,plain,(
    ! [A_242,B_243] :
      ( r1_tarski(A_242,B_243)
      | ~ m1_subset_1(A_242,k1_zfmisc_1(B_243)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1667,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(resolution,[status(thm)],[c_1641,c_1651])).

tff(c_1718,plain,(
    ! [B_249,A_250] :
      ( B_249 = A_250
      | ~ r1_tarski(B_249,A_250)
      | ~ r1_tarski(A_250,B_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1729,plain,(
    ! [A_3] :
      ( A_3 = '#skF_3'
      | ~ r1_tarski(A_3,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1667,c_1718])).

tff(c_1995,plain,(
    ! [B_286] :
      ( k2_relat_1(B_286) = '#skF_3'
      | ~ v5_relat_1(B_286,'#skF_3')
      | ~ v1_relat_1(B_286) ) ),
    inference(resolution,[status(thm)],[c_1976,c_1729])).

tff(c_2034,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2029,c_1995])).

tff(c_2037,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1687,c_2034])).

tff(c_2039,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1716,c_2037])).

tff(c_2040,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1696])).

tff(c_2046,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2040,c_1667])).

tff(c_2053,plain,(
    ! [A_3] : m1_subset_1('#skF_4',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2040,c_1641])).

tff(c_2783,plain,(
    ! [A_410,B_411,C_412,D_413] :
      ( r2_relset_1(A_410,B_411,C_412,C_412)
      | ~ m1_subset_1(D_413,k1_zfmisc_1(k2_zfmisc_1(A_410,B_411)))
      | ~ m1_subset_1(C_412,k1_zfmisc_1(k2_zfmisc_1(A_410,B_411))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2969,plain,(
    ! [A_432,B_433,C_434,A_435] :
      ( r2_relset_1(A_432,B_433,C_434,C_434)
      | ~ m1_subset_1(C_434,k1_zfmisc_1(k2_zfmisc_1(A_432,B_433)))
      | ~ r1_tarski(A_435,k2_zfmisc_1(A_432,B_433)) ) ),
    inference(resolution,[status(thm)],[c_12,c_2783])).

tff(c_3088,plain,(
    ! [A_445,B_446,A_447] :
      ( r2_relset_1(A_445,B_446,'#skF_4','#skF_4')
      | ~ r1_tarski(A_447,k2_zfmisc_1(A_445,B_446)) ) ),
    inference(resolution,[status(thm)],[c_2053,c_2969])).

tff(c_3108,plain,(
    ! [A_445,B_446] : r2_relset_1(A_445,B_446,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_2046,c_3088])).

tff(c_1646,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1630,c_52])).

tff(c_1688,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1646,c_1671])).

tff(c_1704,plain,
    ( k2_relat_1('#skF_5') != '#skF_3'
    | '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1688,c_1669])).

tff(c_2102,plain,
    ( k2_relat_1('#skF_5') != '#skF_4'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2040,c_2040,c_1704])).

tff(c_2103,plain,(
    k2_relat_1('#skF_5') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2102])).

tff(c_2049,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2040,c_2040,c_1646])).

tff(c_2269,plain,(
    ! [C_323,B_324,A_325] :
      ( v5_relat_1(C_323,B_324)
      | ~ m1_subset_1(C_323,k1_zfmisc_1(k2_zfmisc_1(A_325,B_324))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2281,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_2049,c_2269])).

tff(c_2233,plain,(
    ! [B_320,A_321] :
      ( r1_tarski(k2_relat_1(B_320),A_321)
      | ~ v5_relat_1(B_320,A_321)
      | ~ v1_relat_1(B_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2076,plain,(
    ! [B_295,A_296] :
      ( B_295 = A_296
      | ~ r1_tarski(B_295,A_296)
      | ~ r1_tarski(A_296,B_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2081,plain,(
    ! [A_3] :
      ( A_3 = '#skF_4'
      | ~ r1_tarski(A_3,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2046,c_2076])).

tff(c_2257,plain,(
    ! [B_320] :
      ( k2_relat_1(B_320) = '#skF_4'
      | ~ v5_relat_1(B_320,'#skF_4')
      | ~ v1_relat_1(B_320) ) ),
    inference(resolution,[status(thm)],[c_2233,c_2081])).

tff(c_2287,plain,
    ( k2_relat_1('#skF_5') = '#skF_4'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2281,c_2257])).

tff(c_2290,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1688,c_2287])).

tff(c_2292,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2103,c_2290])).

tff(c_2293,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2102])).

tff(c_1643,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1630,c_46])).

tff(c_2051,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2040,c_2040,c_1643])).

tff(c_2297,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2293,c_2051])).

tff(c_3113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3108,c_2297])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:35:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.63/1.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.77/1.82  
% 4.77/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.77/1.82  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 4.77/1.82  
% 4.77/1.82  %Foreground sorts:
% 4.77/1.82  
% 4.77/1.82  
% 4.77/1.82  %Background operators:
% 4.77/1.82  
% 4.77/1.82  
% 4.77/1.82  %Foreground operators:
% 4.77/1.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.77/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.77/1.82  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.77/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.77/1.82  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.77/1.82  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.77/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.77/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.77/1.82  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.77/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.77/1.82  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.77/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.77/1.82  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.77/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.77/1.82  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.77/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.77/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.77/1.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.77/1.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.77/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.77/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.77/1.82  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.77/1.82  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.77/1.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.77/1.82  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 4.77/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.77/1.82  
% 4.84/1.84  tff(f_150, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_2)).
% 4.84/1.84  tff(f_80, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 4.84/1.84  tff(f_110, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 4.84/1.84  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.84/1.84  tff(f_96, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 4.84/1.84  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.84/1.84  tff(f_50, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.84/1.84  tff(f_127, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_partfun1)).
% 4.84/1.84  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.84/1.84  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 4.84/1.84  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.84/1.84  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 4.84/1.84  tff(f_33, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.84/1.84  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.84/1.84  tff(c_710, plain, (![A_142, B_143, C_144, D_145]: (r2_relset_1(A_142, B_143, C_144, C_144) | ~m1_subset_1(D_145, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.84/1.84  tff(c_752, plain, (![C_146]: (r2_relset_1('#skF_2', '#skF_3', C_146, C_146) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_58, c_710])).
% 4.84/1.84  tff(c_769, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_752])).
% 4.84/1.84  tff(c_48, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.84/1.84  tff(c_65, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_48])).
% 4.84/1.84  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.84/1.84  tff(c_54, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.84/1.84  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.84/1.84  tff(c_616, plain, (![C_134, A_135, B_136]: (v1_partfun1(C_134, A_135) | ~v1_funct_2(C_134, A_135, B_136) | ~v1_funct_1(C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))) | v1_xboole_0(B_136))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.84/1.84  tff(c_630, plain, (v1_partfun1('#skF_5', '#skF_2') | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_616])).
% 4.84/1.84  tff(c_642, plain, (v1_partfun1('#skF_5', '#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_630])).
% 4.84/1.84  tff(c_647, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_642])).
% 4.84/1.84  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.84/1.84  tff(c_34, plain, (![A_25]: (r2_hidden('#skF_1'(A_25), A_25) | k1_xboole_0=A_25)), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.84/1.84  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.84/1.84  tff(c_189, plain, (![C_64, B_65, A_66]: (~v1_xboole_0(C_64) | ~m1_subset_1(B_65, k1_zfmisc_1(C_64)) | ~r2_hidden(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.84/1.84  tff(c_220, plain, (![B_70, A_71, A_72]: (~v1_xboole_0(B_70) | ~r2_hidden(A_71, A_72) | ~r1_tarski(A_72, B_70))), inference(resolution, [status(thm)], [c_12, c_189])).
% 4.84/1.84  tff(c_224, plain, (![B_73, A_74]: (~v1_xboole_0(B_73) | ~r1_tarski(A_74, B_73) | k1_xboole_0=A_74)), inference(resolution, [status(thm)], [c_34, c_220])).
% 4.84/1.84  tff(c_241, plain, (![B_2]: (~v1_xboole_0(B_2) | k1_xboole_0=B_2)), inference(resolution, [status(thm)], [c_6, c_224])).
% 4.84/1.84  tff(c_650, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_647, c_241])).
% 4.84/1.84  tff(c_654, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_650])).
% 4.84/1.84  tff(c_656, plain, (~v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_642])).
% 4.84/1.84  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.84/1.84  tff(c_60, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.84/1.84  tff(c_633, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_58, c_616])).
% 4.84/1.84  tff(c_645, plain, (v1_partfun1('#skF_4', '#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_633])).
% 4.84/1.84  tff(c_657, plain, (v1_partfun1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_656, c_645])).
% 4.84/1.84  tff(c_655, plain, (v1_partfun1('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_642])).
% 4.84/1.84  tff(c_50, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.84/1.84  tff(c_787, plain, (![D_149, C_150, A_151, B_152]: (D_149=C_150 | ~r1_partfun1(C_150, D_149) | ~v1_partfun1(D_149, A_151) | ~v1_partfun1(C_150, A_151) | ~m1_subset_1(D_149, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))) | ~v1_funct_1(D_149) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))) | ~v1_funct_1(C_150))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.84/1.84  tff(c_789, plain, (![A_151, B_152]: ('#skF_5'='#skF_4' | ~v1_partfun1('#skF_5', A_151) | ~v1_partfun1('#skF_4', A_151) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_787])).
% 4.84/1.84  tff(c_792, plain, (![A_151, B_152]: ('#skF_5'='#skF_4' | ~v1_partfun1('#skF_5', A_151) | ~v1_partfun1('#skF_4', A_151) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_56, c_789])).
% 4.84/1.84  tff(c_1582, plain, (![A_235, B_236]: (~v1_partfun1('#skF_5', A_235) | ~v1_partfun1('#skF_4', A_235) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_235, B_236))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_235, B_236))))), inference(splitLeft, [status(thm)], [c_792])).
% 4.84/1.84  tff(c_1591, plain, (~v1_partfun1('#skF_5', '#skF_2') | ~v1_partfun1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_52, c_1582])).
% 4.84/1.84  tff(c_1597, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_657, c_655, c_1591])).
% 4.84/1.84  tff(c_1598, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_792])).
% 4.84/1.84  tff(c_46, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.84/1.84  tff(c_1610, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1598, c_46])).
% 4.84/1.84  tff(c_1623, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_769, c_1610])).
% 4.84/1.84  tff(c_1625, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_48])).
% 4.84/1.84  tff(c_1624, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_48])).
% 4.84/1.84  tff(c_1630, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1625, c_1624])).
% 4.84/1.84  tff(c_1647, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1630, c_58])).
% 4.84/1.84  tff(c_1671, plain, (![C_246, A_247, B_248]: (v1_relat_1(C_246) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(A_247, B_248))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.84/1.84  tff(c_1687, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1647, c_1671])).
% 4.84/1.84  tff(c_22, plain, (![A_14]: (k2_relat_1(A_14)!=k1_xboole_0 | k1_xboole_0=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.84/1.84  tff(c_1669, plain, (![A_14]: (k2_relat_1(A_14)!='#skF_3' | A_14='#skF_3' | ~v1_relat_1(A_14))), inference(demodulation, [status(thm), theory('equality')], [c_1625, c_1625, c_22])).
% 4.84/1.84  tff(c_1696, plain, (k2_relat_1('#skF_4')!='#skF_3' | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_1687, c_1669])).
% 4.84/1.84  tff(c_1716, plain, (k2_relat_1('#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_1696])).
% 4.84/1.84  tff(c_2016, plain, (![C_291, B_292, A_293]: (v5_relat_1(C_291, B_292) | ~m1_subset_1(C_291, k1_zfmisc_1(k2_zfmisc_1(A_293, B_292))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.84/1.84  tff(c_2029, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1647, c_2016])).
% 4.84/1.84  tff(c_1976, plain, (![B_286, A_287]: (r1_tarski(k2_relat_1(B_286), A_287) | ~v5_relat_1(B_286, A_287) | ~v1_relat_1(B_286))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.84/1.84  tff(c_8, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.84/1.84  tff(c_1641, plain, (![A_3]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_1625, c_8])).
% 4.84/1.84  tff(c_1651, plain, (![A_242, B_243]: (r1_tarski(A_242, B_243) | ~m1_subset_1(A_242, k1_zfmisc_1(B_243)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.84/1.84  tff(c_1667, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(resolution, [status(thm)], [c_1641, c_1651])).
% 4.84/1.84  tff(c_1718, plain, (![B_249, A_250]: (B_249=A_250 | ~r1_tarski(B_249, A_250) | ~r1_tarski(A_250, B_249))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.84/1.84  tff(c_1729, plain, (![A_3]: (A_3='#skF_3' | ~r1_tarski(A_3, '#skF_3'))), inference(resolution, [status(thm)], [c_1667, c_1718])).
% 4.84/1.84  tff(c_1995, plain, (![B_286]: (k2_relat_1(B_286)='#skF_3' | ~v5_relat_1(B_286, '#skF_3') | ~v1_relat_1(B_286))), inference(resolution, [status(thm)], [c_1976, c_1729])).
% 4.84/1.84  tff(c_2034, plain, (k2_relat_1('#skF_4')='#skF_3' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2029, c_1995])).
% 4.84/1.84  tff(c_2037, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1687, c_2034])).
% 4.84/1.84  tff(c_2039, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1716, c_2037])).
% 4.84/1.84  tff(c_2040, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_1696])).
% 4.84/1.84  tff(c_2046, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2040, c_1667])).
% 4.84/1.84  tff(c_2053, plain, (![A_3]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_2040, c_1641])).
% 4.84/1.84  tff(c_2783, plain, (![A_410, B_411, C_412, D_413]: (r2_relset_1(A_410, B_411, C_412, C_412) | ~m1_subset_1(D_413, k1_zfmisc_1(k2_zfmisc_1(A_410, B_411))) | ~m1_subset_1(C_412, k1_zfmisc_1(k2_zfmisc_1(A_410, B_411))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.84/1.84  tff(c_2969, plain, (![A_432, B_433, C_434, A_435]: (r2_relset_1(A_432, B_433, C_434, C_434) | ~m1_subset_1(C_434, k1_zfmisc_1(k2_zfmisc_1(A_432, B_433))) | ~r1_tarski(A_435, k2_zfmisc_1(A_432, B_433)))), inference(resolution, [status(thm)], [c_12, c_2783])).
% 4.84/1.84  tff(c_3088, plain, (![A_445, B_446, A_447]: (r2_relset_1(A_445, B_446, '#skF_4', '#skF_4') | ~r1_tarski(A_447, k2_zfmisc_1(A_445, B_446)))), inference(resolution, [status(thm)], [c_2053, c_2969])).
% 4.84/1.84  tff(c_3108, plain, (![A_445, B_446]: (r2_relset_1(A_445, B_446, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_2046, c_3088])).
% 4.84/1.84  tff(c_1646, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1630, c_52])).
% 4.84/1.84  tff(c_1688, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1646, c_1671])).
% 4.84/1.84  tff(c_1704, plain, (k2_relat_1('#skF_5')!='#skF_3' | '#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_1688, c_1669])).
% 4.84/1.84  tff(c_2102, plain, (k2_relat_1('#skF_5')!='#skF_4' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2040, c_2040, c_1704])).
% 4.84/1.84  tff(c_2103, plain, (k2_relat_1('#skF_5')!='#skF_4'), inference(splitLeft, [status(thm)], [c_2102])).
% 4.84/1.84  tff(c_2049, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2040, c_2040, c_1646])).
% 4.84/1.84  tff(c_2269, plain, (![C_323, B_324, A_325]: (v5_relat_1(C_323, B_324) | ~m1_subset_1(C_323, k1_zfmisc_1(k2_zfmisc_1(A_325, B_324))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.84/1.84  tff(c_2281, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_2049, c_2269])).
% 4.84/1.84  tff(c_2233, plain, (![B_320, A_321]: (r1_tarski(k2_relat_1(B_320), A_321) | ~v5_relat_1(B_320, A_321) | ~v1_relat_1(B_320))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.84/1.84  tff(c_2076, plain, (![B_295, A_296]: (B_295=A_296 | ~r1_tarski(B_295, A_296) | ~r1_tarski(A_296, B_295))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.84/1.84  tff(c_2081, plain, (![A_3]: (A_3='#skF_4' | ~r1_tarski(A_3, '#skF_4'))), inference(resolution, [status(thm)], [c_2046, c_2076])).
% 4.84/1.84  tff(c_2257, plain, (![B_320]: (k2_relat_1(B_320)='#skF_4' | ~v5_relat_1(B_320, '#skF_4') | ~v1_relat_1(B_320))), inference(resolution, [status(thm)], [c_2233, c_2081])).
% 4.84/1.84  tff(c_2287, plain, (k2_relat_1('#skF_5')='#skF_4' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2281, c_2257])).
% 4.84/1.84  tff(c_2290, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1688, c_2287])).
% 4.84/1.84  tff(c_2292, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2103, c_2290])).
% 4.84/1.84  tff(c_2293, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_2102])).
% 4.84/1.84  tff(c_1643, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1630, c_46])).
% 4.84/1.84  tff(c_2051, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2040, c_2040, c_1643])).
% 4.84/1.84  tff(c_2297, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2293, c_2051])).
% 4.84/1.84  tff(c_3113, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3108, c_2297])).
% 4.84/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.84/1.84  
% 4.84/1.84  Inference rules
% 4.84/1.84  ----------------------
% 4.84/1.84  #Ref     : 0
% 4.84/1.84  #Sup     : 597
% 4.84/1.84  #Fact    : 0
% 4.84/1.84  #Define  : 0
% 4.84/1.84  #Split   : 28
% 4.84/1.84  #Chain   : 0
% 4.84/1.84  #Close   : 0
% 4.84/1.84  
% 4.84/1.84  Ordering : KBO
% 4.84/1.84  
% 4.84/1.84  Simplification rules
% 4.84/1.84  ----------------------
% 4.84/1.84  #Subsume      : 92
% 4.84/1.84  #Demod        : 464
% 4.84/1.84  #Tautology    : 243
% 4.84/1.84  #SimpNegUnit  : 10
% 4.84/1.84  #BackRed      : 58
% 4.84/1.84  
% 4.84/1.84  #Partial instantiations: 0
% 4.84/1.84  #Strategies tried      : 1
% 4.84/1.84  
% 4.84/1.84  Timing (in seconds)
% 4.84/1.84  ----------------------
% 4.84/1.85  Preprocessing        : 0.33
% 4.84/1.85  Parsing              : 0.18
% 4.84/1.85  CNF conversion       : 0.02
% 4.84/1.85  Main loop            : 0.74
% 4.84/1.85  Inferencing          : 0.27
% 4.84/1.85  Reduction            : 0.23
% 4.84/1.85  Demodulation         : 0.16
% 4.84/1.85  BG Simplification    : 0.03
% 4.84/1.85  Subsumption          : 0.13
% 4.84/1.85  Abstraction          : 0.03
% 4.84/1.85  MUC search           : 0.00
% 4.84/1.85  Cooper               : 0.00
% 4.84/1.85  Total                : 1.11
% 4.84/1.85  Index Insertion      : 0.00
% 4.84/1.85  Index Deletion       : 0.00
% 4.84/1.85  Index Matching       : 0.00
% 4.84/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
