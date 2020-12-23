%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:19 EST 2020

% Result     : Theorem 10.30s
% Output     : CNFRefutation 10.30s
% Verified   : 
% Statistics : Number of formulae       :  293 (2312 expanded)
%              Number of leaves         :   35 ( 755 expanded)
%              Depth                    :   18
%              Number of atoms          :  614 (6985 expanded)
%              Number of equality atoms :  262 (1918 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_141,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_funct_2)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_120,axiom,(
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

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_58,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_72,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_70,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_66,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_62,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_14740,plain,(
    ! [A_1052,B_1053,C_1054] :
      ( k1_relset_1(A_1052,B_1053,C_1054) = k1_relat_1(C_1054)
      | ~ m1_subset_1(C_1054,k1_zfmisc_1(k2_zfmisc_1(A_1052,B_1053))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_14774,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_14740])).

tff(c_64,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_9630,plain,(
    ! [A_738,B_739,D_740] :
      ( r2_relset_1(A_738,B_739,D_740,D_740)
      | ~ m1_subset_1(D_740,k1_zfmisc_1(k2_zfmisc_1(A_738,B_739))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_9656,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_9630])).

tff(c_68,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_14775,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_14740])).

tff(c_15326,plain,(
    ! [B_1100,A_1101,C_1102] :
      ( k1_xboole_0 = B_1100
      | k1_relset_1(A_1101,B_1100,C_1102) = A_1101
      | ~ v1_funct_2(C_1102,A_1101,B_1100)
      | ~ m1_subset_1(C_1102,k1_zfmisc_1(k2_zfmisc_1(A_1101,B_1100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_15352,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_15326])).

tff(c_15375,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_14775,c_15352])).

tff(c_15385,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_15375])).

tff(c_164,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_190,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_164])).

tff(c_480,plain,(
    ! [A_96,B_97,D_98] :
      ( r2_relset_1(A_96,B_97,D_98,D_98)
      | ~ m1_subset_1(D_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_506,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_480])).

tff(c_2226,plain,(
    ! [A_228,B_229,C_230] :
      ( k1_relset_1(A_228,B_229,C_230) = k1_relat_1(C_230)
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1(A_228,B_229))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2261,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_2226])).

tff(c_2343,plain,(
    ! [B_244,A_245,C_246] :
      ( k1_xboole_0 = B_244
      | k1_relset_1(A_245,B_244,C_246) = A_245
      | ~ v1_funct_2(C_246,A_245,B_244)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(A_245,B_244))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2361,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_2343])).

tff(c_2382,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2261,c_2361])).

tff(c_2392,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2382])).

tff(c_189,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_164])).

tff(c_2260,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_2226])).

tff(c_2358,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_2343])).

tff(c_2379,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2260,c_2358])).

tff(c_2386,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2379])).

tff(c_149,plain,(
    ! [B_58,A_59] :
      ( m1_subset_1(B_58,A_59)
      | ~ v1_xboole_0(B_58)
      | ~ v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_60,plain,(
    ! [E_40] :
      ( k1_funct_1('#skF_5',E_40) = k1_funct_1('#skF_6',E_40)
      | ~ m1_subset_1(E_40,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_162,plain,(
    ! [B_58] :
      ( k1_funct_1('#skF_5',B_58) = k1_funct_1('#skF_6',B_58)
      | ~ v1_xboole_0(B_58)
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_149,c_60])).

tff(c_311,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_3007,plain,(
    ! [A_291,B_292] :
      ( r2_hidden('#skF_2'(A_291,B_292),k1_relat_1(A_291))
      | B_292 = A_291
      | k1_relat_1(B_292) != k1_relat_1(A_291)
      | ~ v1_funct_1(B_292)
      | ~ v1_relat_1(B_292)
      | ~ v1_funct_1(A_291)
      | ~ v1_relat_1(A_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_3021,plain,(
    ! [B_292] :
      ( r2_hidden('#skF_2'('#skF_6',B_292),'#skF_3')
      | B_292 = '#skF_6'
      | k1_relat_1(B_292) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_292)
      | ~ v1_relat_1(B_292)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2386,c_3007])).

tff(c_3329,plain,(
    ! [B_321] :
      ( r2_hidden('#skF_2'('#skF_6',B_321),'#skF_3')
      | B_321 = '#skF_6'
      | k1_relat_1(B_321) != '#skF_3'
      | ~ v1_funct_1(B_321)
      | ~ v1_relat_1(B_321) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_66,c_2386,c_3021])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( m1_subset_1(B_10,A_9)
      | ~ r2_hidden(B_10,A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3334,plain,(
    ! [B_321] :
      ( m1_subset_1('#skF_2'('#skF_6',B_321),'#skF_3')
      | v1_xboole_0('#skF_3')
      | B_321 = '#skF_6'
      | k1_relat_1(B_321) != '#skF_3'
      | ~ v1_funct_1(B_321)
      | ~ v1_relat_1(B_321) ) ),
    inference(resolution,[status(thm)],[c_3329,c_18])).

tff(c_3518,plain,(
    ! [B_336] :
      ( m1_subset_1('#skF_2'('#skF_6',B_336),'#skF_3')
      | B_336 = '#skF_6'
      | k1_relat_1(B_336) != '#skF_3'
      | ~ v1_funct_1(B_336)
      | ~ v1_relat_1(B_336) ) ),
    inference(negUnitSimplification,[status(thm)],[c_311,c_3334])).

tff(c_3784,plain,(
    ! [B_351] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_6',B_351)) = k1_funct_1('#skF_6','#skF_2'('#skF_6',B_351))
      | B_351 = '#skF_6'
      | k1_relat_1(B_351) != '#skF_3'
      | ~ v1_funct_1(B_351)
      | ~ v1_relat_1(B_351) ) ),
    inference(resolution,[status(thm)],[c_3518,c_60])).

tff(c_34,plain,(
    ! [B_21,A_17] :
      ( k1_funct_1(B_21,'#skF_2'(A_17,B_21)) != k1_funct_1(A_17,'#skF_2'(A_17,B_21))
      | B_21 = A_17
      | k1_relat_1(B_21) != k1_relat_1(A_17)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_3791,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != '#skF_3'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3784,c_34])).

tff(c_3798,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_72,c_2392,c_189,c_66,c_2392,c_2386,c_3791])).

tff(c_58,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_3817,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3798,c_58])).

tff(c_3829,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_3817])).

tff(c_3830,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2382])).

tff(c_26,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_110,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_122,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(resolution,[status(thm)],[c_26,c_110])).

tff(c_3850,plain,(
    ! [A_11] : r1_tarski('#skF_4',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3830,c_122])).

tff(c_14,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3853,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3830,c_3830,c_14])).

tff(c_120,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_62,c_110])).

tff(c_332,plain,(
    ! [B_80,A_81] :
      ( B_80 = A_81
      | ~ r1_tarski(B_80,A_81)
      | ~ r1_tarski(A_81,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_344,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = '#skF_6'
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_120,c_332])).

tff(c_404,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_344])).

tff(c_3921,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3853,c_404])).

tff(c_3930,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3850,c_3921])).

tff(c_3931,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2379])).

tff(c_3952,plain,(
    ! [A_11] : r1_tarski('#skF_4',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3931,c_122])).

tff(c_3955,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3931,c_3931,c_14])).

tff(c_4028,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3955,c_404])).

tff(c_4037,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3952,c_4028])).

tff(c_4038,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_344])).

tff(c_4044,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4038,c_68])).

tff(c_4334,plain,(
    ! [A_392,B_393,C_394] :
      ( k1_relset_1(A_392,B_393,C_394) = k1_relat_1(C_394)
      | ~ m1_subset_1(C_394,k1_zfmisc_1(k2_zfmisc_1(A_392,B_393))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4575,plain,(
    ! [C_409] :
      ( k1_relset_1('#skF_3','#skF_4',C_409) = k1_relat_1(C_409)
      | ~ m1_subset_1(C_409,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4038,c_4334])).

tff(c_4603,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_4044,c_4575])).

tff(c_5083,plain,(
    ! [B_444,A_445,C_446] :
      ( k1_xboole_0 = B_444
      | k1_relset_1(A_445,B_444,C_446) = A_445
      | ~ v1_funct_2(C_446,A_445,B_444)
      | ~ m1_subset_1(C_446,k1_zfmisc_1(k2_zfmisc_1(A_445,B_444))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_5094,plain,(
    ! [C_446] :
      ( k1_xboole_0 = '#skF_4'
      | k1_relset_1('#skF_3','#skF_4',C_446) = '#skF_3'
      | ~ v1_funct_2(C_446,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_446,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4038,c_5083])).

tff(c_5138,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5094])).

tff(c_12,plain,(
    ! [B_8,A_7] :
      ( k1_xboole_0 = B_8
      | k1_xboole_0 = A_7
      | k2_zfmisc_1(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4051,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_4038,c_12])).

tff(c_4223,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_4051])).

tff(c_5161,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5138,c_4223])).

tff(c_5175,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5138,c_5138,c_14])).

tff(c_5307,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5175,c_4038])).

tff(c_5309,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5161,c_5307])).

tff(c_5682,plain,(
    ! [C_480] :
      ( k1_relset_1('#skF_3','#skF_4',C_480) = '#skF_3'
      | ~ v1_funct_2(C_480,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_480,k1_zfmisc_1('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_5094])).

tff(c_5693,plain,
    ( k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_4044,c_5682])).

tff(c_5718,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_4603,c_5693])).

tff(c_4043,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4038,c_62])).

tff(c_4604,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4043,c_4575])).

tff(c_5696,plain,
    ( k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_4043,c_5682])).

tff(c_5721,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_4604,c_5696])).

tff(c_5453,plain,(
    ! [A_464,B_465] :
      ( r2_hidden('#skF_2'(A_464,B_465),k1_relat_1(A_464))
      | B_465 = A_464
      | k1_relat_1(B_465) != k1_relat_1(A_464)
      | ~ v1_funct_1(B_465)
      | ~ v1_relat_1(B_465)
      | ~ v1_funct_1(A_464)
      | ~ v1_relat_1(A_464) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6403,plain,(
    ! [A_516,B_517] :
      ( m1_subset_1('#skF_2'(A_516,B_517),k1_relat_1(A_516))
      | v1_xboole_0(k1_relat_1(A_516))
      | B_517 = A_516
      | k1_relat_1(B_517) != k1_relat_1(A_516)
      | ~ v1_funct_1(B_517)
      | ~ v1_relat_1(B_517)
      | ~ v1_funct_1(A_516)
      | ~ v1_relat_1(A_516) ) ),
    inference(resolution,[status(thm)],[c_5453,c_18])).

tff(c_6409,plain,(
    ! [B_517] :
      ( m1_subset_1('#skF_2'('#skF_6',B_517),'#skF_3')
      | v1_xboole_0(k1_relat_1('#skF_6'))
      | B_517 = '#skF_6'
      | k1_relat_1(B_517) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_517)
      | ~ v1_relat_1(B_517)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5721,c_6403])).

tff(c_6415,plain,(
    ! [B_517] :
      ( m1_subset_1('#skF_2'('#skF_6',B_517),'#skF_3')
      | v1_xboole_0('#skF_3')
      | B_517 = '#skF_6'
      | k1_relat_1(B_517) != '#skF_3'
      | ~ v1_funct_1(B_517)
      | ~ v1_relat_1(B_517) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_66,c_5721,c_5721,c_6409])).

tff(c_6420,plain,(
    ! [B_518] :
      ( m1_subset_1('#skF_2'('#skF_6',B_518),'#skF_3')
      | B_518 = '#skF_6'
      | k1_relat_1(B_518) != '#skF_3'
      | ~ v1_funct_1(B_518)
      | ~ v1_relat_1(B_518) ) ),
    inference(negUnitSimplification,[status(thm)],[c_311,c_6415])).

tff(c_6444,plain,(
    ! [B_522] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_6',B_522)) = k1_funct_1('#skF_6','#skF_2'('#skF_6',B_522))
      | B_522 = '#skF_6'
      | k1_relat_1(B_522) != '#skF_3'
      | ~ v1_funct_1(B_522)
      | ~ v1_relat_1(B_522) ) ),
    inference(resolution,[status(thm)],[c_6420,c_60])).

tff(c_6451,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != '#skF_3'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6444,c_34])).

tff(c_6458,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_72,c_5718,c_189,c_66,c_5721,c_5718,c_6451])).

tff(c_121,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_68,c_110])).

tff(c_345,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_121,c_332])).

tff(c_403,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_345])).

tff(c_4040,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4038,c_403])).

tff(c_6471,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6458,c_4040])).

tff(c_6485,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_6471])).

tff(c_6487,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_4051])).

tff(c_6498,plain,(
    ! [A_11] : r1_tarski('#skF_6',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6487,c_122])).

tff(c_6510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6498,c_4040])).

tff(c_6511,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_345])).

tff(c_6516,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6511,c_68])).

tff(c_6698,plain,(
    ! [A_537,B_538,C_539] :
      ( k1_relset_1(A_537,B_538,C_539) = k1_relat_1(C_539)
      | ~ m1_subset_1(C_539,k1_zfmisc_1(k2_zfmisc_1(A_537,B_538))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_7118,plain,(
    ! [C_581] :
      ( k1_relset_1('#skF_3','#skF_4',C_581) = k1_relat_1(C_581)
      | ~ m1_subset_1(C_581,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6511,c_6698])).

tff(c_7147,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_6516,c_7118])).

tff(c_7226,plain,(
    ! [B_587,C_588,A_589] :
      ( k1_xboole_0 = B_587
      | v1_funct_2(C_588,A_589,B_587)
      | k1_relset_1(A_589,B_587,C_588) != A_589
      | ~ m1_subset_1(C_588,k1_zfmisc_1(k2_zfmisc_1(A_589,B_587))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_7233,plain,(
    ! [C_588] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2(C_588,'#skF_3','#skF_4')
      | k1_relset_1('#skF_3','#skF_4',C_588) != '#skF_3'
      | ~ m1_subset_1(C_588,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6511,c_7226])).

tff(c_7662,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_7233])).

tff(c_6523,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_6511,c_12])).

tff(c_6696,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_6523])).

tff(c_7685,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7662,c_6696])).

tff(c_7699,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7662,c_7662,c_14])).

tff(c_7772,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7699,c_6511])).

tff(c_7774,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7685,c_7772])).

tff(c_7776,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_7233])).

tff(c_7487,plain,(
    ! [B_599,A_600,C_601] :
      ( k1_xboole_0 = B_599
      | k1_relset_1(A_600,B_599,C_601) = A_600
      | ~ v1_funct_2(C_601,A_600,B_599)
      | ~ m1_subset_1(C_601,k1_zfmisc_1(k2_zfmisc_1(A_600,B_599))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_7498,plain,(
    ! [C_601] :
      ( k1_xboole_0 = '#skF_4'
      | k1_relset_1('#skF_3','#skF_4',C_601) = '#skF_3'
      | ~ v1_funct_2(C_601,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_601,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6511,c_7487])).

tff(c_7778,plain,(
    ! [C_620] :
      ( k1_relset_1('#skF_3','#skF_4',C_620) = '#skF_3'
      | ~ v1_funct_2(C_620,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_620,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_7776,c_7498])).

tff(c_7792,plain,
    ( k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_6516,c_7778])).

tff(c_7816,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_7147,c_7792])).

tff(c_6515,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6511,c_62])).

tff(c_7146,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_6515,c_7118])).

tff(c_7789,plain,
    ( k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_6515,c_7778])).

tff(c_7813,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_7146,c_7789])).

tff(c_7843,plain,(
    ! [A_621,B_622] :
      ( r2_hidden('#skF_2'(A_621,B_622),k1_relat_1(A_621))
      | B_622 = A_621
      | k1_relat_1(B_622) != k1_relat_1(A_621)
      | ~ v1_funct_1(B_622)
      | ~ v1_relat_1(B_622)
      | ~ v1_funct_1(A_621)
      | ~ v1_relat_1(A_621) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_7857,plain,(
    ! [B_622] :
      ( r2_hidden('#skF_2'('#skF_6',B_622),'#skF_3')
      | B_622 = '#skF_6'
      | k1_relat_1(B_622) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_622)
      | ~ v1_relat_1(B_622)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7813,c_7843])).

tff(c_8490,plain,(
    ! [B_663] :
      ( r2_hidden('#skF_2'('#skF_6',B_663),'#skF_3')
      | B_663 = '#skF_6'
      | k1_relat_1(B_663) != '#skF_3'
      | ~ v1_funct_1(B_663)
      | ~ v1_relat_1(B_663) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_66,c_7813,c_7857])).

tff(c_8495,plain,(
    ! [B_663] :
      ( m1_subset_1('#skF_2'('#skF_6',B_663),'#skF_3')
      | v1_xboole_0('#skF_3')
      | B_663 = '#skF_6'
      | k1_relat_1(B_663) != '#skF_3'
      | ~ v1_funct_1(B_663)
      | ~ v1_relat_1(B_663) ) ),
    inference(resolution,[status(thm)],[c_8490,c_18])).

tff(c_8764,plain,(
    ! [B_675] :
      ( m1_subset_1('#skF_2'('#skF_6',B_675),'#skF_3')
      | B_675 = '#skF_6'
      | k1_relat_1(B_675) != '#skF_3'
      | ~ v1_funct_1(B_675)
      | ~ v1_relat_1(B_675) ) ),
    inference(negUnitSimplification,[status(thm)],[c_311,c_8495])).

tff(c_9107,plain,(
    ! [B_696] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_6',B_696)) = k1_funct_1('#skF_6','#skF_2'('#skF_6',B_696))
      | B_696 = '#skF_6'
      | k1_relat_1(B_696) != '#skF_3'
      | ~ v1_funct_1(B_696)
      | ~ v1_relat_1(B_696) ) ),
    inference(resolution,[status(thm)],[c_8764,c_60])).

tff(c_9114,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != '#skF_3'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_9107,c_34])).

tff(c_9121,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_72,c_7816,c_189,c_66,c_7816,c_7813,c_9114])).

tff(c_6513,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6511,c_120])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( B_6 = A_5
      | ~ r1_tarski(B_6,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6553,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_6513,c_6])).

tff(c_6590,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_6553])).

tff(c_9153,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9121,c_6590])).

tff(c_9171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_9153])).

tff(c_9173,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_6523])).

tff(c_9184,plain,(
    ! [A_11] : r1_tarski('#skF_5',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9173,c_122])).

tff(c_9196,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9184,c_6590])).

tff(c_9197,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_6553])).

tff(c_9208,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9197,c_58])).

tff(c_9202,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9197,c_9197,c_6516])).

tff(c_9204,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9197,c_6511])).

tff(c_42,plain,(
    ! [A_29,B_30,D_32] :
      ( r2_relset_1(A_29,B_30,D_32,D_32)
      | ~ m1_subset_1(D_32,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_9436,plain,(
    ! [D_718] :
      ( r2_relset_1('#skF_3','#skF_4',D_718,D_718)
      | ~ m1_subset_1(D_718,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9204,c_42])).

tff(c_9438,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_9202,c_9436])).

tff(c_9454,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9208,c_9438])).

tff(c_9456,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_15349,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_15326])).

tff(c_15372,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_14774,c_15349])).

tff(c_15379,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_15372])).

tff(c_15602,plain,(
    ! [A_1122,B_1123] :
      ( r2_hidden('#skF_2'(A_1122,B_1123),k1_relat_1(A_1122))
      | B_1123 = A_1122
      | k1_relat_1(B_1123) != k1_relat_1(A_1122)
      | ~ v1_funct_1(B_1123)
      | ~ v1_relat_1(B_1123)
      | ~ v1_funct_1(A_1122)
      | ~ v1_relat_1(A_1122) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_15616,plain,(
    ! [B_1123] :
      ( r2_hidden('#skF_2'('#skF_6',B_1123),'#skF_3')
      | B_1123 = '#skF_6'
      | k1_relat_1(B_1123) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_1123)
      | ~ v1_relat_1(B_1123)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15379,c_15602])).

tff(c_15876,plain,(
    ! [B_1144] :
      ( r2_hidden('#skF_2'('#skF_6',B_1144),'#skF_3')
      | B_1144 = '#skF_6'
      | k1_relat_1(B_1144) != '#skF_3'
      | ~ v1_funct_1(B_1144)
      | ~ v1_relat_1(B_1144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_66,c_15379,c_15616])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_15884,plain,(
    ! [B_1144] :
      ( ~ v1_xboole_0('#skF_3')
      | B_1144 = '#skF_6'
      | k1_relat_1(B_1144) != '#skF_3'
      | ~ v1_funct_1(B_1144)
      | ~ v1_relat_1(B_1144) ) ),
    inference(resolution,[status(thm)],[c_15876,c_2])).

tff(c_15891,plain,(
    ! [B_1145] :
      ( B_1145 = '#skF_6'
      | k1_relat_1(B_1145) != '#skF_3'
      | ~ v1_funct_1(B_1145)
      | ~ v1_relat_1(B_1145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9456,c_15884])).

tff(c_15903,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != '#skF_3'
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_190,c_15891])).

tff(c_15912,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_15385,c_15903])).

tff(c_15985,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15912,c_58])).

tff(c_15997,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9656,c_15985])).

tff(c_15998,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_15375])).

tff(c_16028,plain,(
    ! [A_11] : r1_tarski('#skF_4',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15998,c_122])).

tff(c_16031,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15998,c_15998,c_14])).

tff(c_9477,plain,(
    ! [B_722,A_723] :
      ( B_722 = A_723
      | ~ r1_tarski(B_722,A_723)
      | ~ r1_tarski(A_723,B_722) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_9489,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = '#skF_6'
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_120,c_9477])).

tff(c_14854,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_9489])).

tff(c_16145,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16031,c_14854])).

tff(c_16156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16028,c_16145])).

tff(c_16157,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_15372])).

tff(c_16187,plain,(
    ! [A_11] : r1_tarski('#skF_4',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16157,c_122])).

tff(c_16190,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16157,c_16157,c_14])).

tff(c_16304,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16190,c_14854])).

tff(c_16315,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16187,c_16304])).

tff(c_16316,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_9489])).

tff(c_16786,plain,(
    ! [B_1193,C_1194,A_1195] :
      ( k1_xboole_0 = B_1193
      | v1_funct_2(C_1194,A_1195,B_1193)
      | k1_relset_1(A_1195,B_1193,C_1194) != A_1195
      | ~ m1_subset_1(C_1194,k1_zfmisc_1(k2_zfmisc_1(A_1195,B_1193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_16793,plain,(
    ! [C_1194] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2(C_1194,'#skF_3','#skF_4')
      | k1_relset_1('#skF_3','#skF_4',C_1194) != '#skF_3'
      | ~ m1_subset_1(C_1194,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16316,c_16786])).

tff(c_17333,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_16793])).

tff(c_16338,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_16316,c_12])).

tff(c_16449,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_16338])).

tff(c_17349,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17333,c_16449])).

tff(c_17369,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17333,c_17333,c_14])).

tff(c_17484,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17369,c_16316])).

tff(c_17486,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17349,c_17484])).

tff(c_17488,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_16793])).

tff(c_30,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_16608,plain,(
    ! [B_1177,A_1178,C_1179] :
      ( k1_xboole_0 = B_1177
      | k1_relset_1(A_1178,B_1177,C_1179) = A_1178
      | ~ v1_funct_2(C_1179,A_1178,B_1177)
      | ~ m1_subset_1(C_1179,k1_zfmisc_1(k2_zfmisc_1(A_1178,B_1177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_17551,plain,(
    ! [B_1238,A_1239,A_1240] :
      ( k1_xboole_0 = B_1238
      | k1_relset_1(A_1239,B_1238,A_1240) = A_1239
      | ~ v1_funct_2(A_1240,A_1239,B_1238)
      | ~ r1_tarski(A_1240,k2_zfmisc_1(A_1239,B_1238)) ) ),
    inference(resolution,[status(thm)],[c_30,c_16608])).

tff(c_17558,plain,(
    ! [A_1240] :
      ( k1_xboole_0 = '#skF_4'
      | k1_relset_1('#skF_3','#skF_4',A_1240) = '#skF_3'
      | ~ v1_funct_2(A_1240,'#skF_3','#skF_4')
      | ~ r1_tarski(A_1240,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16316,c_17551])).

tff(c_17610,plain,(
    ! [A_1243] :
      ( k1_relset_1('#skF_3','#skF_4',A_1243) = '#skF_3'
      | ~ v1_funct_2(A_1243,'#skF_3','#skF_4')
      | ~ r1_tarski(A_1243,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_17488,c_17558])).

tff(c_17617,plain,
    ( k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_17610])).

tff(c_17627,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14774,c_17617])).

tff(c_16323,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16316,c_121])).

tff(c_17620,plain,
    ( k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_17610])).

tff(c_17630,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16323,c_14775,c_17620])).

tff(c_17290,plain,(
    ! [A_1224,B_1225] :
      ( r2_hidden('#skF_2'(A_1224,B_1225),k1_relat_1(A_1224))
      | B_1225 = A_1224
      | k1_relat_1(B_1225) != k1_relat_1(A_1224)
      | ~ v1_funct_1(B_1225)
      | ~ v1_relat_1(B_1225)
      | ~ v1_funct_1(A_1224)
      | ~ v1_relat_1(A_1224) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_17999,plain,(
    ! [A_1264,B_1265] :
      ( ~ v1_xboole_0(k1_relat_1(A_1264))
      | B_1265 = A_1264
      | k1_relat_1(B_1265) != k1_relat_1(A_1264)
      | ~ v1_funct_1(B_1265)
      | ~ v1_relat_1(B_1265)
      | ~ v1_funct_1(A_1264)
      | ~ v1_relat_1(A_1264) ) ),
    inference(resolution,[status(thm)],[c_17290,c_2])).

tff(c_18001,plain,(
    ! [B_1265] :
      ( ~ v1_xboole_0('#skF_3')
      | B_1265 = '#skF_5'
      | k1_relat_1(B_1265) != k1_relat_1('#skF_5')
      | ~ v1_funct_1(B_1265)
      | ~ v1_relat_1(B_1265)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17630,c_17999])).

tff(c_18008,plain,(
    ! [B_1266] :
      ( B_1266 = '#skF_5'
      | k1_relat_1(B_1266) != '#skF_3'
      | ~ v1_funct_1(B_1266)
      | ~ v1_relat_1(B_1266) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_72,c_17630,c_9456,c_18001])).

tff(c_18026,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_6') != '#skF_3'
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_189,c_18008])).

tff(c_18037,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_17627,c_18026])).

tff(c_9490,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_121,c_9477])).

tff(c_9553,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_9490])).

tff(c_16321,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16316,c_9553])).

tff(c_18048,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18037,c_16321])).

tff(c_18068,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_18048])).

tff(c_18070,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_16338])).

tff(c_18087,plain,(
    ! [A_11] : r1_tarski('#skF_6',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18070,c_122])).

tff(c_18101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18087,c_16321])).

tff(c_18102,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_9490])).

tff(c_18107,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18102,c_68])).

tff(c_18387,plain,(
    ! [A_1295,B_1296,C_1297] :
      ( k1_relset_1(A_1295,B_1296,C_1297) = k1_relat_1(C_1297)
      | ~ m1_subset_1(C_1297,k1_zfmisc_1(k2_zfmisc_1(A_1295,B_1296))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_18571,plain,(
    ! [C_1310] :
      ( k1_relset_1('#skF_3','#skF_4',C_1310) = k1_relat_1(C_1310)
      | ~ m1_subset_1(C_1310,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18102,c_18387])).

tff(c_18599,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_18107,c_18571])).

tff(c_18876,plain,(
    ! [B_1332,A_1333,C_1334] :
      ( k1_xboole_0 = B_1332
      | k1_relset_1(A_1333,B_1332,C_1334) = A_1333
      | ~ v1_funct_2(C_1334,A_1333,B_1332)
      | ~ m1_subset_1(C_1334,k1_zfmisc_1(k2_zfmisc_1(A_1333,B_1332))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_18883,plain,(
    ! [C_1334] :
      ( k1_xboole_0 = '#skF_4'
      | k1_relset_1('#skF_3','#skF_4',C_1334) = '#skF_3'
      | ~ v1_funct_2(C_1334,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_1334,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18102,c_18876])).

tff(c_18963,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_18883])).

tff(c_18114,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_18102,c_12])).

tff(c_18246,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_18114])).

tff(c_18983,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18963,c_18246])).

tff(c_18997,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18963,c_18963,c_14])).

tff(c_19124,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18997,c_18102])).

tff(c_19126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18983,c_19124])).

tff(c_19790,plain,(
    ! [C_1388] :
      ( k1_relset_1('#skF_3','#skF_4',C_1388) = '#skF_3'
      | ~ v1_funct_2(C_1388,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_1388,k1_zfmisc_1('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_18883])).

tff(c_19801,plain,
    ( k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_18107,c_19790])).

tff(c_19826,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_18599,c_19801])).

tff(c_18106,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18102,c_62])).

tff(c_18600,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_18106,c_18571])).

tff(c_19804,plain,
    ( k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_18106,c_19790])).

tff(c_19829,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_18600,c_19804])).

tff(c_19500,plain,(
    ! [A_1369,B_1370] :
      ( r2_hidden('#skF_2'(A_1369,B_1370),k1_relat_1(A_1369))
      | B_1370 = A_1369
      | k1_relat_1(B_1370) != k1_relat_1(A_1369)
      | ~ v1_funct_1(B_1370)
      | ~ v1_relat_1(B_1370)
      | ~ v1_funct_1(A_1369)
      | ~ v1_relat_1(A_1369) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_20266,plain,(
    ! [A_1413,B_1414] :
      ( ~ v1_xboole_0(k1_relat_1(A_1413))
      | B_1414 = A_1413
      | k1_relat_1(B_1414) != k1_relat_1(A_1413)
      | ~ v1_funct_1(B_1414)
      | ~ v1_relat_1(B_1414)
      | ~ v1_funct_1(A_1413)
      | ~ v1_relat_1(A_1413) ) ),
    inference(resolution,[status(thm)],[c_19500,c_2])).

tff(c_20268,plain,(
    ! [B_1414] :
      ( ~ v1_xboole_0('#skF_3')
      | B_1414 = '#skF_6'
      | k1_relat_1(B_1414) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_1414)
      | ~ v1_relat_1(B_1414)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19829,c_20266])).

tff(c_20275,plain,(
    ! [B_1415] :
      ( B_1415 = '#skF_6'
      | k1_relat_1(B_1415) != '#skF_3'
      | ~ v1_funct_1(B_1415)
      | ~ v1_relat_1(B_1415) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_66,c_19829,c_9456,c_20268])).

tff(c_20290,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != '#skF_3'
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_190,c_20275])).

tff(c_20300,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_19826,c_20290])).

tff(c_18104,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18102,c_120])).

tff(c_18127,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_18104,c_6])).

tff(c_18170,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_18127])).

tff(c_20335,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20300,c_18170])).

tff(c_20354,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_20335])).

tff(c_20356,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_18114])).

tff(c_20367,plain,(
    ! [A_11] : r1_tarski('#skF_5',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20356,c_122])).

tff(c_20394,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20367,c_18170])).

tff(c_20395,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_18127])).

tff(c_20406,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20395,c_58])).

tff(c_20398,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20395,c_20395,c_18107])).

tff(c_20401,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20395,c_18102])).

tff(c_20729,plain,(
    ! [D_1452] :
      ( r2_relset_1('#skF_3','#skF_4',D_1452,D_1452)
      | ~ m1_subset_1(D_1452,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20401,c_42])).

tff(c_20734,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_20398,c_20729])).

tff(c_20751,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20406,c_20734])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:07:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.30/4.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.30/4.13  
% 10.30/4.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.30/4.13  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 10.30/4.13  
% 10.30/4.13  %Foreground sorts:
% 10.30/4.13  
% 10.30/4.13  
% 10.30/4.13  %Background operators:
% 10.30/4.13  
% 10.30/4.13  
% 10.30/4.13  %Foreground operators:
% 10.30/4.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.30/4.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.30/4.13  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 10.30/4.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.30/4.13  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.30/4.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.30/4.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.30/4.13  tff('#skF_5', type, '#skF_5': $i).
% 10.30/4.13  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.30/4.13  tff('#skF_6', type, '#skF_6': $i).
% 10.30/4.13  tff('#skF_3', type, '#skF_3': $i).
% 10.30/4.13  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.30/4.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.30/4.13  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.30/4.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.30/4.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.30/4.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.30/4.13  tff('#skF_4', type, '#skF_4': $i).
% 10.30/4.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.30/4.13  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.30/4.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.30/4.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.30/4.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.30/4.13  
% 10.30/4.16  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.30/4.16  tff(f_141, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_funct_2)).
% 10.30/4.16  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.30/4.16  tff(f_102, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 10.30/4.16  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 10.30/4.16  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.30/4.16  tff(f_56, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 10.30/4.16  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 10.30/4.16  tff(f_58, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 10.30/4.16  tff(f_62, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.30/4.16  tff(f_43, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 10.30/4.16  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 10.30/4.16  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.30/4.16  tff(c_72, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_141])).
% 10.30/4.16  tff(c_70, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 10.30/4.16  tff(c_66, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_141])).
% 10.30/4.17  tff(c_62, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 10.30/4.17  tff(c_14740, plain, (![A_1052, B_1053, C_1054]: (k1_relset_1(A_1052, B_1053, C_1054)=k1_relat_1(C_1054) | ~m1_subset_1(C_1054, k1_zfmisc_1(k2_zfmisc_1(A_1052, B_1053))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.30/4.17  tff(c_14774, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_62, c_14740])).
% 10.30/4.17  tff(c_64, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 10.30/4.17  tff(c_9630, plain, (![A_738, B_739, D_740]: (r2_relset_1(A_738, B_739, D_740, D_740) | ~m1_subset_1(D_740, k1_zfmisc_1(k2_zfmisc_1(A_738, B_739))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.30/4.17  tff(c_9656, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_62, c_9630])).
% 10.30/4.17  tff(c_68, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 10.30/4.17  tff(c_14775, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_68, c_14740])).
% 10.30/4.17  tff(c_15326, plain, (![B_1100, A_1101, C_1102]: (k1_xboole_0=B_1100 | k1_relset_1(A_1101, B_1100, C_1102)=A_1101 | ~v1_funct_2(C_1102, A_1101, B_1100) | ~m1_subset_1(C_1102, k1_zfmisc_1(k2_zfmisc_1(A_1101, B_1100))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.30/4.17  tff(c_15352, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_15326])).
% 10.30/4.17  tff(c_15375, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_14775, c_15352])).
% 10.30/4.17  tff(c_15385, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_15375])).
% 10.30/4.17  tff(c_164, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.30/4.17  tff(c_190, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_68, c_164])).
% 10.30/4.17  tff(c_480, plain, (![A_96, B_97, D_98]: (r2_relset_1(A_96, B_97, D_98, D_98) | ~m1_subset_1(D_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.30/4.17  tff(c_506, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_62, c_480])).
% 10.30/4.17  tff(c_2226, plain, (![A_228, B_229, C_230]: (k1_relset_1(A_228, B_229, C_230)=k1_relat_1(C_230) | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1(A_228, B_229))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.30/4.17  tff(c_2261, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_68, c_2226])).
% 10.30/4.17  tff(c_2343, plain, (![B_244, A_245, C_246]: (k1_xboole_0=B_244 | k1_relset_1(A_245, B_244, C_246)=A_245 | ~v1_funct_2(C_246, A_245, B_244) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(A_245, B_244))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.30/4.17  tff(c_2361, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_2343])).
% 10.30/4.17  tff(c_2382, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2261, c_2361])).
% 10.30/4.17  tff(c_2392, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_2382])).
% 10.30/4.17  tff(c_189, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_62, c_164])).
% 10.30/4.17  tff(c_2260, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_62, c_2226])).
% 10.30/4.17  tff(c_2358, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_62, c_2343])).
% 10.30/4.17  tff(c_2379, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2260, c_2358])).
% 10.30/4.17  tff(c_2386, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_2379])).
% 10.30/4.17  tff(c_149, plain, (![B_58, A_59]: (m1_subset_1(B_58, A_59) | ~v1_xboole_0(B_58) | ~v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.30/4.17  tff(c_60, plain, (![E_40]: (k1_funct_1('#skF_5', E_40)=k1_funct_1('#skF_6', E_40) | ~m1_subset_1(E_40, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 10.30/4.17  tff(c_162, plain, (![B_58]: (k1_funct_1('#skF_5', B_58)=k1_funct_1('#skF_6', B_58) | ~v1_xboole_0(B_58) | ~v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_149, c_60])).
% 10.30/4.17  tff(c_311, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_162])).
% 10.30/4.17  tff(c_3007, plain, (![A_291, B_292]: (r2_hidden('#skF_2'(A_291, B_292), k1_relat_1(A_291)) | B_292=A_291 | k1_relat_1(B_292)!=k1_relat_1(A_291) | ~v1_funct_1(B_292) | ~v1_relat_1(B_292) | ~v1_funct_1(A_291) | ~v1_relat_1(A_291))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.30/4.17  tff(c_3021, plain, (![B_292]: (r2_hidden('#skF_2'('#skF_6', B_292), '#skF_3') | B_292='#skF_6' | k1_relat_1(B_292)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_292) | ~v1_relat_1(B_292) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2386, c_3007])).
% 10.30/4.17  tff(c_3329, plain, (![B_321]: (r2_hidden('#skF_2'('#skF_6', B_321), '#skF_3') | B_321='#skF_6' | k1_relat_1(B_321)!='#skF_3' | ~v1_funct_1(B_321) | ~v1_relat_1(B_321))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_66, c_2386, c_3021])).
% 10.30/4.17  tff(c_18, plain, (![B_10, A_9]: (m1_subset_1(B_10, A_9) | ~r2_hidden(B_10, A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.30/4.17  tff(c_3334, plain, (![B_321]: (m1_subset_1('#skF_2'('#skF_6', B_321), '#skF_3') | v1_xboole_0('#skF_3') | B_321='#skF_6' | k1_relat_1(B_321)!='#skF_3' | ~v1_funct_1(B_321) | ~v1_relat_1(B_321))), inference(resolution, [status(thm)], [c_3329, c_18])).
% 10.30/4.17  tff(c_3518, plain, (![B_336]: (m1_subset_1('#skF_2'('#skF_6', B_336), '#skF_3') | B_336='#skF_6' | k1_relat_1(B_336)!='#skF_3' | ~v1_funct_1(B_336) | ~v1_relat_1(B_336))), inference(negUnitSimplification, [status(thm)], [c_311, c_3334])).
% 10.30/4.17  tff(c_3784, plain, (![B_351]: (k1_funct_1('#skF_5', '#skF_2'('#skF_6', B_351))=k1_funct_1('#skF_6', '#skF_2'('#skF_6', B_351)) | B_351='#skF_6' | k1_relat_1(B_351)!='#skF_3' | ~v1_funct_1(B_351) | ~v1_relat_1(B_351))), inference(resolution, [status(thm)], [c_3518, c_60])).
% 10.30/4.17  tff(c_34, plain, (![B_21, A_17]: (k1_funct_1(B_21, '#skF_2'(A_17, B_21))!=k1_funct_1(A_17, '#skF_2'(A_17, B_21)) | B_21=A_17 | k1_relat_1(B_21)!=k1_relat_1(A_17) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.30/4.17  tff(c_3791, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!='#skF_3' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3784, c_34])).
% 10.30/4.17  tff(c_3798, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_190, c_72, c_2392, c_189, c_66, c_2392, c_2386, c_3791])).
% 10.30/4.17  tff(c_58, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_141])).
% 10.30/4.17  tff(c_3817, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3798, c_58])).
% 10.30/4.17  tff(c_3829, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_506, c_3817])).
% 10.30/4.17  tff(c_3830, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_2382])).
% 10.30/4.17  tff(c_26, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.30/4.17  tff(c_110, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~m1_subset_1(A_49, k1_zfmisc_1(B_50)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.30/4.17  tff(c_122, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(resolution, [status(thm)], [c_26, c_110])).
% 10.30/4.17  tff(c_3850, plain, (![A_11]: (r1_tarski('#skF_4', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_3830, c_122])).
% 10.30/4.17  tff(c_14, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.30/4.17  tff(c_3853, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3830, c_3830, c_14])).
% 10.30/4.17  tff(c_120, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_110])).
% 10.30/4.17  tff(c_332, plain, (![B_80, A_81]: (B_80=A_81 | ~r1_tarski(B_80, A_81) | ~r1_tarski(A_81, B_80))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.30/4.17  tff(c_344, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_6' | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_6')), inference(resolution, [status(thm)], [c_120, c_332])).
% 10.30/4.17  tff(c_404, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_344])).
% 10.30/4.17  tff(c_3921, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3853, c_404])).
% 10.30/4.17  tff(c_3930, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3850, c_3921])).
% 10.30/4.17  tff(c_3931, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_2379])).
% 10.30/4.17  tff(c_3952, plain, (![A_11]: (r1_tarski('#skF_4', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_3931, c_122])).
% 10.30/4.17  tff(c_3955, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3931, c_3931, c_14])).
% 10.30/4.17  tff(c_4028, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3955, c_404])).
% 10.30/4.17  tff(c_4037, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3952, c_4028])).
% 10.30/4.17  tff(c_4038, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_6'), inference(splitRight, [status(thm)], [c_344])).
% 10.30/4.17  tff(c_4044, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_4038, c_68])).
% 10.30/4.17  tff(c_4334, plain, (![A_392, B_393, C_394]: (k1_relset_1(A_392, B_393, C_394)=k1_relat_1(C_394) | ~m1_subset_1(C_394, k1_zfmisc_1(k2_zfmisc_1(A_392, B_393))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.30/4.17  tff(c_4575, plain, (![C_409]: (k1_relset_1('#skF_3', '#skF_4', C_409)=k1_relat_1(C_409) | ~m1_subset_1(C_409, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_4038, c_4334])).
% 10.30/4.17  tff(c_4603, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_4044, c_4575])).
% 10.30/4.17  tff(c_5083, plain, (![B_444, A_445, C_446]: (k1_xboole_0=B_444 | k1_relset_1(A_445, B_444, C_446)=A_445 | ~v1_funct_2(C_446, A_445, B_444) | ~m1_subset_1(C_446, k1_zfmisc_1(k2_zfmisc_1(A_445, B_444))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.30/4.17  tff(c_5094, plain, (![C_446]: (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', C_446)='#skF_3' | ~v1_funct_2(C_446, '#skF_3', '#skF_4') | ~m1_subset_1(C_446, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_4038, c_5083])).
% 10.30/4.17  tff(c_5138, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_5094])).
% 10.30/4.17  tff(c_12, plain, (![B_8, A_7]: (k1_xboole_0=B_8 | k1_xboole_0=A_7 | k2_zfmisc_1(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.30/4.17  tff(c_4051, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_4038, c_12])).
% 10.30/4.17  tff(c_4223, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_4051])).
% 10.30/4.17  tff(c_5161, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5138, c_4223])).
% 10.30/4.17  tff(c_5175, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5138, c_5138, c_14])).
% 10.30/4.17  tff(c_5307, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5175, c_4038])).
% 10.30/4.17  tff(c_5309, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5161, c_5307])).
% 10.30/4.17  tff(c_5682, plain, (![C_480]: (k1_relset_1('#skF_3', '#skF_4', C_480)='#skF_3' | ~v1_funct_2(C_480, '#skF_3', '#skF_4') | ~m1_subset_1(C_480, k1_zfmisc_1('#skF_6')))), inference(splitRight, [status(thm)], [c_5094])).
% 10.30/4.17  tff(c_5693, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_4044, c_5682])).
% 10.30/4.17  tff(c_5718, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_4603, c_5693])).
% 10.30/4.17  tff(c_4043, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_4038, c_62])).
% 10.30/4.17  tff(c_4604, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_4043, c_4575])).
% 10.30/4.17  tff(c_5696, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_4043, c_5682])).
% 10.30/4.17  tff(c_5721, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_4604, c_5696])).
% 10.30/4.17  tff(c_5453, plain, (![A_464, B_465]: (r2_hidden('#skF_2'(A_464, B_465), k1_relat_1(A_464)) | B_465=A_464 | k1_relat_1(B_465)!=k1_relat_1(A_464) | ~v1_funct_1(B_465) | ~v1_relat_1(B_465) | ~v1_funct_1(A_464) | ~v1_relat_1(A_464))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.30/4.17  tff(c_6403, plain, (![A_516, B_517]: (m1_subset_1('#skF_2'(A_516, B_517), k1_relat_1(A_516)) | v1_xboole_0(k1_relat_1(A_516)) | B_517=A_516 | k1_relat_1(B_517)!=k1_relat_1(A_516) | ~v1_funct_1(B_517) | ~v1_relat_1(B_517) | ~v1_funct_1(A_516) | ~v1_relat_1(A_516))), inference(resolution, [status(thm)], [c_5453, c_18])).
% 10.30/4.17  tff(c_6409, plain, (![B_517]: (m1_subset_1('#skF_2'('#skF_6', B_517), '#skF_3') | v1_xboole_0(k1_relat_1('#skF_6')) | B_517='#skF_6' | k1_relat_1(B_517)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_517) | ~v1_relat_1(B_517) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_5721, c_6403])).
% 10.30/4.17  tff(c_6415, plain, (![B_517]: (m1_subset_1('#skF_2'('#skF_6', B_517), '#skF_3') | v1_xboole_0('#skF_3') | B_517='#skF_6' | k1_relat_1(B_517)!='#skF_3' | ~v1_funct_1(B_517) | ~v1_relat_1(B_517))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_66, c_5721, c_5721, c_6409])).
% 10.30/4.17  tff(c_6420, plain, (![B_518]: (m1_subset_1('#skF_2'('#skF_6', B_518), '#skF_3') | B_518='#skF_6' | k1_relat_1(B_518)!='#skF_3' | ~v1_funct_1(B_518) | ~v1_relat_1(B_518))), inference(negUnitSimplification, [status(thm)], [c_311, c_6415])).
% 10.30/4.17  tff(c_6444, plain, (![B_522]: (k1_funct_1('#skF_5', '#skF_2'('#skF_6', B_522))=k1_funct_1('#skF_6', '#skF_2'('#skF_6', B_522)) | B_522='#skF_6' | k1_relat_1(B_522)!='#skF_3' | ~v1_funct_1(B_522) | ~v1_relat_1(B_522))), inference(resolution, [status(thm)], [c_6420, c_60])).
% 10.30/4.17  tff(c_6451, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!='#skF_3' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6444, c_34])).
% 10.30/4.17  tff(c_6458, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_190, c_72, c_5718, c_189, c_66, c_5721, c_5718, c_6451])).
% 10.30/4.17  tff(c_121, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_110])).
% 10.30/4.17  tff(c_345, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_121, c_332])).
% 10.30/4.17  tff(c_403, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_345])).
% 10.30/4.17  tff(c_4040, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4038, c_403])).
% 10.30/4.17  tff(c_6471, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6458, c_4040])).
% 10.30/4.17  tff(c_6485, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_6471])).
% 10.30/4.17  tff(c_6487, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_4051])).
% 10.30/4.17  tff(c_6498, plain, (![A_11]: (r1_tarski('#skF_6', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_6487, c_122])).
% 10.30/4.17  tff(c_6510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6498, c_4040])).
% 10.30/4.17  tff(c_6511, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_345])).
% 10.30/4.17  tff(c_6516, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_6511, c_68])).
% 10.30/4.17  tff(c_6698, plain, (![A_537, B_538, C_539]: (k1_relset_1(A_537, B_538, C_539)=k1_relat_1(C_539) | ~m1_subset_1(C_539, k1_zfmisc_1(k2_zfmisc_1(A_537, B_538))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.30/4.17  tff(c_7118, plain, (![C_581]: (k1_relset_1('#skF_3', '#skF_4', C_581)=k1_relat_1(C_581) | ~m1_subset_1(C_581, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_6511, c_6698])).
% 10.30/4.17  tff(c_7147, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_6516, c_7118])).
% 10.30/4.17  tff(c_7226, plain, (![B_587, C_588, A_589]: (k1_xboole_0=B_587 | v1_funct_2(C_588, A_589, B_587) | k1_relset_1(A_589, B_587, C_588)!=A_589 | ~m1_subset_1(C_588, k1_zfmisc_1(k2_zfmisc_1(A_589, B_587))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.30/4.17  tff(c_7233, plain, (![C_588]: (k1_xboole_0='#skF_4' | v1_funct_2(C_588, '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', C_588)!='#skF_3' | ~m1_subset_1(C_588, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_6511, c_7226])).
% 10.30/4.17  tff(c_7662, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_7233])).
% 10.30/4.17  tff(c_6523, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_6511, c_12])).
% 10.30/4.17  tff(c_6696, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_6523])).
% 10.30/4.17  tff(c_7685, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7662, c_6696])).
% 10.30/4.17  tff(c_7699, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7662, c_7662, c_14])).
% 10.30/4.17  tff(c_7772, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7699, c_6511])).
% 10.30/4.17  tff(c_7774, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7685, c_7772])).
% 10.30/4.17  tff(c_7776, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_7233])).
% 10.30/4.17  tff(c_7487, plain, (![B_599, A_600, C_601]: (k1_xboole_0=B_599 | k1_relset_1(A_600, B_599, C_601)=A_600 | ~v1_funct_2(C_601, A_600, B_599) | ~m1_subset_1(C_601, k1_zfmisc_1(k2_zfmisc_1(A_600, B_599))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.30/4.17  tff(c_7498, plain, (![C_601]: (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', C_601)='#skF_3' | ~v1_funct_2(C_601, '#skF_3', '#skF_4') | ~m1_subset_1(C_601, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_6511, c_7487])).
% 10.30/4.17  tff(c_7778, plain, (![C_620]: (k1_relset_1('#skF_3', '#skF_4', C_620)='#skF_3' | ~v1_funct_2(C_620, '#skF_3', '#skF_4') | ~m1_subset_1(C_620, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_7776, c_7498])).
% 10.30/4.17  tff(c_7792, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_6516, c_7778])).
% 10.30/4.17  tff(c_7816, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_7147, c_7792])).
% 10.30/4.17  tff(c_6515, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_6511, c_62])).
% 10.30/4.17  tff(c_7146, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_6515, c_7118])).
% 10.30/4.17  tff(c_7789, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_6515, c_7778])).
% 10.30/4.17  tff(c_7813, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_7146, c_7789])).
% 10.30/4.17  tff(c_7843, plain, (![A_621, B_622]: (r2_hidden('#skF_2'(A_621, B_622), k1_relat_1(A_621)) | B_622=A_621 | k1_relat_1(B_622)!=k1_relat_1(A_621) | ~v1_funct_1(B_622) | ~v1_relat_1(B_622) | ~v1_funct_1(A_621) | ~v1_relat_1(A_621))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.30/4.17  tff(c_7857, plain, (![B_622]: (r2_hidden('#skF_2'('#skF_6', B_622), '#skF_3') | B_622='#skF_6' | k1_relat_1(B_622)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_622) | ~v1_relat_1(B_622) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_7813, c_7843])).
% 10.30/4.17  tff(c_8490, plain, (![B_663]: (r2_hidden('#skF_2'('#skF_6', B_663), '#skF_3') | B_663='#skF_6' | k1_relat_1(B_663)!='#skF_3' | ~v1_funct_1(B_663) | ~v1_relat_1(B_663))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_66, c_7813, c_7857])).
% 10.30/4.17  tff(c_8495, plain, (![B_663]: (m1_subset_1('#skF_2'('#skF_6', B_663), '#skF_3') | v1_xboole_0('#skF_3') | B_663='#skF_6' | k1_relat_1(B_663)!='#skF_3' | ~v1_funct_1(B_663) | ~v1_relat_1(B_663))), inference(resolution, [status(thm)], [c_8490, c_18])).
% 10.30/4.17  tff(c_8764, plain, (![B_675]: (m1_subset_1('#skF_2'('#skF_6', B_675), '#skF_3') | B_675='#skF_6' | k1_relat_1(B_675)!='#skF_3' | ~v1_funct_1(B_675) | ~v1_relat_1(B_675))), inference(negUnitSimplification, [status(thm)], [c_311, c_8495])).
% 10.30/4.17  tff(c_9107, plain, (![B_696]: (k1_funct_1('#skF_5', '#skF_2'('#skF_6', B_696))=k1_funct_1('#skF_6', '#skF_2'('#skF_6', B_696)) | B_696='#skF_6' | k1_relat_1(B_696)!='#skF_3' | ~v1_funct_1(B_696) | ~v1_relat_1(B_696))), inference(resolution, [status(thm)], [c_8764, c_60])).
% 10.30/4.17  tff(c_9114, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!='#skF_3' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_9107, c_34])).
% 10.30/4.17  tff(c_9121, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_190, c_72, c_7816, c_189, c_66, c_7816, c_7813, c_9114])).
% 10.30/4.17  tff(c_6513, plain, (r1_tarski('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6511, c_120])).
% 10.30/4.17  tff(c_6, plain, (![B_6, A_5]: (B_6=A_5 | ~r1_tarski(B_6, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.30/4.17  tff(c_6553, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_6513, c_6])).
% 10.30/4.17  tff(c_6590, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_6553])).
% 10.30/4.17  tff(c_9153, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9121, c_6590])).
% 10.30/4.17  tff(c_9171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_9153])).
% 10.30/4.17  tff(c_9173, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_6523])).
% 10.30/4.17  tff(c_9184, plain, (![A_11]: (r1_tarski('#skF_5', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_9173, c_122])).
% 10.30/4.17  tff(c_9196, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9184, c_6590])).
% 10.30/4.17  tff(c_9197, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_6553])).
% 10.30/4.17  tff(c_9208, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9197, c_58])).
% 10.30/4.17  tff(c_9202, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_9197, c_9197, c_6516])).
% 10.30/4.17  tff(c_9204, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_9197, c_6511])).
% 10.30/4.17  tff(c_42, plain, (![A_29, B_30, D_32]: (r2_relset_1(A_29, B_30, D_32, D_32) | ~m1_subset_1(D_32, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.30/4.17  tff(c_9436, plain, (![D_718]: (r2_relset_1('#skF_3', '#skF_4', D_718, D_718) | ~m1_subset_1(D_718, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_9204, c_42])).
% 10.30/4.17  tff(c_9438, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_9202, c_9436])).
% 10.30/4.17  tff(c_9454, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9208, c_9438])).
% 10.30/4.17  tff(c_9456, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_162])).
% 10.30/4.17  tff(c_15349, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_62, c_15326])).
% 10.30/4.17  tff(c_15372, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_14774, c_15349])).
% 10.30/4.17  tff(c_15379, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_15372])).
% 10.30/4.17  tff(c_15602, plain, (![A_1122, B_1123]: (r2_hidden('#skF_2'(A_1122, B_1123), k1_relat_1(A_1122)) | B_1123=A_1122 | k1_relat_1(B_1123)!=k1_relat_1(A_1122) | ~v1_funct_1(B_1123) | ~v1_relat_1(B_1123) | ~v1_funct_1(A_1122) | ~v1_relat_1(A_1122))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.30/4.17  tff(c_15616, plain, (![B_1123]: (r2_hidden('#skF_2'('#skF_6', B_1123), '#skF_3') | B_1123='#skF_6' | k1_relat_1(B_1123)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_1123) | ~v1_relat_1(B_1123) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_15379, c_15602])).
% 10.30/4.17  tff(c_15876, plain, (![B_1144]: (r2_hidden('#skF_2'('#skF_6', B_1144), '#skF_3') | B_1144='#skF_6' | k1_relat_1(B_1144)!='#skF_3' | ~v1_funct_1(B_1144) | ~v1_relat_1(B_1144))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_66, c_15379, c_15616])).
% 10.30/4.17  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.30/4.17  tff(c_15884, plain, (![B_1144]: (~v1_xboole_0('#skF_3') | B_1144='#skF_6' | k1_relat_1(B_1144)!='#skF_3' | ~v1_funct_1(B_1144) | ~v1_relat_1(B_1144))), inference(resolution, [status(thm)], [c_15876, c_2])).
% 10.30/4.17  tff(c_15891, plain, (![B_1145]: (B_1145='#skF_6' | k1_relat_1(B_1145)!='#skF_3' | ~v1_funct_1(B_1145) | ~v1_relat_1(B_1145))), inference(demodulation, [status(thm), theory('equality')], [c_9456, c_15884])).
% 10.30/4.17  tff(c_15903, plain, ('#skF_5'='#skF_6' | k1_relat_1('#skF_5')!='#skF_3' | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_190, c_15891])).
% 10.30/4.17  tff(c_15912, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_15385, c_15903])).
% 10.30/4.17  tff(c_15985, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_15912, c_58])).
% 10.30/4.17  tff(c_15997, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9656, c_15985])).
% 10.30/4.17  tff(c_15998, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_15375])).
% 10.30/4.17  tff(c_16028, plain, (![A_11]: (r1_tarski('#skF_4', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_15998, c_122])).
% 10.30/4.17  tff(c_16031, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15998, c_15998, c_14])).
% 10.30/4.17  tff(c_9477, plain, (![B_722, A_723]: (B_722=A_723 | ~r1_tarski(B_722, A_723) | ~r1_tarski(A_723, B_722))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.30/4.17  tff(c_9489, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_6' | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_6')), inference(resolution, [status(thm)], [c_120, c_9477])).
% 10.30/4.17  tff(c_14854, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_9489])).
% 10.30/4.17  tff(c_16145, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16031, c_14854])).
% 10.30/4.17  tff(c_16156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16028, c_16145])).
% 10.30/4.17  tff(c_16157, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_15372])).
% 10.30/4.17  tff(c_16187, plain, (![A_11]: (r1_tarski('#skF_4', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_16157, c_122])).
% 10.30/4.17  tff(c_16190, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16157, c_16157, c_14])).
% 10.30/4.17  tff(c_16304, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16190, c_14854])).
% 10.30/4.17  tff(c_16315, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16187, c_16304])).
% 10.30/4.17  tff(c_16316, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_6'), inference(splitRight, [status(thm)], [c_9489])).
% 10.30/4.17  tff(c_16786, plain, (![B_1193, C_1194, A_1195]: (k1_xboole_0=B_1193 | v1_funct_2(C_1194, A_1195, B_1193) | k1_relset_1(A_1195, B_1193, C_1194)!=A_1195 | ~m1_subset_1(C_1194, k1_zfmisc_1(k2_zfmisc_1(A_1195, B_1193))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.30/4.17  tff(c_16793, plain, (![C_1194]: (k1_xboole_0='#skF_4' | v1_funct_2(C_1194, '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', C_1194)!='#skF_3' | ~m1_subset_1(C_1194, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_16316, c_16786])).
% 10.30/4.17  tff(c_17333, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_16793])).
% 10.30/4.17  tff(c_16338, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_16316, c_12])).
% 10.30/4.17  tff(c_16449, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_16338])).
% 10.30/4.17  tff(c_17349, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_17333, c_16449])).
% 10.30/4.17  tff(c_17369, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_17333, c_17333, c_14])).
% 10.30/4.17  tff(c_17484, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_17369, c_16316])).
% 10.30/4.17  tff(c_17486, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17349, c_17484])).
% 10.30/4.17  tff(c_17488, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_16793])).
% 10.30/4.17  tff(c_30, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.30/4.17  tff(c_16608, plain, (![B_1177, A_1178, C_1179]: (k1_xboole_0=B_1177 | k1_relset_1(A_1178, B_1177, C_1179)=A_1178 | ~v1_funct_2(C_1179, A_1178, B_1177) | ~m1_subset_1(C_1179, k1_zfmisc_1(k2_zfmisc_1(A_1178, B_1177))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.30/4.17  tff(c_17551, plain, (![B_1238, A_1239, A_1240]: (k1_xboole_0=B_1238 | k1_relset_1(A_1239, B_1238, A_1240)=A_1239 | ~v1_funct_2(A_1240, A_1239, B_1238) | ~r1_tarski(A_1240, k2_zfmisc_1(A_1239, B_1238)))), inference(resolution, [status(thm)], [c_30, c_16608])).
% 10.30/4.17  tff(c_17558, plain, (![A_1240]: (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', A_1240)='#skF_3' | ~v1_funct_2(A_1240, '#skF_3', '#skF_4') | ~r1_tarski(A_1240, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_16316, c_17551])).
% 10.30/4.17  tff(c_17610, plain, (![A_1243]: (k1_relset_1('#skF_3', '#skF_4', A_1243)='#skF_3' | ~v1_funct_2(A_1243, '#skF_3', '#skF_4') | ~r1_tarski(A_1243, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_17488, c_17558])).
% 10.30/4.17  tff(c_17617, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_64, c_17610])).
% 10.30/4.17  tff(c_17627, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14774, c_17617])).
% 10.30/4.17  tff(c_16323, plain, (r1_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16316, c_121])).
% 10.30/4.17  tff(c_17620, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_70, c_17610])).
% 10.30/4.17  tff(c_17630, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16323, c_14775, c_17620])).
% 10.30/4.17  tff(c_17290, plain, (![A_1224, B_1225]: (r2_hidden('#skF_2'(A_1224, B_1225), k1_relat_1(A_1224)) | B_1225=A_1224 | k1_relat_1(B_1225)!=k1_relat_1(A_1224) | ~v1_funct_1(B_1225) | ~v1_relat_1(B_1225) | ~v1_funct_1(A_1224) | ~v1_relat_1(A_1224))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.30/4.17  tff(c_17999, plain, (![A_1264, B_1265]: (~v1_xboole_0(k1_relat_1(A_1264)) | B_1265=A_1264 | k1_relat_1(B_1265)!=k1_relat_1(A_1264) | ~v1_funct_1(B_1265) | ~v1_relat_1(B_1265) | ~v1_funct_1(A_1264) | ~v1_relat_1(A_1264))), inference(resolution, [status(thm)], [c_17290, c_2])).
% 10.30/4.17  tff(c_18001, plain, (![B_1265]: (~v1_xboole_0('#skF_3') | B_1265='#skF_5' | k1_relat_1(B_1265)!=k1_relat_1('#skF_5') | ~v1_funct_1(B_1265) | ~v1_relat_1(B_1265) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_17630, c_17999])).
% 10.30/4.17  tff(c_18008, plain, (![B_1266]: (B_1266='#skF_5' | k1_relat_1(B_1266)!='#skF_3' | ~v1_funct_1(B_1266) | ~v1_relat_1(B_1266))), inference(demodulation, [status(thm), theory('equality')], [c_190, c_72, c_17630, c_9456, c_18001])).
% 10.30/4.17  tff(c_18026, plain, ('#skF_5'='#skF_6' | k1_relat_1('#skF_6')!='#skF_3' | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_189, c_18008])).
% 10.30/4.17  tff(c_18037, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_17627, c_18026])).
% 10.30/4.17  tff(c_9490, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_121, c_9477])).
% 10.30/4.17  tff(c_9553, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_9490])).
% 10.30/4.17  tff(c_16321, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16316, c_9553])).
% 10.30/4.17  tff(c_18048, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_18037, c_16321])).
% 10.30/4.17  tff(c_18068, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_18048])).
% 10.30/4.17  tff(c_18070, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_16338])).
% 10.30/4.17  tff(c_18087, plain, (![A_11]: (r1_tarski('#skF_6', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_18070, c_122])).
% 10.30/4.17  tff(c_18101, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18087, c_16321])).
% 10.30/4.17  tff(c_18102, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_9490])).
% 10.30/4.17  tff(c_18107, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_18102, c_68])).
% 10.30/4.17  tff(c_18387, plain, (![A_1295, B_1296, C_1297]: (k1_relset_1(A_1295, B_1296, C_1297)=k1_relat_1(C_1297) | ~m1_subset_1(C_1297, k1_zfmisc_1(k2_zfmisc_1(A_1295, B_1296))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.30/4.17  tff(c_18571, plain, (![C_1310]: (k1_relset_1('#skF_3', '#skF_4', C_1310)=k1_relat_1(C_1310) | ~m1_subset_1(C_1310, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_18102, c_18387])).
% 10.30/4.17  tff(c_18599, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_18107, c_18571])).
% 10.30/4.17  tff(c_18876, plain, (![B_1332, A_1333, C_1334]: (k1_xboole_0=B_1332 | k1_relset_1(A_1333, B_1332, C_1334)=A_1333 | ~v1_funct_2(C_1334, A_1333, B_1332) | ~m1_subset_1(C_1334, k1_zfmisc_1(k2_zfmisc_1(A_1333, B_1332))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.30/4.17  tff(c_18883, plain, (![C_1334]: (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', C_1334)='#skF_3' | ~v1_funct_2(C_1334, '#skF_3', '#skF_4') | ~m1_subset_1(C_1334, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_18102, c_18876])).
% 10.30/4.17  tff(c_18963, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_18883])).
% 10.30/4.17  tff(c_18114, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_18102, c_12])).
% 10.30/4.17  tff(c_18246, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_18114])).
% 10.30/4.17  tff(c_18983, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_18963, c_18246])).
% 10.30/4.17  tff(c_18997, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18963, c_18963, c_14])).
% 10.30/4.17  tff(c_19124, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_18997, c_18102])).
% 10.30/4.17  tff(c_19126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18983, c_19124])).
% 10.30/4.17  tff(c_19790, plain, (![C_1388]: (k1_relset_1('#skF_3', '#skF_4', C_1388)='#skF_3' | ~v1_funct_2(C_1388, '#skF_3', '#skF_4') | ~m1_subset_1(C_1388, k1_zfmisc_1('#skF_5')))), inference(splitRight, [status(thm)], [c_18883])).
% 10.30/4.17  tff(c_19801, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_18107, c_19790])).
% 10.30/4.17  tff(c_19826, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_18599, c_19801])).
% 10.30/4.17  tff(c_18106, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_18102, c_62])).
% 10.30/4.17  tff(c_18600, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_18106, c_18571])).
% 10.30/4.17  tff(c_19804, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_18106, c_19790])).
% 10.30/4.17  tff(c_19829, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_18600, c_19804])).
% 10.30/4.17  tff(c_19500, plain, (![A_1369, B_1370]: (r2_hidden('#skF_2'(A_1369, B_1370), k1_relat_1(A_1369)) | B_1370=A_1369 | k1_relat_1(B_1370)!=k1_relat_1(A_1369) | ~v1_funct_1(B_1370) | ~v1_relat_1(B_1370) | ~v1_funct_1(A_1369) | ~v1_relat_1(A_1369))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.30/4.17  tff(c_20266, plain, (![A_1413, B_1414]: (~v1_xboole_0(k1_relat_1(A_1413)) | B_1414=A_1413 | k1_relat_1(B_1414)!=k1_relat_1(A_1413) | ~v1_funct_1(B_1414) | ~v1_relat_1(B_1414) | ~v1_funct_1(A_1413) | ~v1_relat_1(A_1413))), inference(resolution, [status(thm)], [c_19500, c_2])).
% 10.30/4.17  tff(c_20268, plain, (![B_1414]: (~v1_xboole_0('#skF_3') | B_1414='#skF_6' | k1_relat_1(B_1414)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_1414) | ~v1_relat_1(B_1414) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_19829, c_20266])).
% 10.30/4.17  tff(c_20275, plain, (![B_1415]: (B_1415='#skF_6' | k1_relat_1(B_1415)!='#skF_3' | ~v1_funct_1(B_1415) | ~v1_relat_1(B_1415))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_66, c_19829, c_9456, c_20268])).
% 10.30/4.17  tff(c_20290, plain, ('#skF_5'='#skF_6' | k1_relat_1('#skF_5')!='#skF_3' | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_190, c_20275])).
% 10.30/4.17  tff(c_20300, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_19826, c_20290])).
% 10.30/4.17  tff(c_18104, plain, (r1_tarski('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_18102, c_120])).
% 10.30/4.17  tff(c_18127, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_18104, c_6])).
% 10.30/4.17  tff(c_18170, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_18127])).
% 10.30/4.17  tff(c_20335, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_20300, c_18170])).
% 10.30/4.17  tff(c_20354, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_20335])).
% 10.30/4.17  tff(c_20356, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_18114])).
% 10.30/4.17  tff(c_20367, plain, (![A_11]: (r1_tarski('#skF_5', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_20356, c_122])).
% 10.30/4.17  tff(c_20394, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20367, c_18170])).
% 10.30/4.17  tff(c_20395, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_18127])).
% 10.30/4.17  tff(c_20406, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_20395, c_58])).
% 10.30/4.17  tff(c_20398, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_20395, c_20395, c_18107])).
% 10.30/4.17  tff(c_20401, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_20395, c_18102])).
% 10.30/4.17  tff(c_20729, plain, (![D_1452]: (r2_relset_1('#skF_3', '#skF_4', D_1452, D_1452) | ~m1_subset_1(D_1452, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_20401, c_42])).
% 10.30/4.17  tff(c_20734, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_20398, c_20729])).
% 10.30/4.17  tff(c_20751, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20406, c_20734])).
% 10.30/4.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.30/4.17  
% 10.30/4.17  Inference rules
% 10.30/4.17  ----------------------
% 10.30/4.17  #Ref     : 11
% 10.30/4.17  #Sup     : 4054
% 10.30/4.17  #Fact    : 0
% 10.30/4.17  #Define  : 0
% 10.30/4.17  #Split   : 111
% 10.30/4.17  #Chain   : 0
% 10.30/4.17  #Close   : 0
% 10.30/4.17  
% 10.30/4.17  Ordering : KBO
% 10.30/4.17  
% 10.30/4.17  Simplification rules
% 10.30/4.17  ----------------------
% 10.30/4.17  #Subsume      : 661
% 10.30/4.17  #Demod        : 4353
% 10.30/4.17  #Tautology    : 1954
% 10.30/4.17  #SimpNegUnit  : 500
% 10.30/4.17  #BackRed      : 939
% 10.30/4.17  
% 10.30/4.17  #Partial instantiations: 0
% 10.30/4.17  #Strategies tried      : 1
% 10.30/4.17  
% 10.30/4.17  Timing (in seconds)
% 10.30/4.17  ----------------------
% 10.30/4.17  Preprocessing        : 0.37
% 10.30/4.17  Parsing              : 0.19
% 10.30/4.17  CNF conversion       : 0.03
% 10.69/4.17  Main loop            : 2.91
% 10.69/4.17  Inferencing          : 0.87
% 10.69/4.17  Reduction            : 1.08
% 10.69/4.17  Demodulation         : 0.74
% 10.69/4.17  BG Simplification    : 0.10
% 10.69/4.17  Subsumption          : 0.61
% 10.69/4.17  Abstraction          : 0.12
% 10.69/4.17  MUC search           : 0.00
% 10.69/4.17  Cooper               : 0.00
% 10.69/4.17  Total                : 3.37
% 10.69/4.17  Index Insertion      : 0.00
% 10.69/4.17  Index Deletion       : 0.00
% 10.69/4.17  Index Matching       : 0.00
% 10.69/4.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
