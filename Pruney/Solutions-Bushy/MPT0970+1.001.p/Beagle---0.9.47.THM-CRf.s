%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0970+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:09 EST 2020

% Result     : Theorem 8.83s
% Output     : CNFRefutation 8.87s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 714 expanded)
%              Number of leaves         :   41 ( 256 expanded)
%              Depth                    :   20
%              Number of atoms          :  285 (2057 expanded)
%              Number of equality atoms :   87 ( 651 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_9 > #skF_5 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_135,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_53,axiom,(
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

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_94,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_73,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_111,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_76,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_60,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_142,plain,(
    ! [C_101,B_102,A_103] :
      ( v1_xboole_0(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(B_102,A_103)))
      | ~ v1_xboole_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_150,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_142])).

tff(c_160,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_204,plain,(
    ! [A_114,B_115,C_116] :
      ( k2_relset_1(A_114,B_115,C_116) = k2_relat_1(C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_212,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_204])).

tff(c_58,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_214,plain,(
    k2_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_58])).

tff(c_107,plain,(
    ! [C_90,A_91,B_92] :
      ( v1_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_115,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_107])).

tff(c_64,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_62,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_240,plain,(
    ! [A_119,B_120,C_121] :
      ( k1_relset_1(A_119,B_120,C_121) = k1_relat_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_252,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_240])).

tff(c_1963,plain,(
    ! [B_279,A_280,C_281] :
      ( k1_xboole_0 = B_279
      | k1_relset_1(A_280,B_279,C_281) = A_280
      | ~ v1_funct_2(C_281,A_280,B_279)
      | ~ m1_subset_1(C_281,k1_zfmisc_1(k2_zfmisc_1(A_280,B_279))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1985,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_1963])).

tff(c_1997,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_252,c_1985])).

tff(c_1999,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1997])).

tff(c_2098,plain,(
    ! [A_288,B_289] :
      ( r2_hidden('#skF_2'(A_288,B_289),k1_relat_1(A_288))
      | r2_hidden('#skF_3'(A_288,B_289),B_289)
      | k2_relat_1(A_288) = B_289
      | ~ v1_funct_1(A_288)
      | ~ v1_relat_1(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2146,plain,(
    ! [B_289] :
      ( r2_hidden('#skF_2'('#skF_8',B_289),'#skF_6')
      | r2_hidden('#skF_3'('#skF_8',B_289),B_289)
      | k2_relat_1('#skF_8') = B_289
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1999,c_2098])).

tff(c_2160,plain,(
    ! [B_289] :
      ( r2_hidden('#skF_2'('#skF_8',B_289),'#skF_6')
      | r2_hidden('#skF_3'('#skF_8',B_289),B_289)
      | k2_relat_1('#skF_8') = B_289 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_64,c_2146])).

tff(c_68,plain,(
    ! [D_78] :
      ( r2_hidden('#skF_9'(D_78),'#skF_6')
      | ~ r2_hidden(D_78,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_66,plain,(
    ! [D_78] :
      ( k1_funct_1('#skF_8','#skF_9'(D_78)) = D_78
      | ~ r2_hidden(D_78,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_3005,plain,(
    ! [A_342,B_343,D_344] :
      ( r2_hidden('#skF_2'(A_342,B_343),k1_relat_1(A_342))
      | k1_funct_1(A_342,D_344) != '#skF_3'(A_342,B_343)
      | ~ r2_hidden(D_344,k1_relat_1(A_342))
      | k2_relat_1(A_342) = B_343
      | ~ v1_funct_1(A_342)
      | ~ v1_relat_1(A_342) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3011,plain,(
    ! [B_343,D_78] :
      ( r2_hidden('#skF_2'('#skF_8',B_343),k1_relat_1('#skF_8'))
      | D_78 != '#skF_3'('#skF_8',B_343)
      | ~ r2_hidden('#skF_9'(D_78),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_343
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_78,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_3005])).

tff(c_3013,plain,(
    ! [B_343,D_78] :
      ( r2_hidden('#skF_2'('#skF_8',B_343),'#skF_6')
      | D_78 != '#skF_3'('#skF_8',B_343)
      | ~ r2_hidden('#skF_9'(D_78),'#skF_6')
      | k2_relat_1('#skF_8') = B_343
      | ~ r2_hidden(D_78,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_64,c_1999,c_1999,c_3011])).

tff(c_3630,plain,(
    ! [B_387] :
      ( r2_hidden('#skF_2'('#skF_8',B_387),'#skF_6')
      | ~ r2_hidden('#skF_9'('#skF_3'('#skF_8',B_387)),'#skF_6')
      | k2_relat_1('#skF_8') = B_387
      | ~ r2_hidden('#skF_3'('#skF_8',B_387),'#skF_7') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3013])).

tff(c_3660,plain,(
    ! [B_390] :
      ( r2_hidden('#skF_2'('#skF_8',B_390),'#skF_6')
      | k2_relat_1('#skF_8') = B_390
      | ~ r2_hidden('#skF_3'('#skF_8',B_390),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_68,c_3630])).

tff(c_3668,plain,
    ( r2_hidden('#skF_2'('#skF_8','#skF_7'),'#skF_6')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_2160,c_3660])).

tff(c_3688,plain,(
    r2_hidden('#skF_2'('#skF_8','#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_214,c_3668])).

tff(c_32,plain,(
    ! [A_11,B_33] :
      ( k1_funct_1(A_11,'#skF_2'(A_11,B_33)) = '#skF_1'(A_11,B_33)
      | r2_hidden('#skF_3'(A_11,B_33),B_33)
      | k2_relat_1(A_11) = B_33
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3194,plain,(
    ! [A_358,B_359,D_360] :
      ( k1_funct_1(A_358,'#skF_2'(A_358,B_359)) = '#skF_1'(A_358,B_359)
      | k1_funct_1(A_358,D_360) != '#skF_3'(A_358,B_359)
      | ~ r2_hidden(D_360,k1_relat_1(A_358))
      | k2_relat_1(A_358) = B_359
      | ~ v1_funct_1(A_358)
      | ~ v1_relat_1(A_358) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3200,plain,(
    ! [B_359,D_78] :
      ( k1_funct_1('#skF_8','#skF_2'('#skF_8',B_359)) = '#skF_1'('#skF_8',B_359)
      | D_78 != '#skF_3'('#skF_8',B_359)
      | ~ r2_hidden('#skF_9'(D_78),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_359
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_78,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_3194])).

tff(c_3202,plain,(
    ! [B_359,D_78] :
      ( k1_funct_1('#skF_8','#skF_2'('#skF_8',B_359)) = '#skF_1'('#skF_8',B_359)
      | D_78 != '#skF_3'('#skF_8',B_359)
      | ~ r2_hidden('#skF_9'(D_78),'#skF_6')
      | k2_relat_1('#skF_8') = B_359
      | ~ r2_hidden(D_78,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_64,c_1999,c_3200])).

tff(c_4045,plain,(
    ! [B_415] :
      ( k1_funct_1('#skF_8','#skF_2'('#skF_8',B_415)) = '#skF_1'('#skF_8',B_415)
      | ~ r2_hidden('#skF_9'('#skF_3'('#skF_8',B_415)),'#skF_6')
      | k2_relat_1('#skF_8') = B_415
      | ~ r2_hidden('#skF_3'('#skF_8',B_415),'#skF_7') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3202])).

tff(c_4547,plain,(
    ! [B_426] :
      ( k1_funct_1('#skF_8','#skF_2'('#skF_8',B_426)) = '#skF_1'('#skF_8',B_426)
      | k2_relat_1('#skF_8') = B_426
      | ~ r2_hidden('#skF_3'('#skF_8',B_426),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_68,c_4045])).

tff(c_4563,plain,
    ( k1_funct_1('#skF_8','#skF_2'('#skF_8','#skF_7')) = '#skF_1'('#skF_8','#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_32,c_4547])).

tff(c_4586,plain,
    ( k1_funct_1('#skF_8','#skF_2'('#skF_8','#skF_7')) = '#skF_1'('#skF_8','#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_64,c_4563])).

tff(c_4587,plain,(
    k1_funct_1('#skF_8','#skF_2'('#skF_8','#skF_7')) = '#skF_1'('#skF_8','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_4586])).

tff(c_1016,plain,(
    ! [A_192,D_193] :
      ( r2_hidden(k1_funct_1(A_192,D_193),k2_relat_1(A_192))
      | ~ r2_hidden(D_193,k1_relat_1(A_192))
      | ~ v1_funct_1(A_192)
      | ~ v1_relat_1(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_297,plain,(
    ! [A_132,B_133,C_134] :
      ( m1_subset_1(k2_relset_1(A_132,B_133,C_134),k1_zfmisc_1(B_133))
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_323,plain,
    ( m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_297])).

tff(c_331,plain,(
    m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_323])).

tff(c_50,plain,(
    ! [A_66,C_68,B_67] :
      ( m1_subset_1(A_66,C_68)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(C_68))
      | ~ r2_hidden(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_336,plain,(
    ! [A_66] :
      ( m1_subset_1(A_66,'#skF_7')
      | ~ r2_hidden(A_66,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_331,c_50])).

tff(c_1020,plain,(
    ! [D_193] :
      ( m1_subset_1(k1_funct_1('#skF_8',D_193),'#skF_7')
      | ~ r2_hidden(D_193,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1016,c_336])).

tff(c_1032,plain,(
    ! [D_193] :
      ( m1_subset_1(k1_funct_1('#skF_8',D_193),'#skF_7')
      | ~ r2_hidden(D_193,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_64,c_1020])).

tff(c_2006,plain,(
    ! [D_193] :
      ( m1_subset_1(k1_funct_1('#skF_8',D_193),'#skF_7')
      | ~ r2_hidden(D_193,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1999,c_1032])).

tff(c_4606,plain,
    ( m1_subset_1('#skF_1'('#skF_8','#skF_7'),'#skF_7')
    | ~ r2_hidden('#skF_2'('#skF_8','#skF_7'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4587,c_2006])).

tff(c_4623,plain,(
    m1_subset_1('#skF_1'('#skF_8','#skF_7'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3688,c_4606])).

tff(c_48,plain,(
    ! [A_64,B_65] :
      ( r2_hidden(A_64,B_65)
      | v1_xboole_0(B_65)
      | ~ m1_subset_1(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_30,plain,(
    ! [A_11,B_33] :
      ( ~ r2_hidden('#skF_1'(A_11,B_33),B_33)
      | r2_hidden('#skF_3'(A_11,B_33),B_33)
      | k2_relat_1(A_11) = B_33
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2706,plain,(
    ! [A_316,B_317,D_318] :
      ( ~ r2_hidden('#skF_1'(A_316,B_317),B_317)
      | k1_funct_1(A_316,D_318) != '#skF_3'(A_316,B_317)
      | ~ r2_hidden(D_318,k1_relat_1(A_316))
      | k2_relat_1(A_316) = B_317
      | ~ v1_funct_1(A_316)
      | ~ v1_relat_1(A_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_8412,plain,(
    ! [A_597,D_598,B_599] :
      ( k1_funct_1(A_597,D_598) != '#skF_3'(A_597,B_599)
      | ~ r2_hidden(D_598,k1_relat_1(A_597))
      | k2_relat_1(A_597) = B_599
      | ~ v1_funct_1(A_597)
      | ~ v1_relat_1(A_597)
      | v1_xboole_0(B_599)
      | ~ m1_subset_1('#skF_1'(A_597,B_599),B_599) ) ),
    inference(resolution,[status(thm)],[c_48,c_2706])).

tff(c_8428,plain,(
    ! [D_78,B_599] :
      ( D_78 != '#skF_3'('#skF_8',B_599)
      | ~ r2_hidden('#skF_9'(D_78),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_599
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | v1_xboole_0(B_599)
      | ~ m1_subset_1('#skF_1'('#skF_8',B_599),B_599)
      | ~ r2_hidden(D_78,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_8412])).

tff(c_8434,plain,(
    ! [D_78,B_599] :
      ( D_78 != '#skF_3'('#skF_8',B_599)
      | ~ r2_hidden('#skF_9'(D_78),'#skF_6')
      | k2_relat_1('#skF_8') = B_599
      | v1_xboole_0(B_599)
      | ~ m1_subset_1('#skF_1'('#skF_8',B_599),B_599)
      | ~ r2_hidden(D_78,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_64,c_1999,c_8428])).

tff(c_8922,plain,(
    ! [B_631] :
      ( ~ r2_hidden('#skF_9'('#skF_3'('#skF_8',B_631)),'#skF_6')
      | k2_relat_1('#skF_8') = B_631
      | v1_xboole_0(B_631)
      | ~ m1_subset_1('#skF_1'('#skF_8',B_631),B_631)
      | ~ r2_hidden('#skF_3'('#skF_8',B_631),'#skF_7') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_8434])).

tff(c_8933,plain,(
    ! [B_632] :
      ( k2_relat_1('#skF_8') = B_632
      | v1_xboole_0(B_632)
      | ~ m1_subset_1('#skF_1'('#skF_8',B_632),B_632)
      | ~ r2_hidden('#skF_3'('#skF_8',B_632),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_68,c_8922])).

tff(c_8938,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | v1_xboole_0('#skF_7')
    | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_4623,c_8933])).

tff(c_8949,plain,(
    ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_214,c_8938])).

tff(c_8975,plain,
    ( ~ r2_hidden('#skF_1'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_30,c_8949])).

tff(c_8999,plain,
    ( ~ r2_hidden('#skF_1'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_64,c_8975])).

tff(c_9000,plain,(
    ~ r2_hidden('#skF_1'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_8999])).

tff(c_9006,plain,
    ( v1_xboole_0('#skF_7')
    | ~ m1_subset_1('#skF_1'('#skF_8','#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_48,c_9000])).

tff(c_9009,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4623,c_9006])).

tff(c_9011,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_9009])).

tff(c_9012,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1997])).

tff(c_38,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_69,plain,(
    ! [A_80] :
      ( k1_xboole_0 = A_80
      | ~ v1_xboole_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_73,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_69])).

tff(c_74,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_38])).

tff(c_9046,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9012,c_74])).

tff(c_9050,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_9046])).

tff(c_9051,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_54,plain,(
    ! [A_72] :
      ( k1_xboole_0 = A_72
      | ~ v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_9056,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_9051,c_54])).

tff(c_9052,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_9070,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_9052,c_54])).

tff(c_9079,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9056,c_9070])).

tff(c_9057,plain,(
    ! [A_633,B_634,C_635] :
      ( k2_relset_1(A_633,B_634,C_635) = k2_relat_1(C_635)
      | ~ m1_subset_1(C_635,k1_zfmisc_1(k2_zfmisc_1(A_633,B_634))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_9065,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_9057])).

tff(c_9103,plain,(
    k2_relset_1('#skF_6','#skF_8','#skF_8') = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9079,c_9065])).

tff(c_9086,plain,(
    k2_relset_1('#skF_6','#skF_8','#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9079,c_9079,c_58])).

tff(c_9104,plain,(
    k2_relat_1('#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9103,c_9086])).

tff(c_40,plain,(
    ! [A_54] : m1_subset_1('#skF_5'(A_54),A_54) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_9085,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9079,c_60])).

tff(c_9209,plain,(
    ! [A_651,B_652,C_653] :
      ( m1_subset_1(k2_relset_1(A_651,B_652,C_653),k1_zfmisc_1(B_652))
      | ~ m1_subset_1(C_653,k1_zfmisc_1(k2_zfmisc_1(A_651,B_652))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_9232,plain,
    ( m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_8'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_9103,c_9209])).

tff(c_9240,plain,(
    m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9085,c_9232])).

tff(c_52,plain,(
    ! [C_71,B_70,A_69] :
      ( ~ v1_xboole_0(C_71)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(C_71))
      | ~ r2_hidden(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_9244,plain,(
    ! [A_69] :
      ( ~ v1_xboole_0('#skF_8')
      | ~ r2_hidden(A_69,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_9240,c_52])).

tff(c_9249,plain,(
    ! [A_654] : ~ r2_hidden(A_654,k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9051,c_9244])).

tff(c_9254,plain,(
    ! [A_64] :
      ( v1_xboole_0(k2_relat_1('#skF_8'))
      | ~ m1_subset_1(A_64,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_48,c_9249])).

tff(c_9256,plain,(
    ! [A_655] : ~ m1_subset_1(A_655,k2_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_9254])).

tff(c_9261,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_40,c_9256])).

tff(c_9262,plain,(
    v1_xboole_0(k2_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_9254])).

tff(c_9073,plain,(
    ! [A_72] :
      ( A_72 = '#skF_8'
      | ~ v1_xboole_0(A_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9056,c_54])).

tff(c_9287,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_9262,c_9073])).

tff(c_9291,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9104,c_9287])).

%------------------------------------------------------------------------------
