%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:25 EST 2020

% Result     : Theorem 6.19s
% Output     : CNFRefutation 6.43s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 221 expanded)
%              Number of leaves         :   43 (  94 expanded)
%              Depth                    :   12
%              Number of atoms          :  165 ( 538 expanded)
%              Number of equality atoms :   38 ( 115 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_131,negated_conjecture,(
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

tff(f_65,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
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

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_80,axiom,(
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

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_68,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_28,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_70,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_102,plain,(
    ! [B_86,A_87] :
      ( v1_relat_1(B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_87))
      | ~ v1_relat_1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_108,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_70,c_102])).

tff(c_112,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_108])).

tff(c_142,plain,(
    ! [C_96,B_97,A_98] :
      ( v5_relat_1(C_96,B_97)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_98,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_151,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_142])).

tff(c_26,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k2_relat_1(B_17),A_16)
      | ~ v5_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3481,plain,(
    ! [A_426,B_427,C_428] :
      ( k2_relset_1(A_426,B_427,C_428) = k2_relat_1(C_428)
      | ~ m1_subset_1(C_428,k1_zfmisc_1(k2_zfmisc_1(A_426,B_427))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3490,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_3481])).

tff(c_3491,plain,(
    k2_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3490,c_68])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_195,plain,(
    ! [C_112,B_113,A_114] :
      ( ~ v1_xboole_0(C_112)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(C_112))
      | ~ r2_hidden(A_114,B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_207,plain,(
    ! [B_117,A_118,A_119] :
      ( ~ v1_xboole_0(B_117)
      | ~ r2_hidden(A_118,A_119)
      | ~ r1_tarski(A_119,B_117) ) ),
    inference(resolution,[status(thm)],[c_18,c_195])).

tff(c_217,plain,(
    ! [B_120,A_121,B_122] :
      ( ~ v1_xboole_0(B_120)
      | ~ r1_tarski(A_121,B_120)
      | r1_tarski(A_121,B_122) ) ),
    inference(resolution,[status(thm)],[c_6,c_207])).

tff(c_227,plain,(
    ! [B_123,B_124] :
      ( ~ v1_xboole_0(B_123)
      | r1_tarski(B_123,B_124) ) ),
    inference(resolution,[status(thm)],[c_14,c_217])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_591,plain,(
    ! [B_168,B_167] :
      ( B_168 = B_167
      | ~ r1_tarski(B_167,B_168)
      | ~ v1_xboole_0(B_168) ) ),
    inference(resolution,[status(thm)],[c_227,c_10])).

tff(c_3395,plain,(
    ! [B_414,A_415] :
      ( k2_relat_1(B_414) = A_415
      | ~ v1_xboole_0(A_415)
      | ~ v5_relat_1(B_414,A_415)
      | ~ v1_relat_1(B_414) ) ),
    inference(resolution,[status(thm)],[c_26,c_591])).

tff(c_3407,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_xboole_0('#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_151,c_3395])).

tff(c_3416,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_3407])).

tff(c_3430,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_3416])).

tff(c_72,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_3380,plain,(
    ! [A_410,B_411,C_412] :
      ( k1_relset_1(A_410,B_411,C_412) = k1_relat_1(C_412)
      | ~ m1_subset_1(C_412,k1_zfmisc_1(k2_zfmisc_1(A_410,B_411))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3389,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_3380])).

tff(c_4808,plain,(
    ! [B_541,A_542,C_543] :
      ( k1_xboole_0 = B_541
      | k1_relset_1(A_542,B_541,C_543) = A_542
      | ~ v1_funct_2(C_543,A_542,B_541)
      | ~ m1_subset_1(C_543,k1_zfmisc_1(k2_zfmisc_1(A_542,B_541))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_4815,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_4808])).

tff(c_4819,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3389,c_4815])).

tff(c_4820,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_4819])).

tff(c_78,plain,(
    ! [D_75] :
      ( r2_hidden('#skF_9'(D_75),'#skF_6')
      | ~ r2_hidden(D_75,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_164,plain,(
    ! [C_104,B_105,A_106] :
      ( r2_hidden(C_104,B_105)
      | ~ r2_hidden(C_104,A_106)
      | ~ r1_tarski(A_106,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_170,plain,(
    ! [D_75,B_105] :
      ( r2_hidden('#skF_9'(D_75),B_105)
      | ~ r1_tarski('#skF_6',B_105)
      | ~ r2_hidden(D_75,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_78,c_164])).

tff(c_74,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_76,plain,(
    ! [D_75] :
      ( k1_funct_1('#skF_8','#skF_9'(D_75)) = D_75
      | ~ r2_hidden(D_75,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_3834,plain,(
    ! [A_452,D_453] :
      ( r2_hidden(k1_funct_1(A_452,D_453),k2_relat_1(A_452))
      | ~ r2_hidden(D_453,k1_relat_1(A_452))
      | ~ v1_funct_1(A_452)
      | ~ v1_relat_1(A_452) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3853,plain,(
    ! [D_75] :
      ( r2_hidden(D_75,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_75),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_75,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_3834])).

tff(c_3904,plain,(
    ! [D_462] :
      ( r2_hidden(D_462,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_462),k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_462,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_74,c_3853])).

tff(c_3909,plain,(
    ! [D_75] :
      ( r2_hidden(D_75,k2_relat_1('#skF_8'))
      | ~ r1_tarski('#skF_6',k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_75,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_170,c_3904])).

tff(c_3985,plain,(
    ~ r1_tarski('#skF_6',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_3909])).

tff(c_4821,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4820,c_3985])).

tff(c_4826,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_4821])).

tff(c_4827,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_4819])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4858,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4827,c_8])).

tff(c_4861,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3430,c_4858])).

tff(c_4899,plain,(
    ! [D_546] :
      ( r2_hidden(D_546,k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_546,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_3909])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5208,plain,(
    ! [A_561] :
      ( r1_tarski(A_561,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_561,k2_relat_1('#skF_8')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_4899,c_4])).

tff(c_5218,plain,(
    r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6,c_5208])).

tff(c_5229,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_5218,c_10])).

tff(c_5240,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_3491,c_5229])).

tff(c_5249,plain,
    ( ~ v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_26,c_5240])).

tff(c_5254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_151,c_5249])).

tff(c_5255,plain,(
    k2_relat_1('#skF_8') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_3416])).

tff(c_5308,plain,(
    ! [A_562,B_563,C_564] :
      ( k2_relset_1(A_562,B_563,C_564) = k2_relat_1(C_564)
      | ~ m1_subset_1(C_564,k1_zfmisc_1(k2_zfmisc_1(A_562,B_563))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_5315,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_5308])).

tff(c_5318,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5255,c_5315])).

tff(c_5320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_5318])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:42:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.19/2.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.19/2.28  
% 6.19/2.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.19/2.28  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 6.19/2.28  
% 6.19/2.28  %Foreground sorts:
% 6.19/2.28  
% 6.19/2.28  
% 6.19/2.28  %Background operators:
% 6.19/2.28  
% 6.19/2.28  
% 6.19/2.28  %Foreground operators:
% 6.19/2.28  tff('#skF_9', type, '#skF_9': $i > $i).
% 6.19/2.28  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.19/2.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.19/2.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.19/2.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.19/2.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.19/2.28  tff('#skF_7', type, '#skF_7': $i).
% 6.19/2.28  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.19/2.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.19/2.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.19/2.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.19/2.28  tff('#skF_6', type, '#skF_6': $i).
% 6.19/2.28  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 6.19/2.28  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.19/2.28  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.19/2.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.19/2.28  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.19/2.28  tff('#skF_8', type, '#skF_8': $i).
% 6.19/2.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.19/2.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.19/2.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.19/2.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.19/2.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.19/2.28  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.19/2.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.19/2.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.19/2.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.19/2.28  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.19/2.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.19/2.28  
% 6.43/2.30  tff(f_131, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 6.43/2.30  tff(f_65, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.43/2.30  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.43/2.30  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.43/2.30  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 6.43/2.30  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.43/2.30  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.43/2.30  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.43/2.30  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.43/2.30  tff(f_50, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 6.43/2.30  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.43/2.30  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.43/2.30  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 6.43/2.30  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.43/2.30  tff(c_68, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.43/2.30  tff(c_28, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.43/2.30  tff(c_70, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.43/2.30  tff(c_102, plain, (![B_86, A_87]: (v1_relat_1(B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(A_87)) | ~v1_relat_1(A_87))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.43/2.30  tff(c_108, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_70, c_102])).
% 6.43/2.30  tff(c_112, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_108])).
% 6.43/2.30  tff(c_142, plain, (![C_96, B_97, A_98]: (v5_relat_1(C_96, B_97) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_98, B_97))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.43/2.30  tff(c_151, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_70, c_142])).
% 6.43/2.30  tff(c_26, plain, (![B_17, A_16]: (r1_tarski(k2_relat_1(B_17), A_16) | ~v5_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.43/2.30  tff(c_3481, plain, (![A_426, B_427, C_428]: (k2_relset_1(A_426, B_427, C_428)=k2_relat_1(C_428) | ~m1_subset_1(C_428, k1_zfmisc_1(k2_zfmisc_1(A_426, B_427))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.43/2.30  tff(c_3490, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_70, c_3481])).
% 6.43/2.30  tff(c_3491, plain, (k2_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_3490, c_68])).
% 6.43/2.30  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.43/2.30  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.43/2.30  tff(c_18, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.43/2.30  tff(c_195, plain, (![C_112, B_113, A_114]: (~v1_xboole_0(C_112) | ~m1_subset_1(B_113, k1_zfmisc_1(C_112)) | ~r2_hidden(A_114, B_113))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.43/2.30  tff(c_207, plain, (![B_117, A_118, A_119]: (~v1_xboole_0(B_117) | ~r2_hidden(A_118, A_119) | ~r1_tarski(A_119, B_117))), inference(resolution, [status(thm)], [c_18, c_195])).
% 6.43/2.30  tff(c_217, plain, (![B_120, A_121, B_122]: (~v1_xboole_0(B_120) | ~r1_tarski(A_121, B_120) | r1_tarski(A_121, B_122))), inference(resolution, [status(thm)], [c_6, c_207])).
% 6.43/2.30  tff(c_227, plain, (![B_123, B_124]: (~v1_xboole_0(B_123) | r1_tarski(B_123, B_124))), inference(resolution, [status(thm)], [c_14, c_217])).
% 6.43/2.30  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.43/2.30  tff(c_591, plain, (![B_168, B_167]: (B_168=B_167 | ~r1_tarski(B_167, B_168) | ~v1_xboole_0(B_168))), inference(resolution, [status(thm)], [c_227, c_10])).
% 6.43/2.30  tff(c_3395, plain, (![B_414, A_415]: (k2_relat_1(B_414)=A_415 | ~v1_xboole_0(A_415) | ~v5_relat_1(B_414, A_415) | ~v1_relat_1(B_414))), inference(resolution, [status(thm)], [c_26, c_591])).
% 6.43/2.30  tff(c_3407, plain, (k2_relat_1('#skF_8')='#skF_7' | ~v1_xboole_0('#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_151, c_3395])).
% 6.43/2.30  tff(c_3416, plain, (k2_relat_1('#skF_8')='#skF_7' | ~v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_3407])).
% 6.43/2.30  tff(c_3430, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_3416])).
% 6.43/2.30  tff(c_72, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.43/2.30  tff(c_3380, plain, (![A_410, B_411, C_412]: (k1_relset_1(A_410, B_411, C_412)=k1_relat_1(C_412) | ~m1_subset_1(C_412, k1_zfmisc_1(k2_zfmisc_1(A_410, B_411))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.43/2.30  tff(c_3389, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_70, c_3380])).
% 6.43/2.30  tff(c_4808, plain, (![B_541, A_542, C_543]: (k1_xboole_0=B_541 | k1_relset_1(A_542, B_541, C_543)=A_542 | ~v1_funct_2(C_543, A_542, B_541) | ~m1_subset_1(C_543, k1_zfmisc_1(k2_zfmisc_1(A_542, B_541))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.43/2.30  tff(c_4815, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_70, c_4808])).
% 6.43/2.30  tff(c_4819, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_3389, c_4815])).
% 6.43/2.30  tff(c_4820, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_4819])).
% 6.43/2.30  tff(c_78, plain, (![D_75]: (r2_hidden('#skF_9'(D_75), '#skF_6') | ~r2_hidden(D_75, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.43/2.30  tff(c_164, plain, (![C_104, B_105, A_106]: (r2_hidden(C_104, B_105) | ~r2_hidden(C_104, A_106) | ~r1_tarski(A_106, B_105))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.43/2.30  tff(c_170, plain, (![D_75, B_105]: (r2_hidden('#skF_9'(D_75), B_105) | ~r1_tarski('#skF_6', B_105) | ~r2_hidden(D_75, '#skF_7'))), inference(resolution, [status(thm)], [c_78, c_164])).
% 6.43/2.30  tff(c_74, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.43/2.30  tff(c_76, plain, (![D_75]: (k1_funct_1('#skF_8', '#skF_9'(D_75))=D_75 | ~r2_hidden(D_75, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.43/2.30  tff(c_3834, plain, (![A_452, D_453]: (r2_hidden(k1_funct_1(A_452, D_453), k2_relat_1(A_452)) | ~r2_hidden(D_453, k1_relat_1(A_452)) | ~v1_funct_1(A_452) | ~v1_relat_1(A_452))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.43/2.30  tff(c_3853, plain, (![D_75]: (r2_hidden(D_75, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_75), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_75, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_3834])).
% 6.43/2.30  tff(c_3904, plain, (![D_462]: (r2_hidden(D_462, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_462), k1_relat_1('#skF_8')) | ~r2_hidden(D_462, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_74, c_3853])).
% 6.43/2.30  tff(c_3909, plain, (![D_75]: (r2_hidden(D_75, k2_relat_1('#skF_8')) | ~r1_tarski('#skF_6', k1_relat_1('#skF_8')) | ~r2_hidden(D_75, '#skF_7'))), inference(resolution, [status(thm)], [c_170, c_3904])).
% 6.43/2.30  tff(c_3985, plain, (~r1_tarski('#skF_6', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_3909])).
% 6.43/2.30  tff(c_4821, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4820, c_3985])).
% 6.43/2.30  tff(c_4826, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_4821])).
% 6.43/2.30  tff(c_4827, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_4819])).
% 6.43/2.30  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.43/2.30  tff(c_4858, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_4827, c_8])).
% 6.43/2.30  tff(c_4861, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3430, c_4858])).
% 6.43/2.30  tff(c_4899, plain, (![D_546]: (r2_hidden(D_546, k2_relat_1('#skF_8')) | ~r2_hidden(D_546, '#skF_7'))), inference(splitRight, [status(thm)], [c_3909])).
% 6.43/2.30  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.43/2.30  tff(c_5208, plain, (![A_561]: (r1_tarski(A_561, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_1'(A_561, k2_relat_1('#skF_8')), '#skF_7'))), inference(resolution, [status(thm)], [c_4899, c_4])).
% 6.43/2.30  tff(c_5218, plain, (r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6, c_5208])).
% 6.43/2.30  tff(c_5229, plain, (k2_relat_1('#skF_8')='#skF_7' | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_5218, c_10])).
% 6.43/2.30  tff(c_5240, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_3491, c_5229])).
% 6.43/2.30  tff(c_5249, plain, (~v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_26, c_5240])).
% 6.43/2.30  tff(c_5254, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_151, c_5249])).
% 6.43/2.30  tff(c_5255, plain, (k2_relat_1('#skF_8')='#skF_7'), inference(splitRight, [status(thm)], [c_3416])).
% 6.43/2.30  tff(c_5308, plain, (![A_562, B_563, C_564]: (k2_relset_1(A_562, B_563, C_564)=k2_relat_1(C_564) | ~m1_subset_1(C_564, k1_zfmisc_1(k2_zfmisc_1(A_562, B_563))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.43/2.30  tff(c_5315, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_70, c_5308])).
% 6.43/2.30  tff(c_5318, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_5255, c_5315])).
% 6.43/2.30  tff(c_5320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_5318])).
% 6.43/2.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.43/2.30  
% 6.43/2.30  Inference rules
% 6.43/2.30  ----------------------
% 6.43/2.30  #Ref     : 0
% 6.43/2.30  #Sup     : 1051
% 6.43/2.30  #Fact    : 0
% 6.43/2.30  #Define  : 0
% 6.43/2.30  #Split   : 47
% 6.43/2.30  #Chain   : 0
% 6.43/2.30  #Close   : 0
% 6.43/2.30  
% 6.43/2.30  Ordering : KBO
% 6.43/2.30  
% 6.43/2.30  Simplification rules
% 6.43/2.30  ----------------------
% 6.43/2.30  #Subsume      : 582
% 6.43/2.30  #Demod        : 962
% 6.43/2.30  #Tautology    : 345
% 6.43/2.30  #SimpNegUnit  : 114
% 6.43/2.30  #BackRed      : 175
% 6.43/2.30  
% 6.43/2.30  #Partial instantiations: 0
% 6.43/2.30  #Strategies tried      : 1
% 6.43/2.30  
% 6.43/2.30  Timing (in seconds)
% 6.43/2.30  ----------------------
% 6.43/2.30  Preprocessing        : 0.37
% 6.43/2.30  Parsing              : 0.19
% 6.43/2.30  CNF conversion       : 0.03
% 6.43/2.30  Main loop            : 1.13
% 6.43/2.30  Inferencing          : 0.39
% 6.43/2.30  Reduction            : 0.36
% 6.43/2.30  Demodulation         : 0.25
% 6.43/2.30  BG Simplification    : 0.04
% 6.43/2.30  Subsumption          : 0.24
% 6.43/2.30  Abstraction          : 0.05
% 6.43/2.30  MUC search           : 0.00
% 6.43/2.30  Cooper               : 0.00
% 6.43/2.30  Total                : 1.54
% 6.43/2.30  Index Insertion      : 0.00
% 6.43/2.30  Index Deletion       : 0.00
% 6.43/2.30  Index Matching       : 0.00
% 6.43/2.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
