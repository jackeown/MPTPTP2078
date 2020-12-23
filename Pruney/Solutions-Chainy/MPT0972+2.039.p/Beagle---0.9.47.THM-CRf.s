%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:40 EST 2020

% Result     : Theorem 8.90s
% Output     : CNFRefutation 9.21s
% Verified   : 
% Statistics : Number of formulae       :  107 (1050 expanded)
%              Number of leaves         :   36 ( 377 expanded)
%              Depth                    :   12
%              Number of atoms          :  184 (3445 expanded)
%              Number of equality atoms :   71 (1114 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_129,negated_conjecture,(
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

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_108,axiom,(
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
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_69,axiom,(
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

tff(f_47,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_74,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_60,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_58,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_409,plain,(
    ! [A_107,B_108,C_109] :
      ( k1_relset_1(A_107,B_108,C_109) = k1_relat_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_427,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_409])).

tff(c_1381,plain,(
    ! [B_201,A_202,C_203] :
      ( k1_xboole_0 = B_201
      | k1_relset_1(A_202,B_201,C_203) = A_202
      | ~ v1_funct_2(C_203,A_202,B_201)
      | ~ m1_subset_1(C_203,k1_zfmisc_1(k2_zfmisc_1(A_202,B_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1388,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_1381])).

tff(c_1401,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_427,c_1388])).

tff(c_1406,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1401])).

tff(c_250,plain,(
    ! [A_74,B_75,D_76] :
      ( r2_relset_1(A_74,B_75,D_76,D_76)
      | ~ m1_subset_1(D_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_263,plain,(
    r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_250])).

tff(c_64,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_122,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_139,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_122])).

tff(c_68,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_66,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_428,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_409])).

tff(c_1391,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_1381])).

tff(c_1404,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_428,c_1391])).

tff(c_1412,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1404])).

tff(c_138,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_122])).

tff(c_62,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1587,plain,(
    ! [A_225,B_226] :
      ( r2_hidden('#skF_4'(A_225,B_226),k1_relat_1(A_225))
      | B_226 = A_225
      | k1_relat_1(B_226) != k1_relat_1(A_225)
      | ~ v1_funct_1(B_226)
      | ~ v1_relat_1(B_226)
      | ~ v1_funct_1(A_225)
      | ~ v1_relat_1(A_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1598,plain,(
    ! [B_226] :
      ( r2_hidden('#skF_4'('#skF_8',B_226),'#skF_5')
      | B_226 = '#skF_8'
      | k1_relat_1(B_226) != k1_relat_1('#skF_8')
      | ~ v1_funct_1(B_226)
      | ~ v1_relat_1(B_226)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1406,c_1587])).

tff(c_1646,plain,(
    ! [B_235] :
      ( r2_hidden('#skF_4'('#skF_8',B_235),'#skF_5')
      | B_235 = '#skF_8'
      | k1_relat_1(B_235) != '#skF_5'
      | ~ v1_funct_1(B_235)
      | ~ v1_relat_1(B_235) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_62,c_1406,c_1598])).

tff(c_56,plain,(
    ! [E_39] :
      ( k1_funct_1('#skF_7',E_39) = k1_funct_1('#skF_8',E_39)
      | ~ r2_hidden(E_39,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_3770,plain,(
    ! [B_403] :
      ( k1_funct_1('#skF_7','#skF_4'('#skF_8',B_403)) = k1_funct_1('#skF_8','#skF_4'('#skF_8',B_403))
      | B_403 = '#skF_8'
      | k1_relat_1(B_403) != '#skF_5'
      | ~ v1_funct_1(B_403)
      | ~ v1_relat_1(B_403) ) ),
    inference(resolution,[status(thm)],[c_1646,c_56])).

tff(c_28,plain,(
    ! [B_18,A_14] :
      ( k1_funct_1(B_18,'#skF_4'(A_14,B_18)) != k1_funct_1(A_14,'#skF_4'(A_14,B_18))
      | B_18 = A_14
      | k1_relat_1(B_18) != k1_relat_1(A_14)
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3777,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | '#skF_7' = '#skF_8'
    | k1_relat_1('#skF_7') != '#skF_5'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_3770,c_28])).

tff(c_3784,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_68,c_1412,c_138,c_62,c_1406,c_1412,c_3777])).

tff(c_54,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_3832,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3784,c_54])).

tff(c_3843,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_3832])).

tff(c_3844,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1404])).

tff(c_20,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3890,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3844,c_3844,c_20])).

tff(c_98,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,B_48)
      | ~ m1_subset_1(A_47,k1_zfmisc_1(B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_109,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_58,c_98])).

tff(c_3990,plain,(
    r1_tarski('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3890,c_109])).

tff(c_16,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_265,plain,(
    ! [A_77,B_78] :
      ( r2_hidden('#skF_2'(A_77,B_78),B_78)
      | r2_hidden('#skF_3'(A_77,B_78),A_77)
      | B_78 = A_77 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_32,plain,(
    ! [B_21,A_20] :
      ( ~ r1_tarski(B_21,A_20)
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_613,plain,(
    ! [B_136,A_137] :
      ( ~ r1_tarski(B_136,'#skF_2'(A_137,B_136))
      | r2_hidden('#skF_3'(A_137,B_136),A_137)
      | B_136 = A_137 ) ),
    inference(resolution,[status(thm)],[c_265,c_32])).

tff(c_618,plain,(
    ! [A_138] :
      ( r2_hidden('#skF_3'(A_138,k1_xboole_0),A_138)
      | k1_xboole_0 = A_138 ) ),
    inference(resolution,[status(thm)],[c_16,c_613])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_644,plain,(
    ! [A_140,B_141] :
      ( r2_hidden('#skF_3'(A_140,k1_xboole_0),B_141)
      | ~ r1_tarski(A_140,B_141)
      | k1_xboole_0 = A_140 ) ),
    inference(resolution,[status(thm)],[c_618,c_2])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | ~ r2_hidden('#skF_3'(A_6,B_7),B_7)
      | B_7 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_672,plain,(
    ! [A_144] :
      ( r2_hidden('#skF_2'(A_144,k1_xboole_0),k1_xboole_0)
      | ~ r1_tarski(A_144,k1_xboole_0)
      | k1_xboole_0 = A_144 ) ),
    inference(resolution,[status(thm)],[c_644,c_10])).

tff(c_680,plain,(
    ! [A_144] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_2'(A_144,k1_xboole_0))
      | ~ r1_tarski(A_144,k1_xboole_0)
      | k1_xboole_0 = A_144 ) ),
    inference(resolution,[status(thm)],[c_672,c_32])).

tff(c_690,plain,(
    ! [A_144] :
      ( ~ r1_tarski(A_144,k1_xboole_0)
      | k1_xboole_0 = A_144 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_680])).

tff(c_4126,plain,(
    ! [A_419] :
      ( ~ r1_tarski(A_419,'#skF_6')
      | A_419 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3844,c_3844,c_690])).

tff(c_4141,plain,(
    '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_3990,c_4126])).

tff(c_110,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_64,c_98])).

tff(c_3989,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3890,c_110])).

tff(c_4142,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3989,c_4126])).

tff(c_4200,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4141,c_4142])).

tff(c_3845,plain,(
    k1_relat_1('#skF_7') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1404])).

tff(c_4201,plain,(
    k1_relat_1('#skF_8') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4200,c_3845])).

tff(c_4211,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1406,c_4201])).

tff(c_4212,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1401])).

tff(c_4258,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4212,c_4212,c_20])).

tff(c_4355,plain,(
    r1_tarski('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4258,c_109])).

tff(c_4508,plain,(
    ! [A_437] :
      ( ~ r1_tarski(A_437,'#skF_6')
      | A_437 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4212,c_4212,c_690])).

tff(c_4523,plain,(
    '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_4355,c_4508])).

tff(c_4354,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4258,c_110])).

tff(c_4524,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_4354,c_4508])).

tff(c_4559,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4523,c_4524])).

tff(c_264,plain,(
    r2_relset_1('#skF_5','#skF_6','#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_250])).

tff(c_4548,plain,(
    r2_relset_1('#skF_5','#skF_8','#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4523,c_264])).

tff(c_4716,plain,(
    r2_relset_1('#skF_5','#skF_8','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4559,c_4559,c_4548])).

tff(c_4550,plain,(
    ~ r2_relset_1('#skF_5','#skF_8','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4523,c_54])).

tff(c_4725,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4716,c_4559,c_4550])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.31  % Computer   : n001.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % DateTime   : Tue Dec  1 10:24:59 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.90/3.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.90/3.43  
% 8.90/3.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.90/3.43  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 8.90/3.43  
% 8.90/3.43  %Foreground sorts:
% 8.90/3.43  
% 8.90/3.43  
% 8.90/3.43  %Background operators:
% 8.90/3.43  
% 8.90/3.43  
% 8.90/3.43  %Foreground operators:
% 8.90/3.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.90/3.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.90/3.43  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 8.90/3.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.90/3.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.90/3.43  tff('#skF_7', type, '#skF_7': $i).
% 8.90/3.43  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.90/3.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.90/3.43  tff('#skF_5', type, '#skF_5': $i).
% 8.90/3.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.90/3.43  tff('#skF_6', type, '#skF_6': $i).
% 8.90/3.43  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.90/3.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.90/3.43  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.90/3.43  tff('#skF_8', type, '#skF_8': $i).
% 8.90/3.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.90/3.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.90/3.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.90/3.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.90/3.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.90/3.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.90/3.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.90/3.43  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.90/3.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.90/3.43  
% 9.21/3.45  tff(f_129, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_2)).
% 9.21/3.45  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.21/3.45  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 9.21/3.45  tff(f_90, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.21/3.45  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.21/3.45  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 9.21/3.45  tff(f_47, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.21/3.45  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.21/3.46  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.21/3.46  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 9.21/3.46  tff(f_74, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 9.21/3.46  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.21/3.46  tff(c_60, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.21/3.46  tff(c_58, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.21/3.46  tff(c_409, plain, (![A_107, B_108, C_109]: (k1_relset_1(A_107, B_108, C_109)=k1_relat_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.21/3.46  tff(c_427, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_58, c_409])).
% 9.21/3.46  tff(c_1381, plain, (![B_201, A_202, C_203]: (k1_xboole_0=B_201 | k1_relset_1(A_202, B_201, C_203)=A_202 | ~v1_funct_2(C_203, A_202, B_201) | ~m1_subset_1(C_203, k1_zfmisc_1(k2_zfmisc_1(A_202, B_201))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.21/3.46  tff(c_1388, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_58, c_1381])).
% 9.21/3.46  tff(c_1401, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_427, c_1388])).
% 9.21/3.46  tff(c_1406, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_1401])).
% 9.21/3.46  tff(c_250, plain, (![A_74, B_75, D_76]: (r2_relset_1(A_74, B_75, D_76, D_76) | ~m1_subset_1(D_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.21/3.46  tff(c_263, plain, (r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_58, c_250])).
% 9.21/3.46  tff(c_64, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.21/3.46  tff(c_122, plain, (![C_51, A_52, B_53]: (v1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.21/3.46  tff(c_139, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_64, c_122])).
% 9.21/3.46  tff(c_68, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.21/3.46  tff(c_66, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.21/3.46  tff(c_428, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_64, c_409])).
% 9.21/3.46  tff(c_1391, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_5' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_64, c_1381])).
% 9.21/3.46  tff(c_1404, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_428, c_1391])).
% 9.21/3.46  tff(c_1412, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitLeft, [status(thm)], [c_1404])).
% 9.21/3.46  tff(c_138, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_58, c_122])).
% 9.21/3.46  tff(c_62, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.21/3.46  tff(c_1587, plain, (![A_225, B_226]: (r2_hidden('#skF_4'(A_225, B_226), k1_relat_1(A_225)) | B_226=A_225 | k1_relat_1(B_226)!=k1_relat_1(A_225) | ~v1_funct_1(B_226) | ~v1_relat_1(B_226) | ~v1_funct_1(A_225) | ~v1_relat_1(A_225))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.21/3.46  tff(c_1598, plain, (![B_226]: (r2_hidden('#skF_4'('#skF_8', B_226), '#skF_5') | B_226='#skF_8' | k1_relat_1(B_226)!=k1_relat_1('#skF_8') | ~v1_funct_1(B_226) | ~v1_relat_1(B_226) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1406, c_1587])).
% 9.21/3.46  tff(c_1646, plain, (![B_235]: (r2_hidden('#skF_4'('#skF_8', B_235), '#skF_5') | B_235='#skF_8' | k1_relat_1(B_235)!='#skF_5' | ~v1_funct_1(B_235) | ~v1_relat_1(B_235))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_62, c_1406, c_1598])).
% 9.21/3.46  tff(c_56, plain, (![E_39]: (k1_funct_1('#skF_7', E_39)=k1_funct_1('#skF_8', E_39) | ~r2_hidden(E_39, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.21/3.46  tff(c_3770, plain, (![B_403]: (k1_funct_1('#skF_7', '#skF_4'('#skF_8', B_403))=k1_funct_1('#skF_8', '#skF_4'('#skF_8', B_403)) | B_403='#skF_8' | k1_relat_1(B_403)!='#skF_5' | ~v1_funct_1(B_403) | ~v1_relat_1(B_403))), inference(resolution, [status(thm)], [c_1646, c_56])).
% 9.21/3.46  tff(c_28, plain, (![B_18, A_14]: (k1_funct_1(B_18, '#skF_4'(A_14, B_18))!=k1_funct_1(A_14, '#skF_4'(A_14, B_18)) | B_18=A_14 | k1_relat_1(B_18)!=k1_relat_1(A_14) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.21/3.46  tff(c_3777, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | '#skF_7'='#skF_8' | k1_relat_1('#skF_7')!='#skF_5' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_3770, c_28])).
% 9.21/3.46  tff(c_3784, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_139, c_68, c_1412, c_138, c_62, c_1406, c_1412, c_3777])).
% 9.21/3.46  tff(c_54, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.21/3.46  tff(c_3832, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3784, c_54])).
% 9.21/3.46  tff(c_3843, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_263, c_3832])).
% 9.21/3.46  tff(c_3844, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_1404])).
% 9.21/3.46  tff(c_20, plain, (![A_10]: (k2_zfmisc_1(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.21/3.46  tff(c_3890, plain, (![A_10]: (k2_zfmisc_1(A_10, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3844, c_3844, c_20])).
% 9.21/3.46  tff(c_98, plain, (![A_47, B_48]: (r1_tarski(A_47, B_48) | ~m1_subset_1(A_47, k1_zfmisc_1(B_48)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.21/3.46  tff(c_109, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_58, c_98])).
% 9.21/3.46  tff(c_3990, plain, (r1_tarski('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3890, c_109])).
% 9.21/3.46  tff(c_16, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.21/3.46  tff(c_265, plain, (![A_77, B_78]: (r2_hidden('#skF_2'(A_77, B_78), B_78) | r2_hidden('#skF_3'(A_77, B_78), A_77) | B_78=A_77)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.21/3.46  tff(c_32, plain, (![B_21, A_20]: (~r1_tarski(B_21, A_20) | ~r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.21/3.46  tff(c_613, plain, (![B_136, A_137]: (~r1_tarski(B_136, '#skF_2'(A_137, B_136)) | r2_hidden('#skF_3'(A_137, B_136), A_137) | B_136=A_137)), inference(resolution, [status(thm)], [c_265, c_32])).
% 9.21/3.46  tff(c_618, plain, (![A_138]: (r2_hidden('#skF_3'(A_138, k1_xboole_0), A_138) | k1_xboole_0=A_138)), inference(resolution, [status(thm)], [c_16, c_613])).
% 9.21/3.46  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.21/3.46  tff(c_644, plain, (![A_140, B_141]: (r2_hidden('#skF_3'(A_140, k1_xboole_0), B_141) | ~r1_tarski(A_140, B_141) | k1_xboole_0=A_140)), inference(resolution, [status(thm)], [c_618, c_2])).
% 9.21/3.46  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | ~r2_hidden('#skF_3'(A_6, B_7), B_7) | B_7=A_6)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.21/3.46  tff(c_672, plain, (![A_144]: (r2_hidden('#skF_2'(A_144, k1_xboole_0), k1_xboole_0) | ~r1_tarski(A_144, k1_xboole_0) | k1_xboole_0=A_144)), inference(resolution, [status(thm)], [c_644, c_10])).
% 9.21/3.46  tff(c_680, plain, (![A_144]: (~r1_tarski(k1_xboole_0, '#skF_2'(A_144, k1_xboole_0)) | ~r1_tarski(A_144, k1_xboole_0) | k1_xboole_0=A_144)), inference(resolution, [status(thm)], [c_672, c_32])).
% 9.21/3.46  tff(c_690, plain, (![A_144]: (~r1_tarski(A_144, k1_xboole_0) | k1_xboole_0=A_144)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_680])).
% 9.21/3.46  tff(c_4126, plain, (![A_419]: (~r1_tarski(A_419, '#skF_6') | A_419='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3844, c_3844, c_690])).
% 9.21/3.46  tff(c_4141, plain, ('#skF_6'='#skF_8'), inference(resolution, [status(thm)], [c_3990, c_4126])).
% 9.21/3.46  tff(c_110, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_64, c_98])).
% 9.21/3.46  tff(c_3989, plain, (r1_tarski('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3890, c_110])).
% 9.21/3.46  tff(c_4142, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_3989, c_4126])).
% 9.21/3.46  tff(c_4200, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4141, c_4142])).
% 9.21/3.46  tff(c_3845, plain, (k1_relat_1('#skF_7')!='#skF_5'), inference(splitRight, [status(thm)], [c_1404])).
% 9.21/3.46  tff(c_4201, plain, (k1_relat_1('#skF_8')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4200, c_3845])).
% 9.21/3.46  tff(c_4211, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1406, c_4201])).
% 9.21/3.46  tff(c_4212, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_1401])).
% 9.21/3.46  tff(c_4258, plain, (![A_10]: (k2_zfmisc_1(A_10, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4212, c_4212, c_20])).
% 9.21/3.46  tff(c_4355, plain, (r1_tarski('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4258, c_109])).
% 9.21/3.46  tff(c_4508, plain, (![A_437]: (~r1_tarski(A_437, '#skF_6') | A_437='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4212, c_4212, c_690])).
% 9.21/3.46  tff(c_4523, plain, ('#skF_6'='#skF_8'), inference(resolution, [status(thm)], [c_4355, c_4508])).
% 9.21/3.46  tff(c_4354, plain, (r1_tarski('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4258, c_110])).
% 9.21/3.46  tff(c_4524, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_4354, c_4508])).
% 9.21/3.46  tff(c_4559, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4523, c_4524])).
% 9.21/3.46  tff(c_264, plain, (r2_relset_1('#skF_5', '#skF_6', '#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_64, c_250])).
% 9.21/3.46  tff(c_4548, plain, (r2_relset_1('#skF_5', '#skF_8', '#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_4523, c_264])).
% 9.21/3.46  tff(c_4716, plain, (r2_relset_1('#skF_5', '#skF_8', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4559, c_4559, c_4548])).
% 9.21/3.46  tff(c_4550, plain, (~r2_relset_1('#skF_5', '#skF_8', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4523, c_54])).
% 9.21/3.46  tff(c_4725, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4716, c_4559, c_4550])).
% 9.21/3.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.21/3.46  
% 9.21/3.46  Inference rules
% 9.21/3.46  ----------------------
% 9.21/3.46  #Ref     : 3
% 9.21/3.46  #Sup     : 921
% 9.21/3.46  #Fact    : 0
% 9.21/3.46  #Define  : 0
% 9.21/3.46  #Split   : 9
% 9.21/3.46  #Chain   : 0
% 9.21/3.46  #Close   : 0
% 9.21/3.46  
% 9.21/3.46  Ordering : KBO
% 9.21/3.46  
% 9.21/3.46  Simplification rules
% 9.21/3.46  ----------------------
% 9.21/3.46  #Subsume      : 164
% 9.21/3.46  #Demod        : 1121
% 9.21/3.46  #Tautology    : 479
% 9.21/3.46  #SimpNegUnit  : 48
% 9.21/3.46  #BackRed      : 354
% 9.21/3.46  
% 9.21/3.46  #Partial instantiations: 0
% 9.21/3.46  #Strategies tried      : 1
% 9.21/3.46  
% 9.21/3.46  Timing (in seconds)
% 9.21/3.46  ----------------------
% 9.21/3.46  Preprocessing        : 0.58
% 9.21/3.46  Parsing              : 0.29
% 9.21/3.46  CNF conversion       : 0.05
% 9.21/3.46  Main loop            : 1.92
% 9.21/3.46  Inferencing          : 0.65
% 9.21/3.46  Reduction            : 0.61
% 9.21/3.46  Demodulation         : 0.41
% 9.21/3.46  BG Simplification    : 0.07
% 9.21/3.46  Subsumption          : 0.42
% 9.21/3.46  Abstraction          : 0.08
% 9.21/3.46  MUC search           : 0.00
% 9.21/3.46  Cooper               : 0.00
% 9.21/3.46  Total                : 2.56
% 9.21/3.46  Index Insertion      : 0.00
% 9.21/3.46  Index Deletion       : 0.00
% 9.21/3.46  Index Matching       : 0.00
% 9.21/3.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
