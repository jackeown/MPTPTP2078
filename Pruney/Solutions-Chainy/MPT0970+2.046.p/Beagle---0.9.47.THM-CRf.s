%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:25 EST 2020

% Result     : Theorem 5.33s
% Output     : CNFRefutation 5.33s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 177 expanded)
%              Number of leaves         :   41 (  79 expanded)
%              Depth                    :   12
%              Number of atoms          :  146 ( 427 expanded)
%              Number of equality atoms :   34 ( 102 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_65,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

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

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(c_28,plain,(
    ! [A_19,B_20] : v1_relat_1(k2_zfmisc_1(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_70,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_145,plain,(
    ! [B_97,A_98] :
      ( v1_relat_1(B_97)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_98))
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_151,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_70,c_145])).

tff(c_158,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_151])).

tff(c_207,plain,(
    ! [C_107,B_108,A_109] :
      ( v5_relat_1(C_107,B_108)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_109,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_220,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_207])).

tff(c_26,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k2_relat_1(B_18),A_17)
      | ~ v5_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_366,plain,(
    ! [A_134,B_135,C_136] :
      ( k2_relset_1(A_134,B_135,C_136) = k2_relat_1(C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_379,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_366])).

tff(c_68,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_395,plain,(
    k2_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_68])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_72,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1923,plain,(
    ! [A_271,B_272,C_273] :
      ( k1_relset_1(A_271,B_272,C_273) = k1_relat_1(C_273)
      | ~ m1_subset_1(C_273,k1_zfmisc_1(k2_zfmisc_1(A_271,B_272))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1941,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_1923])).

tff(c_3094,plain,(
    ! [B_371,A_372,C_373] :
      ( k1_xboole_0 = B_371
      | k1_relset_1(A_372,B_371,C_373) = A_372
      | ~ v1_funct_2(C_373,A_372,B_371)
      | ~ m1_subset_1(C_373,k1_zfmisc_1(k2_zfmisc_1(A_372,B_371))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_3113,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_3094])).

tff(c_3124,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1941,c_3113])).

tff(c_3127,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_3124])).

tff(c_78,plain,(
    ! [D_76] :
      ( r2_hidden('#skF_9'(D_76),'#skF_6')
      | ~ r2_hidden(D_76,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_349,plain,(
    ! [C_128,B_129,A_130] :
      ( r2_hidden(C_128,B_129)
      | ~ r2_hidden(C_128,A_130)
      | ~ r1_tarski(A_130,B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_355,plain,(
    ! [D_76,B_129] :
      ( r2_hidden('#skF_9'(D_76),B_129)
      | ~ r1_tarski('#skF_6',B_129)
      | ~ r2_hidden(D_76,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_78,c_349])).

tff(c_74,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_76,plain,(
    ! [D_76] :
      ( k1_funct_1('#skF_8','#skF_9'(D_76)) = D_76
      | ~ r2_hidden(D_76,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2227,plain,(
    ! [A_312,D_313] :
      ( r2_hidden(k1_funct_1(A_312,D_313),k2_relat_1(A_312))
      | ~ r2_hidden(D_313,k1_relat_1(A_312))
      | ~ v1_funct_1(A_312)
      | ~ v1_relat_1(A_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2240,plain,(
    ! [D_76] :
      ( r2_hidden(D_76,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_76),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_76,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_2227])).

tff(c_2306,plain,(
    ! [D_322] :
      ( r2_hidden(D_322,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_322),k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_322,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_74,c_2240])).

tff(c_2311,plain,(
    ! [D_76] :
      ( r2_hidden(D_76,k2_relat_1('#skF_8'))
      | ~ r1_tarski('#skF_6',k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_76,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_355,c_2306])).

tff(c_2312,plain,(
    ~ r1_tarski('#skF_6',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_2311])).

tff(c_3128,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3127,c_2312])).

tff(c_3133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3128])).

tff(c_3134,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_3124])).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_88,plain,(
    ! [A_86,B_87] :
      ( r1_tarski(A_86,B_87)
      | ~ m1_subset_1(A_86,k1_zfmisc_1(B_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_100,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(resolution,[status(thm)],[c_14,c_88])).

tff(c_3186,plain,(
    ! [A_377] : r1_tarski('#skF_7',A_377) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3134,c_100])).

tff(c_188,plain,(
    ! [B_103,A_104] :
      ( r1_tarski(k2_relat_1(B_103),A_104)
      | ~ v5_relat_1(B_103,A_104)
      | ~ v1_relat_1(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_204,plain,(
    ! [B_103,A_104] :
      ( k2_relat_1(B_103) = A_104
      | ~ r1_tarski(A_104,k2_relat_1(B_103))
      | ~ v5_relat_1(B_103,A_104)
      | ~ v1_relat_1(B_103) ) ),
    inference(resolution,[status(thm)],[c_188,c_8])).

tff(c_3737,plain,(
    ! [B_424] :
      ( k2_relat_1(B_424) = '#skF_7'
      | ~ v5_relat_1(B_424,'#skF_7')
      | ~ v1_relat_1(B_424) ) ),
    inference(resolution,[status(thm)],[c_3186,c_204])).

tff(c_3756,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_220,c_3737])).

tff(c_3769,plain,(
    k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_3756])).

tff(c_3771,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_395,c_3769])).

tff(c_3806,plain,(
    ! [D_428] :
      ( r2_hidden(D_428,k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_428,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_2311])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3933,plain,(
    ! [A_444] :
      ( r1_tarski(A_444,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_444,k2_relat_1('#skF_8')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_3806,c_4])).

tff(c_3943,plain,(
    r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6,c_3933])).

tff(c_3950,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_3943,c_8])).

tff(c_3957,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_395,c_3950])).

tff(c_3960,plain,
    ( ~ v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_26,c_3957])).

tff(c_3964,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_220,c_3960])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:06:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.33/2.00  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.33/2.01  
% 5.33/2.01  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.33/2.01  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 5.33/2.01  
% 5.33/2.01  %Foreground sorts:
% 5.33/2.01  
% 5.33/2.01  
% 5.33/2.01  %Background operators:
% 5.33/2.01  
% 5.33/2.01  
% 5.33/2.01  %Foreground operators:
% 5.33/2.01  tff('#skF_9', type, '#skF_9': $i > $i).
% 5.33/2.01  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.33/2.01  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.33/2.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.33/2.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.33/2.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.33/2.01  tff('#skF_7', type, '#skF_7': $i).
% 5.33/2.01  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.33/2.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.33/2.01  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.33/2.01  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.33/2.01  tff('#skF_6', type, '#skF_6': $i).
% 5.33/2.01  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.33/2.01  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.33/2.01  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.33/2.01  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.33/2.01  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.33/2.01  tff('#skF_8', type, '#skF_8': $i).
% 5.33/2.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.33/2.01  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.33/2.01  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.33/2.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.33/2.01  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.33/2.01  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.33/2.01  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.33/2.01  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.33/2.01  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.33/2.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.33/2.01  
% 5.33/2.02  tff(f_65, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.33/2.02  tff(f_131, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 5.33/2.02  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.33/2.02  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.33/2.02  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 5.33/2.02  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.33/2.02  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.33/2.02  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.33/2.02  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.33/2.02  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.33/2.02  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 5.33/2.02  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 5.33/2.02  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.33/2.02  tff(c_28, plain, (![A_19, B_20]: (v1_relat_1(k2_zfmisc_1(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.33/2.02  tff(c_70, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.33/2.02  tff(c_145, plain, (![B_97, A_98]: (v1_relat_1(B_97) | ~m1_subset_1(B_97, k1_zfmisc_1(A_98)) | ~v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.33/2.02  tff(c_151, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_70, c_145])).
% 5.33/2.02  tff(c_158, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_151])).
% 5.33/2.02  tff(c_207, plain, (![C_107, B_108, A_109]: (v5_relat_1(C_107, B_108) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_109, B_108))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.33/2.02  tff(c_220, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_70, c_207])).
% 5.33/2.02  tff(c_26, plain, (![B_18, A_17]: (r1_tarski(k2_relat_1(B_18), A_17) | ~v5_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.33/2.02  tff(c_366, plain, (![A_134, B_135, C_136]: (k2_relset_1(A_134, B_135, C_136)=k2_relat_1(C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.33/2.02  tff(c_379, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_70, c_366])).
% 5.33/2.02  tff(c_68, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.33/2.02  tff(c_395, plain, (k2_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_379, c_68])).
% 5.33/2.02  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.33/2.02  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.33/2.02  tff(c_72, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.33/2.02  tff(c_1923, plain, (![A_271, B_272, C_273]: (k1_relset_1(A_271, B_272, C_273)=k1_relat_1(C_273) | ~m1_subset_1(C_273, k1_zfmisc_1(k2_zfmisc_1(A_271, B_272))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.33/2.02  tff(c_1941, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_70, c_1923])).
% 5.33/2.02  tff(c_3094, plain, (![B_371, A_372, C_373]: (k1_xboole_0=B_371 | k1_relset_1(A_372, B_371, C_373)=A_372 | ~v1_funct_2(C_373, A_372, B_371) | ~m1_subset_1(C_373, k1_zfmisc_1(k2_zfmisc_1(A_372, B_371))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.33/2.02  tff(c_3113, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_70, c_3094])).
% 5.33/2.02  tff(c_3124, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1941, c_3113])).
% 5.33/2.02  tff(c_3127, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_3124])).
% 5.33/2.02  tff(c_78, plain, (![D_76]: (r2_hidden('#skF_9'(D_76), '#skF_6') | ~r2_hidden(D_76, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.33/2.02  tff(c_349, plain, (![C_128, B_129, A_130]: (r2_hidden(C_128, B_129) | ~r2_hidden(C_128, A_130) | ~r1_tarski(A_130, B_129))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.33/2.02  tff(c_355, plain, (![D_76, B_129]: (r2_hidden('#skF_9'(D_76), B_129) | ~r1_tarski('#skF_6', B_129) | ~r2_hidden(D_76, '#skF_7'))), inference(resolution, [status(thm)], [c_78, c_349])).
% 5.33/2.02  tff(c_74, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.33/2.02  tff(c_76, plain, (![D_76]: (k1_funct_1('#skF_8', '#skF_9'(D_76))=D_76 | ~r2_hidden(D_76, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.33/2.02  tff(c_2227, plain, (![A_312, D_313]: (r2_hidden(k1_funct_1(A_312, D_313), k2_relat_1(A_312)) | ~r2_hidden(D_313, k1_relat_1(A_312)) | ~v1_funct_1(A_312) | ~v1_relat_1(A_312))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.33/2.02  tff(c_2240, plain, (![D_76]: (r2_hidden(D_76, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_76), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_76, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_2227])).
% 5.33/2.02  tff(c_2306, plain, (![D_322]: (r2_hidden(D_322, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_322), k1_relat_1('#skF_8')) | ~r2_hidden(D_322, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_74, c_2240])).
% 5.33/2.02  tff(c_2311, plain, (![D_76]: (r2_hidden(D_76, k2_relat_1('#skF_8')) | ~r1_tarski('#skF_6', k1_relat_1('#skF_8')) | ~r2_hidden(D_76, '#skF_7'))), inference(resolution, [status(thm)], [c_355, c_2306])).
% 5.33/2.02  tff(c_2312, plain, (~r1_tarski('#skF_6', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_2311])).
% 5.33/2.02  tff(c_3128, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3127, c_2312])).
% 5.33/2.02  tff(c_3133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_3128])).
% 5.33/2.02  tff(c_3134, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_3124])).
% 5.33/2.02  tff(c_14, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.33/2.02  tff(c_88, plain, (![A_86, B_87]: (r1_tarski(A_86, B_87) | ~m1_subset_1(A_86, k1_zfmisc_1(B_87)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.33/2.02  tff(c_100, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(resolution, [status(thm)], [c_14, c_88])).
% 5.33/2.02  tff(c_3186, plain, (![A_377]: (r1_tarski('#skF_7', A_377))), inference(demodulation, [status(thm), theory('equality')], [c_3134, c_100])).
% 5.33/2.02  tff(c_188, plain, (![B_103, A_104]: (r1_tarski(k2_relat_1(B_103), A_104) | ~v5_relat_1(B_103, A_104) | ~v1_relat_1(B_103))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.33/2.02  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.33/2.02  tff(c_204, plain, (![B_103, A_104]: (k2_relat_1(B_103)=A_104 | ~r1_tarski(A_104, k2_relat_1(B_103)) | ~v5_relat_1(B_103, A_104) | ~v1_relat_1(B_103))), inference(resolution, [status(thm)], [c_188, c_8])).
% 5.33/2.02  tff(c_3737, plain, (![B_424]: (k2_relat_1(B_424)='#skF_7' | ~v5_relat_1(B_424, '#skF_7') | ~v1_relat_1(B_424))), inference(resolution, [status(thm)], [c_3186, c_204])).
% 5.33/2.02  tff(c_3756, plain, (k2_relat_1('#skF_8')='#skF_7' | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_220, c_3737])).
% 5.33/2.02  tff(c_3769, plain, (k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_158, c_3756])).
% 5.33/2.02  tff(c_3771, plain, $false, inference(negUnitSimplification, [status(thm)], [c_395, c_3769])).
% 5.33/2.02  tff(c_3806, plain, (![D_428]: (r2_hidden(D_428, k2_relat_1('#skF_8')) | ~r2_hidden(D_428, '#skF_7'))), inference(splitRight, [status(thm)], [c_2311])).
% 5.33/2.02  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.33/2.02  tff(c_3933, plain, (![A_444]: (r1_tarski(A_444, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_1'(A_444, k2_relat_1('#skF_8')), '#skF_7'))), inference(resolution, [status(thm)], [c_3806, c_4])).
% 5.33/2.02  tff(c_3943, plain, (r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6, c_3933])).
% 5.33/2.02  tff(c_3950, plain, (k2_relat_1('#skF_8')='#skF_7' | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_3943, c_8])).
% 5.33/2.02  tff(c_3957, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_395, c_3950])).
% 5.33/2.02  tff(c_3960, plain, (~v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_26, c_3957])).
% 5.33/2.02  tff(c_3964, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_158, c_220, c_3960])).
% 5.33/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.33/2.02  
% 5.33/2.02  Inference rules
% 5.33/2.02  ----------------------
% 5.33/2.02  #Ref     : 0
% 5.33/2.02  #Sup     : 791
% 5.33/2.02  #Fact    : 0
% 5.33/2.02  #Define  : 0
% 5.33/2.02  #Split   : 38
% 5.33/2.02  #Chain   : 0
% 5.33/2.02  #Close   : 0
% 5.33/2.02  
% 5.33/2.02  Ordering : KBO
% 5.33/2.02  
% 5.33/2.02  Simplification rules
% 5.33/2.02  ----------------------
% 5.33/2.02  #Subsume      : 154
% 5.33/2.02  #Demod        : 574
% 5.33/2.02  #Tautology    : 233
% 5.33/2.02  #SimpNegUnit  : 31
% 5.33/2.02  #BackRed      : 115
% 5.33/2.02  
% 5.33/2.02  #Partial instantiations: 0
% 5.33/2.02  #Strategies tried      : 1
% 5.33/2.02  
% 5.33/2.02  Timing (in seconds)
% 5.33/2.02  ----------------------
% 5.33/2.03  Preprocessing        : 0.36
% 5.33/2.03  Parsing              : 0.19
% 5.33/2.03  CNF conversion       : 0.03
% 5.33/2.03  Main loop            : 0.87
% 5.33/2.03  Inferencing          : 0.28
% 5.33/2.03  Reduction            : 0.29
% 5.33/2.03  Demodulation         : 0.20
% 5.33/2.03  BG Simplification    : 0.04
% 5.33/2.03  Subsumption          : 0.18
% 5.33/2.03  Abstraction          : 0.04
% 5.33/2.03  MUC search           : 0.00
% 5.33/2.03  Cooper               : 0.00
% 5.33/2.03  Total                : 1.26
% 5.33/2.03  Index Insertion      : 0.00
% 5.33/2.03  Index Deletion       : 0.00
% 5.33/2.03  Index Matching       : 0.00
% 5.33/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
