%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:25 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 174 expanded)
%              Number of leaves         :   40 (  78 expanded)
%              Depth                    :   11
%              Number of atoms          :  137 ( 425 expanded)
%              Number of equality atoms :   35 ( 104 expanded)
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

tff(f_121,negated_conjecture,(
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

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_55,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

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

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_102,axiom,(
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

tff(f_70,axiom,(
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
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(c_64,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_197,plain,(
    ! [A_115,B_116,C_117] :
      ( k2_relset_1(A_115,B_116,C_117) = k2_relat_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_201,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_64,c_197])).

tff(c_62,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_202,plain,(
    k2_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_62])).

tff(c_22,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_95,plain,(
    ! [B_83,A_84] :
      ( v1_relat_1(B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_84))
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_98,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_64,c_95])).

tff(c_101,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_98])).

tff(c_158,plain,(
    ! [C_100,B_101,A_102] :
      ( v5_relat_1(C_100,B_101)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_102,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_162,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_158])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_66,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_177,plain,(
    ! [A_109,B_110,C_111] :
      ( k1_relset_1(A_109,B_110,C_111) = k1_relat_1(C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_181,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_64,c_177])).

tff(c_360,plain,(
    ! [B_160,A_161,C_162] :
      ( k1_xboole_0 = B_160
      | k1_relset_1(A_161,B_160,C_162) = A_161
      | ~ v1_funct_2(C_162,A_161,B_160)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_161,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_363,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_360])).

tff(c_366,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_181,c_363])).

tff(c_367,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_366])).

tff(c_72,plain,(
    ! [D_71] :
      ( r2_hidden('#skF_9'(D_71),'#skF_6')
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_140,plain,(
    ! [C_94,B_95,A_96] :
      ( r2_hidden(C_94,B_95)
      | ~ r2_hidden(C_94,A_96)
      | ~ r1_tarski(A_96,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_146,plain,(
    ! [D_71,B_95] :
      ( r2_hidden('#skF_9'(D_71),B_95)
      | ~ r1_tarski('#skF_6',B_95)
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_72,c_140])).

tff(c_68,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_70,plain,(
    ! [D_71] :
      ( k1_funct_1('#skF_8','#skF_9'(D_71)) = D_71
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_207,plain,(
    ! [A_118,D_119] :
      ( r2_hidden(k1_funct_1(A_118,D_119),k2_relat_1(A_118))
      | ~ r2_hidden(D_119,k1_relat_1(A_118))
      | ~ v1_funct_1(A_118)
      | ~ v1_relat_1(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_212,plain,(
    ! [D_71] :
      ( r2_hidden(D_71,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_71),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_207])).

tff(c_233,plain,(
    ! [D_122] :
      ( r2_hidden(D_122,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_122),k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_122,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_68,c_212])).

tff(c_238,plain,(
    ! [D_71] :
      ( r2_hidden(D_71,k2_relat_1('#skF_8'))
      | ~ r1_tarski('#skF_6',k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_146,c_233])).

tff(c_239,plain,(
    ~ r1_tarski('#skF_6',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_238])).

tff(c_368,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_239])).

tff(c_373,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_368])).

tff(c_374,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_366])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_396,plain,(
    ! [A_163] : r1_tarski('#skF_7',A_163) ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_14])).

tff(c_130,plain,(
    ! [B_91,A_92] :
      ( r1_tarski(k2_relat_1(B_91),A_92)
      | ~ v5_relat_1(B_91,A_92)
      | ~ v1_relat_1(B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_138,plain,(
    ! [B_91,A_92] :
      ( k2_relat_1(B_91) = A_92
      | ~ r1_tarski(A_92,k2_relat_1(B_91))
      | ~ v5_relat_1(B_91,A_92)
      | ~ v1_relat_1(B_91) ) ),
    inference(resolution,[status(thm)],[c_130,c_8])).

tff(c_451,plain,(
    ! [B_170] :
      ( k2_relat_1(B_170) = '#skF_7'
      | ~ v5_relat_1(B_170,'#skF_7')
      | ~ v1_relat_1(B_170) ) ),
    inference(resolution,[status(thm)],[c_396,c_138])).

tff(c_454,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_162,c_451])).

tff(c_457,plain,(
    k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_454])).

tff(c_459,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_202,c_457])).

tff(c_470,plain,(
    ! [D_171] :
      ( r2_hidden(D_171,k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_171,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_238])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_510,plain,(
    ! [A_182] :
      ( r1_tarski(A_182,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_182,k2_relat_1('#skF_8')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_470,c_4])).

tff(c_520,plain,(
    r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6,c_510])).

tff(c_523,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_520,c_138])).

tff(c_530,plain,(
    k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_162,c_523])).

tff(c_532,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_202,c_530])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:24:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.64/1.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.94  
% 3.64/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.94  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 3.64/1.94  
% 3.64/1.94  %Foreground sorts:
% 3.64/1.94  
% 3.64/1.94  
% 3.64/1.94  %Background operators:
% 3.64/1.94  
% 3.64/1.94  
% 3.64/1.94  %Foreground operators:
% 3.64/1.94  tff('#skF_9', type, '#skF_9': $i > $i).
% 3.64/1.94  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.64/1.94  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.64/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.64/1.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.64/1.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.64/1.94  tff('#skF_7', type, '#skF_7': $i).
% 3.64/1.94  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.64/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.64/1.94  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.64/1.94  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.64/1.94  tff('#skF_6', type, '#skF_6': $i).
% 3.64/1.94  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.64/1.94  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.64/1.94  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.64/1.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.64/1.94  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.64/1.94  tff('#skF_8', type, '#skF_8': $i).
% 3.64/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.64/1.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.64/1.94  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.64/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.64/1.94  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.64/1.94  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.64/1.94  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.64/1.94  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.64/1.94  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.64/1.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.64/1.94  
% 3.64/1.97  tff(f_121, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 3.64/1.97  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.64/1.97  tff(f_55, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.64/1.97  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.64/1.97  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.64/1.97  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.64/1.97  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.64/1.97  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.64/1.97  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.64/1.97  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 3.64/1.97  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.64/1.97  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.64/1.97  tff(c_64, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.64/1.97  tff(c_197, plain, (![A_115, B_116, C_117]: (k2_relset_1(A_115, B_116, C_117)=k2_relat_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.64/1.97  tff(c_201, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_64, c_197])).
% 3.64/1.97  tff(c_62, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.64/1.97  tff(c_202, plain, (k2_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_201, c_62])).
% 3.64/1.97  tff(c_22, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.64/1.97  tff(c_95, plain, (![B_83, A_84]: (v1_relat_1(B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(A_84)) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.64/1.97  tff(c_98, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_64, c_95])).
% 3.64/1.97  tff(c_101, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_98])).
% 3.64/1.97  tff(c_158, plain, (![C_100, B_101, A_102]: (v5_relat_1(C_100, B_101) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_102, B_101))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.64/1.97  tff(c_162, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_64, c_158])).
% 3.64/1.97  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.64/1.97  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.64/1.97  tff(c_66, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.64/1.97  tff(c_177, plain, (![A_109, B_110, C_111]: (k1_relset_1(A_109, B_110, C_111)=k1_relat_1(C_111) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.64/1.97  tff(c_181, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_64, c_177])).
% 3.64/1.97  tff(c_360, plain, (![B_160, A_161, C_162]: (k1_xboole_0=B_160 | k1_relset_1(A_161, B_160, C_162)=A_161 | ~v1_funct_2(C_162, A_161, B_160) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_161, B_160))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.64/1.97  tff(c_363, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_64, c_360])).
% 3.64/1.97  tff(c_366, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_181, c_363])).
% 3.64/1.97  tff(c_367, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_366])).
% 3.64/1.97  tff(c_72, plain, (![D_71]: (r2_hidden('#skF_9'(D_71), '#skF_6') | ~r2_hidden(D_71, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.64/1.97  tff(c_140, plain, (![C_94, B_95, A_96]: (r2_hidden(C_94, B_95) | ~r2_hidden(C_94, A_96) | ~r1_tarski(A_96, B_95))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.64/1.97  tff(c_146, plain, (![D_71, B_95]: (r2_hidden('#skF_9'(D_71), B_95) | ~r1_tarski('#skF_6', B_95) | ~r2_hidden(D_71, '#skF_7'))), inference(resolution, [status(thm)], [c_72, c_140])).
% 3.64/1.97  tff(c_68, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.64/1.97  tff(c_70, plain, (![D_71]: (k1_funct_1('#skF_8', '#skF_9'(D_71))=D_71 | ~r2_hidden(D_71, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.64/1.97  tff(c_207, plain, (![A_118, D_119]: (r2_hidden(k1_funct_1(A_118, D_119), k2_relat_1(A_118)) | ~r2_hidden(D_119, k1_relat_1(A_118)) | ~v1_funct_1(A_118) | ~v1_relat_1(A_118))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.64/1.97  tff(c_212, plain, (![D_71]: (r2_hidden(D_71, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_71), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_71, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_207])).
% 3.64/1.97  tff(c_233, plain, (![D_122]: (r2_hidden(D_122, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_122), k1_relat_1('#skF_8')) | ~r2_hidden(D_122, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_68, c_212])).
% 3.64/1.97  tff(c_238, plain, (![D_71]: (r2_hidden(D_71, k2_relat_1('#skF_8')) | ~r1_tarski('#skF_6', k1_relat_1('#skF_8')) | ~r2_hidden(D_71, '#skF_7'))), inference(resolution, [status(thm)], [c_146, c_233])).
% 3.64/1.97  tff(c_239, plain, (~r1_tarski('#skF_6', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_238])).
% 3.64/1.97  tff(c_368, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_367, c_239])).
% 3.64/1.97  tff(c_373, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_368])).
% 3.64/1.97  tff(c_374, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_366])).
% 3.64/1.97  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.64/1.97  tff(c_396, plain, (![A_163]: (r1_tarski('#skF_7', A_163))), inference(demodulation, [status(thm), theory('equality')], [c_374, c_14])).
% 3.64/1.97  tff(c_130, plain, (![B_91, A_92]: (r1_tarski(k2_relat_1(B_91), A_92) | ~v5_relat_1(B_91, A_92) | ~v1_relat_1(B_91))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.64/1.97  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.64/1.97  tff(c_138, plain, (![B_91, A_92]: (k2_relat_1(B_91)=A_92 | ~r1_tarski(A_92, k2_relat_1(B_91)) | ~v5_relat_1(B_91, A_92) | ~v1_relat_1(B_91))), inference(resolution, [status(thm)], [c_130, c_8])).
% 3.64/1.97  tff(c_451, plain, (![B_170]: (k2_relat_1(B_170)='#skF_7' | ~v5_relat_1(B_170, '#skF_7') | ~v1_relat_1(B_170))), inference(resolution, [status(thm)], [c_396, c_138])).
% 3.64/1.97  tff(c_454, plain, (k2_relat_1('#skF_8')='#skF_7' | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_162, c_451])).
% 3.64/1.97  tff(c_457, plain, (k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_101, c_454])).
% 3.64/1.97  tff(c_459, plain, $false, inference(negUnitSimplification, [status(thm)], [c_202, c_457])).
% 3.64/1.97  tff(c_470, plain, (![D_171]: (r2_hidden(D_171, k2_relat_1('#skF_8')) | ~r2_hidden(D_171, '#skF_7'))), inference(splitRight, [status(thm)], [c_238])).
% 3.64/1.97  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.64/1.97  tff(c_510, plain, (![A_182]: (r1_tarski(A_182, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_1'(A_182, k2_relat_1('#skF_8')), '#skF_7'))), inference(resolution, [status(thm)], [c_470, c_4])).
% 3.64/1.97  tff(c_520, plain, (r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6, c_510])).
% 3.64/1.97  tff(c_523, plain, (k2_relat_1('#skF_8')='#skF_7' | ~v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_520, c_138])).
% 3.64/1.97  tff(c_530, plain, (k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_101, c_162, c_523])).
% 3.64/1.97  tff(c_532, plain, $false, inference(negUnitSimplification, [status(thm)], [c_202, c_530])).
% 3.64/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.97  
% 3.64/1.97  Inference rules
% 3.64/1.97  ----------------------
% 3.64/1.97  #Ref     : 0
% 3.64/1.97  #Sup     : 89
% 3.64/1.97  #Fact    : 0
% 3.64/1.97  #Define  : 0
% 3.64/1.97  #Split   : 5
% 3.64/1.97  #Chain   : 0
% 3.64/1.97  #Close   : 0
% 3.64/1.97  
% 3.64/1.97  Ordering : KBO
% 3.64/1.97  
% 3.64/1.97  Simplification rules
% 3.64/1.97  ----------------------
% 3.64/1.97  #Subsume      : 14
% 3.64/1.97  #Demod        : 57
% 3.64/1.97  #Tautology    : 28
% 3.64/1.97  #SimpNegUnit  : 2
% 3.64/1.97  #BackRed      : 20
% 3.64/1.97  
% 3.64/1.97  #Partial instantiations: 0
% 3.64/1.97  #Strategies tried      : 1
% 3.64/1.97  
% 3.64/1.97  Timing (in seconds)
% 3.64/1.97  ----------------------
% 3.64/1.97  Preprocessing        : 0.55
% 3.64/1.97  Parsing              : 0.27
% 3.64/1.97  CNF conversion       : 0.05
% 3.64/1.98  Main loop            : 0.49
% 3.64/1.98  Inferencing          : 0.17
% 3.64/1.98  Reduction            : 0.14
% 3.64/1.98  Demodulation         : 0.10
% 3.64/1.98  BG Simplification    : 0.03
% 3.64/1.98  Subsumption          : 0.11
% 3.64/1.98  Abstraction          : 0.03
% 3.64/1.98  MUC search           : 0.00
% 3.64/1.98  Cooper               : 0.00
% 3.64/1.98  Total                : 1.09
% 3.64/1.98  Index Insertion      : 0.00
% 3.64/1.98  Index Deletion       : 0.00
% 3.64/1.98  Index Matching       : 0.00
% 3.64/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
