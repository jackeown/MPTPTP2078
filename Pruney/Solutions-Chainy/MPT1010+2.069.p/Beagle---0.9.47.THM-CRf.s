%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:14 EST 2020

% Result     : Theorem 11.88s
% Output     : CNFRefutation 11.88s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 107 expanded)
%              Number of leaves         :   42 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :  107 ( 197 expanded)
%              Number of equality atoms :   36 (  66 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_112,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_101,axiom,(
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

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_62,axiom,(
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

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_38,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_67,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_68,plain,(
    k1_funct_1('#skF_10','#skF_9') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_70,plain,(
    r2_hidden('#skF_9','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_72,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_132,plain,(
    ! [C_88,A_89,B_90] :
      ( v1_relat_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_136,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_72,c_132])).

tff(c_76,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_74,plain,(
    v1_funct_2('#skF_10','#skF_7',k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_190,plain,(
    ! [A_112,B_113,C_114] :
      ( k1_relset_1(A_112,B_113,C_114) = k1_relat_1(C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_194,plain,(
    k1_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_72,c_190])).

tff(c_292,plain,(
    ! [B_152,A_153,C_154] :
      ( k1_xboole_0 = B_152
      | k1_relset_1(A_153,B_152,C_154) = A_153
      | ~ v1_funct_2(C_154,A_153,B_152)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_153,B_152))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_299,plain,
    ( k1_tarski('#skF_8') = k1_xboole_0
    | k1_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = '#skF_7'
    | ~ v1_funct_2('#skF_10','#skF_7',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_72,c_292])).

tff(c_303,plain,
    ( k1_tarski('#skF_8') = k1_xboole_0
    | k1_relat_1('#skF_10') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_194,c_299])).

tff(c_304,plain,(
    k1_relat_1('#skF_10') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_303])).

tff(c_180,plain,(
    ! [A_108,B_109,C_110] :
      ( k2_relset_1(A_108,B_109,C_110) = k2_relat_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_184,plain,(
    k2_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_72,c_180])).

tff(c_199,plain,(
    ! [A_115,B_116,C_117] :
      ( m1_subset_1(k2_relset_1(A_115,B_116,C_117),k1_zfmisc_1(B_116))
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_214,plain,
    ( m1_subset_1(k2_relat_1('#skF_10'),k1_zfmisc_1(k1_tarski('#skF_8')))
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_199])).

tff(c_219,plain,(
    m1_subset_1(k2_relat_1('#skF_10'),k1_zfmisc_1(k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_214])).

tff(c_220,plain,(
    ! [A_118,D_119] :
      ( r2_hidden(k1_funct_1(A_118,D_119),k2_relat_1(A_118))
      | ~ r2_hidden(D_119,k1_relat_1(A_118))
      | ~ v1_funct_1(A_118)
      | ~ v1_relat_1(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_26,plain,(
    ! [C_14,A_11,B_12] :
      ( r2_hidden(C_14,A_11)
      | ~ r2_hidden(C_14,B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_32321,plain,(
    ! [A_22263,D_22264,A_22265] :
      ( r2_hidden(k1_funct_1(A_22263,D_22264),A_22265)
      | ~ m1_subset_1(k2_relat_1(A_22263),k1_zfmisc_1(A_22265))
      | ~ r2_hidden(D_22264,k1_relat_1(A_22263))
      | ~ v1_funct_1(A_22263)
      | ~ v1_relat_1(A_22263) ) ),
    inference(resolution,[status(thm)],[c_220,c_26])).

tff(c_32383,plain,(
    ! [D_22264] :
      ( r2_hidden(k1_funct_1('#skF_10',D_22264),k1_tarski('#skF_8'))
      | ~ r2_hidden(D_22264,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_219,c_32321])).

tff(c_32387,plain,(
    ! [D_22436] :
      ( r2_hidden(k1_funct_1('#skF_10',D_22436),k1_tarski('#skF_8'))
      | ~ r2_hidden(D_22436,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_76,c_304,c_32383])).

tff(c_22,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_137,plain,(
    ! [D_91,B_92,A_93] :
      ( D_91 = B_92
      | D_91 = A_93
      | ~ r2_hidden(D_91,k2_tarski(A_93,B_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_143,plain,(
    ! [D_91,A_8] :
      ( D_91 = A_8
      | D_91 = A_8
      | ~ r2_hidden(D_91,k1_tarski(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_137])).

tff(c_32799,plain,(
    ! [D_22607] :
      ( k1_funct_1('#skF_10',D_22607) = '#skF_8'
      | ~ r2_hidden(D_22607,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_32387,c_143])).

tff(c_32987,plain,(
    k1_funct_1('#skF_10','#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_70,c_32799])).

tff(c_33007,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_32987])).

tff(c_33008,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_303])).

tff(c_79,plain,(
    ! [A_75] : k2_tarski(A_75,A_75) = k1_tarski(A_75) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [D_7,B_3] : r2_hidden(D_7,k2_tarski(D_7,B_3)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_85,plain,(
    ! [A_75] : r2_hidden(A_75,k1_tarski(A_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_8])).

tff(c_97,plain,(
    ! [B_79,A_80] :
      ( ~ r1_tarski(B_79,A_80)
      | ~ r2_hidden(A_80,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_111,plain,(
    ! [A_75] : ~ r1_tarski(k1_tarski(A_75),A_75) ),
    inference(resolution,[status(thm)],[c_85,c_97])).

tff(c_33024,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_33008,c_111])).

tff(c_33032,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_33024])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:55:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.88/4.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.88/4.79  
% 11.88/4.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.88/4.79  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_4
% 11.88/4.79  
% 11.88/4.79  %Foreground sorts:
% 11.88/4.79  
% 11.88/4.79  
% 11.88/4.79  %Background operators:
% 11.88/4.79  
% 11.88/4.79  
% 11.88/4.79  %Foreground operators:
% 11.88/4.79  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.88/4.79  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 11.88/4.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.88/4.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.88/4.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.88/4.79  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 11.88/4.79  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.88/4.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.88/4.79  tff('#skF_7', type, '#skF_7': $i).
% 11.88/4.79  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 11.88/4.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.88/4.79  tff('#skF_10', type, '#skF_10': $i).
% 11.88/4.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.88/4.79  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.88/4.79  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.88/4.79  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.88/4.79  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.88/4.79  tff('#skF_9', type, '#skF_9': $i).
% 11.88/4.79  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.88/4.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.88/4.79  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 11.88/4.79  tff('#skF_8', type, '#skF_8': $i).
% 11.88/4.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.88/4.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.88/4.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.88/4.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.88/4.79  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 11.88/4.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.88/4.79  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 11.88/4.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.88/4.79  
% 11.88/4.80  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.88/4.80  tff(f_112, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 11.88/4.80  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.88/4.80  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.88/4.80  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 11.88/4.80  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 11.88/4.80  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 11.88/4.80  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 11.88/4.80  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 11.88/4.80  tff(f_38, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 11.88/4.80  tff(f_36, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 11.88/4.80  tff(f_67, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 11.88/4.80  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.88/4.80  tff(c_68, plain, (k1_funct_1('#skF_10', '#skF_9')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_112])).
% 11.88/4.80  tff(c_70, plain, (r2_hidden('#skF_9', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_112])).
% 11.88/4.80  tff(c_72, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8'))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 11.88/4.80  tff(c_132, plain, (![C_88, A_89, B_90]: (v1_relat_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.88/4.80  tff(c_136, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_72, c_132])).
% 11.88/4.80  tff(c_76, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_112])).
% 11.88/4.80  tff(c_74, plain, (v1_funct_2('#skF_10', '#skF_7', k1_tarski('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 11.88/4.80  tff(c_190, plain, (![A_112, B_113, C_114]: (k1_relset_1(A_112, B_113, C_114)=k1_relat_1(C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 11.88/4.80  tff(c_194, plain, (k1_relset_1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_72, c_190])).
% 11.88/4.80  tff(c_292, plain, (![B_152, A_153, C_154]: (k1_xboole_0=B_152 | k1_relset_1(A_153, B_152, C_154)=A_153 | ~v1_funct_2(C_154, A_153, B_152) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_153, B_152))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.88/4.80  tff(c_299, plain, (k1_tarski('#skF_8')=k1_xboole_0 | k1_relset_1('#skF_7', k1_tarski('#skF_8'), '#skF_10')='#skF_7' | ~v1_funct_2('#skF_10', '#skF_7', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_72, c_292])).
% 11.88/4.80  tff(c_303, plain, (k1_tarski('#skF_8')=k1_xboole_0 | k1_relat_1('#skF_10')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_194, c_299])).
% 11.88/4.80  tff(c_304, plain, (k1_relat_1('#skF_10')='#skF_7'), inference(splitLeft, [status(thm)], [c_303])).
% 11.88/4.80  tff(c_180, plain, (![A_108, B_109, C_110]: (k2_relset_1(A_108, B_109, C_110)=k2_relat_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.88/4.80  tff(c_184, plain, (k2_relset_1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_72, c_180])).
% 11.88/4.80  tff(c_199, plain, (![A_115, B_116, C_117]: (m1_subset_1(k2_relset_1(A_115, B_116, C_117), k1_zfmisc_1(B_116)) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.88/4.80  tff(c_214, plain, (m1_subset_1(k2_relat_1('#skF_10'), k1_zfmisc_1(k1_tarski('#skF_8'))) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8'))))), inference(superposition, [status(thm), theory('equality')], [c_184, c_199])).
% 11.88/4.80  tff(c_219, plain, (m1_subset_1(k2_relat_1('#skF_10'), k1_zfmisc_1(k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_214])).
% 11.88/4.80  tff(c_220, plain, (![A_118, D_119]: (r2_hidden(k1_funct_1(A_118, D_119), k2_relat_1(A_118)) | ~r2_hidden(D_119, k1_relat_1(A_118)) | ~v1_funct_1(A_118) | ~v1_relat_1(A_118))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.88/4.80  tff(c_26, plain, (![C_14, A_11, B_12]: (r2_hidden(C_14, A_11) | ~r2_hidden(C_14, B_12) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.88/4.80  tff(c_32321, plain, (![A_22263, D_22264, A_22265]: (r2_hidden(k1_funct_1(A_22263, D_22264), A_22265) | ~m1_subset_1(k2_relat_1(A_22263), k1_zfmisc_1(A_22265)) | ~r2_hidden(D_22264, k1_relat_1(A_22263)) | ~v1_funct_1(A_22263) | ~v1_relat_1(A_22263))), inference(resolution, [status(thm)], [c_220, c_26])).
% 11.88/4.80  tff(c_32383, plain, (![D_22264]: (r2_hidden(k1_funct_1('#skF_10', D_22264), k1_tarski('#skF_8')) | ~r2_hidden(D_22264, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_219, c_32321])).
% 11.88/4.80  tff(c_32387, plain, (![D_22436]: (r2_hidden(k1_funct_1('#skF_10', D_22436), k1_tarski('#skF_8')) | ~r2_hidden(D_22436, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_76, c_304, c_32383])).
% 11.88/4.80  tff(c_22, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.88/4.80  tff(c_137, plain, (![D_91, B_92, A_93]: (D_91=B_92 | D_91=A_93 | ~r2_hidden(D_91, k2_tarski(A_93, B_92)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.88/4.80  tff(c_143, plain, (![D_91, A_8]: (D_91=A_8 | D_91=A_8 | ~r2_hidden(D_91, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_137])).
% 11.88/4.80  tff(c_32799, plain, (![D_22607]: (k1_funct_1('#skF_10', D_22607)='#skF_8' | ~r2_hidden(D_22607, '#skF_7'))), inference(resolution, [status(thm)], [c_32387, c_143])).
% 11.88/4.80  tff(c_32987, plain, (k1_funct_1('#skF_10', '#skF_9')='#skF_8'), inference(resolution, [status(thm)], [c_70, c_32799])).
% 11.88/4.80  tff(c_33007, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_32987])).
% 11.88/4.80  tff(c_33008, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_303])).
% 11.88/4.80  tff(c_79, plain, (![A_75]: (k2_tarski(A_75, A_75)=k1_tarski(A_75))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.88/4.80  tff(c_8, plain, (![D_7, B_3]: (r2_hidden(D_7, k2_tarski(D_7, B_3)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.88/4.80  tff(c_85, plain, (![A_75]: (r2_hidden(A_75, k1_tarski(A_75)))), inference(superposition, [status(thm), theory('equality')], [c_79, c_8])).
% 11.88/4.80  tff(c_97, plain, (![B_79, A_80]: (~r1_tarski(B_79, A_80) | ~r2_hidden(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.88/4.80  tff(c_111, plain, (![A_75]: (~r1_tarski(k1_tarski(A_75), A_75))), inference(resolution, [status(thm)], [c_85, c_97])).
% 11.88/4.80  tff(c_33024, plain, (~r1_tarski(k1_xboole_0, '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_33008, c_111])).
% 11.88/4.80  tff(c_33032, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_33024])).
% 11.88/4.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.88/4.80  
% 11.88/4.80  Inference rules
% 11.88/4.80  ----------------------
% 11.88/4.80  #Ref     : 0
% 11.88/4.80  #Sup     : 3552
% 11.88/4.80  #Fact    : 20
% 11.88/4.80  #Define  : 0
% 11.88/4.80  #Split   : 10
% 11.88/4.80  #Chain   : 0
% 11.88/4.80  #Close   : 0
% 11.88/4.80  
% 11.88/4.80  Ordering : KBO
% 11.88/4.80  
% 11.88/4.80  Simplification rules
% 11.88/4.80  ----------------------
% 11.88/4.80  #Subsume      : 324
% 11.88/4.80  #Demod        : 536
% 11.88/4.80  #Tautology    : 224
% 11.88/4.80  #SimpNegUnit  : 7
% 11.88/4.80  #BackRed      : 16
% 11.88/4.80  
% 11.88/4.80  #Partial instantiations: 13860
% 11.88/4.80  #Strategies tried      : 1
% 11.88/4.80  
% 11.88/4.80  Timing (in seconds)
% 11.88/4.80  ----------------------
% 11.88/4.81  Preprocessing        : 0.42
% 11.88/4.81  Parsing              : 0.21
% 11.88/4.81  CNF conversion       : 0.03
% 11.88/4.81  Main loop            : 3.53
% 11.88/4.81  Inferencing          : 1.21
% 11.88/4.81  Reduction            : 0.70
% 11.88/4.81  Demodulation         : 0.48
% 11.88/4.81  BG Simplification    : 0.18
% 11.88/4.81  Subsumption          : 1.30
% 11.88/4.81  Abstraction          : 0.28
% 11.88/4.81  MUC search           : 0.00
% 11.88/4.81  Cooper               : 0.00
% 11.88/4.81  Total                : 3.98
% 11.88/4.81  Index Insertion      : 0.00
% 11.88/4.81  Index Deletion       : 0.00
% 11.88/4.81  Index Matching       : 0.00
% 11.88/4.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
