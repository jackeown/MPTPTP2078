%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:34 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 249 expanded)
%              Number of leaves         :   40 ( 100 expanded)
%              Depth                    :   13
%              Number of atoms          :  156 ( 529 expanded)
%              Number of equality atoms :   72 ( 238 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_124,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_65,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_112,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_86,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_119,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_123,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_119])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_32,plain,(
    ! [A_15] :
      ( k1_relat_1(A_15) != k1_xboole_0
      | k1_xboole_0 = A_15
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_130,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_123,c_32])).

tff(c_132,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_189,plain,(
    ! [B_70,A_71] :
      ( k1_tarski(k1_funct_1(B_70,A_71)) = k2_relat_1(B_70)
      | k1_tarski(A_71) != k1_relat_1(B_70)
      | ~ v1_funct_1(B_70)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_179,plain,(
    ! [A_67,B_68,C_69] :
      ( k2_relset_1(A_67,B_68,C_69) = k2_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_183,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_179])).

tff(c_48,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') != k1_tarski(k1_funct_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_184,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_48])).

tff(c_195,plain,
    ( k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_184])).

tff(c_214,plain,(
    k1_tarski('#skF_2') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_56,c_195])).

tff(c_153,plain,(
    ! [C_58,A_59,B_60] :
      ( v4_relat_1(C_58,A_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_157,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_153])).

tff(c_24,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(B_14),A_13)
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_250,plain,(
    ! [B_82,C_83,A_84] :
      ( k2_tarski(B_82,C_83) = A_84
      | k1_tarski(C_83) = A_84
      | k1_tarski(B_82) = A_84
      | k1_xboole_0 = A_84
      | ~ r1_tarski(A_84,k2_tarski(B_82,C_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_272,plain,(
    ! [A_4,A_84] :
      ( k2_tarski(A_4,A_4) = A_84
      | k1_tarski(A_4) = A_84
      | k1_tarski(A_4) = A_84
      | k1_xboole_0 = A_84
      | ~ r1_tarski(A_84,k1_tarski(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_250])).

tff(c_306,plain,(
    ! [A_91,A_92] :
      ( k1_tarski(A_91) = A_92
      | k1_tarski(A_91) = A_92
      | k1_tarski(A_91) = A_92
      | k1_xboole_0 = A_92
      | ~ r1_tarski(A_92,k1_tarski(A_91)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_272])).

tff(c_330,plain,(
    ! [A_93,B_94] :
      ( k1_tarski(A_93) = k1_relat_1(B_94)
      | k1_relat_1(B_94) = k1_xboole_0
      | ~ v4_relat_1(B_94,k1_tarski(A_93))
      | ~ v1_relat_1(B_94) ) ),
    inference(resolution,[status(thm)],[c_24,c_306])).

tff(c_336,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_157,c_330])).

tff(c_339,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_336])).

tff(c_341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_214,c_339])).

tff(c_342,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_343,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_360,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_343])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_350,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_342,c_26])).

tff(c_463,plain,(
    ! [B_118,A_119] :
      ( k1_tarski(k1_funct_1(B_118,A_119)) = k2_relat_1(B_118)
      | k1_tarski(A_119) != k1_relat_1(B_118)
      | ~ v1_funct_1(B_118)
      | ~ v1_relat_1(B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_439,plain,(
    ! [A_114,B_115,C_116] :
      ( k2_relset_1(A_114,B_115,C_116) = k2_relat_1(C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_442,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_439])).

tff(c_444,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_442])).

tff(c_445,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_48])).

tff(c_469,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_463,c_445])).

tff(c_487,plain,(
    k1_tarski('#skF_2') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_56,c_360,c_350,c_469])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_347,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | A_1 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_2])).

tff(c_4,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_348,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_4])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_351,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_50])).

tff(c_54,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_46,plain,(
    ! [D_32,C_31,A_29,B_30] :
      ( r2_hidden(k1_funct_1(D_32,C_31),k2_relset_1(A_29,B_30,D_32))
      | k1_xboole_0 = B_30
      | ~ r2_hidden(C_31,A_29)
      | ~ m1_subset_1(D_32,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | ~ v1_funct_2(D_32,A_29,B_30)
      | ~ v1_funct_1(D_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_547,plain,(
    ! [D_128,C_129,A_130,B_131] :
      ( r2_hidden(k1_funct_1(D_128,C_129),k2_relset_1(A_130,B_131,D_128))
      | B_131 = '#skF_4'
      | ~ r2_hidden(C_129,A_130)
      | ~ m1_subset_1(D_128,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131)))
      | ~ v1_funct_2(D_128,A_130,B_131)
      | ~ v1_funct_1(D_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_46])).

tff(c_553,plain,(
    ! [C_129] :
      ( r2_hidden(k1_funct_1('#skF_4',C_129),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_129,k1_tarski('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3')))
      | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_444,c_547])).

tff(c_556,plain,(
    ! [C_129] :
      ( r2_hidden(k1_funct_1('#skF_4',C_129),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_129,k1_tarski('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_553])).

tff(c_558,plain,(
    ! [C_132] :
      ( r2_hidden(k1_funct_1('#skF_4',C_132),'#skF_4')
      | ~ r2_hidden(C_132,k1_tarski('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_351,c_556])).

tff(c_36,plain,(
    ! [B_19,A_18] :
      ( ~ r1_tarski(B_19,A_18)
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_561,plain,(
    ! [C_132] :
      ( ~ r1_tarski('#skF_4',k1_funct_1('#skF_4',C_132))
      | ~ r2_hidden(C_132,k1_tarski('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_558,c_36])).

tff(c_565,plain,(
    ! [C_133] : ~ r2_hidden(C_133,k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_561])).

tff(c_569,plain,(
    k1_tarski('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_347,c_565])).

tff(c_573,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_487,c_569])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:15:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.46  
% 3.00/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.46  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.00/1.46  
% 3.00/1.46  %Foreground sorts:
% 3.00/1.46  
% 3.00/1.46  
% 3.00/1.46  %Background operators:
% 3.00/1.46  
% 3.00/1.46  
% 3.00/1.46  %Foreground operators:
% 3.00/1.46  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.00/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.00/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.00/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.00/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.00/1.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.00/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.00/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.00/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.00/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.00/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.00/1.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.00/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.00/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.00/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.00/1.47  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.00/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.00/1.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.00/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.00/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.00/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.00/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.00/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.00/1.47  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.00/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.00/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.00/1.47  
% 3.00/1.48  tff(f_124, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 3.00/1.48  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.00/1.48  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.00/1.48  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.00/1.48  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.00/1.48  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.00/1.48  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.00/1.48  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.00/1.48  tff(f_56, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.00/1.48  tff(f_65, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.00/1.48  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.00/1.48  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.00/1.48  tff(f_112, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 3.00/1.48  tff(f_86, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.00/1.48  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.00/1.48  tff(c_119, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.00/1.48  tff(c_123, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_119])).
% 3.00/1.48  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.00/1.48  tff(c_32, plain, (![A_15]: (k1_relat_1(A_15)!=k1_xboole_0 | k1_xboole_0=A_15 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.00/1.48  tff(c_130, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_123, c_32])).
% 3.00/1.48  tff(c_132, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_130])).
% 3.00/1.48  tff(c_189, plain, (![B_70, A_71]: (k1_tarski(k1_funct_1(B_70, A_71))=k2_relat_1(B_70) | k1_tarski(A_71)!=k1_relat_1(B_70) | ~v1_funct_1(B_70) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.00/1.48  tff(c_179, plain, (![A_67, B_68, C_69]: (k2_relset_1(A_67, B_68, C_69)=k2_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.00/1.48  tff(c_183, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_179])).
% 3.00/1.48  tff(c_48, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')!=k1_tarski(k1_funct_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.00/1.48  tff(c_184, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_183, c_48])).
% 3.00/1.48  tff(c_195, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_189, c_184])).
% 3.00/1.48  tff(c_214, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_56, c_195])).
% 3.00/1.48  tff(c_153, plain, (![C_58, A_59, B_60]: (v4_relat_1(C_58, A_59) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.00/1.48  tff(c_157, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_52, c_153])).
% 3.00/1.48  tff(c_24, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(B_14), A_13) | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.00/1.48  tff(c_6, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.00/1.48  tff(c_250, plain, (![B_82, C_83, A_84]: (k2_tarski(B_82, C_83)=A_84 | k1_tarski(C_83)=A_84 | k1_tarski(B_82)=A_84 | k1_xboole_0=A_84 | ~r1_tarski(A_84, k2_tarski(B_82, C_83)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.00/1.48  tff(c_272, plain, (![A_4, A_84]: (k2_tarski(A_4, A_4)=A_84 | k1_tarski(A_4)=A_84 | k1_tarski(A_4)=A_84 | k1_xboole_0=A_84 | ~r1_tarski(A_84, k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_250])).
% 3.00/1.48  tff(c_306, plain, (![A_91, A_92]: (k1_tarski(A_91)=A_92 | k1_tarski(A_91)=A_92 | k1_tarski(A_91)=A_92 | k1_xboole_0=A_92 | ~r1_tarski(A_92, k1_tarski(A_91)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_272])).
% 3.00/1.48  tff(c_330, plain, (![A_93, B_94]: (k1_tarski(A_93)=k1_relat_1(B_94) | k1_relat_1(B_94)=k1_xboole_0 | ~v4_relat_1(B_94, k1_tarski(A_93)) | ~v1_relat_1(B_94))), inference(resolution, [status(thm)], [c_24, c_306])).
% 3.00/1.48  tff(c_336, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_157, c_330])).
% 3.00/1.48  tff(c_339, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_123, c_336])).
% 3.00/1.48  tff(c_341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_132, c_214, c_339])).
% 3.00/1.48  tff(c_342, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_130])).
% 3.00/1.48  tff(c_343, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_130])).
% 3.00/1.48  tff(c_360, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_342, c_343])).
% 3.00/1.48  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.00/1.48  tff(c_350, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_342, c_342, c_26])).
% 3.00/1.48  tff(c_463, plain, (![B_118, A_119]: (k1_tarski(k1_funct_1(B_118, A_119))=k2_relat_1(B_118) | k1_tarski(A_119)!=k1_relat_1(B_118) | ~v1_funct_1(B_118) | ~v1_relat_1(B_118))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.00/1.48  tff(c_439, plain, (![A_114, B_115, C_116]: (k2_relset_1(A_114, B_115, C_116)=k2_relat_1(C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.00/1.48  tff(c_442, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_439])).
% 3.00/1.48  tff(c_444, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_350, c_442])).
% 3.00/1.48  tff(c_445, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_444, c_48])).
% 3.00/1.48  tff(c_469, plain, (k2_relat_1('#skF_4')!='#skF_4' | k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_463, c_445])).
% 3.00/1.48  tff(c_487, plain, (k1_tarski('#skF_2')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_123, c_56, c_360, c_350, c_469])).
% 3.00/1.48  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.00/1.48  tff(c_347, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | A_1='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_342, c_2])).
% 3.00/1.48  tff(c_4, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.00/1.48  tff(c_348, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_342, c_4])).
% 3.00/1.48  tff(c_50, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.00/1.48  tff(c_351, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_342, c_50])).
% 3.00/1.48  tff(c_54, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.00/1.48  tff(c_46, plain, (![D_32, C_31, A_29, B_30]: (r2_hidden(k1_funct_1(D_32, C_31), k2_relset_1(A_29, B_30, D_32)) | k1_xboole_0=B_30 | ~r2_hidden(C_31, A_29) | ~m1_subset_1(D_32, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))) | ~v1_funct_2(D_32, A_29, B_30) | ~v1_funct_1(D_32))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.00/1.48  tff(c_547, plain, (![D_128, C_129, A_130, B_131]: (r2_hidden(k1_funct_1(D_128, C_129), k2_relset_1(A_130, B_131, D_128)) | B_131='#skF_4' | ~r2_hidden(C_129, A_130) | ~m1_subset_1(D_128, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))) | ~v1_funct_2(D_128, A_130, B_131) | ~v1_funct_1(D_128))), inference(demodulation, [status(thm), theory('equality')], [c_342, c_46])).
% 3.00/1.48  tff(c_553, plain, (![C_129]: (r2_hidden(k1_funct_1('#skF_4', C_129), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_129, k1_tarski('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_444, c_547])).
% 3.00/1.48  tff(c_556, plain, (![C_129]: (r2_hidden(k1_funct_1('#skF_4', C_129), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_129, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_553])).
% 3.00/1.48  tff(c_558, plain, (![C_132]: (r2_hidden(k1_funct_1('#skF_4', C_132), '#skF_4') | ~r2_hidden(C_132, k1_tarski('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_351, c_556])).
% 3.00/1.48  tff(c_36, plain, (![B_19, A_18]: (~r1_tarski(B_19, A_18) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.00/1.48  tff(c_561, plain, (![C_132]: (~r1_tarski('#skF_4', k1_funct_1('#skF_4', C_132)) | ~r2_hidden(C_132, k1_tarski('#skF_2')))), inference(resolution, [status(thm)], [c_558, c_36])).
% 3.00/1.48  tff(c_565, plain, (![C_133]: (~r2_hidden(C_133, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_348, c_561])).
% 3.00/1.48  tff(c_569, plain, (k1_tarski('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_347, c_565])).
% 3.00/1.48  tff(c_573, plain, $false, inference(negUnitSimplification, [status(thm)], [c_487, c_569])).
% 3.00/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.48  
% 3.00/1.48  Inference rules
% 3.00/1.48  ----------------------
% 3.00/1.48  #Ref     : 0
% 3.00/1.48  #Sup     : 107
% 3.00/1.48  #Fact    : 0
% 3.00/1.48  #Define  : 0
% 3.00/1.48  #Split   : 3
% 3.00/1.48  #Chain   : 0
% 3.00/1.48  #Close   : 0
% 3.00/1.48  
% 3.00/1.48  Ordering : KBO
% 3.00/1.48  
% 3.00/1.48  Simplification rules
% 3.00/1.48  ----------------------
% 3.00/1.48  #Subsume      : 12
% 3.00/1.48  #Demod        : 78
% 3.00/1.48  #Tautology    : 55
% 3.00/1.48  #SimpNegUnit  : 4
% 3.00/1.48  #BackRed      : 10
% 3.00/1.48  
% 3.00/1.48  #Partial instantiations: 0
% 3.00/1.48  #Strategies tried      : 1
% 3.00/1.48  
% 3.00/1.48  Timing (in seconds)
% 3.00/1.48  ----------------------
% 3.00/1.49  Preprocessing        : 0.36
% 3.00/1.49  Parsing              : 0.19
% 3.00/1.49  CNF conversion       : 0.02
% 3.00/1.49  Main loop            : 0.32
% 3.00/1.49  Inferencing          : 0.12
% 3.00/1.49  Reduction            : 0.10
% 3.00/1.49  Demodulation         : 0.07
% 3.00/1.49  BG Simplification    : 0.02
% 3.00/1.49  Subsumption          : 0.06
% 3.00/1.49  Abstraction          : 0.02
% 3.00/1.49  MUC search           : 0.00
% 3.00/1.49  Cooper               : 0.00
% 3.00/1.49  Total                : 0.72
% 3.00/1.49  Index Insertion      : 0.00
% 3.00/1.49  Index Deletion       : 0.00
% 3.00/1.49  Index Matching       : 0.00
% 3.00/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
