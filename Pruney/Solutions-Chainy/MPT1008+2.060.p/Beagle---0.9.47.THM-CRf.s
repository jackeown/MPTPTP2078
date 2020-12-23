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
% DateTime   : Thu Dec  3 10:14:34 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 287 expanded)
%              Number of leaves         :   41 ( 112 expanded)
%              Depth                    :   13
%              Number of atoms          :  173 ( 619 expanded)
%              Number of equality atoms :   81 ( 277 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_137,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_57,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_113,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_125,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_78,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_121,plain,(
    ! [C_70,A_71,B_72] :
      ( v1_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_125,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_121])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_30,plain,(
    ! [A_13] :
      ( k1_relat_1(A_13) != k1_xboole_0
      | k1_xboole_0 = A_13
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_133,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_125,c_30])).

tff(c_135,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_191,plain,(
    ! [B_90,A_91] :
      ( k1_tarski(k1_funct_1(B_90,A_91)) = k2_relat_1(B_90)
      | k1_tarski(A_91) != k1_relat_1(B_90)
      | ~ v1_funct_1(B_90)
      | ~ v1_relat_1(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_181,plain,(
    ! [A_87,B_88,C_89] :
      ( k2_relset_1(A_87,B_88,C_89) = k2_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_185,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_181])).

tff(c_50,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') != k1_tarski(k1_funct_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_186,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_50])).

tff(c_197,plain,
    ( k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_186])).

tff(c_216,plain,(
    k1_tarski('#skF_2') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_58,c_197])).

tff(c_157,plain,(
    ! [C_77,A_78,B_79] :
      ( v4_relat_1(C_77,A_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_161,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_157])).

tff(c_22,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(B_12),A_11)
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_252,plain,(
    ! [B_102,C_103,A_104] :
      ( k2_tarski(B_102,C_103) = A_104
      | k1_tarski(C_103) = A_104
      | k1_tarski(B_102) = A_104
      | k1_xboole_0 = A_104
      | ~ r1_tarski(A_104,k2_tarski(B_102,C_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_274,plain,(
    ! [A_2,A_104] :
      ( k2_tarski(A_2,A_2) = A_104
      | k1_tarski(A_2) = A_104
      | k1_tarski(A_2) = A_104
      | k1_xboole_0 = A_104
      | ~ r1_tarski(A_104,k1_tarski(A_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_252])).

tff(c_296,plain,(
    ! [A_111,A_112] :
      ( k1_tarski(A_111) = A_112
      | k1_tarski(A_111) = A_112
      | k1_tarski(A_111) = A_112
      | k1_xboole_0 = A_112
      | ~ r1_tarski(A_112,k1_tarski(A_111)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_274])).

tff(c_320,plain,(
    ! [A_113,B_114] :
      ( k1_tarski(A_113) = k1_relat_1(B_114)
      | k1_relat_1(B_114) = k1_xboole_0
      | ~ v4_relat_1(B_114,k1_tarski(A_113))
      | ~ v1_relat_1(B_114) ) ),
    inference(resolution,[status(thm)],[c_22,c_296])).

tff(c_326,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_161,c_320])).

tff(c_329,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_326])).

tff(c_331,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_216,c_329])).

tff(c_332,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_340,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_332,c_24])).

tff(c_28,plain,(
    ! [A_13] :
      ( k2_relat_1(A_13) != k1_xboole_0
      | k1_xboole_0 = A_13
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_132,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_125,c_28])).

tff(c_134,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_334,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_134])).

tff(c_358,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_334])).

tff(c_359,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_372,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_359,c_26])).

tff(c_360,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_379,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_360])).

tff(c_479,plain,(
    ! [B_139,A_140] :
      ( k1_tarski(k1_funct_1(B_139,A_140)) = k2_relat_1(B_139)
      | k1_tarski(A_140) != k1_relat_1(B_139)
      | ~ v1_funct_1(B_139)
      | ~ v1_relat_1(B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_468,plain,(
    ! [A_136,B_137,C_138] :
      ( k2_relset_1(A_136,B_137,C_138) = k2_relat_1(C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_471,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_468])).

tff(c_473,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_471])).

tff(c_474,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_50])).

tff(c_485,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_479,c_474])).

tff(c_503,plain,(
    k1_tarski('#skF_2') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_58,c_372,c_379,c_485])).

tff(c_46,plain,(
    ! [A_27] :
      ( r2_hidden('#skF_1'(A_27),A_27)
      | k1_xboole_0 = A_27 ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_369,plain,(
    ! [A_27] :
      ( r2_hidden('#skF_1'(A_27),A_27)
      | A_27 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_46])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_370,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_2])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_373,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_52])).

tff(c_56,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_48,plain,(
    ! [D_52,C_51,A_49,B_50] :
      ( r2_hidden(k1_funct_1(D_52,C_51),k2_relset_1(A_49,B_50,D_52))
      | k1_xboole_0 = B_50
      | ~ r2_hidden(C_51,A_49)
      | ~ m1_subset_1(D_52,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50)))
      | ~ v1_funct_2(D_52,A_49,B_50)
      | ~ v1_funct_1(D_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_632,plain,(
    ! [D_165,C_166,A_167,B_168] :
      ( r2_hidden(k1_funct_1(D_165,C_166),k2_relset_1(A_167,B_168,D_165))
      | B_168 = '#skF_4'
      | ~ r2_hidden(C_166,A_167)
      | ~ m1_subset_1(D_165,k1_zfmisc_1(k2_zfmisc_1(A_167,B_168)))
      | ~ v1_funct_2(D_165,A_167,B_168)
      | ~ v1_funct_1(D_165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_48])).

tff(c_638,plain,(
    ! [C_166] :
      ( r2_hidden(k1_funct_1('#skF_4',C_166),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_166,k1_tarski('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3')))
      | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_473,c_632])).

tff(c_641,plain,(
    ! [C_166] :
      ( r2_hidden(k1_funct_1('#skF_4',C_166),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_166,k1_tarski('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_638])).

tff(c_643,plain,(
    ! [C_169] :
      ( r2_hidden(k1_funct_1('#skF_4',C_169),'#skF_4')
      | ~ r2_hidden(C_169,k1_tarski('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_373,c_641])).

tff(c_34,plain,(
    ! [B_17,A_16] :
      ( ~ r1_tarski(B_17,A_16)
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_646,plain,(
    ! [C_169] :
      ( ~ r1_tarski('#skF_4',k1_funct_1('#skF_4',C_169))
      | ~ r2_hidden(C_169,k1_tarski('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_643,c_34])).

tff(c_650,plain,(
    ! [C_170] : ~ r2_hidden(C_170,k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_370,c_646])).

tff(c_654,plain,(
    k1_tarski('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_369,c_650])).

tff(c_658,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_503,c_654])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:54:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.37  
% 2.76/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.37  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.76/1.37  
% 2.76/1.37  %Foreground sorts:
% 2.76/1.37  
% 2.76/1.37  
% 2.76/1.37  %Background operators:
% 2.76/1.37  
% 2.76/1.37  
% 2.76/1.37  %Foreground operators:
% 2.76/1.37  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.76/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.76/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.76/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.76/1.37  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.76/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.76/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.76/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.76/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.76/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.76/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.76/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.76/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.76/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.76/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.76/1.37  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.76/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.76/1.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.76/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.76/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.76/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.76/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.76/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.76/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.76/1.37  
% 2.76/1.39  tff(f_137, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 2.76/1.39  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.76/1.39  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.76/1.39  tff(f_73, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 2.76/1.39  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.76/1.39  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.76/1.39  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.76/1.39  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.76/1.39  tff(f_48, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 2.76/1.39  tff(f_57, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.76/1.39  tff(f_113, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 2.76/1.39  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.76/1.39  tff(f_125, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 2.76/1.39  tff(f_78, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.76/1.39  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.76/1.39  tff(c_121, plain, (![C_70, A_71, B_72]: (v1_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.76/1.39  tff(c_125, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_121])).
% 2.76/1.39  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.76/1.39  tff(c_30, plain, (![A_13]: (k1_relat_1(A_13)!=k1_xboole_0 | k1_xboole_0=A_13 | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.76/1.39  tff(c_133, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_125, c_30])).
% 2.76/1.39  tff(c_135, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_133])).
% 2.76/1.39  tff(c_191, plain, (![B_90, A_91]: (k1_tarski(k1_funct_1(B_90, A_91))=k2_relat_1(B_90) | k1_tarski(A_91)!=k1_relat_1(B_90) | ~v1_funct_1(B_90) | ~v1_relat_1(B_90))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.76/1.39  tff(c_181, plain, (![A_87, B_88, C_89]: (k2_relset_1(A_87, B_88, C_89)=k2_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.76/1.39  tff(c_185, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_181])).
% 2.76/1.39  tff(c_50, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')!=k1_tarski(k1_funct_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.76/1.39  tff(c_186, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_185, c_50])).
% 2.76/1.39  tff(c_197, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_191, c_186])).
% 2.76/1.39  tff(c_216, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_125, c_58, c_197])).
% 2.76/1.39  tff(c_157, plain, (![C_77, A_78, B_79]: (v4_relat_1(C_77, A_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.76/1.39  tff(c_161, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_157])).
% 2.76/1.39  tff(c_22, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(B_12), A_11) | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.76/1.39  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.76/1.39  tff(c_252, plain, (![B_102, C_103, A_104]: (k2_tarski(B_102, C_103)=A_104 | k1_tarski(C_103)=A_104 | k1_tarski(B_102)=A_104 | k1_xboole_0=A_104 | ~r1_tarski(A_104, k2_tarski(B_102, C_103)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.76/1.39  tff(c_274, plain, (![A_2, A_104]: (k2_tarski(A_2, A_2)=A_104 | k1_tarski(A_2)=A_104 | k1_tarski(A_2)=A_104 | k1_xboole_0=A_104 | ~r1_tarski(A_104, k1_tarski(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_252])).
% 2.76/1.39  tff(c_296, plain, (![A_111, A_112]: (k1_tarski(A_111)=A_112 | k1_tarski(A_111)=A_112 | k1_tarski(A_111)=A_112 | k1_xboole_0=A_112 | ~r1_tarski(A_112, k1_tarski(A_111)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_274])).
% 2.76/1.39  tff(c_320, plain, (![A_113, B_114]: (k1_tarski(A_113)=k1_relat_1(B_114) | k1_relat_1(B_114)=k1_xboole_0 | ~v4_relat_1(B_114, k1_tarski(A_113)) | ~v1_relat_1(B_114))), inference(resolution, [status(thm)], [c_22, c_296])).
% 2.76/1.39  tff(c_326, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_161, c_320])).
% 2.76/1.39  tff(c_329, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_125, c_326])).
% 2.76/1.39  tff(c_331, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135, c_216, c_329])).
% 2.76/1.39  tff(c_332, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_133])).
% 2.76/1.39  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.76/1.39  tff(c_340, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_332, c_332, c_24])).
% 2.76/1.39  tff(c_28, plain, (![A_13]: (k2_relat_1(A_13)!=k1_xboole_0 | k1_xboole_0=A_13 | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.76/1.39  tff(c_132, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_125, c_28])).
% 2.76/1.39  tff(c_134, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_132])).
% 2.76/1.39  tff(c_334, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_332, c_134])).
% 2.76/1.39  tff(c_358, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_340, c_334])).
% 2.76/1.39  tff(c_359, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_132])).
% 2.76/1.39  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.76/1.39  tff(c_372, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_359, c_359, c_26])).
% 2.76/1.39  tff(c_360, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_132])).
% 2.76/1.39  tff(c_379, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_359, c_360])).
% 2.76/1.39  tff(c_479, plain, (![B_139, A_140]: (k1_tarski(k1_funct_1(B_139, A_140))=k2_relat_1(B_139) | k1_tarski(A_140)!=k1_relat_1(B_139) | ~v1_funct_1(B_139) | ~v1_relat_1(B_139))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.76/1.39  tff(c_468, plain, (![A_136, B_137, C_138]: (k2_relset_1(A_136, B_137, C_138)=k2_relat_1(C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.76/1.39  tff(c_471, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_468])).
% 2.76/1.39  tff(c_473, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_379, c_471])).
% 2.76/1.39  tff(c_474, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_473, c_50])).
% 2.76/1.39  tff(c_485, plain, (k2_relat_1('#skF_4')!='#skF_4' | k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_479, c_474])).
% 2.76/1.39  tff(c_503, plain, (k1_tarski('#skF_2')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_125, c_58, c_372, c_379, c_485])).
% 2.76/1.39  tff(c_46, plain, (![A_27]: (r2_hidden('#skF_1'(A_27), A_27) | k1_xboole_0=A_27)), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.76/1.39  tff(c_369, plain, (![A_27]: (r2_hidden('#skF_1'(A_27), A_27) | A_27='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_359, c_46])).
% 2.76/1.39  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.76/1.39  tff(c_370, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_359, c_2])).
% 2.76/1.39  tff(c_52, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.76/1.39  tff(c_373, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_359, c_52])).
% 2.76/1.39  tff(c_56, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.76/1.39  tff(c_48, plain, (![D_52, C_51, A_49, B_50]: (r2_hidden(k1_funct_1(D_52, C_51), k2_relset_1(A_49, B_50, D_52)) | k1_xboole_0=B_50 | ~r2_hidden(C_51, A_49) | ~m1_subset_1(D_52, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))) | ~v1_funct_2(D_52, A_49, B_50) | ~v1_funct_1(D_52))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.76/1.39  tff(c_632, plain, (![D_165, C_166, A_167, B_168]: (r2_hidden(k1_funct_1(D_165, C_166), k2_relset_1(A_167, B_168, D_165)) | B_168='#skF_4' | ~r2_hidden(C_166, A_167) | ~m1_subset_1(D_165, k1_zfmisc_1(k2_zfmisc_1(A_167, B_168))) | ~v1_funct_2(D_165, A_167, B_168) | ~v1_funct_1(D_165))), inference(demodulation, [status(thm), theory('equality')], [c_359, c_48])).
% 2.76/1.39  tff(c_638, plain, (![C_166]: (r2_hidden(k1_funct_1('#skF_4', C_166), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_166, k1_tarski('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_473, c_632])).
% 2.76/1.39  tff(c_641, plain, (![C_166]: (r2_hidden(k1_funct_1('#skF_4', C_166), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_166, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_638])).
% 2.76/1.39  tff(c_643, plain, (![C_169]: (r2_hidden(k1_funct_1('#skF_4', C_169), '#skF_4') | ~r2_hidden(C_169, k1_tarski('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_373, c_641])).
% 2.76/1.39  tff(c_34, plain, (![B_17, A_16]: (~r1_tarski(B_17, A_16) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.76/1.39  tff(c_646, plain, (![C_169]: (~r1_tarski('#skF_4', k1_funct_1('#skF_4', C_169)) | ~r2_hidden(C_169, k1_tarski('#skF_2')))), inference(resolution, [status(thm)], [c_643, c_34])).
% 2.76/1.39  tff(c_650, plain, (![C_170]: (~r2_hidden(C_170, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_370, c_646])).
% 2.76/1.39  tff(c_654, plain, (k1_tarski('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_369, c_650])).
% 2.76/1.39  tff(c_658, plain, $false, inference(negUnitSimplification, [status(thm)], [c_503, c_654])).
% 2.76/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.39  
% 2.76/1.39  Inference rules
% 2.76/1.39  ----------------------
% 2.76/1.39  #Ref     : 0
% 2.76/1.39  #Sup     : 125
% 2.76/1.39  #Fact    : 0
% 2.76/1.39  #Define  : 0
% 2.76/1.39  #Split   : 3
% 2.76/1.39  #Chain   : 0
% 2.76/1.39  #Close   : 0
% 2.76/1.39  
% 2.76/1.39  Ordering : KBO
% 2.76/1.39  
% 2.76/1.39  Simplification rules
% 2.76/1.39  ----------------------
% 2.76/1.39  #Subsume      : 18
% 2.76/1.39  #Demod        : 103
% 2.76/1.39  #Tautology    : 66
% 2.76/1.39  #SimpNegUnit  : 3
% 2.76/1.39  #BackRed      : 19
% 2.76/1.39  
% 2.76/1.39  #Partial instantiations: 0
% 2.76/1.39  #Strategies tried      : 1
% 2.76/1.39  
% 2.76/1.39  Timing (in seconds)
% 2.76/1.39  ----------------------
% 2.76/1.39  Preprocessing        : 0.32
% 2.76/1.39  Parsing              : 0.18
% 2.76/1.39  CNF conversion       : 0.02
% 2.76/1.39  Main loop            : 0.31
% 2.76/1.39  Inferencing          : 0.12
% 2.76/1.39  Reduction            : 0.10
% 2.76/1.39  Demodulation         : 0.07
% 2.76/1.39  BG Simplification    : 0.02
% 2.76/1.39  Subsumption          : 0.06
% 2.76/1.39  Abstraction          : 0.01
% 2.76/1.39  MUC search           : 0.00
% 2.76/1.39  Cooper               : 0.00
% 2.76/1.39  Total                : 0.67
% 2.76/1.39  Index Insertion      : 0.00
% 2.76/1.39  Index Deletion       : 0.00
% 2.76/1.39  Index Matching       : 0.00
% 2.76/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
