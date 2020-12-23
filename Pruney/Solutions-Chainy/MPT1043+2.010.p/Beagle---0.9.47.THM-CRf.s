%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:04 EST 2020

% Result     : Theorem 4.14s
% Output     : CNFRefutation 4.61s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 475 expanded)
%              Number of leaves         :   29 ( 168 expanded)
%              Depth                    :   16
%              Number of atoms          :  249 (1147 expanded)
%              Number of equality atoms :   13 (  59 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => r1_tarski(k5_partfun1(A,B,C),k1_funct_2(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( r2_hidden(D,k5_partfun1(A,B,C))
         => ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B)
        & v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => v1_xboole_0(k5_partfun1(A,B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_partfun1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => r2_hidden(C,k1_funct_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_funct_2)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_44,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => r2_hidden(B,k1_funct_2(A,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_2)).

tff(c_32,plain,(
    ~ r1_tarski(k5_partfun1('#skF_3','#skF_4','#skF_5'),k1_funct_2('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_92,plain,(
    ! [A_40,B_41] :
      ( ~ r2_hidden('#skF_2'(A_40,B_41),B_41)
      | r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_97,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_92])).

tff(c_36,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_136,plain,(
    ! [D_50,A_51,B_52,C_53] :
      ( v1_funct_1(D_50)
      | ~ r2_hidden(D_50,k5_partfun1(A_51,B_52,C_53))
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52)))
      | ~ v1_funct_1(C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_367,plain,(
    ! [A_106,B_107,C_108,B_109] :
      ( v1_funct_1('#skF_2'(k5_partfun1(A_106,B_107,C_108),B_109))
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107)))
      | ~ v1_funct_1(C_108)
      | r1_tarski(k5_partfun1(A_106,B_107,C_108),B_109) ) ),
    inference(resolution,[status(thm)],[c_10,c_136])).

tff(c_369,plain,(
    ! [B_109] :
      ( v1_funct_1('#skF_2'(k5_partfun1('#skF_3','#skF_4','#skF_5'),B_109))
      | ~ v1_funct_1('#skF_5')
      | r1_tarski(k5_partfun1('#skF_3','#skF_4','#skF_5'),B_109) ) ),
    inference(resolution,[status(thm)],[c_34,c_367])).

tff(c_372,plain,(
    ! [B_109] :
      ( v1_funct_1('#skF_2'(k5_partfun1('#skF_3','#skF_4','#skF_5'),B_109))
      | r1_tarski(k5_partfun1('#skF_3','#skF_4','#skF_5'),B_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_369])).

tff(c_98,plain,(
    ! [C_42,B_43,A_44] :
      ( r2_hidden(C_42,B_43)
      | ~ r2_hidden(C_42,A_44)
      | ~ r1_tarski(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_103,plain,(
    ! [A_5,B_6,B_43] :
      ( r2_hidden('#skF_2'(A_5,B_6),B_43)
      | ~ r1_tarski(A_5,B_43)
      | r1_tarski(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_98])).

tff(c_291,plain,(
    ! [D_84,A_85,B_86,C_87] :
      ( v1_funct_2(D_84,A_85,B_86)
      | ~ r2_hidden(D_84,k5_partfun1(A_85,B_86,C_87))
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86)))
      | ~ v1_funct_1(C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_437,plain,(
    ! [A_133,A_132,B_131,C_134,B_130] :
      ( v1_funct_2('#skF_2'(A_132,B_131),A_133,B_130)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_133,B_130)))
      | ~ v1_funct_1(C_134)
      | ~ r1_tarski(A_132,k5_partfun1(A_133,B_130,C_134))
      | r1_tarski(A_132,B_131) ) ),
    inference(resolution,[status(thm)],[c_103,c_291])).

tff(c_441,plain,(
    ! [A_132,B_131] :
      ( v1_funct_2('#skF_2'(A_132,B_131),'#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | ~ r1_tarski(A_132,k5_partfun1('#skF_3','#skF_4','#skF_5'))
      | r1_tarski(A_132,B_131) ) ),
    inference(resolution,[status(thm)],[c_34,c_437])).

tff(c_445,plain,(
    ! [A_132,B_131] :
      ( v1_funct_2('#skF_2'(A_132,B_131),'#skF_3','#skF_4')
      | ~ r1_tarski(A_132,k5_partfun1('#skF_3','#skF_4','#skF_5'))
      | r1_tarski(A_132,B_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_441])).

tff(c_62,plain,(
    ! [A_35,B_36] :
      ( r2_hidden('#skF_2'(A_35,B_36),A_35)
      | r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_71,plain,(
    ! [A_37,B_38] :
      ( ~ v1_xboole_0(A_37)
      | r1_tarski(A_37,B_38) ) ),
    inference(resolution,[status(thm)],[c_62,c_2])).

tff(c_83,plain,(
    ~ v1_xboole_0(k5_partfun1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_71,c_32])).

tff(c_271,plain,(
    ! [A_75,B_76,C_77] :
      ( v1_xboole_0(k5_partfun1(A_75,B_76,C_77))
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76)))
      | ~ v1_funct_1(C_77)
      | ~ v1_xboole_0(B_76)
      | v1_xboole_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_274,plain,
    ( v1_xboole_0(k5_partfun1('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_271])).

tff(c_277,plain,
    ( v1_xboole_0(k5_partfun1('#skF_3','#skF_4','#skF_5'))
    | ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_274])).

tff(c_278,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_277])).

tff(c_279,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_278])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_104,plain,(
    ! [A_1,B_43] :
      ( r2_hidden('#skF_1'(A_1),B_43)
      | ~ r1_tarski(A_1,B_43)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_98])).

tff(c_349,plain,(
    ! [D_99,A_100,B_101,C_102] :
      ( m1_subset_1(D_99,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | ~ r2_hidden(D_99,k5_partfun1(A_100,B_101,C_102))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | ~ v1_funct_1(C_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_447,plain,(
    ! [A_137,A_138,B_139,C_140] :
      ( m1_subset_1('#skF_1'(A_137),k1_zfmisc_1(k2_zfmisc_1(A_138,B_139)))
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139)))
      | ~ v1_funct_1(C_140)
      | ~ r1_tarski(A_137,k5_partfun1(A_138,B_139,C_140))
      | v1_xboole_0(A_137) ) ),
    inference(resolution,[status(thm)],[c_104,c_349])).

tff(c_451,plain,(
    ! [A_137] :
      ( m1_subset_1('#skF_1'(A_137),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_1('#skF_5')
      | ~ r1_tarski(A_137,k5_partfun1('#skF_3','#skF_4','#skF_5'))
      | v1_xboole_0(A_137) ) ),
    inference(resolution,[status(thm)],[c_34,c_447])).

tff(c_497,plain,(
    ! [A_145] :
      ( m1_subset_1('#skF_1'(A_145),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ r1_tarski(A_145,k5_partfun1('#skF_3','#skF_4','#skF_5'))
      | v1_xboole_0(A_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_451])).

tff(c_22,plain,(
    ! [B_18,C_19,A_17] :
      ( k1_xboole_0 = B_18
      | r2_hidden(C_19,k1_funct_2(A_17,B_18))
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18)))
      | ~ v1_funct_2(C_19,A_17,B_18)
      | ~ v1_funct_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_526,plain,(
    ! [A_145] :
      ( k1_xboole_0 = '#skF_4'
      | r2_hidden('#skF_1'(A_145),k1_funct_2('#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_1'(A_145),'#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_1'(A_145))
      | ~ r1_tarski(A_145,k5_partfun1('#skF_3','#skF_4','#skF_5'))
      | v1_xboole_0(A_145) ) ),
    inference(resolution,[status(thm)],[c_497,c_22])).

tff(c_546,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_526])).

tff(c_12,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_51,plain,(
    ! [B_32,A_33] :
      ( ~ r1_tarski(B_32,A_33)
      | ~ r2_hidden(A_33,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_56,plain,(
    ! [A_34] :
      ( ~ r1_tarski(A_34,'#skF_1'(A_34))
      | v1_xboole_0(A_34) ) ),
    inference(resolution,[status(thm)],[c_4,c_51])).

tff(c_61,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_56])).

tff(c_552,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_61])).

tff(c_556,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_279,c_552])).

tff(c_558,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_526])).

tff(c_572,plain,(
    ! [B_152,A_154,A_153,B_151,C_150] :
      ( m1_subset_1('#skF_2'(A_153,B_152),k1_zfmisc_1(k2_zfmisc_1(A_154,B_151)))
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_154,B_151)))
      | ~ v1_funct_1(C_150)
      | ~ r1_tarski(A_153,k5_partfun1(A_154,B_151,C_150))
      | r1_tarski(A_153,B_152) ) ),
    inference(resolution,[status(thm)],[c_103,c_349])).

tff(c_580,plain,(
    ! [A_153,B_152] :
      ( m1_subset_1('#skF_2'(A_153,B_152),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_1('#skF_5')
      | ~ r1_tarski(A_153,k5_partfun1('#skF_3','#skF_4','#skF_5'))
      | r1_tarski(A_153,B_152) ) ),
    inference(resolution,[status(thm)],[c_34,c_572])).

tff(c_587,plain,(
    ! [A_155,B_156] :
      ( m1_subset_1('#skF_2'(A_155,B_156),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ r1_tarski(A_155,k5_partfun1('#skF_3','#skF_4','#skF_5'))
      | r1_tarski(A_155,B_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_580])).

tff(c_607,plain,(
    ! [A_155,B_156] :
      ( k1_xboole_0 = '#skF_4'
      | r2_hidden('#skF_2'(A_155,B_156),k1_funct_2('#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_2'(A_155,B_156),'#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_2'(A_155,B_156))
      | ~ r1_tarski(A_155,k5_partfun1('#skF_3','#skF_4','#skF_5'))
      | r1_tarski(A_155,B_156) ) ),
    inference(resolution,[status(thm)],[c_587,c_22])).

tff(c_759,plain,(
    ! [A_183,B_184] :
      ( r2_hidden('#skF_2'(A_183,B_184),k1_funct_2('#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_2'(A_183,B_184),'#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_2'(A_183,B_184))
      | ~ r1_tarski(A_183,k5_partfun1('#skF_3','#skF_4','#skF_5'))
      | r1_tarski(A_183,B_184) ) ),
    inference(negUnitSimplification,[status(thm)],[c_558,c_607])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_776,plain,(
    ! [A_185] :
      ( ~ v1_funct_2('#skF_2'(A_185,k1_funct_2('#skF_3','#skF_4')),'#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_2'(A_185,k1_funct_2('#skF_3','#skF_4')))
      | ~ r1_tarski(A_185,k5_partfun1('#skF_3','#skF_4','#skF_5'))
      | r1_tarski(A_185,k1_funct_2('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_759,c_8])).

tff(c_799,plain,(
    ! [A_188] :
      ( ~ v1_funct_1('#skF_2'(A_188,k1_funct_2('#skF_3','#skF_4')))
      | ~ r1_tarski(A_188,k5_partfun1('#skF_3','#skF_4','#skF_5'))
      | r1_tarski(A_188,k1_funct_2('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_445,c_776])).

tff(c_807,plain,
    ( ~ r1_tarski(k5_partfun1('#skF_3','#skF_4','#skF_5'),k5_partfun1('#skF_3','#skF_4','#skF_5'))
    | r1_tarski(k5_partfun1('#skF_3','#skF_4','#skF_5'),k1_funct_2('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_372,c_799])).

tff(c_811,plain,(
    r1_tarski(k5_partfun1('#skF_3','#skF_4','#skF_5'),k1_funct_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_807])).

tff(c_813,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_811])).

tff(c_815,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_278])).

tff(c_14,plain,(
    ! [A_11] :
      ( k1_xboole_0 = A_11
      | ~ r1_tarski(A_11,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_85,plain,(
    ! [A_37] :
      ( k1_xboole_0 = A_37
      | ~ v1_xboole_0(A_37) ) ),
    inference(resolution,[status(thm)],[c_71,c_14])).

tff(c_823,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_815,c_85])).

tff(c_814,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_278])).

tff(c_819,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_814,c_85])).

tff(c_836,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_823,c_819])).

tff(c_843,plain,(
    ~ r1_tarski(k5_partfun1('#skF_4','#skF_4','#skF_5'),k1_funct_2('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_836,c_836,c_32])).

tff(c_844,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_836,c_34])).

tff(c_1060,plain,(
    ! [A_225,B_226,C_227,B_228] :
      ( v1_funct_1('#skF_2'(k5_partfun1(A_225,B_226,C_227),B_228))
      | ~ m1_subset_1(C_227,k1_zfmisc_1(k2_zfmisc_1(A_225,B_226)))
      | ~ v1_funct_1(C_227)
      | r1_tarski(k5_partfun1(A_225,B_226,C_227),B_228) ) ),
    inference(resolution,[status(thm)],[c_10,c_136])).

tff(c_1062,plain,(
    ! [B_228] :
      ( v1_funct_1('#skF_2'(k5_partfun1('#skF_4','#skF_4','#skF_5'),B_228))
      | ~ v1_funct_1('#skF_5')
      | r1_tarski(k5_partfun1('#skF_4','#skF_4','#skF_5'),B_228) ) ),
    inference(resolution,[status(thm)],[c_844,c_1060])).

tff(c_1065,plain,(
    ! [B_228] :
      ( v1_funct_1('#skF_2'(k5_partfun1('#skF_4','#skF_4','#skF_5'),B_228))
      | r1_tarski(k5_partfun1('#skF_4','#skF_4','#skF_5'),B_228) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1062])).

tff(c_966,plain,(
    ! [D_197,A_198,B_199,C_200] :
      ( v1_funct_2(D_197,A_198,B_199)
      | ~ r2_hidden(D_197,k5_partfun1(A_198,B_199,C_200))
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_198,B_199)))
      | ~ v1_funct_1(C_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1234,plain,(
    ! [B_261,A_263,C_264,A_262,B_260] :
      ( v1_funct_2('#skF_2'(A_262,B_260),A_263,B_261)
      | ~ m1_subset_1(C_264,k1_zfmisc_1(k2_zfmisc_1(A_263,B_261)))
      | ~ v1_funct_1(C_264)
      | ~ r1_tarski(A_262,k5_partfun1(A_263,B_261,C_264))
      | r1_tarski(A_262,B_260) ) ),
    inference(resolution,[status(thm)],[c_103,c_966])).

tff(c_1242,plain,(
    ! [A_262,B_260] :
      ( v1_funct_2('#skF_2'(A_262,B_260),'#skF_4','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | ~ r1_tarski(A_262,k5_partfun1('#skF_4','#skF_4','#skF_5'))
      | r1_tarski(A_262,B_260) ) ),
    inference(resolution,[status(thm)],[c_844,c_1234])).

tff(c_1248,plain,(
    ! [A_262,B_260] :
      ( v1_funct_2('#skF_2'(A_262,B_260),'#skF_4','#skF_4')
      | ~ r1_tarski(A_262,k5_partfun1('#skF_4','#skF_4','#skF_5'))
      | r1_tarski(A_262,B_260) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1242])).

tff(c_1042,plain,(
    ! [D_218,A_219,B_220,C_221] :
      ( m1_subset_1(D_218,k1_zfmisc_1(k2_zfmisc_1(A_219,B_220)))
      | ~ r2_hidden(D_218,k5_partfun1(A_219,B_220,C_221))
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(A_219,B_220)))
      | ~ v1_funct_1(C_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1267,plain,(
    ! [A_269,A_272,C_270,B_271,B_273] :
      ( m1_subset_1('#skF_2'(A_272,B_271),k1_zfmisc_1(k2_zfmisc_1(A_269,B_273)))
      | ~ m1_subset_1(C_270,k1_zfmisc_1(k2_zfmisc_1(A_269,B_273)))
      | ~ v1_funct_1(C_270)
      | ~ r1_tarski(A_272,k5_partfun1(A_269,B_273,C_270))
      | r1_tarski(A_272,B_271) ) ),
    inference(resolution,[status(thm)],[c_103,c_1042])).

tff(c_1275,plain,(
    ! [A_272,B_271] :
      ( m1_subset_1('#skF_2'(A_272,B_271),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
      | ~ v1_funct_1('#skF_5')
      | ~ r1_tarski(A_272,k5_partfun1('#skF_4','#skF_4','#skF_5'))
      | r1_tarski(A_272,B_271) ) ),
    inference(resolution,[status(thm)],[c_844,c_1267])).

tff(c_1282,plain,(
    ! [A_274,B_275] :
      ( m1_subset_1('#skF_2'(A_274,B_275),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
      | ~ r1_tarski(A_274,k5_partfun1('#skF_4','#skF_4','#skF_5'))
      | r1_tarski(A_274,B_275) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1275])).

tff(c_24,plain,(
    ! [B_21,A_20] :
      ( r2_hidden(B_21,k1_funct_2(A_20,A_20))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ v1_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1459,plain,(
    ! [A_302,B_303] :
      ( r2_hidden('#skF_2'(A_302,B_303),k1_funct_2('#skF_4','#skF_4'))
      | ~ v1_funct_2('#skF_2'(A_302,B_303),'#skF_4','#skF_4')
      | ~ v1_funct_1('#skF_2'(A_302,B_303))
      | ~ r1_tarski(A_302,k5_partfun1('#skF_4','#skF_4','#skF_5'))
      | r1_tarski(A_302,B_303) ) ),
    inference(resolution,[status(thm)],[c_1282,c_24])).

tff(c_1476,plain,(
    ! [A_304] :
      ( ~ v1_funct_2('#skF_2'(A_304,k1_funct_2('#skF_4','#skF_4')),'#skF_4','#skF_4')
      | ~ v1_funct_1('#skF_2'(A_304,k1_funct_2('#skF_4','#skF_4')))
      | ~ r1_tarski(A_304,k5_partfun1('#skF_4','#skF_4','#skF_5'))
      | r1_tarski(A_304,k1_funct_2('#skF_4','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1459,c_8])).

tff(c_1499,plain,(
    ! [A_307] :
      ( ~ v1_funct_1('#skF_2'(A_307,k1_funct_2('#skF_4','#skF_4')))
      | ~ r1_tarski(A_307,k5_partfun1('#skF_4','#skF_4','#skF_5'))
      | r1_tarski(A_307,k1_funct_2('#skF_4','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1248,c_1476])).

tff(c_1507,plain,
    ( ~ r1_tarski(k5_partfun1('#skF_4','#skF_4','#skF_5'),k5_partfun1('#skF_4','#skF_4','#skF_5'))
    | r1_tarski(k5_partfun1('#skF_4','#skF_4','#skF_5'),k1_funct_2('#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_1065,c_1499])).

tff(c_1511,plain,(
    r1_tarski(k5_partfun1('#skF_4','#skF_4','#skF_5'),k1_funct_2('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_1507])).

tff(c_1513,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_843,c_1511])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 18:22:16 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.14/1.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.49/1.79  
% 4.49/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.49/1.79  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 4.49/1.79  
% 4.49/1.79  %Foreground sorts:
% 4.49/1.79  
% 4.49/1.79  
% 4.49/1.79  %Background operators:
% 4.49/1.79  
% 4.49/1.79  
% 4.49/1.79  %Foreground operators:
% 4.49/1.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.49/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.49/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.49/1.79  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.49/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.49/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.49/1.79  tff('#skF_5', type, '#skF_5': $i).
% 4.49/1.79  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.49/1.79  tff('#skF_3', type, '#skF_3': $i).
% 4.49/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.49/1.79  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 4.49/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.49/1.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.49/1.79  tff('#skF_4', type, '#skF_4': $i).
% 4.49/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.49/1.79  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.49/1.79  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 4.49/1.79  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.49/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.49/1.79  
% 4.61/1.82  tff(f_100, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r1_tarski(k5_partfun1(A, B, C), k1_funct_2(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t159_funct_2)).
% 4.61/1.82  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.61/1.82  tff(f_93, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (r2_hidden(D, k5_partfun1(A, B, C)) => ((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_2)).
% 4.61/1.82  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.61/1.82  tff(f_60, axiom, (![A, B, C]: ((((~v1_xboole_0(A) & v1_xboole_0(B)) & v1_funct_1(C)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => v1_xboole_0(k5_partfun1(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_partfun1)).
% 4.61/1.82  tff(f_72, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => r2_hidden(C, k1_funct_2(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_funct_2)).
% 4.61/1.82  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.61/1.82  tff(f_49, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.61/1.82  tff(f_44, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 4.61/1.82  tff(f_80, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => r2_hidden(B, k1_funct_2(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_2)).
% 4.61/1.82  tff(c_32, plain, (~r1_tarski(k5_partfun1('#skF_3', '#skF_4', '#skF_5'), k1_funct_2('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.61/1.82  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.61/1.82  tff(c_92, plain, (![A_40, B_41]: (~r2_hidden('#skF_2'(A_40, B_41), B_41) | r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.61/1.82  tff(c_97, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_92])).
% 4.61/1.82  tff(c_36, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.61/1.82  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.61/1.82  tff(c_136, plain, (![D_50, A_51, B_52, C_53]: (v1_funct_1(D_50) | ~r2_hidden(D_50, k5_partfun1(A_51, B_52, C_53)) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))) | ~v1_funct_1(C_53))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.61/1.82  tff(c_367, plain, (![A_106, B_107, C_108, B_109]: (v1_funct_1('#skF_2'(k5_partfun1(A_106, B_107, C_108), B_109)) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))) | ~v1_funct_1(C_108) | r1_tarski(k5_partfun1(A_106, B_107, C_108), B_109))), inference(resolution, [status(thm)], [c_10, c_136])).
% 4.61/1.82  tff(c_369, plain, (![B_109]: (v1_funct_1('#skF_2'(k5_partfun1('#skF_3', '#skF_4', '#skF_5'), B_109)) | ~v1_funct_1('#skF_5') | r1_tarski(k5_partfun1('#skF_3', '#skF_4', '#skF_5'), B_109))), inference(resolution, [status(thm)], [c_34, c_367])).
% 4.61/1.82  tff(c_372, plain, (![B_109]: (v1_funct_1('#skF_2'(k5_partfun1('#skF_3', '#skF_4', '#skF_5'), B_109)) | r1_tarski(k5_partfun1('#skF_3', '#skF_4', '#skF_5'), B_109))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_369])).
% 4.61/1.82  tff(c_98, plain, (![C_42, B_43, A_44]: (r2_hidden(C_42, B_43) | ~r2_hidden(C_42, A_44) | ~r1_tarski(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.61/1.82  tff(c_103, plain, (![A_5, B_6, B_43]: (r2_hidden('#skF_2'(A_5, B_6), B_43) | ~r1_tarski(A_5, B_43) | r1_tarski(A_5, B_6))), inference(resolution, [status(thm)], [c_10, c_98])).
% 4.61/1.82  tff(c_291, plain, (![D_84, A_85, B_86, C_87]: (v1_funct_2(D_84, A_85, B_86) | ~r2_hidden(D_84, k5_partfun1(A_85, B_86, C_87)) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))) | ~v1_funct_1(C_87))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.61/1.82  tff(c_437, plain, (![A_133, A_132, B_131, C_134, B_130]: (v1_funct_2('#skF_2'(A_132, B_131), A_133, B_130) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_133, B_130))) | ~v1_funct_1(C_134) | ~r1_tarski(A_132, k5_partfun1(A_133, B_130, C_134)) | r1_tarski(A_132, B_131))), inference(resolution, [status(thm)], [c_103, c_291])).
% 4.61/1.82  tff(c_441, plain, (![A_132, B_131]: (v1_funct_2('#skF_2'(A_132, B_131), '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | ~r1_tarski(A_132, k5_partfun1('#skF_3', '#skF_4', '#skF_5')) | r1_tarski(A_132, B_131))), inference(resolution, [status(thm)], [c_34, c_437])).
% 4.61/1.82  tff(c_445, plain, (![A_132, B_131]: (v1_funct_2('#skF_2'(A_132, B_131), '#skF_3', '#skF_4') | ~r1_tarski(A_132, k5_partfun1('#skF_3', '#skF_4', '#skF_5')) | r1_tarski(A_132, B_131))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_441])).
% 4.61/1.82  tff(c_62, plain, (![A_35, B_36]: (r2_hidden('#skF_2'(A_35, B_36), A_35) | r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.61/1.82  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.61/1.82  tff(c_71, plain, (![A_37, B_38]: (~v1_xboole_0(A_37) | r1_tarski(A_37, B_38))), inference(resolution, [status(thm)], [c_62, c_2])).
% 4.61/1.82  tff(c_83, plain, (~v1_xboole_0(k5_partfun1('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_71, c_32])).
% 4.61/1.82  tff(c_271, plain, (![A_75, B_76, C_77]: (v1_xboole_0(k5_partfun1(A_75, B_76, C_77)) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))) | ~v1_funct_1(C_77) | ~v1_xboole_0(B_76) | v1_xboole_0(A_75))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.61/1.82  tff(c_274, plain, (v1_xboole_0(k5_partfun1('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_271])).
% 4.61/1.82  tff(c_277, plain, (v1_xboole_0(k5_partfun1('#skF_3', '#skF_4', '#skF_5')) | ~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_274])).
% 4.61/1.82  tff(c_278, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_83, c_277])).
% 4.61/1.82  tff(c_279, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_278])).
% 4.61/1.82  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.61/1.82  tff(c_104, plain, (![A_1, B_43]: (r2_hidden('#skF_1'(A_1), B_43) | ~r1_tarski(A_1, B_43) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_98])).
% 4.61/1.82  tff(c_349, plain, (![D_99, A_100, B_101, C_102]: (m1_subset_1(D_99, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))) | ~r2_hidden(D_99, k5_partfun1(A_100, B_101, C_102)) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))) | ~v1_funct_1(C_102))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.61/1.82  tff(c_447, plain, (![A_137, A_138, B_139, C_140]: (m1_subset_1('#skF_1'(A_137), k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))) | ~v1_funct_1(C_140) | ~r1_tarski(A_137, k5_partfun1(A_138, B_139, C_140)) | v1_xboole_0(A_137))), inference(resolution, [status(thm)], [c_104, c_349])).
% 4.61/1.82  tff(c_451, plain, (![A_137]: (m1_subset_1('#skF_1'(A_137), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_5') | ~r1_tarski(A_137, k5_partfun1('#skF_3', '#skF_4', '#skF_5')) | v1_xboole_0(A_137))), inference(resolution, [status(thm)], [c_34, c_447])).
% 4.61/1.82  tff(c_497, plain, (![A_145]: (m1_subset_1('#skF_1'(A_145), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~r1_tarski(A_145, k5_partfun1('#skF_3', '#skF_4', '#skF_5')) | v1_xboole_0(A_145))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_451])).
% 4.61/1.82  tff(c_22, plain, (![B_18, C_19, A_17]: (k1_xboole_0=B_18 | r2_hidden(C_19, k1_funct_2(A_17, B_18)) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))) | ~v1_funct_2(C_19, A_17, B_18) | ~v1_funct_1(C_19))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.61/1.82  tff(c_526, plain, (![A_145]: (k1_xboole_0='#skF_4' | r2_hidden('#skF_1'(A_145), k1_funct_2('#skF_3', '#skF_4')) | ~v1_funct_2('#skF_1'(A_145), '#skF_3', '#skF_4') | ~v1_funct_1('#skF_1'(A_145)) | ~r1_tarski(A_145, k5_partfun1('#skF_3', '#skF_4', '#skF_5')) | v1_xboole_0(A_145))), inference(resolution, [status(thm)], [c_497, c_22])).
% 4.61/1.82  tff(c_546, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_526])).
% 4.61/1.82  tff(c_12, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.61/1.82  tff(c_51, plain, (![B_32, A_33]: (~r1_tarski(B_32, A_33) | ~r2_hidden(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.61/1.82  tff(c_56, plain, (![A_34]: (~r1_tarski(A_34, '#skF_1'(A_34)) | v1_xboole_0(A_34))), inference(resolution, [status(thm)], [c_4, c_51])).
% 4.61/1.82  tff(c_61, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_56])).
% 4.61/1.82  tff(c_552, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_546, c_61])).
% 4.61/1.82  tff(c_556, plain, $false, inference(negUnitSimplification, [status(thm)], [c_279, c_552])).
% 4.61/1.82  tff(c_558, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_526])).
% 4.61/1.82  tff(c_572, plain, (![B_152, A_154, A_153, B_151, C_150]: (m1_subset_1('#skF_2'(A_153, B_152), k1_zfmisc_1(k2_zfmisc_1(A_154, B_151))) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_154, B_151))) | ~v1_funct_1(C_150) | ~r1_tarski(A_153, k5_partfun1(A_154, B_151, C_150)) | r1_tarski(A_153, B_152))), inference(resolution, [status(thm)], [c_103, c_349])).
% 4.61/1.82  tff(c_580, plain, (![A_153, B_152]: (m1_subset_1('#skF_2'(A_153, B_152), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_5') | ~r1_tarski(A_153, k5_partfun1('#skF_3', '#skF_4', '#skF_5')) | r1_tarski(A_153, B_152))), inference(resolution, [status(thm)], [c_34, c_572])).
% 4.61/1.82  tff(c_587, plain, (![A_155, B_156]: (m1_subset_1('#skF_2'(A_155, B_156), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~r1_tarski(A_155, k5_partfun1('#skF_3', '#skF_4', '#skF_5')) | r1_tarski(A_155, B_156))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_580])).
% 4.61/1.82  tff(c_607, plain, (![A_155, B_156]: (k1_xboole_0='#skF_4' | r2_hidden('#skF_2'(A_155, B_156), k1_funct_2('#skF_3', '#skF_4')) | ~v1_funct_2('#skF_2'(A_155, B_156), '#skF_3', '#skF_4') | ~v1_funct_1('#skF_2'(A_155, B_156)) | ~r1_tarski(A_155, k5_partfun1('#skF_3', '#skF_4', '#skF_5')) | r1_tarski(A_155, B_156))), inference(resolution, [status(thm)], [c_587, c_22])).
% 4.61/1.82  tff(c_759, plain, (![A_183, B_184]: (r2_hidden('#skF_2'(A_183, B_184), k1_funct_2('#skF_3', '#skF_4')) | ~v1_funct_2('#skF_2'(A_183, B_184), '#skF_3', '#skF_4') | ~v1_funct_1('#skF_2'(A_183, B_184)) | ~r1_tarski(A_183, k5_partfun1('#skF_3', '#skF_4', '#skF_5')) | r1_tarski(A_183, B_184))), inference(negUnitSimplification, [status(thm)], [c_558, c_607])).
% 4.61/1.82  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.61/1.82  tff(c_776, plain, (![A_185]: (~v1_funct_2('#skF_2'(A_185, k1_funct_2('#skF_3', '#skF_4')), '#skF_3', '#skF_4') | ~v1_funct_1('#skF_2'(A_185, k1_funct_2('#skF_3', '#skF_4'))) | ~r1_tarski(A_185, k5_partfun1('#skF_3', '#skF_4', '#skF_5')) | r1_tarski(A_185, k1_funct_2('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_759, c_8])).
% 4.61/1.82  tff(c_799, plain, (![A_188]: (~v1_funct_1('#skF_2'(A_188, k1_funct_2('#skF_3', '#skF_4'))) | ~r1_tarski(A_188, k5_partfun1('#skF_3', '#skF_4', '#skF_5')) | r1_tarski(A_188, k1_funct_2('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_445, c_776])).
% 4.61/1.82  tff(c_807, plain, (~r1_tarski(k5_partfun1('#skF_3', '#skF_4', '#skF_5'), k5_partfun1('#skF_3', '#skF_4', '#skF_5')) | r1_tarski(k5_partfun1('#skF_3', '#skF_4', '#skF_5'), k1_funct_2('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_372, c_799])).
% 4.61/1.82  tff(c_811, plain, (r1_tarski(k5_partfun1('#skF_3', '#skF_4', '#skF_5'), k1_funct_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_807])).
% 4.61/1.82  tff(c_813, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_811])).
% 4.61/1.82  tff(c_815, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_278])).
% 4.61/1.82  tff(c_14, plain, (![A_11]: (k1_xboole_0=A_11 | ~r1_tarski(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.61/1.82  tff(c_85, plain, (![A_37]: (k1_xboole_0=A_37 | ~v1_xboole_0(A_37))), inference(resolution, [status(thm)], [c_71, c_14])).
% 4.61/1.82  tff(c_823, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_815, c_85])).
% 4.61/1.82  tff(c_814, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_278])).
% 4.61/1.82  tff(c_819, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_814, c_85])).
% 4.61/1.82  tff(c_836, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_823, c_819])).
% 4.61/1.82  tff(c_843, plain, (~r1_tarski(k5_partfun1('#skF_4', '#skF_4', '#skF_5'), k1_funct_2('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_836, c_836, c_32])).
% 4.61/1.82  tff(c_844, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_836, c_34])).
% 4.61/1.82  tff(c_1060, plain, (![A_225, B_226, C_227, B_228]: (v1_funct_1('#skF_2'(k5_partfun1(A_225, B_226, C_227), B_228)) | ~m1_subset_1(C_227, k1_zfmisc_1(k2_zfmisc_1(A_225, B_226))) | ~v1_funct_1(C_227) | r1_tarski(k5_partfun1(A_225, B_226, C_227), B_228))), inference(resolution, [status(thm)], [c_10, c_136])).
% 4.61/1.82  tff(c_1062, plain, (![B_228]: (v1_funct_1('#skF_2'(k5_partfun1('#skF_4', '#skF_4', '#skF_5'), B_228)) | ~v1_funct_1('#skF_5') | r1_tarski(k5_partfun1('#skF_4', '#skF_4', '#skF_5'), B_228))), inference(resolution, [status(thm)], [c_844, c_1060])).
% 4.61/1.82  tff(c_1065, plain, (![B_228]: (v1_funct_1('#skF_2'(k5_partfun1('#skF_4', '#skF_4', '#skF_5'), B_228)) | r1_tarski(k5_partfun1('#skF_4', '#skF_4', '#skF_5'), B_228))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1062])).
% 4.61/1.82  tff(c_966, plain, (![D_197, A_198, B_199, C_200]: (v1_funct_2(D_197, A_198, B_199) | ~r2_hidden(D_197, k5_partfun1(A_198, B_199, C_200)) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_198, B_199))) | ~v1_funct_1(C_200))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.61/1.82  tff(c_1234, plain, (![B_261, A_263, C_264, A_262, B_260]: (v1_funct_2('#skF_2'(A_262, B_260), A_263, B_261) | ~m1_subset_1(C_264, k1_zfmisc_1(k2_zfmisc_1(A_263, B_261))) | ~v1_funct_1(C_264) | ~r1_tarski(A_262, k5_partfun1(A_263, B_261, C_264)) | r1_tarski(A_262, B_260))), inference(resolution, [status(thm)], [c_103, c_966])).
% 4.61/1.82  tff(c_1242, plain, (![A_262, B_260]: (v1_funct_2('#skF_2'(A_262, B_260), '#skF_4', '#skF_4') | ~v1_funct_1('#skF_5') | ~r1_tarski(A_262, k5_partfun1('#skF_4', '#skF_4', '#skF_5')) | r1_tarski(A_262, B_260))), inference(resolution, [status(thm)], [c_844, c_1234])).
% 4.61/1.82  tff(c_1248, plain, (![A_262, B_260]: (v1_funct_2('#skF_2'(A_262, B_260), '#skF_4', '#skF_4') | ~r1_tarski(A_262, k5_partfun1('#skF_4', '#skF_4', '#skF_5')) | r1_tarski(A_262, B_260))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1242])).
% 4.61/1.82  tff(c_1042, plain, (![D_218, A_219, B_220, C_221]: (m1_subset_1(D_218, k1_zfmisc_1(k2_zfmisc_1(A_219, B_220))) | ~r2_hidden(D_218, k5_partfun1(A_219, B_220, C_221)) | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(A_219, B_220))) | ~v1_funct_1(C_221))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.61/1.82  tff(c_1267, plain, (![A_269, A_272, C_270, B_271, B_273]: (m1_subset_1('#skF_2'(A_272, B_271), k1_zfmisc_1(k2_zfmisc_1(A_269, B_273))) | ~m1_subset_1(C_270, k1_zfmisc_1(k2_zfmisc_1(A_269, B_273))) | ~v1_funct_1(C_270) | ~r1_tarski(A_272, k5_partfun1(A_269, B_273, C_270)) | r1_tarski(A_272, B_271))), inference(resolution, [status(thm)], [c_103, c_1042])).
% 4.61/1.82  tff(c_1275, plain, (![A_272, B_271]: (m1_subset_1('#skF_2'(A_272, B_271), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~v1_funct_1('#skF_5') | ~r1_tarski(A_272, k5_partfun1('#skF_4', '#skF_4', '#skF_5')) | r1_tarski(A_272, B_271))), inference(resolution, [status(thm)], [c_844, c_1267])).
% 4.61/1.82  tff(c_1282, plain, (![A_274, B_275]: (m1_subset_1('#skF_2'(A_274, B_275), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~r1_tarski(A_274, k5_partfun1('#skF_4', '#skF_4', '#skF_5')) | r1_tarski(A_274, B_275))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1275])).
% 4.61/1.82  tff(c_24, plain, (![B_21, A_20]: (r2_hidden(B_21, k1_funct_2(A_20, A_20)) | ~m1_subset_1(B_21, k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~v1_funct_2(B_21, A_20, A_20) | ~v1_funct_1(B_21))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.61/1.82  tff(c_1459, plain, (![A_302, B_303]: (r2_hidden('#skF_2'(A_302, B_303), k1_funct_2('#skF_4', '#skF_4')) | ~v1_funct_2('#skF_2'(A_302, B_303), '#skF_4', '#skF_4') | ~v1_funct_1('#skF_2'(A_302, B_303)) | ~r1_tarski(A_302, k5_partfun1('#skF_4', '#skF_4', '#skF_5')) | r1_tarski(A_302, B_303))), inference(resolution, [status(thm)], [c_1282, c_24])).
% 4.61/1.82  tff(c_1476, plain, (![A_304]: (~v1_funct_2('#skF_2'(A_304, k1_funct_2('#skF_4', '#skF_4')), '#skF_4', '#skF_4') | ~v1_funct_1('#skF_2'(A_304, k1_funct_2('#skF_4', '#skF_4'))) | ~r1_tarski(A_304, k5_partfun1('#skF_4', '#skF_4', '#skF_5')) | r1_tarski(A_304, k1_funct_2('#skF_4', '#skF_4')))), inference(resolution, [status(thm)], [c_1459, c_8])).
% 4.61/1.82  tff(c_1499, plain, (![A_307]: (~v1_funct_1('#skF_2'(A_307, k1_funct_2('#skF_4', '#skF_4'))) | ~r1_tarski(A_307, k5_partfun1('#skF_4', '#skF_4', '#skF_5')) | r1_tarski(A_307, k1_funct_2('#skF_4', '#skF_4')))), inference(resolution, [status(thm)], [c_1248, c_1476])).
% 4.61/1.82  tff(c_1507, plain, (~r1_tarski(k5_partfun1('#skF_4', '#skF_4', '#skF_5'), k5_partfun1('#skF_4', '#skF_4', '#skF_5')) | r1_tarski(k5_partfun1('#skF_4', '#skF_4', '#skF_5'), k1_funct_2('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_1065, c_1499])).
% 4.61/1.82  tff(c_1511, plain, (r1_tarski(k5_partfun1('#skF_4', '#skF_4', '#skF_5'), k1_funct_2('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_1507])).
% 4.61/1.82  tff(c_1513, plain, $false, inference(negUnitSimplification, [status(thm)], [c_843, c_1511])).
% 4.61/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.61/1.82  
% 4.61/1.82  Inference rules
% 4.61/1.82  ----------------------
% 4.61/1.82  #Ref     : 0
% 4.61/1.82  #Sup     : 314
% 4.61/1.82  #Fact    : 0
% 4.61/1.82  #Define  : 0
% 4.61/1.82  #Split   : 10
% 4.61/1.82  #Chain   : 0
% 4.61/1.82  #Close   : 0
% 4.61/1.82  
% 4.61/1.82  Ordering : KBO
% 4.61/1.82  
% 4.61/1.82  Simplification rules
% 4.61/1.82  ----------------------
% 4.61/1.82  #Subsume      : 66
% 4.61/1.82  #Demod        : 98
% 4.61/1.82  #Tautology    : 63
% 4.61/1.82  #SimpNegUnit  : 10
% 4.61/1.82  #BackRed      : 20
% 4.61/1.82  
% 4.61/1.82  #Partial instantiations: 0
% 4.61/1.82  #Strategies tried      : 1
% 4.61/1.82  
% 4.61/1.82  Timing (in seconds)
% 4.61/1.82  ----------------------
% 4.61/1.82  Preprocessing        : 0.31
% 4.61/1.82  Parsing              : 0.18
% 4.61/1.82  CNF conversion       : 0.02
% 4.61/1.82  Main loop            : 0.68
% 4.61/1.82  Inferencing          : 0.25
% 4.61/1.82  Reduction            : 0.18
% 4.61/1.82  Demodulation         : 0.12
% 4.61/1.82  BG Simplification    : 0.03
% 4.61/1.82  Subsumption          : 0.17
% 4.61/1.82  Abstraction          : 0.03
% 4.61/1.82  MUC search           : 0.00
% 4.61/1.82  Cooper               : 0.00
% 4.61/1.82  Total                : 1.04
% 4.61/1.82  Index Insertion      : 0.00
% 4.61/1.82  Index Deletion       : 0.00
% 4.61/1.82  Index Matching       : 0.00
% 4.61/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
