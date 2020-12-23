%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:32 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 161 expanded)
%              Number of leaves         :   42 (  72 expanded)
%              Depth                    :   13
%              Number of atoms          :  144 ( 324 expanded)
%              Number of equality atoms :   60 ( 134 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_42,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_125,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_66,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_113,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_87,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_14,plain,(
    ! [A_12] : ~ v1_xboole_0(k1_tarski(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_128,plain,(
    ! [C_56,A_57,B_58] :
      ( v1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_132,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_128])).

tff(c_36,plain,(
    ! [A_18] :
      ( k1_relat_1(A_18) != k1_xboole_0
      | k1_xboole_0 = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_139,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_132,c_36])).

tff(c_141,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_198,plain,(
    ! [B_76,A_77] :
      ( k1_tarski(k1_funct_1(B_76,A_77)) = k2_relat_1(B_76)
      | k1_tarski(A_77) != k1_relat_1(B_76)
      | ~ v1_funct_1(B_76)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_188,plain,(
    ! [A_73,B_74,C_75] :
      ( k2_relset_1(A_73,B_74,C_75) = k2_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_192,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_188])).

tff(c_52,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') != k1_tarski(k1_funct_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_193,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_52])).

tff(c_204,plain,
    ( k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_193])).

tff(c_225,plain,(
    k1_tarski('#skF_2') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_60,c_204])).

tff(c_148,plain,(
    ! [C_62,A_63,B_64] :
      ( v4_relat_1(C_62,A_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_152,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_56,c_148])).

tff(c_28,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_240,plain,(
    ! [B_82,C_83,A_84] :
      ( k2_tarski(B_82,C_83) = A_84
      | k1_tarski(C_83) = A_84
      | k1_tarski(B_82) = A_84
      | k1_xboole_0 = A_84
      | ~ r1_tarski(A_84,k2_tarski(B_82,C_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_256,plain,(
    ! [A_6,A_84] :
      ( k2_tarski(A_6,A_6) = A_84
      | k1_tarski(A_6) = A_84
      | k1_tarski(A_6) = A_84
      | k1_xboole_0 = A_84
      | ~ r1_tarski(A_84,k1_tarski(A_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_240])).

tff(c_271,plain,(
    ! [A_85,A_86] :
      ( k1_tarski(A_85) = A_86
      | k1_tarski(A_85) = A_86
      | k1_tarski(A_85) = A_86
      | k1_xboole_0 = A_86
      | ~ r1_tarski(A_86,k1_tarski(A_85)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_256])).

tff(c_295,plain,(
    ! [A_87,B_88] :
      ( k1_tarski(A_87) = k1_relat_1(B_88)
      | k1_relat_1(B_88) = k1_xboole_0
      | ~ v4_relat_1(B_88,k1_tarski(A_87))
      | ~ v1_relat_1(B_88) ) ),
    inference(resolution,[status(thm)],[c_28,c_271])).

tff(c_301,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_152,c_295])).

tff(c_304,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_301])).

tff(c_306,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_225,c_304])).

tff(c_307,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_312,plain,(
    ! [A_5] : r1_tarski('#skF_4',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_6])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_315,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_54])).

tff(c_58,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_30,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_314,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_307,c_30])).

tff(c_409,plain,(
    ! [A_107,B_108,C_109] :
      ( k2_relset_1(A_107,B_108,C_109) = k2_relat_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_412,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_409])).

tff(c_414,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_412])).

tff(c_50,plain,(
    ! [D_35,C_34,A_32,B_33] :
      ( r2_hidden(k1_funct_1(D_35,C_34),k2_relset_1(A_32,B_33,D_35))
      | k1_xboole_0 = B_33
      | ~ r2_hidden(C_34,A_32)
      | ~ m1_subset_1(D_35,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | ~ v1_funct_2(D_35,A_32,B_33)
      | ~ v1_funct_1(D_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_543,plain,(
    ! [D_126,C_127,A_128,B_129] :
      ( r2_hidden(k1_funct_1(D_126,C_127),k2_relset_1(A_128,B_129,D_126))
      | B_129 = '#skF_4'
      | ~ r2_hidden(C_127,A_128)
      | ~ m1_subset_1(D_126,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129)))
      | ~ v1_funct_2(D_126,A_128,B_129)
      | ~ v1_funct_1(D_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_50])).

tff(c_552,plain,(
    ! [C_127] :
      ( r2_hidden(k1_funct_1('#skF_4',C_127),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_127,k1_tarski('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3')))
      | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_543])).

tff(c_556,plain,(
    ! [C_127] :
      ( r2_hidden(k1_funct_1('#skF_4',C_127),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_127,k1_tarski('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_552])).

tff(c_558,plain,(
    ! [C_130] :
      ( r2_hidden(k1_funct_1('#skF_4',C_130),'#skF_4')
      | ~ r2_hidden(C_130,k1_tarski('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_315,c_556])).

tff(c_40,plain,(
    ! [B_22,A_21] :
      ( ~ r1_tarski(B_22,A_21)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_561,plain,(
    ! [C_130] :
      ( ~ r1_tarski('#skF_4',k1_funct_1('#skF_4',C_130))
      | ~ r2_hidden(C_130,k1_tarski('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_558,c_40])).

tff(c_571,plain,(
    ! [C_131] : ~ r2_hidden(C_131,k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_561])).

tff(c_575,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_4,c_571])).

tff(c_579,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_575])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:03:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.85/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.59  
% 2.85/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.59  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.85/1.59  
% 2.85/1.59  %Foreground sorts:
% 2.85/1.59  
% 2.85/1.59  
% 2.85/1.59  %Background operators:
% 2.85/1.59  
% 2.85/1.59  
% 2.85/1.59  %Foreground operators:
% 2.85/1.59  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.85/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.85/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.85/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.85/1.59  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.85/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.85/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.85/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.85/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.85/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.85/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.85/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.85/1.59  tff('#skF_2', type, '#skF_2': $i).
% 2.85/1.59  tff('#skF_3', type, '#skF_3': $i).
% 2.85/1.59  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.85/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.85/1.59  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.85/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.85/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.85/1.59  tff('#skF_4', type, '#skF_4': $i).
% 2.85/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.59  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.85/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.85/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.85/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.85/1.59  
% 2.85/1.60  tff(f_42, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 2.85/1.60  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.85/1.60  tff(f_125, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 2.85/1.60  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.85/1.60  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.85/1.60  tff(f_82, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 2.85/1.60  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.85/1.60  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.85/1.60  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.85/1.60  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.85/1.60  tff(f_57, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 2.85/1.60  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.85/1.60  tff(f_66, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.85/1.60  tff(f_113, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 2.85/1.60  tff(f_87, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.85/1.60  tff(c_14, plain, (![A_12]: (~v1_xboole_0(k1_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.85/1.60  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.85/1.60  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.85/1.60  tff(c_128, plain, (![C_56, A_57, B_58]: (v1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.85/1.60  tff(c_132, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_128])).
% 2.85/1.60  tff(c_36, plain, (![A_18]: (k1_relat_1(A_18)!=k1_xboole_0 | k1_xboole_0=A_18 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.85/1.60  tff(c_139, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_132, c_36])).
% 2.85/1.60  tff(c_141, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_139])).
% 2.85/1.60  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.85/1.60  tff(c_198, plain, (![B_76, A_77]: (k1_tarski(k1_funct_1(B_76, A_77))=k2_relat_1(B_76) | k1_tarski(A_77)!=k1_relat_1(B_76) | ~v1_funct_1(B_76) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.85/1.60  tff(c_188, plain, (![A_73, B_74, C_75]: (k2_relset_1(A_73, B_74, C_75)=k2_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.85/1.60  tff(c_192, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_188])).
% 2.85/1.60  tff(c_52, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')!=k1_tarski(k1_funct_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.85/1.60  tff(c_193, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_192, c_52])).
% 2.85/1.60  tff(c_204, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_198, c_193])).
% 2.85/1.60  tff(c_225, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_60, c_204])).
% 2.85/1.60  tff(c_148, plain, (![C_62, A_63, B_64]: (v4_relat_1(C_62, A_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.85/1.60  tff(c_152, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_56, c_148])).
% 2.85/1.60  tff(c_28, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(B_17), A_16) | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.85/1.60  tff(c_8, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.85/1.60  tff(c_240, plain, (![B_82, C_83, A_84]: (k2_tarski(B_82, C_83)=A_84 | k1_tarski(C_83)=A_84 | k1_tarski(B_82)=A_84 | k1_xboole_0=A_84 | ~r1_tarski(A_84, k2_tarski(B_82, C_83)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.85/1.60  tff(c_256, plain, (![A_6, A_84]: (k2_tarski(A_6, A_6)=A_84 | k1_tarski(A_6)=A_84 | k1_tarski(A_6)=A_84 | k1_xboole_0=A_84 | ~r1_tarski(A_84, k1_tarski(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_240])).
% 2.85/1.60  tff(c_271, plain, (![A_85, A_86]: (k1_tarski(A_85)=A_86 | k1_tarski(A_85)=A_86 | k1_tarski(A_85)=A_86 | k1_xboole_0=A_86 | ~r1_tarski(A_86, k1_tarski(A_85)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_256])).
% 2.85/1.60  tff(c_295, plain, (![A_87, B_88]: (k1_tarski(A_87)=k1_relat_1(B_88) | k1_relat_1(B_88)=k1_xboole_0 | ~v4_relat_1(B_88, k1_tarski(A_87)) | ~v1_relat_1(B_88))), inference(resolution, [status(thm)], [c_28, c_271])).
% 2.85/1.60  tff(c_301, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_152, c_295])).
% 2.85/1.60  tff(c_304, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_132, c_301])).
% 2.85/1.60  tff(c_306, plain, $false, inference(negUnitSimplification, [status(thm)], [c_141, c_225, c_304])).
% 2.85/1.61  tff(c_307, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_139])).
% 2.85/1.61  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.85/1.61  tff(c_312, plain, (![A_5]: (r1_tarski('#skF_4', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_307, c_6])).
% 2.85/1.61  tff(c_54, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.85/1.61  tff(c_315, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_307, c_54])).
% 2.85/1.61  tff(c_58, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.85/1.61  tff(c_30, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.85/1.61  tff(c_314, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_307, c_307, c_30])).
% 2.85/1.61  tff(c_409, plain, (![A_107, B_108, C_109]: (k2_relset_1(A_107, B_108, C_109)=k2_relat_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.85/1.61  tff(c_412, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_409])).
% 2.85/1.61  tff(c_414, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_314, c_412])).
% 2.85/1.61  tff(c_50, plain, (![D_35, C_34, A_32, B_33]: (r2_hidden(k1_funct_1(D_35, C_34), k2_relset_1(A_32, B_33, D_35)) | k1_xboole_0=B_33 | ~r2_hidden(C_34, A_32) | ~m1_subset_1(D_35, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | ~v1_funct_2(D_35, A_32, B_33) | ~v1_funct_1(D_35))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.85/1.61  tff(c_543, plain, (![D_126, C_127, A_128, B_129]: (r2_hidden(k1_funct_1(D_126, C_127), k2_relset_1(A_128, B_129, D_126)) | B_129='#skF_4' | ~r2_hidden(C_127, A_128) | ~m1_subset_1(D_126, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))) | ~v1_funct_2(D_126, A_128, B_129) | ~v1_funct_1(D_126))), inference(demodulation, [status(thm), theory('equality')], [c_307, c_50])).
% 2.85/1.61  tff(c_552, plain, (![C_127]: (r2_hidden(k1_funct_1('#skF_4', C_127), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_127, k1_tarski('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_414, c_543])).
% 2.85/1.61  tff(c_556, plain, (![C_127]: (r2_hidden(k1_funct_1('#skF_4', C_127), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_127, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_552])).
% 2.85/1.61  tff(c_558, plain, (![C_130]: (r2_hidden(k1_funct_1('#skF_4', C_130), '#skF_4') | ~r2_hidden(C_130, k1_tarski('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_315, c_556])).
% 2.85/1.61  tff(c_40, plain, (![B_22, A_21]: (~r1_tarski(B_22, A_21) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.85/1.61  tff(c_561, plain, (![C_130]: (~r1_tarski('#skF_4', k1_funct_1('#skF_4', C_130)) | ~r2_hidden(C_130, k1_tarski('#skF_2')))), inference(resolution, [status(thm)], [c_558, c_40])).
% 2.85/1.61  tff(c_571, plain, (![C_131]: (~r2_hidden(C_131, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_561])).
% 2.85/1.61  tff(c_575, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_4, c_571])).
% 2.85/1.61  tff(c_579, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_575])).
% 2.85/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.61  
% 2.85/1.61  Inference rules
% 2.85/1.61  ----------------------
% 2.85/1.61  #Ref     : 0
% 2.85/1.61  #Sup     : 108
% 2.85/1.61  #Fact    : 0
% 2.85/1.61  #Define  : 0
% 2.85/1.61  #Split   : 3
% 2.85/1.61  #Chain   : 0
% 2.85/1.61  #Close   : 0
% 2.85/1.61  
% 2.85/1.61  Ordering : KBO
% 2.85/1.61  
% 2.85/1.61  Simplification rules
% 2.85/1.61  ----------------------
% 2.85/1.61  #Subsume      : 11
% 2.85/1.61  #Demod        : 75
% 2.85/1.61  #Tautology    : 54
% 2.85/1.61  #SimpNegUnit  : 8
% 2.85/1.61  #BackRed      : 9
% 2.85/1.61  
% 2.85/1.61  #Partial instantiations: 0
% 2.85/1.61  #Strategies tried      : 1
% 2.85/1.61  
% 2.85/1.61  Timing (in seconds)
% 2.85/1.61  ----------------------
% 2.85/1.61  Preprocessing        : 0.46
% 2.85/1.61  Parsing              : 0.26
% 2.85/1.61  CNF conversion       : 0.03
% 2.85/1.61  Main loop            : 0.31
% 2.85/1.61  Inferencing          : 0.11
% 2.85/1.61  Reduction            : 0.10
% 2.85/1.61  Demodulation         : 0.07
% 2.85/1.61  BG Simplification    : 0.02
% 2.85/1.61  Subsumption          : 0.05
% 2.85/1.61  Abstraction          : 0.02
% 2.85/1.61  MUC search           : 0.00
% 2.85/1.61  Cooper               : 0.00
% 2.85/1.61  Total                : 0.81
% 2.85/1.61  Index Insertion      : 0.00
% 2.85/1.61  Index Deletion       : 0.00
% 2.85/1.61  Index Matching       : 0.00
% 2.85/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
