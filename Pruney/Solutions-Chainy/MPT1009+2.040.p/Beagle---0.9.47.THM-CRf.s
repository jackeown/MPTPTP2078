%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:47 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 195 expanded)
%              Number of leaves         :   42 (  83 expanded)
%              Depth                    :   11
%              Number of atoms          :  158 ( 396 expanded)
%              Number of equality atoms :   83 ( 156 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_129,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_117,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(D,k1_enumset1(A,B,C))
    <=> ~ ( D != k1_xboole_0
          & D != k1_tarski(A)
          & D != k1_tarski(B)
          & D != k1_tarski(C)
          & D != k2_tarski(A,B)
          & D != k2_tarski(B,C)
          & D != k2_tarski(A,C)
          & D != k1_enumset1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_87,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_68,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_128,plain,(
    ! [C_56,A_57,B_58] :
      ( v1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_136,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_128])).

tff(c_42,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k9_relat_1(B_21,A_20),k2_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_50,plain,(
    ! [A_22] :
      ( k1_relat_1(A_22) != k1_xboole_0
      | k1_xboole_0 = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_144,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_136,c_50])).

tff(c_160,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_387,plain,(
    ! [B_110,A_111] :
      ( k1_tarski(k1_funct_1(B_110,A_111)) = k2_relat_1(B_110)
      | k1_tarski(A_111) != k1_relat_1(B_110)
      | ~ v1_funct_1(B_110)
      | ~ v1_relat_1(B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_349,plain,(
    ! [A_98,B_99,C_100,D_101] :
      ( k7_relset_1(A_98,B_99,C_100,D_101) = k9_relat_1(C_100,D_101)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_355,plain,(
    ! [D_101] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_101) = k9_relat_1('#skF_4',D_101) ),
    inference(resolution,[status(thm)],[c_66,c_349])).

tff(c_62,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_365,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_62])).

tff(c_399,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_387,c_365])).

tff(c_420,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_70,c_399])).

tff(c_422,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_420])).

tff(c_265,plain,(
    ! [C_75,A_76,B_77] :
      ( v4_relat_1(C_75,A_76)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_273,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_66,c_265])).

tff(c_10,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_40,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k1_relat_1(B_19),A_18)
      | ~ v4_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_12,plain,(
    ! [A_5,B_6] : k1_enumset1(A_5,A_5,B_6) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_445,plain,(
    ! [A_114,B_115,C_116,D_117] :
      ( k1_enumset1(A_114,B_115,C_116) = D_117
      | k2_tarski(A_114,C_116) = D_117
      | k2_tarski(B_115,C_116) = D_117
      | k2_tarski(A_114,B_115) = D_117
      | k1_tarski(C_116) = D_117
      | k1_tarski(B_115) = D_117
      | k1_tarski(A_114) = D_117
      | k1_xboole_0 = D_117
      | ~ r1_tarski(D_117,k1_enumset1(A_114,B_115,C_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_470,plain,(
    ! [A_5,B_6,D_117] :
      ( k1_enumset1(A_5,A_5,B_6) = D_117
      | k2_tarski(A_5,B_6) = D_117
      | k2_tarski(A_5,B_6) = D_117
      | k2_tarski(A_5,A_5) = D_117
      | k1_tarski(B_6) = D_117
      | k1_tarski(A_5) = D_117
      | k1_tarski(A_5) = D_117
      | k1_xboole_0 = D_117
      | ~ r1_tarski(D_117,k2_tarski(A_5,B_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_445])).

tff(c_677,plain,(
    ! [A_163,B_164,D_165] :
      ( k2_tarski(A_163,B_164) = D_165
      | k2_tarski(A_163,B_164) = D_165
      | k2_tarski(A_163,B_164) = D_165
      | k1_tarski(A_163) = D_165
      | k1_tarski(B_164) = D_165
      | k1_tarski(A_163) = D_165
      | k1_tarski(A_163) = D_165
      | k1_xboole_0 = D_165
      | ~ r1_tarski(D_165,k2_tarski(A_163,B_164)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12,c_470])).

tff(c_717,plain,(
    ! [A_166,B_167,B_168] :
      ( k2_tarski(A_166,B_167) = k1_relat_1(B_168)
      | k1_tarski(B_167) = k1_relat_1(B_168)
      | k1_tarski(A_166) = k1_relat_1(B_168)
      | k1_relat_1(B_168) = k1_xboole_0
      | ~ v4_relat_1(B_168,k2_tarski(A_166,B_167))
      | ~ v1_relat_1(B_168) ) ),
    inference(resolution,[status(thm)],[c_40,c_677])).

tff(c_724,plain,(
    ! [A_4,B_168] :
      ( k2_tarski(A_4,A_4) = k1_relat_1(B_168)
      | k1_tarski(A_4) = k1_relat_1(B_168)
      | k1_tarski(A_4) = k1_relat_1(B_168)
      | k1_relat_1(B_168) = k1_xboole_0
      | ~ v4_relat_1(B_168,k1_tarski(A_4))
      | ~ v1_relat_1(B_168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_717])).

tff(c_729,plain,(
    ! [A_169,B_170] :
      ( k1_tarski(A_169) = k1_relat_1(B_170)
      | k1_tarski(A_169) = k1_relat_1(B_170)
      | k1_tarski(A_169) = k1_relat_1(B_170)
      | k1_relat_1(B_170) = k1_xboole_0
      | ~ v4_relat_1(B_170,k1_tarski(A_169))
      | ~ v1_relat_1(B_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_724])).

tff(c_735,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_273,c_729])).

tff(c_742,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_735])).

tff(c_744,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_422,c_742])).

tff(c_745,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_420])).

tff(c_781,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_745])).

tff(c_785,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_781])).

tff(c_786,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_792,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_786,c_8])).

tff(c_44,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_793,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_786,c_786,c_44])).

tff(c_899,plain,(
    ! [B_184,A_185] :
      ( r1_tarski(k9_relat_1(B_184,A_185),k2_relat_1(B_184))
      | ~ v1_relat_1(B_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_904,plain,(
    ! [A_185] :
      ( r1_tarski(k9_relat_1('#skF_4',A_185),'#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_793,c_899])).

tff(c_908,plain,(
    ! [A_186] : r1_tarski(k9_relat_1('#skF_4',A_186),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_904])).

tff(c_846,plain,(
    ! [B_178,A_179] :
      ( B_178 = A_179
      | ~ r1_tarski(B_178,A_179)
      | ~ r1_tarski(A_179,B_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_863,plain,(
    ! [A_3] :
      ( A_3 = '#skF_4'
      | ~ r1_tarski(A_3,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_792,c_846])).

tff(c_914,plain,(
    ! [A_186] : k9_relat_1('#skF_4',A_186) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_908,c_863])).

tff(c_34,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_791,plain,(
    ! [A_14] : m1_subset_1('#skF_4',k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_786,c_34])).

tff(c_1050,plain,(
    ! [A_219,B_220,C_221,D_222] :
      ( k7_relset_1(A_219,B_220,C_221,D_222) = k9_relat_1(C_221,D_222)
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(A_219,B_220))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1053,plain,(
    ! [A_219,B_220,D_222] : k7_relset_1(A_219,B_220,'#skF_4',D_222) = k9_relat_1('#skF_4',D_222) ),
    inference(resolution,[status(thm)],[c_791,c_1050])).

tff(c_1055,plain,(
    ! [A_219,B_220,D_222] : k7_relset_1(A_219,B_220,'#skF_4',D_222) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_914,c_1053])).

tff(c_1056,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1055,c_62])).

tff(c_1059,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_792,c_1056])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:51:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.55/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.61  
% 3.55/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.62  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.55/1.62  
% 3.55/1.62  %Foreground sorts:
% 3.55/1.62  
% 3.55/1.62  
% 3.55/1.62  %Background operators:
% 3.55/1.62  
% 3.55/1.62  
% 3.55/1.62  %Foreground operators:
% 3.55/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.55/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.55/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.55/1.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.55/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.55/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.55/1.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.55/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.55/1.62  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.55/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.55/1.62  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.55/1.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.55/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.55/1.62  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.55/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.55/1.62  tff('#skF_1', type, '#skF_1': $i).
% 3.55/1.62  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.55/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.55/1.62  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.55/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.55/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.55/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.55/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.55/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.55/1.62  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.55/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.55/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.55/1.62  
% 3.55/1.63  tff(f_129, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 3.55/1.63  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.55/1.63  tff(f_84, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 3.55/1.63  tff(f_95, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.55/1.63  tff(f_103, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.55/1.63  tff(f_117, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.55/1.63  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.55/1.63  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.55/1.63  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.55/1.63  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.55/1.63  tff(f_66, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 3.55/1.63  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.55/1.63  tff(f_87, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.55/1.63  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.55/1.63  tff(f_68, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.55/1.63  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.55/1.63  tff(c_128, plain, (![C_56, A_57, B_58]: (v1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.55/1.63  tff(c_136, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_128])).
% 3.55/1.63  tff(c_42, plain, (![B_21, A_20]: (r1_tarski(k9_relat_1(B_21, A_20), k2_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.55/1.63  tff(c_50, plain, (![A_22]: (k1_relat_1(A_22)!=k1_xboole_0 | k1_xboole_0=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.55/1.63  tff(c_144, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_136, c_50])).
% 3.55/1.63  tff(c_160, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_144])).
% 3.55/1.63  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.55/1.63  tff(c_387, plain, (![B_110, A_111]: (k1_tarski(k1_funct_1(B_110, A_111))=k2_relat_1(B_110) | k1_tarski(A_111)!=k1_relat_1(B_110) | ~v1_funct_1(B_110) | ~v1_relat_1(B_110))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.55/1.63  tff(c_349, plain, (![A_98, B_99, C_100, D_101]: (k7_relset_1(A_98, B_99, C_100, D_101)=k9_relat_1(C_100, D_101) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.55/1.63  tff(c_355, plain, (![D_101]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_101)=k9_relat_1('#skF_4', D_101))), inference(resolution, [status(thm)], [c_66, c_349])).
% 3.55/1.63  tff(c_62, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.55/1.63  tff(c_365, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_355, c_62])).
% 3.55/1.63  tff(c_399, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_387, c_365])).
% 3.55/1.63  tff(c_420, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_70, c_399])).
% 3.55/1.63  tff(c_422, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_420])).
% 3.55/1.63  tff(c_265, plain, (![C_75, A_76, B_77]: (v4_relat_1(C_75, A_76) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.55/1.63  tff(c_273, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_66, c_265])).
% 3.55/1.63  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.55/1.63  tff(c_40, plain, (![B_19, A_18]: (r1_tarski(k1_relat_1(B_19), A_18) | ~v4_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.55/1.63  tff(c_12, plain, (![A_5, B_6]: (k1_enumset1(A_5, A_5, B_6)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.55/1.63  tff(c_445, plain, (![A_114, B_115, C_116, D_117]: (k1_enumset1(A_114, B_115, C_116)=D_117 | k2_tarski(A_114, C_116)=D_117 | k2_tarski(B_115, C_116)=D_117 | k2_tarski(A_114, B_115)=D_117 | k1_tarski(C_116)=D_117 | k1_tarski(B_115)=D_117 | k1_tarski(A_114)=D_117 | k1_xboole_0=D_117 | ~r1_tarski(D_117, k1_enumset1(A_114, B_115, C_116)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.55/1.63  tff(c_470, plain, (![A_5, B_6, D_117]: (k1_enumset1(A_5, A_5, B_6)=D_117 | k2_tarski(A_5, B_6)=D_117 | k2_tarski(A_5, B_6)=D_117 | k2_tarski(A_5, A_5)=D_117 | k1_tarski(B_6)=D_117 | k1_tarski(A_5)=D_117 | k1_tarski(A_5)=D_117 | k1_xboole_0=D_117 | ~r1_tarski(D_117, k2_tarski(A_5, B_6)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_445])).
% 3.55/1.63  tff(c_677, plain, (![A_163, B_164, D_165]: (k2_tarski(A_163, B_164)=D_165 | k2_tarski(A_163, B_164)=D_165 | k2_tarski(A_163, B_164)=D_165 | k1_tarski(A_163)=D_165 | k1_tarski(B_164)=D_165 | k1_tarski(A_163)=D_165 | k1_tarski(A_163)=D_165 | k1_xboole_0=D_165 | ~r1_tarski(D_165, k2_tarski(A_163, B_164)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12, c_470])).
% 3.55/1.63  tff(c_717, plain, (![A_166, B_167, B_168]: (k2_tarski(A_166, B_167)=k1_relat_1(B_168) | k1_tarski(B_167)=k1_relat_1(B_168) | k1_tarski(A_166)=k1_relat_1(B_168) | k1_relat_1(B_168)=k1_xboole_0 | ~v4_relat_1(B_168, k2_tarski(A_166, B_167)) | ~v1_relat_1(B_168))), inference(resolution, [status(thm)], [c_40, c_677])).
% 3.55/1.63  tff(c_724, plain, (![A_4, B_168]: (k2_tarski(A_4, A_4)=k1_relat_1(B_168) | k1_tarski(A_4)=k1_relat_1(B_168) | k1_tarski(A_4)=k1_relat_1(B_168) | k1_relat_1(B_168)=k1_xboole_0 | ~v4_relat_1(B_168, k1_tarski(A_4)) | ~v1_relat_1(B_168))), inference(superposition, [status(thm), theory('equality')], [c_10, c_717])).
% 3.55/1.63  tff(c_729, plain, (![A_169, B_170]: (k1_tarski(A_169)=k1_relat_1(B_170) | k1_tarski(A_169)=k1_relat_1(B_170) | k1_tarski(A_169)=k1_relat_1(B_170) | k1_relat_1(B_170)=k1_xboole_0 | ~v4_relat_1(B_170, k1_tarski(A_169)) | ~v1_relat_1(B_170))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_724])).
% 3.55/1.63  tff(c_735, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_273, c_729])).
% 3.55/1.63  tff(c_742, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_136, c_735])).
% 3.55/1.63  tff(c_744, plain, $false, inference(negUnitSimplification, [status(thm)], [c_160, c_422, c_742])).
% 3.55/1.63  tff(c_745, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_420])).
% 3.55/1.63  tff(c_781, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_745])).
% 3.55/1.63  tff(c_785, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_136, c_781])).
% 3.55/1.63  tff(c_786, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_144])).
% 3.55/1.63  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.55/1.63  tff(c_792, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_786, c_8])).
% 3.55/1.63  tff(c_44, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.55/1.63  tff(c_793, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_786, c_786, c_44])).
% 3.55/1.63  tff(c_899, plain, (![B_184, A_185]: (r1_tarski(k9_relat_1(B_184, A_185), k2_relat_1(B_184)) | ~v1_relat_1(B_184))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.55/1.63  tff(c_904, plain, (![A_185]: (r1_tarski(k9_relat_1('#skF_4', A_185), '#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_793, c_899])).
% 3.55/1.63  tff(c_908, plain, (![A_186]: (r1_tarski(k9_relat_1('#skF_4', A_186), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_904])).
% 3.55/1.63  tff(c_846, plain, (![B_178, A_179]: (B_178=A_179 | ~r1_tarski(B_178, A_179) | ~r1_tarski(A_179, B_178))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.55/1.63  tff(c_863, plain, (![A_3]: (A_3='#skF_4' | ~r1_tarski(A_3, '#skF_4'))), inference(resolution, [status(thm)], [c_792, c_846])).
% 3.55/1.63  tff(c_914, plain, (![A_186]: (k9_relat_1('#skF_4', A_186)='#skF_4')), inference(resolution, [status(thm)], [c_908, c_863])).
% 3.55/1.63  tff(c_34, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.55/1.63  tff(c_791, plain, (![A_14]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_786, c_34])).
% 3.55/1.63  tff(c_1050, plain, (![A_219, B_220, C_221, D_222]: (k7_relset_1(A_219, B_220, C_221, D_222)=k9_relat_1(C_221, D_222) | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(A_219, B_220))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.55/1.63  tff(c_1053, plain, (![A_219, B_220, D_222]: (k7_relset_1(A_219, B_220, '#skF_4', D_222)=k9_relat_1('#skF_4', D_222))), inference(resolution, [status(thm)], [c_791, c_1050])).
% 3.55/1.63  tff(c_1055, plain, (![A_219, B_220, D_222]: (k7_relset_1(A_219, B_220, '#skF_4', D_222)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_914, c_1053])).
% 3.55/1.63  tff(c_1056, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1055, c_62])).
% 3.55/1.63  tff(c_1059, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_792, c_1056])).
% 3.55/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.63  
% 3.55/1.63  Inference rules
% 3.55/1.63  ----------------------
% 3.55/1.63  #Ref     : 0
% 3.55/1.63  #Sup     : 208
% 3.55/1.63  #Fact    : 0
% 3.55/1.63  #Define  : 0
% 3.55/1.63  #Split   : 3
% 3.55/1.63  #Chain   : 0
% 3.55/1.63  #Close   : 0
% 3.55/1.63  
% 3.55/1.63  Ordering : KBO
% 3.55/1.63  
% 3.55/1.63  Simplification rules
% 3.55/1.63  ----------------------
% 3.55/1.63  #Subsume      : 25
% 3.55/1.63  #Demod        : 175
% 3.55/1.63  #Tautology    : 109
% 3.55/1.63  #SimpNegUnit  : 1
% 3.55/1.63  #BackRed      : 17
% 3.55/1.63  
% 3.55/1.63  #Partial instantiations: 0
% 3.55/1.63  #Strategies tried      : 1
% 3.55/1.63  
% 3.55/1.63  Timing (in seconds)
% 3.55/1.63  ----------------------
% 3.55/1.64  Preprocessing        : 0.36
% 3.55/1.64  Parsing              : 0.19
% 3.55/1.64  CNF conversion       : 0.02
% 3.55/1.64  Main loop            : 0.45
% 3.55/1.64  Inferencing          : 0.16
% 3.55/1.64  Reduction            : 0.15
% 3.55/1.64  Demodulation         : 0.11
% 3.55/1.64  BG Simplification    : 0.02
% 3.55/1.64  Subsumption          : 0.09
% 3.55/1.64  Abstraction          : 0.02
% 3.55/1.64  MUC search           : 0.00
% 3.55/1.64  Cooper               : 0.00
% 3.55/1.64  Total                : 0.84
% 3.55/1.64  Index Insertion      : 0.00
% 3.55/1.64  Index Deletion       : 0.00
% 3.55/1.64  Index Matching       : 0.00
% 3.55/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
