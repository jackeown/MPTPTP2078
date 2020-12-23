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
% DateTime   : Thu Dec  3 10:10:56 EST 2020

% Result     : Theorem 5.34s
% Output     : CNFRefutation 5.34s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 859 expanded)
%              Number of leaves         :   35 ( 283 expanded)
%              Depth                    :   15
%              Number of atoms          :  241 (2206 expanded)
%              Number of equality atoms :   62 ( 392 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_mcart_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_124,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_80,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_98,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_111,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

tff(f_52,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_66,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_62,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_3548,plain,(
    ! [C_494,A_495,B_496] :
      ( m1_subset_1(C_494,k1_zfmisc_1(k2_zfmisc_1(A_495,B_496)))
      | ~ r1_tarski(k2_relat_1(C_494),B_496)
      | ~ r1_tarski(k1_relat_1(C_494),A_495)
      | ~ v1_relat_1(C_494) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_60,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_68,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60])).

tff(c_105,plain,(
    ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_30,plain,(
    ! [A_16] :
      ( r2_hidden('#skF_1'(A_16),A_16)
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_18,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_181,plain,(
    ! [C_70,B_71,A_72] :
      ( ~ v1_xboole_0(C_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(C_70))
      | ~ r2_hidden(A_72,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_354,plain,(
    ! [B_94,A_95,A_96] :
      ( ~ v1_xboole_0(B_94)
      | ~ r2_hidden(A_95,A_96)
      | ~ r1_tarski(A_96,B_94) ) ),
    inference(resolution,[status(thm)],[c_18,c_181])).

tff(c_358,plain,(
    ! [B_97,A_98] :
      ( ~ v1_xboole_0(B_97)
      | ~ r1_tarski(A_98,B_97)
      | k1_xboole_0 = A_98 ) ),
    inference(resolution,[status(thm)],[c_30,c_354])).

tff(c_369,plain,
    ( ~ v1_xboole_0('#skF_3')
    | k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_62,c_358])).

tff(c_381,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_369])).

tff(c_382,plain,(
    ! [C_105,A_106,B_107] :
      ( m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107)))
      | ~ r1_tarski(k2_relat_1(C_105),B_107)
      | ~ r1_tarski(k1_relat_1(C_105),A_106)
      | ~ v1_relat_1(C_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_733,plain,(
    ! [C_163,A_164,B_165] :
      ( r1_tarski(C_163,k2_zfmisc_1(A_164,B_165))
      | ~ r1_tarski(k2_relat_1(C_163),B_165)
      | ~ r1_tarski(k1_relat_1(C_163),A_164)
      | ~ v1_relat_1(C_163) ) ),
    inference(resolution,[status(thm)],[c_382,c_16])).

tff(c_735,plain,(
    ! [A_164] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_164,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_164)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_733])).

tff(c_747,plain,(
    ! [A_166] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_166,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_166) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_735])).

tff(c_752,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_747])).

tff(c_291,plain,(
    ! [A_88,B_89,C_90] :
      ( k1_relset_1(A_88,B_89,C_90) = k1_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_306,plain,(
    ! [A_88,B_89,A_5] :
      ( k1_relset_1(A_88,B_89,A_5) = k1_relat_1(A_5)
      | ~ r1_tarski(A_5,k2_zfmisc_1(A_88,B_89)) ) ),
    inference(resolution,[status(thm)],[c_18,c_291])).

tff(c_761,plain,(
    k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_752,c_306])).

tff(c_613,plain,(
    ! [B_147,C_148,A_149] :
      ( k1_xboole_0 = B_147
      | v1_funct_2(C_148,A_149,B_147)
      | k1_relset_1(A_149,B_147,C_148) != A_149
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_149,B_147))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1022,plain,(
    ! [B_194,A_195,A_196] :
      ( k1_xboole_0 = B_194
      | v1_funct_2(A_195,A_196,B_194)
      | k1_relset_1(A_196,B_194,A_195) != A_196
      | ~ r1_tarski(A_195,k2_zfmisc_1(A_196,B_194)) ) ),
    inference(resolution,[status(thm)],[c_18,c_613])).

tff(c_1031,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3')
    | k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') != k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_752,c_1022])).

tff(c_1049,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_761,c_1031])).

tff(c_1050,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_1049])).

tff(c_1104,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1050,c_2])).

tff(c_1106,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_381,c_1104])).

tff(c_1108,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_369])).

tff(c_370,plain,(
    ! [B_2] :
      ( ~ v1_xboole_0(B_2)
      | k1_xboole_0 = B_2 ) ),
    inference(resolution,[status(thm)],[c_8,c_358])).

tff(c_1112,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1108,c_370])).

tff(c_1107,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_369])).

tff(c_1139,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1112,c_1107])).

tff(c_152,plain,(
    ! [B_66,A_67] :
      ( B_66 = A_67
      | ~ r1_tarski(B_66,A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_163,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_62,c_152])).

tff(c_180,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_1140,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1139,c_180])).

tff(c_1144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1140])).

tff(c_1145,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_1506,plain,(
    ! [C_262,A_263,B_264] :
      ( m1_subset_1(C_262,k1_zfmisc_1(k2_zfmisc_1(A_263,B_264)))
      | ~ r1_tarski(k2_relat_1(C_262),B_264)
      | ~ r1_tarski(k1_relat_1(C_262),A_263)
      | ~ v1_relat_1(C_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1990,plain,(
    ! [C_311,A_312,B_313] :
      ( r1_tarski(C_311,k2_zfmisc_1(A_312,B_313))
      | ~ r1_tarski(k2_relat_1(C_311),B_313)
      | ~ r1_tarski(k1_relat_1(C_311),A_312)
      | ~ v1_relat_1(C_311) ) ),
    inference(resolution,[status(thm)],[c_1506,c_16])).

tff(c_2036,plain,(
    ! [C_318,A_319] :
      ( r1_tarski(C_318,k2_zfmisc_1(A_319,k2_relat_1(C_318)))
      | ~ r1_tarski(k1_relat_1(C_318),A_319)
      | ~ v1_relat_1(C_318) ) ),
    inference(resolution,[status(thm)],[c_8,c_1990])).

tff(c_2053,plain,(
    ! [A_319] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_319,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_319)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1145,c_2036])).

tff(c_2072,plain,(
    ! [A_320] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_320,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_320) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2053])).

tff(c_2082,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_2072])).

tff(c_1407,plain,(
    ! [A_239,B_240,C_241] :
      ( k1_relset_1(A_239,B_240,C_241) = k1_relat_1(C_241)
      | ~ m1_subset_1(C_241,k1_zfmisc_1(k2_zfmisc_1(A_239,B_240))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1422,plain,(
    ! [A_239,B_240,A_5] :
      ( k1_relset_1(A_239,B_240,A_5) = k1_relat_1(A_5)
      | ~ r1_tarski(A_5,k2_zfmisc_1(A_239,B_240)) ) ),
    inference(resolution,[status(thm)],[c_18,c_1407])).

tff(c_2091,plain,(
    k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2082,c_1422])).

tff(c_1723,plain,(
    ! [B_293,C_294,A_295] :
      ( k1_xboole_0 = B_293
      | v1_funct_2(C_294,A_295,B_293)
      | k1_relset_1(A_295,B_293,C_294) != A_295
      | ~ m1_subset_1(C_294,k1_zfmisc_1(k2_zfmisc_1(A_295,B_293))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2362,plain,(
    ! [B_345,A_346,A_347] :
      ( k1_xboole_0 = B_345
      | v1_funct_2(A_346,A_347,B_345)
      | k1_relset_1(A_347,B_345,A_346) != A_347
      | ~ r1_tarski(A_346,k2_zfmisc_1(A_347,B_345)) ) ),
    inference(resolution,[status(thm)],[c_18,c_1723])).

tff(c_2368,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3')
    | k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') != k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2082,c_2362])).

tff(c_2391,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2091,c_2368])).

tff(c_2392,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_2391])).

tff(c_12,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1980,plain,(
    ! [C_309,A_310] :
      ( m1_subset_1(C_309,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_309),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_309),A_310)
      | ~ v1_relat_1(C_309) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1506])).

tff(c_1982,plain,(
    ! [A_310] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_3',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_310)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1145,c_1980])).

tff(c_1986,plain,(
    ! [A_310] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_3',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_310) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1982])).

tff(c_1989,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1986])).

tff(c_2408,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2392,c_1989])).

tff(c_2457,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2408])).

tff(c_2459,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1986])).

tff(c_1154,plain,(
    ! [C_197,B_198,A_199] :
      ( ~ v1_xboole_0(C_197)
      | ~ m1_subset_1(B_198,k1_zfmisc_1(C_197))
      | ~ r2_hidden(A_199,B_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1337,plain,(
    ! [B_226,A_227,A_228] :
      ( ~ v1_xboole_0(B_226)
      | ~ r2_hidden(A_227,A_228)
      | ~ r1_tarski(A_228,B_226) ) ),
    inference(resolution,[status(thm)],[c_18,c_1154])).

tff(c_1340,plain,(
    ! [B_226,A_16] :
      ( ~ v1_xboole_0(B_226)
      | ~ r1_tarski(A_16,B_226)
      | k1_xboole_0 = A_16 ) ),
    inference(resolution,[status(thm)],[c_30,c_1337])).

tff(c_2468,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2459,c_1340])).

tff(c_2476,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2468])).

tff(c_2913,plain,(
    ! [A_388] :
      ( r2_hidden('#skF_1'(A_388),A_388)
      | A_388 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2476,c_30])).

tff(c_2524,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2476,c_2])).

tff(c_2458,plain,(
    ! [A_310] :
      ( ~ r1_tarski(k1_relat_1('#skF_4'),A_310)
      | m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(splitRight,[status(thm)],[c_1986])).

tff(c_2530,plain,(
    ! [A_310] :
      ( ~ r1_tarski(k1_relat_1('#skF_4'),A_310)
      | m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2476,c_2458])).

tff(c_2561,plain,(
    ! [A_356] : ~ r1_tarski(k1_relat_1('#skF_4'),A_356) ),
    inference(splitLeft,[status(thm)],[c_2530])).

tff(c_2566,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_8,c_2561])).

tff(c_2567,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2530])).

tff(c_20,plain,(
    ! [C_9,B_8,A_7] :
      ( ~ v1_xboole_0(C_9)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(C_9))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2598,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_7,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2567,c_20])).

tff(c_2604,plain,(
    ! [A_7] : ~ r2_hidden(A_7,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2524,c_2598])).

tff(c_2928,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2913,c_2604])).

tff(c_2605,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_2567,c_16])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2609,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_2605,c_4])).

tff(c_2911,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2609])).

tff(c_2934,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2928,c_2911])).

tff(c_2967,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2934])).

tff(c_2968,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2609])).

tff(c_14,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_129,plain,(
    ! [A_60,B_61] : m1_subset_1('#skF_2'(A_60,B_61),k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_135,plain,(
    ! [B_4] : m1_subset_1('#skF_2'(k1_xboole_0,B_4),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_129])).

tff(c_1158,plain,(
    ! [A_199,B_4] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_199,'#skF_2'(k1_xboole_0,B_4)) ) ),
    inference(resolution,[status(thm)],[c_135,c_1154])).

tff(c_1277,plain,(
    ! [A_216,B_217] : ~ r2_hidden(A_216,'#skF_2'(k1_xboole_0,B_217)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1158])).

tff(c_1285,plain,(
    ! [B_217] : '#skF_2'(k1_xboole_0,B_217) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_1277])).

tff(c_2610,plain,(
    ! [B_366] : '#skF_2'('#skF_3',B_366) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2476,c_2476,c_1285])).

tff(c_48,plain,(
    ! [A_37,B_38] : v1_funct_2('#skF_2'(A_37,B_38),A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2630,plain,(
    ! [B_366] : v1_funct_2('#skF_3','#skF_3',B_366) ),
    inference(superposition,[status(thm),theory(equality)],[c_2610,c_48])).

tff(c_2984,plain,(
    ! [B_366] : v1_funct_2('#skF_4','#skF_4',B_366) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2968,c_2968,c_2630])).

tff(c_24,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2523,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2476,c_2476,c_24])).

tff(c_3000,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2968,c_2968,c_2523])).

tff(c_3008,plain,(
    ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2968,c_105])).

tff(c_3103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2984,c_3000,c_3008])).

tff(c_3104,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_3559,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3548,c_3104])).

tff(c_3572,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_8,c_62,c_3559])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.34/2.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.34/2.03  
% 5.34/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.34/2.03  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_mcart_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 5.34/2.03  
% 5.34/2.03  %Foreground sorts:
% 5.34/2.03  
% 5.34/2.03  
% 5.34/2.03  %Background operators:
% 5.34/2.03  
% 5.34/2.03  
% 5.34/2.03  %Foreground operators:
% 5.34/2.03  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.34/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.34/2.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.34/2.03  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.34/2.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.34/2.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.34/2.03  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.34/2.03  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.34/2.03  tff('#skF_3', type, '#skF_3': $i).
% 5.34/2.03  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.34/2.03  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.34/2.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.34/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.34/2.03  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.34/2.03  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.34/2.03  tff('#skF_4', type, '#skF_4': $i).
% 5.34/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.34/2.03  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.34/2.03  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.34/2.03  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 5.34/2.03  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.34/2.03  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.34/2.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.34/2.03  
% 5.34/2.06  tff(f_124, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 5.34/2.06  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.34/2.06  tff(f_64, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 5.34/2.06  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.34/2.06  tff(f_80, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_mcart_1)).
% 5.34/2.06  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.34/2.06  tff(f_49, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 5.34/2.06  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.34/2.06  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.34/2.06  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.34/2.06  tff(f_111, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_funct_2)).
% 5.34/2.06  tff(f_52, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 5.34/2.06  tff(c_66, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.34/2.06  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.34/2.06  tff(c_62, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.34/2.06  tff(c_3548, plain, (![C_494, A_495, B_496]: (m1_subset_1(C_494, k1_zfmisc_1(k2_zfmisc_1(A_495, B_496))) | ~r1_tarski(k2_relat_1(C_494), B_496) | ~r1_tarski(k1_relat_1(C_494), A_495) | ~v1_relat_1(C_494))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.34/2.06  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.34/2.06  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.34/2.06  tff(c_60, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.34/2.06  tff(c_68, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60])).
% 5.34/2.06  tff(c_105, plain, (~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_68])).
% 5.34/2.06  tff(c_30, plain, (![A_16]: (r2_hidden('#skF_1'(A_16), A_16) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.34/2.06  tff(c_18, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.34/2.06  tff(c_181, plain, (![C_70, B_71, A_72]: (~v1_xboole_0(C_70) | ~m1_subset_1(B_71, k1_zfmisc_1(C_70)) | ~r2_hidden(A_72, B_71))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.34/2.06  tff(c_354, plain, (![B_94, A_95, A_96]: (~v1_xboole_0(B_94) | ~r2_hidden(A_95, A_96) | ~r1_tarski(A_96, B_94))), inference(resolution, [status(thm)], [c_18, c_181])).
% 5.34/2.06  tff(c_358, plain, (![B_97, A_98]: (~v1_xboole_0(B_97) | ~r1_tarski(A_98, B_97) | k1_xboole_0=A_98)), inference(resolution, [status(thm)], [c_30, c_354])).
% 5.34/2.06  tff(c_369, plain, (~v1_xboole_0('#skF_3') | k2_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_62, c_358])).
% 5.34/2.06  tff(c_381, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_369])).
% 5.34/2.06  tff(c_382, plain, (![C_105, A_106, B_107]: (m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))) | ~r1_tarski(k2_relat_1(C_105), B_107) | ~r1_tarski(k1_relat_1(C_105), A_106) | ~v1_relat_1(C_105))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.34/2.06  tff(c_16, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.34/2.06  tff(c_733, plain, (![C_163, A_164, B_165]: (r1_tarski(C_163, k2_zfmisc_1(A_164, B_165)) | ~r1_tarski(k2_relat_1(C_163), B_165) | ~r1_tarski(k1_relat_1(C_163), A_164) | ~v1_relat_1(C_163))), inference(resolution, [status(thm)], [c_382, c_16])).
% 5.34/2.06  tff(c_735, plain, (![A_164]: (r1_tarski('#skF_4', k2_zfmisc_1(A_164, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_164) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_733])).
% 5.34/2.06  tff(c_747, plain, (![A_166]: (r1_tarski('#skF_4', k2_zfmisc_1(A_166, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_166))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_735])).
% 5.34/2.06  tff(c_752, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_8, c_747])).
% 5.34/2.06  tff(c_291, plain, (![A_88, B_89, C_90]: (k1_relset_1(A_88, B_89, C_90)=k1_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.34/2.06  tff(c_306, plain, (![A_88, B_89, A_5]: (k1_relset_1(A_88, B_89, A_5)=k1_relat_1(A_5) | ~r1_tarski(A_5, k2_zfmisc_1(A_88, B_89)))), inference(resolution, [status(thm)], [c_18, c_291])).
% 5.34/2.06  tff(c_761, plain, (k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_752, c_306])).
% 5.34/2.06  tff(c_613, plain, (![B_147, C_148, A_149]: (k1_xboole_0=B_147 | v1_funct_2(C_148, A_149, B_147) | k1_relset_1(A_149, B_147, C_148)!=A_149 | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_149, B_147))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.34/2.06  tff(c_1022, plain, (![B_194, A_195, A_196]: (k1_xboole_0=B_194 | v1_funct_2(A_195, A_196, B_194) | k1_relset_1(A_196, B_194, A_195)!=A_196 | ~r1_tarski(A_195, k2_zfmisc_1(A_196, B_194)))), inference(resolution, [status(thm)], [c_18, c_613])).
% 5.34/2.06  tff(c_1031, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3') | k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')!=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_752, c_1022])).
% 5.34/2.06  tff(c_1049, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_761, c_1031])).
% 5.34/2.06  tff(c_1050, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_105, c_1049])).
% 5.34/2.06  tff(c_1104, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1050, c_2])).
% 5.34/2.06  tff(c_1106, plain, $false, inference(negUnitSimplification, [status(thm)], [c_381, c_1104])).
% 5.34/2.06  tff(c_1108, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_369])).
% 5.34/2.06  tff(c_370, plain, (![B_2]: (~v1_xboole_0(B_2) | k1_xboole_0=B_2)), inference(resolution, [status(thm)], [c_8, c_358])).
% 5.34/2.06  tff(c_1112, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1108, c_370])).
% 5.34/2.06  tff(c_1107, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_369])).
% 5.34/2.06  tff(c_1139, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1112, c_1107])).
% 5.34/2.06  tff(c_152, plain, (![B_66, A_67]: (B_66=A_67 | ~r1_tarski(B_66, A_67) | ~r1_tarski(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.34/2.06  tff(c_163, plain, (k2_relat_1('#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_152])).
% 5.34/2.06  tff(c_180, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_163])).
% 5.34/2.06  tff(c_1140, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1139, c_180])).
% 5.34/2.06  tff(c_1144, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_1140])).
% 5.34/2.06  tff(c_1145, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_163])).
% 5.34/2.06  tff(c_1506, plain, (![C_262, A_263, B_264]: (m1_subset_1(C_262, k1_zfmisc_1(k2_zfmisc_1(A_263, B_264))) | ~r1_tarski(k2_relat_1(C_262), B_264) | ~r1_tarski(k1_relat_1(C_262), A_263) | ~v1_relat_1(C_262))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.34/2.06  tff(c_1990, plain, (![C_311, A_312, B_313]: (r1_tarski(C_311, k2_zfmisc_1(A_312, B_313)) | ~r1_tarski(k2_relat_1(C_311), B_313) | ~r1_tarski(k1_relat_1(C_311), A_312) | ~v1_relat_1(C_311))), inference(resolution, [status(thm)], [c_1506, c_16])).
% 5.34/2.06  tff(c_2036, plain, (![C_318, A_319]: (r1_tarski(C_318, k2_zfmisc_1(A_319, k2_relat_1(C_318))) | ~r1_tarski(k1_relat_1(C_318), A_319) | ~v1_relat_1(C_318))), inference(resolution, [status(thm)], [c_8, c_1990])).
% 5.34/2.06  tff(c_2053, plain, (![A_319]: (r1_tarski('#skF_4', k2_zfmisc_1(A_319, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_319) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1145, c_2036])).
% 5.34/2.06  tff(c_2072, plain, (![A_320]: (r1_tarski('#skF_4', k2_zfmisc_1(A_320, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_320))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2053])).
% 5.34/2.06  tff(c_2082, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_8, c_2072])).
% 5.34/2.06  tff(c_1407, plain, (![A_239, B_240, C_241]: (k1_relset_1(A_239, B_240, C_241)=k1_relat_1(C_241) | ~m1_subset_1(C_241, k1_zfmisc_1(k2_zfmisc_1(A_239, B_240))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.34/2.06  tff(c_1422, plain, (![A_239, B_240, A_5]: (k1_relset_1(A_239, B_240, A_5)=k1_relat_1(A_5) | ~r1_tarski(A_5, k2_zfmisc_1(A_239, B_240)))), inference(resolution, [status(thm)], [c_18, c_1407])).
% 5.34/2.06  tff(c_2091, plain, (k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2082, c_1422])).
% 5.34/2.06  tff(c_1723, plain, (![B_293, C_294, A_295]: (k1_xboole_0=B_293 | v1_funct_2(C_294, A_295, B_293) | k1_relset_1(A_295, B_293, C_294)!=A_295 | ~m1_subset_1(C_294, k1_zfmisc_1(k2_zfmisc_1(A_295, B_293))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.34/2.06  tff(c_2362, plain, (![B_345, A_346, A_347]: (k1_xboole_0=B_345 | v1_funct_2(A_346, A_347, B_345) | k1_relset_1(A_347, B_345, A_346)!=A_347 | ~r1_tarski(A_346, k2_zfmisc_1(A_347, B_345)))), inference(resolution, [status(thm)], [c_18, c_1723])).
% 5.34/2.06  tff(c_2368, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3') | k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')!=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2082, c_2362])).
% 5.34/2.06  tff(c_2391, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2091, c_2368])).
% 5.34/2.06  tff(c_2392, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_105, c_2391])).
% 5.34/2.06  tff(c_12, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.34/2.06  tff(c_1980, plain, (![C_309, A_310]: (m1_subset_1(C_309, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_309), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_309), A_310) | ~v1_relat_1(C_309))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1506])).
% 5.34/2.06  tff(c_1982, plain, (![A_310]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_4'), A_310) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1145, c_1980])).
% 5.34/2.06  tff(c_1986, plain, (![A_310]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_4'), A_310))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1982])).
% 5.34/2.06  tff(c_1989, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1986])).
% 5.34/2.06  tff(c_2408, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2392, c_1989])).
% 5.34/2.06  tff(c_2457, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_2408])).
% 5.34/2.06  tff(c_2459, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1986])).
% 5.34/2.06  tff(c_1154, plain, (![C_197, B_198, A_199]: (~v1_xboole_0(C_197) | ~m1_subset_1(B_198, k1_zfmisc_1(C_197)) | ~r2_hidden(A_199, B_198))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.34/2.06  tff(c_1337, plain, (![B_226, A_227, A_228]: (~v1_xboole_0(B_226) | ~r2_hidden(A_227, A_228) | ~r1_tarski(A_228, B_226))), inference(resolution, [status(thm)], [c_18, c_1154])).
% 5.34/2.06  tff(c_1340, plain, (![B_226, A_16]: (~v1_xboole_0(B_226) | ~r1_tarski(A_16, B_226) | k1_xboole_0=A_16)), inference(resolution, [status(thm)], [c_30, c_1337])).
% 5.34/2.06  tff(c_2468, plain, (~v1_xboole_0(k1_xboole_0) | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2459, c_1340])).
% 5.34/2.06  tff(c_2476, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2468])).
% 5.34/2.06  tff(c_2913, plain, (![A_388]: (r2_hidden('#skF_1'(A_388), A_388) | A_388='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2476, c_30])).
% 5.34/2.06  tff(c_2524, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2476, c_2])).
% 5.34/2.06  tff(c_2458, plain, (![A_310]: (~r1_tarski(k1_relat_1('#skF_4'), A_310) | m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_1986])).
% 5.34/2.06  tff(c_2530, plain, (![A_310]: (~r1_tarski(k1_relat_1('#skF_4'), A_310) | m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2476, c_2458])).
% 5.34/2.06  tff(c_2561, plain, (![A_356]: (~r1_tarski(k1_relat_1('#skF_4'), A_356))), inference(splitLeft, [status(thm)], [c_2530])).
% 5.34/2.06  tff(c_2566, plain, $false, inference(resolution, [status(thm)], [c_8, c_2561])).
% 5.34/2.06  tff(c_2567, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2530])).
% 5.34/2.06  tff(c_20, plain, (![C_9, B_8, A_7]: (~v1_xboole_0(C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(C_9)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.34/2.06  tff(c_2598, plain, (![A_7]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_7, '#skF_4'))), inference(resolution, [status(thm)], [c_2567, c_20])).
% 5.34/2.06  tff(c_2604, plain, (![A_7]: (~r2_hidden(A_7, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2524, c_2598])).
% 5.34/2.06  tff(c_2928, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_2913, c_2604])).
% 5.34/2.06  tff(c_2605, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_2567, c_16])).
% 5.34/2.06  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.34/2.06  tff(c_2609, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_2605, c_4])).
% 5.34/2.06  tff(c_2911, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_2609])).
% 5.34/2.06  tff(c_2934, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2928, c_2911])).
% 5.34/2.06  tff(c_2967, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_2934])).
% 5.34/2.06  tff(c_2968, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_2609])).
% 5.34/2.06  tff(c_14, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.34/2.06  tff(c_129, plain, (![A_60, B_61]: (m1_subset_1('#skF_2'(A_60, B_61), k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.34/2.06  tff(c_135, plain, (![B_4]: (m1_subset_1('#skF_2'(k1_xboole_0, B_4), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_129])).
% 5.34/2.06  tff(c_1158, plain, (![A_199, B_4]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_199, '#skF_2'(k1_xboole_0, B_4)))), inference(resolution, [status(thm)], [c_135, c_1154])).
% 5.34/2.06  tff(c_1277, plain, (![A_216, B_217]: (~r2_hidden(A_216, '#skF_2'(k1_xboole_0, B_217)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1158])).
% 5.34/2.06  tff(c_1285, plain, (![B_217]: ('#skF_2'(k1_xboole_0, B_217)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_1277])).
% 5.34/2.06  tff(c_2610, plain, (![B_366]: ('#skF_2'('#skF_3', B_366)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2476, c_2476, c_1285])).
% 5.34/2.06  tff(c_48, plain, (![A_37, B_38]: (v1_funct_2('#skF_2'(A_37, B_38), A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.34/2.06  tff(c_2630, plain, (![B_366]: (v1_funct_2('#skF_3', '#skF_3', B_366))), inference(superposition, [status(thm), theory('equality')], [c_2610, c_48])).
% 5.34/2.06  tff(c_2984, plain, (![B_366]: (v1_funct_2('#skF_4', '#skF_4', B_366))), inference(demodulation, [status(thm), theory('equality')], [c_2968, c_2968, c_2630])).
% 5.34/2.06  tff(c_24, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.34/2.06  tff(c_2523, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2476, c_2476, c_24])).
% 5.34/2.06  tff(c_3000, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2968, c_2968, c_2523])).
% 5.34/2.06  tff(c_3008, plain, (~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2968, c_105])).
% 5.34/2.06  tff(c_3103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2984, c_3000, c_3008])).
% 5.34/2.06  tff(c_3104, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')))), inference(splitRight, [status(thm)], [c_68])).
% 5.34/2.06  tff(c_3559, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_3548, c_3104])).
% 5.34/2.06  tff(c_3572, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_8, c_62, c_3559])).
% 5.34/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.34/2.06  
% 5.34/2.06  Inference rules
% 5.34/2.06  ----------------------
% 5.34/2.06  #Ref     : 0
% 5.34/2.06  #Sup     : 716
% 5.34/2.06  #Fact    : 0
% 5.34/2.06  #Define  : 0
% 5.34/2.06  #Split   : 21
% 5.34/2.06  #Chain   : 0
% 5.34/2.06  #Close   : 0
% 5.34/2.06  
% 5.34/2.06  Ordering : KBO
% 5.34/2.06  
% 5.34/2.06  Simplification rules
% 5.34/2.06  ----------------------
% 5.34/2.06  #Subsume      : 66
% 5.34/2.06  #Demod        : 1022
% 5.34/2.06  #Tautology    : 390
% 5.34/2.06  #SimpNegUnit  : 3
% 5.34/2.06  #BackRed      : 256
% 5.34/2.06  
% 5.34/2.06  #Partial instantiations: 0
% 5.34/2.06  #Strategies tried      : 1
% 5.34/2.06  
% 5.34/2.06  Timing (in seconds)
% 5.34/2.06  ----------------------
% 5.34/2.06  Preprocessing        : 0.35
% 5.34/2.06  Parsing              : 0.18
% 5.34/2.06  CNF conversion       : 0.02
% 5.34/2.06  Main loop            : 0.90
% 5.34/2.06  Inferencing          : 0.30
% 5.34/2.06  Reduction            : 0.31
% 5.34/2.06  Demodulation         : 0.22
% 5.34/2.06  BG Simplification    : 0.04
% 5.34/2.06  Subsumption          : 0.18
% 5.34/2.06  Abstraction          : 0.04
% 5.34/2.06  MUC search           : 0.00
% 5.34/2.06  Cooper               : 0.00
% 5.34/2.06  Total                : 1.30
% 5.34/2.06  Index Insertion      : 0.00
% 5.34/2.06  Index Deletion       : 0.00
% 5.34/2.06  Index Matching       : 0.00
% 5.34/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
