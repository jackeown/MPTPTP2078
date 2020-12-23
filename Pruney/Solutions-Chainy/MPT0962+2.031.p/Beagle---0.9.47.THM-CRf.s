%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:55 EST 2020

% Result     : Theorem 4.59s
% Output     : CNFRefutation 4.59s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 344 expanded)
%              Number of leaves         :   31 ( 127 expanded)
%              Depth                    :   10
%              Number of atoms          :  241 ( 886 expanded)
%              Number of equality atoms :   69 ( 174 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k3_mcart_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_83,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,axiom,(
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

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(c_54,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_50,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2390,plain,(
    ! [C_536,A_537,B_538] :
      ( m1_subset_1(C_536,k1_zfmisc_1(k2_zfmisc_1(A_537,B_538)))
      | ~ r1_tarski(k2_relat_1(C_536),B_538)
      | ~ r1_tarski(k1_relat_1(C_536),A_537)
      | ~ v1_relat_1(C_536) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_48,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_56,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48])).

tff(c_74,plain,(
    ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_30,plain,(
    ! [A_20] :
      ( r2_hidden('#skF_2'(A_20),A_20)
      | k1_xboole_0 = A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_139,plain,(
    ! [C_58,B_59,A_60] :
      ( r2_hidden(C_58,B_59)
      | ~ r2_hidden(C_58,A_60)
      | ~ r1_tarski(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_153,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_2'(A_65),B_66)
      | ~ r1_tarski(A_65,B_66)
      | k1_xboole_0 = A_65 ) ),
    inference(resolution,[status(thm)],[c_30,c_139])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_275,plain,(
    ! [A_101,B_102,B_103] :
      ( r2_hidden('#skF_2'(A_101),B_102)
      | ~ r1_tarski(B_103,B_102)
      | ~ r1_tarski(A_101,B_103)
      | k1_xboole_0 = A_101 ) ),
    inference(resolution,[status(thm)],[c_153,c_2])).

tff(c_285,plain,(
    ! [A_104] :
      ( r2_hidden('#skF_2'(A_104),'#skF_3')
      | ~ r1_tarski(A_104,k2_relat_1('#skF_4'))
      | k1_xboole_0 = A_104 ) ),
    inference(resolution,[status(thm)],[c_50,c_275])).

tff(c_32,plain,(
    ! [D_32,A_20,C_31,E_33] :
      ( ~ r2_hidden(D_32,A_20)
      | k3_mcart_1(C_31,D_32,E_33) != '#skF_2'(A_20)
      | k1_xboole_0 = A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_295,plain,(
    ! [C_31,A_104,E_33] :
      ( k3_mcart_1(C_31,'#skF_2'(A_104),E_33) != '#skF_2'('#skF_3')
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(A_104,k2_relat_1('#skF_4'))
      | k1_xboole_0 = A_104 ) ),
    inference(resolution,[status(thm)],[c_285,c_32])).

tff(c_386,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_295])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_321,plain,(
    ! [A_119,B_120] :
      ( r2_hidden('#skF_2'(A_119),B_120)
      | ~ r1_tarski('#skF_3',B_120)
      | ~ r1_tarski(A_119,k2_relat_1('#skF_4'))
      | k1_xboole_0 = A_119 ) ),
    inference(resolution,[status(thm)],[c_285,c_2])).

tff(c_24,plain,(
    ! [B_13,A_12] :
      ( ~ r1_tarski(B_13,A_12)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_335,plain,(
    ! [B_121,A_122] :
      ( ~ r1_tarski(B_121,'#skF_2'(A_122))
      | ~ r1_tarski('#skF_3',B_121)
      | ~ r1_tarski(A_122,k2_relat_1('#skF_4'))
      | k1_xboole_0 = A_122 ) ),
    inference(resolution,[status(thm)],[c_321,c_24])).

tff(c_343,plain,(
    ! [A_122] :
      ( ~ r1_tarski('#skF_3',k1_xboole_0)
      | ~ r1_tarski(A_122,k2_relat_1('#skF_4'))
      | k1_xboole_0 = A_122 ) ),
    inference(resolution,[status(thm)],[c_14,c_335])).

tff(c_344,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_343])).

tff(c_392,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_344])).

tff(c_423,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_392])).

tff(c_425,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_295])).

tff(c_439,plain,(
    ! [C_135,A_136,B_137] :
      ( m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137)))
      | ~ r1_tarski(k2_relat_1(C_135),B_137)
      | ~ r1_tarski(k1_relat_1(C_135),A_136)
      | ~ v1_relat_1(C_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_512,plain,(
    ! [C_155,A_156,B_157] :
      ( r1_tarski(C_155,k2_zfmisc_1(A_156,B_157))
      | ~ r1_tarski(k2_relat_1(C_155),B_157)
      | ~ r1_tarski(k1_relat_1(C_155),A_156)
      | ~ v1_relat_1(C_155) ) ),
    inference(resolution,[status(thm)],[c_439,c_16])).

tff(c_514,plain,(
    ! [A_156] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_156,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_156)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_512])).

tff(c_522,plain,(
    ! [A_158] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_158,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_514])).

tff(c_527,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_522])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_235,plain,(
    ! [A_88,B_89,C_90] :
      ( k1_relset_1(A_88,B_89,C_90) = k1_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_240,plain,(
    ! [A_88,B_89,A_9] :
      ( k1_relset_1(A_88,B_89,A_9) = k1_relat_1(A_9)
      | ~ r1_tarski(A_9,k2_zfmisc_1(A_88,B_89)) ) ),
    inference(resolution,[status(thm)],[c_18,c_235])).

tff(c_539,plain,(
    k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_527,c_240])).

tff(c_641,plain,(
    ! [B_173,C_174,A_175] :
      ( k1_xboole_0 = B_173
      | v1_funct_2(C_174,A_175,B_173)
      | k1_relset_1(A_175,B_173,C_174) != A_175
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_175,B_173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_864,plain,(
    ! [B_206,A_207,A_208] :
      ( k1_xboole_0 = B_206
      | v1_funct_2(A_207,A_208,B_206)
      | k1_relset_1(A_208,B_206,A_207) != A_208
      | ~ r1_tarski(A_207,k2_zfmisc_1(A_208,B_206)) ) ),
    inference(resolution,[status(thm)],[c_18,c_641])).

tff(c_873,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3')
    | k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') != k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_527,c_864])).

tff(c_888,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_539,c_873])).

tff(c_890,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_425,c_888])).

tff(c_892,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_343])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_187,plain,(
    ! [A_79,B_80,B_81] :
      ( r2_hidden('#skF_1'(A_79,B_80),B_81)
      | ~ r1_tarski(A_79,B_81)
      | r1_tarski(A_79,B_80) ) ),
    inference(resolution,[status(thm)],[c_6,c_139])).

tff(c_206,plain,(
    ! [B_82,A_83,B_84] :
      ( ~ r1_tarski(B_82,'#skF_1'(A_83,B_84))
      | ~ r1_tarski(A_83,B_82)
      | r1_tarski(A_83,B_84) ) ),
    inference(resolution,[status(thm)],[c_187,c_24])).

tff(c_216,plain,(
    ! [A_83,B_84] :
      ( ~ r1_tarski(A_83,k1_xboole_0)
      | r1_tarski(A_83,B_84) ) ),
    inference(resolution,[status(thm)],[c_14,c_206])).

tff(c_909,plain,(
    ! [B_84] : r1_tarski('#skF_3',B_84) ),
    inference(resolution,[status(thm)],[c_892,c_216])).

tff(c_105,plain,(
    ! [B_53,A_54] :
      ( B_53 = A_54
      | ~ r1_tarski(B_53,A_54)
      | ~ r1_tarski(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_112,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_50,c_105])).

tff(c_131,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_960,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_909,c_131])).

tff(c_961,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_85,plain,(
    ! [A_49] :
      ( k2_relat_1(A_49) = k1_xboole_0
      | k1_relat_1(A_49) != k1_xboole_0
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_89,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_85])).

tff(c_90,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_98,plain,(
    ! [A_52] :
      ( k1_relat_1(A_52) = k1_xboole_0
      | k2_relat_1(A_52) != k1_xboole_0
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_101,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_98])).

tff(c_104,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_101])).

tff(c_963,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_961,c_104])).

tff(c_1190,plain,(
    ! [C_281,A_282,B_283] :
      ( m1_subset_1(C_281,k1_zfmisc_1(k2_zfmisc_1(A_282,B_283)))
      | ~ r1_tarski(k2_relat_1(C_281),B_283)
      | ~ r1_tarski(k1_relat_1(C_281),A_282)
      | ~ v1_relat_1(C_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1238,plain,(
    ! [C_300,A_301,B_302] :
      ( r1_tarski(C_300,k2_zfmisc_1(A_301,B_302))
      | ~ r1_tarski(k2_relat_1(C_300),B_302)
      | ~ r1_tarski(k1_relat_1(C_300),A_301)
      | ~ v1_relat_1(C_300) ) ),
    inference(resolution,[status(thm)],[c_1190,c_16])).

tff(c_1247,plain,(
    ! [C_303,A_304] :
      ( r1_tarski(C_303,k2_zfmisc_1(A_304,k2_relat_1(C_303)))
      | ~ r1_tarski(k1_relat_1(C_303),A_304)
      | ~ v1_relat_1(C_303) ) ),
    inference(resolution,[status(thm)],[c_12,c_1238])).

tff(c_1270,plain,(
    ! [A_304] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_304,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_304)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_961,c_1247])).

tff(c_1280,plain,(
    ! [A_305] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_305,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_305) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1270])).

tff(c_1290,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_1280])).

tff(c_1075,plain,(
    ! [A_245,B_246,C_247] :
      ( k1_relset_1(A_245,B_246,C_247) = k1_relat_1(C_247)
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k2_zfmisc_1(A_245,B_246))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1080,plain,(
    ! [A_245,B_246,A_9] :
      ( k1_relset_1(A_245,B_246,A_9) = k1_relat_1(A_9)
      | ~ r1_tarski(A_9,k2_zfmisc_1(A_245,B_246)) ) ),
    inference(resolution,[status(thm)],[c_18,c_1075])).

tff(c_1302,plain,(
    k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1290,c_1080])).

tff(c_1304,plain,(
    ! [B_306,C_307,A_308] :
      ( k1_xboole_0 = B_306
      | v1_funct_2(C_307,A_308,B_306)
      | k1_relset_1(A_308,B_306,C_307) != A_308
      | ~ m1_subset_1(C_307,k1_zfmisc_1(k2_zfmisc_1(A_308,B_306))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1531,plain,(
    ! [B_328,A_329,A_330] :
      ( k1_xboole_0 = B_328
      | v1_funct_2(A_329,A_330,B_328)
      | k1_relset_1(A_330,B_328,A_329) != A_330
      | ~ r1_tarski(A_329,k2_zfmisc_1(A_330,B_328)) ) ),
    inference(resolution,[status(thm)],[c_18,c_1304])).

tff(c_1540,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3')
    | k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') != k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1290,c_1531])).

tff(c_1558,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1302,c_1540])).

tff(c_1560,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_963,c_1558])).

tff(c_1562,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_1561,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_1835,plain,(
    ! [C_407,A_408,B_409] :
      ( m1_subset_1(C_407,k1_zfmisc_1(k2_zfmisc_1(A_408,B_409)))
      | ~ r1_tarski(k2_relat_1(C_407),B_409)
      | ~ r1_tarski(k1_relat_1(C_407),A_408)
      | ~ v1_relat_1(C_407) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1878,plain,(
    ! [C_425,A_426,B_427] :
      ( r1_tarski(C_425,k2_zfmisc_1(A_426,B_427))
      | ~ r1_tarski(k2_relat_1(C_425),B_427)
      | ~ r1_tarski(k1_relat_1(C_425),A_426)
      | ~ v1_relat_1(C_425) ) ),
    inference(resolution,[status(thm)],[c_1835,c_16])).

tff(c_1880,plain,(
    ! [A_426,B_427] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_426,B_427))
      | ~ r1_tarski(k1_xboole_0,B_427)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_426)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1561,c_1878])).

tff(c_1887,plain,(
    ! [A_428,B_429] : r1_tarski('#skF_4',k2_zfmisc_1(A_428,B_429)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_14,c_1562,c_14,c_1880])).

tff(c_1714,plain,(
    ! [A_369,B_370,C_371] :
      ( k1_relset_1(A_369,B_370,C_371) = k1_relat_1(C_371)
      | ~ m1_subset_1(C_371,k1_zfmisc_1(k2_zfmisc_1(A_369,B_370))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1719,plain,(
    ! [A_369,B_370,A_9] :
      ( k1_relset_1(A_369,B_370,A_9) = k1_relat_1(A_9)
      | ~ r1_tarski(A_9,k2_zfmisc_1(A_369,B_370)) ) ),
    inference(resolution,[status(thm)],[c_18,c_1714])).

tff(c_1906,plain,(
    ! [A_428,B_429] : k1_relset_1(A_428,B_429,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1887,c_1719])).

tff(c_1915,plain,(
    ! [A_428,B_429] : k1_relset_1(A_428,B_429,'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1562,c_1906])).

tff(c_1775,plain,(
    ! [C_392,B_393] :
      ( v1_funct_2(C_392,k1_xboole_0,B_393)
      | k1_relset_1(k1_xboole_0,B_393,C_392) != k1_xboole_0
      | ~ m1_subset_1(C_392,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_393))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1780,plain,(
    ! [A_9,B_393] :
      ( v1_funct_2(A_9,k1_xboole_0,B_393)
      | k1_relset_1(k1_xboole_0,B_393,A_9) != k1_xboole_0
      | ~ r1_tarski(A_9,k2_zfmisc_1(k1_xboole_0,B_393)) ) ),
    inference(resolution,[status(thm)],[c_18,c_1775])).

tff(c_1911,plain,(
    ! [B_429] :
      ( v1_funct_2('#skF_4',k1_xboole_0,B_429)
      | k1_relset_1(k1_xboole_0,B_429,'#skF_4') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1887,c_1780])).

tff(c_2015,plain,(
    ! [B_429] : v1_funct_2('#skF_4',k1_xboole_0,B_429) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1915,c_1911])).

tff(c_1569,plain,(
    ~ v1_funct_2('#skF_4',k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1562,c_74])).

tff(c_2018,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2015,c_1569])).

tff(c_2019,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2408,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2390,c_2019])).

tff(c_2419,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_12,c_50,c_2408])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:24:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.59/1.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.59/1.86  
% 4.59/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.59/1.86  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k3_mcart_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.59/1.86  
% 4.59/1.86  %Foreground sorts:
% 4.59/1.86  
% 4.59/1.86  
% 4.59/1.86  %Background operators:
% 4.59/1.86  
% 4.59/1.86  
% 4.59/1.86  %Foreground operators:
% 4.59/1.86  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.59/1.86  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.59/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.59/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.59/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.59/1.86  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 4.59/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.59/1.86  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.59/1.86  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.59/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.59/1.86  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.59/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.59/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.59/1.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.59/1.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.59/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.59/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.59/1.86  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.59/1.86  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.59/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.59/1.86  
% 4.59/1.88  tff(f_114, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 4.59/1.88  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.59/1.88  tff(f_67, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 4.59/1.88  tff(f_83, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 4.59/1.88  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.59/1.88  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.59/1.88  tff(f_55, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.59/1.88  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.59/1.88  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.59/1.88  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.59/1.88  tff(f_50, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 4.59/1.88  tff(c_54, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.59/1.88  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.59/1.88  tff(c_50, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.59/1.88  tff(c_2390, plain, (![C_536, A_537, B_538]: (m1_subset_1(C_536, k1_zfmisc_1(k2_zfmisc_1(A_537, B_538))) | ~r1_tarski(k2_relat_1(C_536), B_538) | ~r1_tarski(k1_relat_1(C_536), A_537) | ~v1_relat_1(C_536))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.59/1.88  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.59/1.88  tff(c_48, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.59/1.88  tff(c_56, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48])).
% 4.59/1.88  tff(c_74, plain, (~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_56])).
% 4.59/1.88  tff(c_30, plain, (![A_20]: (r2_hidden('#skF_2'(A_20), A_20) | k1_xboole_0=A_20)), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.59/1.88  tff(c_139, plain, (![C_58, B_59, A_60]: (r2_hidden(C_58, B_59) | ~r2_hidden(C_58, A_60) | ~r1_tarski(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.59/1.88  tff(c_153, plain, (![A_65, B_66]: (r2_hidden('#skF_2'(A_65), B_66) | ~r1_tarski(A_65, B_66) | k1_xboole_0=A_65)), inference(resolution, [status(thm)], [c_30, c_139])).
% 4.59/1.88  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.59/1.88  tff(c_275, plain, (![A_101, B_102, B_103]: (r2_hidden('#skF_2'(A_101), B_102) | ~r1_tarski(B_103, B_102) | ~r1_tarski(A_101, B_103) | k1_xboole_0=A_101)), inference(resolution, [status(thm)], [c_153, c_2])).
% 4.59/1.88  tff(c_285, plain, (![A_104]: (r2_hidden('#skF_2'(A_104), '#skF_3') | ~r1_tarski(A_104, k2_relat_1('#skF_4')) | k1_xboole_0=A_104)), inference(resolution, [status(thm)], [c_50, c_275])).
% 4.59/1.88  tff(c_32, plain, (![D_32, A_20, C_31, E_33]: (~r2_hidden(D_32, A_20) | k3_mcart_1(C_31, D_32, E_33)!='#skF_2'(A_20) | k1_xboole_0=A_20)), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.59/1.88  tff(c_295, plain, (![C_31, A_104, E_33]: (k3_mcart_1(C_31, '#skF_2'(A_104), E_33)!='#skF_2'('#skF_3') | k1_xboole_0='#skF_3' | ~r1_tarski(A_104, k2_relat_1('#skF_4')) | k1_xboole_0=A_104)), inference(resolution, [status(thm)], [c_285, c_32])).
% 4.59/1.88  tff(c_386, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_295])).
% 4.59/1.88  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.59/1.88  tff(c_321, plain, (![A_119, B_120]: (r2_hidden('#skF_2'(A_119), B_120) | ~r1_tarski('#skF_3', B_120) | ~r1_tarski(A_119, k2_relat_1('#skF_4')) | k1_xboole_0=A_119)), inference(resolution, [status(thm)], [c_285, c_2])).
% 4.59/1.88  tff(c_24, plain, (![B_13, A_12]: (~r1_tarski(B_13, A_12) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.59/1.88  tff(c_335, plain, (![B_121, A_122]: (~r1_tarski(B_121, '#skF_2'(A_122)) | ~r1_tarski('#skF_3', B_121) | ~r1_tarski(A_122, k2_relat_1('#skF_4')) | k1_xboole_0=A_122)), inference(resolution, [status(thm)], [c_321, c_24])).
% 4.59/1.88  tff(c_343, plain, (![A_122]: (~r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski(A_122, k2_relat_1('#skF_4')) | k1_xboole_0=A_122)), inference(resolution, [status(thm)], [c_14, c_335])).
% 4.59/1.88  tff(c_344, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_343])).
% 4.59/1.88  tff(c_392, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_386, c_344])).
% 4.59/1.88  tff(c_423, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_392])).
% 4.59/1.88  tff(c_425, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_295])).
% 4.59/1.88  tff(c_439, plain, (![C_135, A_136, B_137]: (m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))) | ~r1_tarski(k2_relat_1(C_135), B_137) | ~r1_tarski(k1_relat_1(C_135), A_136) | ~v1_relat_1(C_135))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.59/1.88  tff(c_16, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.59/1.88  tff(c_512, plain, (![C_155, A_156, B_157]: (r1_tarski(C_155, k2_zfmisc_1(A_156, B_157)) | ~r1_tarski(k2_relat_1(C_155), B_157) | ~r1_tarski(k1_relat_1(C_155), A_156) | ~v1_relat_1(C_155))), inference(resolution, [status(thm)], [c_439, c_16])).
% 4.59/1.88  tff(c_514, plain, (![A_156]: (r1_tarski('#skF_4', k2_zfmisc_1(A_156, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_156) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_512])).
% 4.59/1.88  tff(c_522, plain, (![A_158]: (r1_tarski('#skF_4', k2_zfmisc_1(A_158, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_158))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_514])).
% 4.59/1.88  tff(c_527, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_522])).
% 4.59/1.88  tff(c_18, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.59/1.88  tff(c_235, plain, (![A_88, B_89, C_90]: (k1_relset_1(A_88, B_89, C_90)=k1_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.59/1.88  tff(c_240, plain, (![A_88, B_89, A_9]: (k1_relset_1(A_88, B_89, A_9)=k1_relat_1(A_9) | ~r1_tarski(A_9, k2_zfmisc_1(A_88, B_89)))), inference(resolution, [status(thm)], [c_18, c_235])).
% 4.59/1.88  tff(c_539, plain, (k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_527, c_240])).
% 4.59/1.88  tff(c_641, plain, (![B_173, C_174, A_175]: (k1_xboole_0=B_173 | v1_funct_2(C_174, A_175, B_173) | k1_relset_1(A_175, B_173, C_174)!=A_175 | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_175, B_173))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.59/1.88  tff(c_864, plain, (![B_206, A_207, A_208]: (k1_xboole_0=B_206 | v1_funct_2(A_207, A_208, B_206) | k1_relset_1(A_208, B_206, A_207)!=A_208 | ~r1_tarski(A_207, k2_zfmisc_1(A_208, B_206)))), inference(resolution, [status(thm)], [c_18, c_641])).
% 4.59/1.88  tff(c_873, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3') | k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')!=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_527, c_864])).
% 4.59/1.88  tff(c_888, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_539, c_873])).
% 4.59/1.88  tff(c_890, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_425, c_888])).
% 4.59/1.88  tff(c_892, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_343])).
% 4.59/1.88  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.59/1.88  tff(c_187, plain, (![A_79, B_80, B_81]: (r2_hidden('#skF_1'(A_79, B_80), B_81) | ~r1_tarski(A_79, B_81) | r1_tarski(A_79, B_80))), inference(resolution, [status(thm)], [c_6, c_139])).
% 4.59/1.88  tff(c_206, plain, (![B_82, A_83, B_84]: (~r1_tarski(B_82, '#skF_1'(A_83, B_84)) | ~r1_tarski(A_83, B_82) | r1_tarski(A_83, B_84))), inference(resolution, [status(thm)], [c_187, c_24])).
% 4.59/1.88  tff(c_216, plain, (![A_83, B_84]: (~r1_tarski(A_83, k1_xboole_0) | r1_tarski(A_83, B_84))), inference(resolution, [status(thm)], [c_14, c_206])).
% 4.59/1.88  tff(c_909, plain, (![B_84]: (r1_tarski('#skF_3', B_84))), inference(resolution, [status(thm)], [c_892, c_216])).
% 4.59/1.88  tff(c_105, plain, (![B_53, A_54]: (B_53=A_54 | ~r1_tarski(B_53, A_54) | ~r1_tarski(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.59/1.88  tff(c_112, plain, (k2_relat_1('#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_105])).
% 4.59/1.88  tff(c_131, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_112])).
% 4.59/1.88  tff(c_960, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_909, c_131])).
% 4.59/1.88  tff(c_961, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_112])).
% 4.59/1.88  tff(c_85, plain, (![A_49]: (k2_relat_1(A_49)=k1_xboole_0 | k1_relat_1(A_49)!=k1_xboole_0 | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.59/1.88  tff(c_89, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_85])).
% 4.59/1.88  tff(c_90, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_89])).
% 4.59/1.88  tff(c_98, plain, (![A_52]: (k1_relat_1(A_52)=k1_xboole_0 | k2_relat_1(A_52)!=k1_xboole_0 | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.59/1.88  tff(c_101, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_98])).
% 4.59/1.88  tff(c_104, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_90, c_101])).
% 4.59/1.88  tff(c_963, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_961, c_104])).
% 4.59/1.88  tff(c_1190, plain, (![C_281, A_282, B_283]: (m1_subset_1(C_281, k1_zfmisc_1(k2_zfmisc_1(A_282, B_283))) | ~r1_tarski(k2_relat_1(C_281), B_283) | ~r1_tarski(k1_relat_1(C_281), A_282) | ~v1_relat_1(C_281))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.59/1.88  tff(c_1238, plain, (![C_300, A_301, B_302]: (r1_tarski(C_300, k2_zfmisc_1(A_301, B_302)) | ~r1_tarski(k2_relat_1(C_300), B_302) | ~r1_tarski(k1_relat_1(C_300), A_301) | ~v1_relat_1(C_300))), inference(resolution, [status(thm)], [c_1190, c_16])).
% 4.59/1.88  tff(c_1247, plain, (![C_303, A_304]: (r1_tarski(C_303, k2_zfmisc_1(A_304, k2_relat_1(C_303))) | ~r1_tarski(k1_relat_1(C_303), A_304) | ~v1_relat_1(C_303))), inference(resolution, [status(thm)], [c_12, c_1238])).
% 4.59/1.88  tff(c_1270, plain, (![A_304]: (r1_tarski('#skF_4', k2_zfmisc_1(A_304, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_304) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_961, c_1247])).
% 4.59/1.88  tff(c_1280, plain, (![A_305]: (r1_tarski('#skF_4', k2_zfmisc_1(A_305, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_305))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1270])).
% 4.59/1.88  tff(c_1290, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_1280])).
% 4.59/1.88  tff(c_1075, plain, (![A_245, B_246, C_247]: (k1_relset_1(A_245, B_246, C_247)=k1_relat_1(C_247) | ~m1_subset_1(C_247, k1_zfmisc_1(k2_zfmisc_1(A_245, B_246))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.59/1.88  tff(c_1080, plain, (![A_245, B_246, A_9]: (k1_relset_1(A_245, B_246, A_9)=k1_relat_1(A_9) | ~r1_tarski(A_9, k2_zfmisc_1(A_245, B_246)))), inference(resolution, [status(thm)], [c_18, c_1075])).
% 4.59/1.88  tff(c_1302, plain, (k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1290, c_1080])).
% 4.59/1.88  tff(c_1304, plain, (![B_306, C_307, A_308]: (k1_xboole_0=B_306 | v1_funct_2(C_307, A_308, B_306) | k1_relset_1(A_308, B_306, C_307)!=A_308 | ~m1_subset_1(C_307, k1_zfmisc_1(k2_zfmisc_1(A_308, B_306))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.59/1.88  tff(c_1531, plain, (![B_328, A_329, A_330]: (k1_xboole_0=B_328 | v1_funct_2(A_329, A_330, B_328) | k1_relset_1(A_330, B_328, A_329)!=A_330 | ~r1_tarski(A_329, k2_zfmisc_1(A_330, B_328)))), inference(resolution, [status(thm)], [c_18, c_1304])).
% 4.59/1.88  tff(c_1540, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3') | k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')!=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1290, c_1531])).
% 4.59/1.88  tff(c_1558, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1302, c_1540])).
% 4.59/1.88  tff(c_1560, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_963, c_1558])).
% 4.59/1.88  tff(c_1562, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_89])).
% 4.59/1.88  tff(c_1561, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_89])).
% 4.59/1.88  tff(c_1835, plain, (![C_407, A_408, B_409]: (m1_subset_1(C_407, k1_zfmisc_1(k2_zfmisc_1(A_408, B_409))) | ~r1_tarski(k2_relat_1(C_407), B_409) | ~r1_tarski(k1_relat_1(C_407), A_408) | ~v1_relat_1(C_407))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.59/1.88  tff(c_1878, plain, (![C_425, A_426, B_427]: (r1_tarski(C_425, k2_zfmisc_1(A_426, B_427)) | ~r1_tarski(k2_relat_1(C_425), B_427) | ~r1_tarski(k1_relat_1(C_425), A_426) | ~v1_relat_1(C_425))), inference(resolution, [status(thm)], [c_1835, c_16])).
% 4.59/1.88  tff(c_1880, plain, (![A_426, B_427]: (r1_tarski('#skF_4', k2_zfmisc_1(A_426, B_427)) | ~r1_tarski(k1_xboole_0, B_427) | ~r1_tarski(k1_relat_1('#skF_4'), A_426) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1561, c_1878])).
% 4.59/1.88  tff(c_1887, plain, (![A_428, B_429]: (r1_tarski('#skF_4', k2_zfmisc_1(A_428, B_429)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_14, c_1562, c_14, c_1880])).
% 4.59/1.88  tff(c_1714, plain, (![A_369, B_370, C_371]: (k1_relset_1(A_369, B_370, C_371)=k1_relat_1(C_371) | ~m1_subset_1(C_371, k1_zfmisc_1(k2_zfmisc_1(A_369, B_370))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.59/1.88  tff(c_1719, plain, (![A_369, B_370, A_9]: (k1_relset_1(A_369, B_370, A_9)=k1_relat_1(A_9) | ~r1_tarski(A_9, k2_zfmisc_1(A_369, B_370)))), inference(resolution, [status(thm)], [c_18, c_1714])).
% 4.59/1.88  tff(c_1906, plain, (![A_428, B_429]: (k1_relset_1(A_428, B_429, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1887, c_1719])).
% 4.59/1.88  tff(c_1915, plain, (![A_428, B_429]: (k1_relset_1(A_428, B_429, '#skF_4')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1562, c_1906])).
% 4.59/1.88  tff(c_1775, plain, (![C_392, B_393]: (v1_funct_2(C_392, k1_xboole_0, B_393) | k1_relset_1(k1_xboole_0, B_393, C_392)!=k1_xboole_0 | ~m1_subset_1(C_392, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_393))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.59/1.88  tff(c_1780, plain, (![A_9, B_393]: (v1_funct_2(A_9, k1_xboole_0, B_393) | k1_relset_1(k1_xboole_0, B_393, A_9)!=k1_xboole_0 | ~r1_tarski(A_9, k2_zfmisc_1(k1_xboole_0, B_393)))), inference(resolution, [status(thm)], [c_18, c_1775])).
% 4.59/1.88  tff(c_1911, plain, (![B_429]: (v1_funct_2('#skF_4', k1_xboole_0, B_429) | k1_relset_1(k1_xboole_0, B_429, '#skF_4')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1887, c_1780])).
% 4.59/1.88  tff(c_2015, plain, (![B_429]: (v1_funct_2('#skF_4', k1_xboole_0, B_429))), inference(demodulation, [status(thm), theory('equality')], [c_1915, c_1911])).
% 4.59/1.88  tff(c_1569, plain, (~v1_funct_2('#skF_4', k1_xboole_0, '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1562, c_74])).
% 4.59/1.88  tff(c_2018, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2015, c_1569])).
% 4.59/1.88  tff(c_2019, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')))), inference(splitRight, [status(thm)], [c_56])).
% 4.59/1.88  tff(c_2408, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2390, c_2019])).
% 4.59/1.88  tff(c_2419, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_12, c_50, c_2408])).
% 4.59/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.59/1.88  
% 4.59/1.88  Inference rules
% 4.59/1.88  ----------------------
% 4.59/1.88  #Ref     : 0
% 4.59/1.88  #Sup     : 464
% 4.59/1.88  #Fact    : 0
% 4.59/1.88  #Define  : 0
% 4.59/1.88  #Split   : 19
% 4.59/1.88  #Chain   : 0
% 4.59/1.88  #Close   : 0
% 4.59/1.88  
% 4.59/1.88  Ordering : KBO
% 4.59/1.88  
% 4.59/1.88  Simplification rules
% 4.59/1.88  ----------------------
% 4.59/1.88  #Subsume      : 48
% 4.59/1.88  #Demod        : 337
% 4.59/1.88  #Tautology    : 120
% 4.59/1.88  #SimpNegUnit  : 17
% 4.59/1.88  #BackRed      : 135
% 4.59/1.88  
% 4.59/1.88  #Partial instantiations: 0
% 4.59/1.88  #Strategies tried      : 1
% 4.59/1.88  
% 4.59/1.88  Timing (in seconds)
% 4.59/1.88  ----------------------
% 4.59/1.88  Preprocessing        : 0.34
% 4.59/1.88  Parsing              : 0.18
% 4.59/1.88  CNF conversion       : 0.02
% 4.59/1.88  Main loop            : 0.71
% 4.59/1.88  Inferencing          : 0.24
% 4.59/1.88  Reduction            : 0.20
% 4.59/1.88  Demodulation         : 0.13
% 4.59/1.88  BG Simplification    : 0.03
% 4.59/1.88  Subsumption          : 0.17
% 4.59/1.88  Abstraction          : 0.04
% 4.59/1.88  MUC search           : 0.00
% 4.59/1.88  Cooper               : 0.00
% 4.59/1.88  Total                : 1.09
% 4.59/1.88  Index Insertion      : 0.00
% 4.59/1.88  Index Deletion       : 0.00
% 4.59/1.88  Index Matching       : 0.00
% 4.59/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
