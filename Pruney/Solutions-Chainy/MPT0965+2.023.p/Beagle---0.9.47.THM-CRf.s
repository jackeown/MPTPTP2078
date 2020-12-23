%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:03 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 153 expanded)
%              Number of leaves         :   37 (  69 expanded)
%              Depth                    :   10
%              Number of atoms          :  183 ( 361 expanded)
%              Number of equality atoms :   27 (  53 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(f_118,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_105,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_69,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_48,plain,(
    r2_hidden('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_56,plain,(
    ! [B_35,A_36] :
      ( ~ r2_hidden(B_35,A_36)
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_56])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_52,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_986,plain,(
    ! [A_233,B_234,C_235] :
      ( k1_relset_1(A_233,B_234,C_235) = k1_relat_1(C_235)
      | ~ m1_subset_1(C_235,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_995,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_986])).

tff(c_1244,plain,(
    ! [B_289,A_290,C_291] :
      ( k1_xboole_0 = B_289
      | k1_relset_1(A_290,B_289,C_291) = A_290
      | ~ v1_funct_2(C_291,A_290,B_289)
      | ~ m1_subset_1(C_291,k1_zfmisc_1(k2_zfmisc_1(A_290,B_289))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1255,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1244])).

tff(c_1260,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_995,c_1255])).

tff(c_1261,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1260])).

tff(c_22,plain,(
    ! [A_20,B_21] : v1_relat_1(k2_zfmisc_1(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_880,plain,(
    ! [B_200,A_201] :
      ( v1_relat_1(B_200)
      | ~ m1_subset_1(B_200,k1_zfmisc_1(A_201))
      | ~ v1_relat_1(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_886,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_880])).

tff(c_890,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_886])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_124,plain,(
    ! [C_57,B_58,A_59] :
      ( v5_relat_1(C_57,B_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_59,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_133,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_124])).

tff(c_86,plain,(
    ! [B_44,A_45] :
      ( v1_relat_1(B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_92,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_86])).

tff(c_96,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_92])).

tff(c_192,plain,(
    ! [A_77,B_78,C_79] :
      ( k1_relset_1(A_77,B_78,C_79) = k1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_201,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_192])).

tff(c_487,plain,(
    ! [B_142,A_143,C_144] :
      ( k1_xboole_0 = B_142
      | k1_relset_1(A_143,B_142,C_144) = A_143
      | ~ v1_funct_2(C_144,A_143,B_142)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_143,B_142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_498,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_487])).

tff(c_503,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_201,c_498])).

tff(c_504,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_503])).

tff(c_20,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k2_relat_1(B_19),A_18)
      | ~ v5_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_329,plain,(
    ! [B_108,A_109] :
      ( r2_hidden(k1_funct_1(B_108,A_109),k2_relat_1(B_108))
      | ~ r2_hidden(A_109,k1_relat_1(B_108))
      | ~ v1_funct_1(B_108)
      | ~ v1_relat_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_184,plain,(
    ! [A_73,C_74,B_75] :
      ( m1_subset_1(A_73,C_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(C_74))
      | ~ r2_hidden(A_73,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_189,plain,(
    ! [A_73,B_8,A_7] :
      ( m1_subset_1(A_73,B_8)
      | ~ r2_hidden(A_73,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(resolution,[status(thm)],[c_10,c_184])).

tff(c_793,plain,(
    ! [B_192,A_193,B_194] :
      ( m1_subset_1(k1_funct_1(B_192,A_193),B_194)
      | ~ r1_tarski(k2_relat_1(B_192),B_194)
      | ~ r2_hidden(A_193,k1_relat_1(B_192))
      | ~ v1_funct_1(B_192)
      | ~ v1_relat_1(B_192) ) ),
    inference(resolution,[status(thm)],[c_329,c_189])).

tff(c_797,plain,(
    ! [B_195,A_196,A_197] :
      ( m1_subset_1(k1_funct_1(B_195,A_196),A_197)
      | ~ r2_hidden(A_196,k1_relat_1(B_195))
      | ~ v1_funct_1(B_195)
      | ~ v5_relat_1(B_195,A_197)
      | ~ v1_relat_1(B_195) ) ),
    inference(resolution,[status(thm)],[c_20,c_793])).

tff(c_799,plain,(
    ! [A_196,A_197] :
      ( m1_subset_1(k1_funct_1('#skF_5',A_196),A_197)
      | ~ r2_hidden(A_196,'#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_197)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_504,c_797])).

tff(c_810,plain,(
    ! [A_198,A_199] :
      ( m1_subset_1(k1_funct_1('#skF_5',A_198),A_199)
      | ~ r2_hidden(A_198,'#skF_2')
      | ~ v5_relat_1('#skF_5',A_199) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_54,c_799])).

tff(c_76,plain,(
    ! [A_42,B_43] :
      ( r2_hidden(A_42,B_43)
      | v1_xboole_0(B_43)
      | ~ m1_subset_1(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_44,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_84,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1(k1_funct_1('#skF_5','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_44])).

tff(c_85,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_5','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_854,plain,
    ( ~ r2_hidden('#skF_4','#skF_2')
    | ~ v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_810,c_85])).

tff(c_877,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_48,c_854])).

tff(c_878,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_906,plain,(
    ! [C_207,B_208,A_209] :
      ( v5_relat_1(C_207,B_208)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(A_209,B_208))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_915,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_906])).

tff(c_939,plain,(
    ! [B_221,A_222] :
      ( r1_tarski(k2_relat_1(B_221),A_222)
      | ~ v5_relat_1(B_221,A_222)
      | ~ v1_relat_1(B_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_898,plain,(
    ! [C_204,B_205,A_206] :
      ( ~ v1_xboole_0(C_204)
      | ~ m1_subset_1(B_205,k1_zfmisc_1(C_204))
      | ~ r2_hidden(A_206,B_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_916,plain,(
    ! [B_210,A_211,A_212] :
      ( ~ v1_xboole_0(B_210)
      | ~ r2_hidden(A_211,A_212)
      | ~ r1_tarski(A_212,B_210) ) ),
    inference(resolution,[status(thm)],[c_10,c_898])).

tff(c_924,plain,(
    ! [B_210,A_1] :
      ( ~ v1_xboole_0(B_210)
      | ~ r1_tarski(A_1,B_210)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_916])).

tff(c_1087,plain,(
    ! [A_249,B_250] :
      ( ~ v1_xboole_0(A_249)
      | v1_xboole_0(k2_relat_1(B_250))
      | ~ v5_relat_1(B_250,A_249)
      | ~ v1_relat_1(B_250) ) ),
    inference(resolution,[status(thm)],[c_939,c_924])).

tff(c_1089,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_915,c_1087])).

tff(c_1092,plain,(
    v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_890,c_878,c_1089])).

tff(c_1057,plain,(
    ! [B_245,A_246] :
      ( r2_hidden(k1_funct_1(B_245,A_246),k2_relat_1(B_245))
      | ~ r2_hidden(A_246,k1_relat_1(B_245))
      | ~ v1_funct_1(B_245)
      | ~ v1_relat_1(B_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1109,plain,(
    ! [B_254,A_255] :
      ( ~ v1_xboole_0(k2_relat_1(B_254))
      | ~ r2_hidden(A_255,k1_relat_1(B_254))
      | ~ v1_funct_1(B_254)
      | ~ v1_relat_1(B_254) ) ),
    inference(resolution,[status(thm)],[c_1057,c_2])).

tff(c_1131,plain,(
    ! [B_258] :
      ( ~ v1_xboole_0(k2_relat_1(B_258))
      | ~ v1_funct_1(B_258)
      | ~ v1_relat_1(B_258)
      | v1_xboole_0(k1_relat_1(B_258)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1109])).

tff(c_1134,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1092,c_1131])).

tff(c_1137,plain,(
    v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_890,c_54,c_1134])).

tff(c_1262,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1261,c_1137])).

tff(c_1265,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1262])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:07:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.50  
% 3.28/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.50  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.28/1.50  
% 3.28/1.50  %Foreground sorts:
% 3.28/1.50  
% 3.28/1.50  
% 3.28/1.50  %Background operators:
% 3.28/1.50  
% 3.28/1.50  
% 3.28/1.50  %Foreground operators:
% 3.28/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.28/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.28/1.50  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.28/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.28/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.28/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.28/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.28/1.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.28/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.28/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.28/1.50  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.28/1.50  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.28/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.28/1.50  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.28/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.28/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.28/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.28/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.50  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.28/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.28/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.28/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.28/1.50  
% 3.28/1.52  tff(f_118, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 3.28/1.52  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.28/1.52  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.28/1.52  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.28/1.52  tff(f_69, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.28/1.52  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.28/1.52  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.28/1.52  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.28/1.52  tff(f_77, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 3.28/1.52  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.28/1.52  tff(f_47, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.28/1.52  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.28/1.52  tff(f_54, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.28/1.52  tff(c_48, plain, (r2_hidden('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.28/1.52  tff(c_56, plain, (![B_35, A_36]: (~r2_hidden(B_35, A_36) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.28/1.52  tff(c_60, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_56])).
% 3.28/1.52  tff(c_46, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.28/1.52  tff(c_52, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.28/1.52  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.28/1.52  tff(c_986, plain, (![A_233, B_234, C_235]: (k1_relset_1(A_233, B_234, C_235)=k1_relat_1(C_235) | ~m1_subset_1(C_235, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.28/1.52  tff(c_995, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_986])).
% 3.28/1.52  tff(c_1244, plain, (![B_289, A_290, C_291]: (k1_xboole_0=B_289 | k1_relset_1(A_290, B_289, C_291)=A_290 | ~v1_funct_2(C_291, A_290, B_289) | ~m1_subset_1(C_291, k1_zfmisc_1(k2_zfmisc_1(A_290, B_289))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.28/1.52  tff(c_1255, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_1244])).
% 3.28/1.52  tff(c_1260, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_995, c_1255])).
% 3.28/1.52  tff(c_1261, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_46, c_1260])).
% 3.28/1.52  tff(c_22, plain, (![A_20, B_21]: (v1_relat_1(k2_zfmisc_1(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.28/1.52  tff(c_880, plain, (![B_200, A_201]: (v1_relat_1(B_200) | ~m1_subset_1(B_200, k1_zfmisc_1(A_201)) | ~v1_relat_1(A_201))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.28/1.52  tff(c_886, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_50, c_880])).
% 3.28/1.52  tff(c_890, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_886])).
% 3.28/1.52  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.28/1.52  tff(c_124, plain, (![C_57, B_58, A_59]: (v5_relat_1(C_57, B_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_59, B_58))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.28/1.52  tff(c_133, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_124])).
% 3.28/1.52  tff(c_86, plain, (![B_44, A_45]: (v1_relat_1(B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_45)) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.28/1.52  tff(c_92, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_50, c_86])).
% 3.28/1.52  tff(c_96, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_92])).
% 3.28/1.52  tff(c_192, plain, (![A_77, B_78, C_79]: (k1_relset_1(A_77, B_78, C_79)=k1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.28/1.52  tff(c_201, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_192])).
% 3.28/1.52  tff(c_487, plain, (![B_142, A_143, C_144]: (k1_xboole_0=B_142 | k1_relset_1(A_143, B_142, C_144)=A_143 | ~v1_funct_2(C_144, A_143, B_142) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_143, B_142))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.28/1.52  tff(c_498, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_487])).
% 3.28/1.52  tff(c_503, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_201, c_498])).
% 3.28/1.52  tff(c_504, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_46, c_503])).
% 3.28/1.52  tff(c_20, plain, (![B_19, A_18]: (r1_tarski(k2_relat_1(B_19), A_18) | ~v5_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.28/1.52  tff(c_329, plain, (![B_108, A_109]: (r2_hidden(k1_funct_1(B_108, A_109), k2_relat_1(B_108)) | ~r2_hidden(A_109, k1_relat_1(B_108)) | ~v1_funct_1(B_108) | ~v1_relat_1(B_108))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.28/1.52  tff(c_10, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.28/1.52  tff(c_184, plain, (![A_73, C_74, B_75]: (m1_subset_1(A_73, C_74) | ~m1_subset_1(B_75, k1_zfmisc_1(C_74)) | ~r2_hidden(A_73, B_75))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.28/1.52  tff(c_189, plain, (![A_73, B_8, A_7]: (m1_subset_1(A_73, B_8) | ~r2_hidden(A_73, A_7) | ~r1_tarski(A_7, B_8))), inference(resolution, [status(thm)], [c_10, c_184])).
% 3.28/1.52  tff(c_793, plain, (![B_192, A_193, B_194]: (m1_subset_1(k1_funct_1(B_192, A_193), B_194) | ~r1_tarski(k2_relat_1(B_192), B_194) | ~r2_hidden(A_193, k1_relat_1(B_192)) | ~v1_funct_1(B_192) | ~v1_relat_1(B_192))), inference(resolution, [status(thm)], [c_329, c_189])).
% 3.28/1.52  tff(c_797, plain, (![B_195, A_196, A_197]: (m1_subset_1(k1_funct_1(B_195, A_196), A_197) | ~r2_hidden(A_196, k1_relat_1(B_195)) | ~v1_funct_1(B_195) | ~v5_relat_1(B_195, A_197) | ~v1_relat_1(B_195))), inference(resolution, [status(thm)], [c_20, c_793])).
% 3.28/1.52  tff(c_799, plain, (![A_196, A_197]: (m1_subset_1(k1_funct_1('#skF_5', A_196), A_197) | ~r2_hidden(A_196, '#skF_2') | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_197) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_504, c_797])).
% 3.28/1.52  tff(c_810, plain, (![A_198, A_199]: (m1_subset_1(k1_funct_1('#skF_5', A_198), A_199) | ~r2_hidden(A_198, '#skF_2') | ~v5_relat_1('#skF_5', A_199))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_54, c_799])).
% 3.28/1.52  tff(c_76, plain, (![A_42, B_43]: (r2_hidden(A_42, B_43) | v1_xboole_0(B_43) | ~m1_subset_1(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.28/1.52  tff(c_44, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.28/1.52  tff(c_84, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1(k1_funct_1('#skF_5', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_76, c_44])).
% 3.28/1.52  tff(c_85, plain, (~m1_subset_1(k1_funct_1('#skF_5', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_84])).
% 3.28/1.52  tff(c_854, plain, (~r2_hidden('#skF_4', '#skF_2') | ~v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_810, c_85])).
% 3.28/1.52  tff(c_877, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_133, c_48, c_854])).
% 3.28/1.52  tff(c_878, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_84])).
% 3.28/1.52  tff(c_906, plain, (![C_207, B_208, A_209]: (v5_relat_1(C_207, B_208) | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(A_209, B_208))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.28/1.52  tff(c_915, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_906])).
% 3.28/1.52  tff(c_939, plain, (![B_221, A_222]: (r1_tarski(k2_relat_1(B_221), A_222) | ~v5_relat_1(B_221, A_222) | ~v1_relat_1(B_221))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.28/1.52  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.28/1.52  tff(c_898, plain, (![C_204, B_205, A_206]: (~v1_xboole_0(C_204) | ~m1_subset_1(B_205, k1_zfmisc_1(C_204)) | ~r2_hidden(A_206, B_205))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.28/1.52  tff(c_916, plain, (![B_210, A_211, A_212]: (~v1_xboole_0(B_210) | ~r2_hidden(A_211, A_212) | ~r1_tarski(A_212, B_210))), inference(resolution, [status(thm)], [c_10, c_898])).
% 3.28/1.52  tff(c_924, plain, (![B_210, A_1]: (~v1_xboole_0(B_210) | ~r1_tarski(A_1, B_210) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_916])).
% 3.28/1.52  tff(c_1087, plain, (![A_249, B_250]: (~v1_xboole_0(A_249) | v1_xboole_0(k2_relat_1(B_250)) | ~v5_relat_1(B_250, A_249) | ~v1_relat_1(B_250))), inference(resolution, [status(thm)], [c_939, c_924])).
% 3.28/1.52  tff(c_1089, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0(k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_915, c_1087])).
% 3.28/1.52  tff(c_1092, plain, (v1_xboole_0(k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_890, c_878, c_1089])).
% 3.28/1.52  tff(c_1057, plain, (![B_245, A_246]: (r2_hidden(k1_funct_1(B_245, A_246), k2_relat_1(B_245)) | ~r2_hidden(A_246, k1_relat_1(B_245)) | ~v1_funct_1(B_245) | ~v1_relat_1(B_245))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.28/1.52  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.28/1.52  tff(c_1109, plain, (![B_254, A_255]: (~v1_xboole_0(k2_relat_1(B_254)) | ~r2_hidden(A_255, k1_relat_1(B_254)) | ~v1_funct_1(B_254) | ~v1_relat_1(B_254))), inference(resolution, [status(thm)], [c_1057, c_2])).
% 3.28/1.52  tff(c_1131, plain, (![B_258]: (~v1_xboole_0(k2_relat_1(B_258)) | ~v1_funct_1(B_258) | ~v1_relat_1(B_258) | v1_xboole_0(k1_relat_1(B_258)))), inference(resolution, [status(thm)], [c_4, c_1109])).
% 3.28/1.52  tff(c_1134, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | v1_xboole_0(k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_1092, c_1131])).
% 3.28/1.52  tff(c_1137, plain, (v1_xboole_0(k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_890, c_54, c_1134])).
% 3.28/1.52  tff(c_1262, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1261, c_1137])).
% 3.28/1.52  tff(c_1265, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_1262])).
% 3.28/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.52  
% 3.28/1.52  Inference rules
% 3.28/1.52  ----------------------
% 3.28/1.52  #Ref     : 0
% 3.28/1.52  #Sup     : 243
% 3.28/1.52  #Fact    : 0
% 3.28/1.52  #Define  : 0
% 3.28/1.52  #Split   : 10
% 3.28/1.52  #Chain   : 0
% 3.28/1.52  #Close   : 0
% 3.28/1.52  
% 3.28/1.52  Ordering : KBO
% 3.28/1.52  
% 3.28/1.52  Simplification rules
% 3.28/1.52  ----------------------
% 3.28/1.52  #Subsume      : 21
% 3.28/1.52  #Demod        : 45
% 3.28/1.52  #Tautology    : 25
% 3.28/1.52  #SimpNegUnit  : 8
% 3.28/1.52  #BackRed      : 3
% 3.28/1.52  
% 3.28/1.52  #Partial instantiations: 0
% 3.28/1.52  #Strategies tried      : 1
% 3.28/1.52  
% 3.28/1.52  Timing (in seconds)
% 3.28/1.52  ----------------------
% 3.28/1.52  Preprocessing        : 0.31
% 3.28/1.52  Parsing              : 0.16
% 3.28/1.52  CNF conversion       : 0.02
% 3.28/1.52  Main loop            : 0.45
% 3.28/1.52  Inferencing          : 0.17
% 3.28/1.52  Reduction            : 0.12
% 3.28/1.52  Demodulation         : 0.08
% 3.28/1.53  BG Simplification    : 0.02
% 3.28/1.53  Subsumption          : 0.09
% 3.28/1.53  Abstraction          : 0.02
% 3.28/1.53  MUC search           : 0.00
% 3.28/1.53  Cooper               : 0.00
% 3.28/1.53  Total                : 0.80
% 3.28/1.53  Index Insertion      : 0.00
% 3.28/1.53  Index Deletion       : 0.00
% 3.28/1.53  Index Matching       : 0.00
% 3.28/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
