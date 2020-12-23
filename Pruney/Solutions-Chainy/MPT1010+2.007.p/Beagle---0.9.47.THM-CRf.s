%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:06 EST 2020

% Result     : Theorem 13.98s
% Output     : CNFRefutation 13.98s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 130 expanded)
%              Number of leaves         :   50 (  67 expanded)
%              Depth                    :   10
%              Number of atoms          :  153 ( 247 expanded)
%              Number of equality atoms :   45 (  83 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_1 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

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

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_139,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_128,axiom,(
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

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_91,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_50,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_52,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_96,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_90,plain,(
    k1_funct_1('#skF_11','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_94,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_8',k1_tarski('#skF_9')))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_349,plain,(
    ! [C_154,B_155,A_156] :
      ( v5_relat_1(C_154,B_155)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_156,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_358,plain,(
    v5_relat_1('#skF_11',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_94,c_349])).

tff(c_92,plain,(
    r2_hidden('#skF_10','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_246,plain,(
    ! [C_129,A_130,B_131] :
      ( v1_relat_1(C_129)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_255,plain,(
    v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_94,c_246])).

tff(c_98,plain,(
    v1_funct_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_96,plain,(
    v1_funct_2('#skF_11','#skF_8',k1_tarski('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_467,plain,(
    ! [A_193,B_194,C_195] :
      ( k1_relset_1(A_193,B_194,C_195) = k1_relat_1(C_195)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_193,B_194))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_481,plain,(
    k1_relset_1('#skF_8',k1_tarski('#skF_9'),'#skF_11') = k1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_94,c_467])).

tff(c_956,plain,(
    ! [B_249,A_250,C_251] :
      ( k1_xboole_0 = B_249
      | k1_relset_1(A_250,B_249,C_251) = A_250
      | ~ v1_funct_2(C_251,A_250,B_249)
      | ~ m1_subset_1(C_251,k1_zfmisc_1(k2_zfmisc_1(A_250,B_249))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_967,plain,
    ( k1_tarski('#skF_9') = k1_xboole_0
    | k1_relset_1('#skF_8',k1_tarski('#skF_9'),'#skF_11') = '#skF_8'
    | ~ v1_funct_2('#skF_11','#skF_8',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_94,c_956])).

tff(c_972,plain,
    ( k1_tarski('#skF_9') = k1_xboole_0
    | k1_relat_1('#skF_11') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_481,c_967])).

tff(c_973,plain,(
    k1_relat_1('#skF_11') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_972])).

tff(c_48,plain,(
    ! [B_27,A_26] :
      ( r1_tarski(k2_relat_1(B_27),A_26)
      | ~ v5_relat_1(B_27,A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_588,plain,(
    ! [A_211,D_212] :
      ( r2_hidden(k1_funct_1(A_211,D_212),k2_relat_1(A_211))
      | ~ r2_hidden(D_212,k1_relat_1(A_211))
      | ~ v1_funct_1(A_211)
      | ~ v1_relat_1(A_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_42,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(A_21,k1_zfmisc_1(B_22))
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_375,plain,(
    ! [A_160,C_161,B_162] :
      ( m1_subset_1(A_160,C_161)
      | ~ m1_subset_1(B_162,k1_zfmisc_1(C_161))
      | ~ r2_hidden(A_160,B_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_380,plain,(
    ! [A_160,B_22,A_21] :
      ( m1_subset_1(A_160,B_22)
      | ~ r2_hidden(A_160,A_21)
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(resolution,[status(thm)],[c_42,c_375])).

tff(c_31927,plain,(
    ! [A_136740,D_136741,B_136742] :
      ( m1_subset_1(k1_funct_1(A_136740,D_136741),B_136742)
      | ~ r1_tarski(k2_relat_1(A_136740),B_136742)
      | ~ r2_hidden(D_136741,k1_relat_1(A_136740))
      | ~ v1_funct_1(A_136740)
      | ~ v1_relat_1(A_136740) ) ),
    inference(resolution,[status(thm)],[c_588,c_380])).

tff(c_31940,plain,(
    ! [B_137085,D_137086,A_137087] :
      ( m1_subset_1(k1_funct_1(B_137085,D_137086),A_137087)
      | ~ r2_hidden(D_137086,k1_relat_1(B_137085))
      | ~ v1_funct_1(B_137085)
      | ~ v5_relat_1(B_137085,A_137087)
      | ~ v1_relat_1(B_137085) ) ),
    inference(resolution,[status(thm)],[c_48,c_31927])).

tff(c_31984,plain,(
    ! [D_137086,A_137087] :
      ( m1_subset_1(k1_funct_1('#skF_11',D_137086),A_137087)
      | ~ r2_hidden(D_137086,'#skF_8')
      | ~ v1_funct_1('#skF_11')
      | ~ v5_relat_1('#skF_11',A_137087)
      | ~ v1_relat_1('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_973,c_31940])).

tff(c_32010,plain,(
    ! [D_137430,A_137431] :
      ( m1_subset_1(k1_funct_1('#skF_11',D_137430),A_137431)
      | ~ r2_hidden(D_137430,'#skF_8')
      | ~ v5_relat_1('#skF_11',A_137431) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_98,c_31984])).

tff(c_32,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_159,plain,(
    ! [A_110,B_111] : k1_enumset1(A_110,A_110,B_111) = k2_tarski(A_110,B_111) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_114,plain,(
    ! [E_86,B_87,C_88] : r2_hidden(E_86,k1_enumset1(E_86,B_87,C_88)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_118,plain,(
    ! [E_86,B_87,C_88] : ~ v1_xboole_0(k1_enumset1(E_86,B_87,C_88)) ),
    inference(resolution,[status(thm)],[c_114,c_2])).

tff(c_179,plain,(
    ! [A_110,B_111] : ~ v1_xboole_0(k2_tarski(A_110,B_111)) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_118])).

tff(c_38,plain,(
    ! [A_19,B_20] :
      ( r2_hidden(A_19,B_20)
      | v1_xboole_0(B_20)
      | ~ m1_subset_1(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_34,plain,(
    ! [A_14,B_15] : k1_enumset1(A_14,A_14,B_15) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_502,plain,(
    ! [E_200,C_201,B_202,A_203] :
      ( E_200 = C_201
      | E_200 = B_202
      | E_200 = A_203
      | ~ r2_hidden(E_200,k1_enumset1(A_203,B_202,C_201)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_600,plain,(
    ! [E_213,B_214,A_215] :
      ( E_213 = B_214
      | E_213 = A_215
      | E_213 = A_215
      | ~ r2_hidden(E_213,k2_tarski(A_215,B_214)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_502])).

tff(c_604,plain,(
    ! [B_214,A_19,A_215] :
      ( B_214 = A_19
      | A_215 = A_19
      | v1_xboole_0(k2_tarski(A_215,B_214))
      | ~ m1_subset_1(A_19,k2_tarski(A_215,B_214)) ) ),
    inference(resolution,[status(thm)],[c_38,c_600])).

tff(c_628,plain,(
    ! [B_216,A_217,A_218] :
      ( B_216 = A_217
      | A_218 = A_217
      | ~ m1_subset_1(A_217,k2_tarski(A_218,B_216)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_604])).

tff(c_635,plain,(
    ! [A_217,A_13] :
      ( A_217 = A_13
      | A_217 = A_13
      | ~ m1_subset_1(A_217,k1_tarski(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_628])).

tff(c_35473,plain,(
    ! [D_154768,A_154769] :
      ( k1_funct_1('#skF_11',D_154768) = A_154769
      | ~ r2_hidden(D_154768,'#skF_8')
      | ~ v5_relat_1('#skF_11',k1_tarski(A_154769)) ) ),
    inference(resolution,[status(thm)],[c_32010,c_635])).

tff(c_35560,plain,(
    ! [A_155150] :
      ( k1_funct_1('#skF_11','#skF_10') = A_155150
      | ~ v5_relat_1('#skF_11',k1_tarski(A_155150)) ) ),
    inference(resolution,[status(thm)],[c_92,c_35473])).

tff(c_35576,plain,(
    k1_funct_1('#skF_11','#skF_10') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_358,c_35560])).

tff(c_35580,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_35576])).

tff(c_35581,plain,(
    k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_972])).

tff(c_10,plain,(
    ! [E_12,A_6,B_7] : r2_hidden(E_12,k1_enumset1(A_6,B_7,E_12)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_192,plain,(
    ! [B_115,A_116] : r2_hidden(B_115,k2_tarski(A_116,B_115)) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_10])).

tff(c_204,plain,(
    ! [A_117] : r2_hidden(A_117,k1_tarski(A_117)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_192])).

tff(c_68,plain,(
    ! [B_69,A_68] :
      ( ~ r1_tarski(B_69,A_68)
      | ~ r2_hidden(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_211,plain,(
    ! [A_117] : ~ r1_tarski(k1_tarski(A_117),A_117) ),
    inference(resolution,[status(thm)],[c_204,c_68])).

tff(c_35611,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_35581,c_211])).

tff(c_35625,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_35611])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:35:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.98/5.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.98/5.45  
% 13.98/5.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.98/5.45  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_1 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 13.98/5.45  
% 13.98/5.45  %Foreground sorts:
% 13.98/5.45  
% 13.98/5.45  
% 13.98/5.45  %Background operators:
% 13.98/5.45  
% 13.98/5.45  
% 13.98/5.45  %Foreground operators:
% 13.98/5.45  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 13.98/5.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.98/5.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.98/5.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.98/5.45  tff('#skF_11', type, '#skF_11': $i).
% 13.98/5.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.98/5.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 13.98/5.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.98/5.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.98/5.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.98/5.45  tff('#skF_10', type, '#skF_10': $i).
% 13.98/5.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.98/5.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.98/5.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.98/5.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 13.98/5.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.98/5.45  tff('#skF_9', type, '#skF_9': $i).
% 13.98/5.45  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 13.98/5.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 13.98/5.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.98/5.45  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 13.98/5.45  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 13.98/5.45  tff('#skF_8', type, '#skF_8': $i).
% 13.98/5.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.98/5.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.98/5.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.98/5.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.98/5.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 13.98/5.45  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 13.98/5.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.98/5.45  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 13.98/5.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.98/5.45  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 13.98/5.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.98/5.45  
% 13.98/5.47  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 13.98/5.47  tff(f_139, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 13.98/5.47  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 13.98/5.47  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 13.98/5.47  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 13.98/5.47  tff(f_128, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 13.98/5.47  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 13.98/5.47  tff(f_91, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 13.98/5.47  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 13.98/5.47  tff(f_70, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 13.98/5.47  tff(f_50, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 13.98/5.47  tff(f_52, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 13.98/5.47  tff(f_48, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 13.98/5.47  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 13.98/5.47  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 13.98/5.47  tff(f_96, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 13.98/5.47  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.98/5.47  tff(c_90, plain, (k1_funct_1('#skF_11', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_139])).
% 13.98/5.47  tff(c_94, plain, (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_8', k1_tarski('#skF_9'))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 13.98/5.47  tff(c_349, plain, (![C_154, B_155, A_156]: (v5_relat_1(C_154, B_155) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_156, B_155))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 13.98/5.47  tff(c_358, plain, (v5_relat_1('#skF_11', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_94, c_349])).
% 13.98/5.47  tff(c_92, plain, (r2_hidden('#skF_10', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_139])).
% 13.98/5.47  tff(c_246, plain, (![C_129, A_130, B_131]: (v1_relat_1(C_129) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.98/5.47  tff(c_255, plain, (v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_94, c_246])).
% 13.98/5.47  tff(c_98, plain, (v1_funct_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_139])).
% 13.98/5.47  tff(c_96, plain, (v1_funct_2('#skF_11', '#skF_8', k1_tarski('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 13.98/5.47  tff(c_467, plain, (![A_193, B_194, C_195]: (k1_relset_1(A_193, B_194, C_195)=k1_relat_1(C_195) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_193, B_194))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 13.98/5.47  tff(c_481, plain, (k1_relset_1('#skF_8', k1_tarski('#skF_9'), '#skF_11')=k1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_94, c_467])).
% 13.98/5.47  tff(c_956, plain, (![B_249, A_250, C_251]: (k1_xboole_0=B_249 | k1_relset_1(A_250, B_249, C_251)=A_250 | ~v1_funct_2(C_251, A_250, B_249) | ~m1_subset_1(C_251, k1_zfmisc_1(k2_zfmisc_1(A_250, B_249))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 13.98/5.47  tff(c_967, plain, (k1_tarski('#skF_9')=k1_xboole_0 | k1_relset_1('#skF_8', k1_tarski('#skF_9'), '#skF_11')='#skF_8' | ~v1_funct_2('#skF_11', '#skF_8', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_94, c_956])).
% 13.98/5.47  tff(c_972, plain, (k1_tarski('#skF_9')=k1_xboole_0 | k1_relat_1('#skF_11')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_481, c_967])).
% 13.98/5.47  tff(c_973, plain, (k1_relat_1('#skF_11')='#skF_8'), inference(splitLeft, [status(thm)], [c_972])).
% 13.98/5.47  tff(c_48, plain, (![B_27, A_26]: (r1_tarski(k2_relat_1(B_27), A_26) | ~v5_relat_1(B_27, A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_76])).
% 13.98/5.47  tff(c_588, plain, (![A_211, D_212]: (r2_hidden(k1_funct_1(A_211, D_212), k2_relat_1(A_211)) | ~r2_hidden(D_212, k1_relat_1(A_211)) | ~v1_funct_1(A_211) | ~v1_relat_1(A_211))), inference(cnfTransformation, [status(thm)], [f_91])).
% 13.98/5.47  tff(c_42, plain, (![A_21, B_22]: (m1_subset_1(A_21, k1_zfmisc_1(B_22)) | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.98/5.47  tff(c_375, plain, (![A_160, C_161, B_162]: (m1_subset_1(A_160, C_161) | ~m1_subset_1(B_162, k1_zfmisc_1(C_161)) | ~r2_hidden(A_160, B_162))), inference(cnfTransformation, [status(thm)], [f_70])).
% 13.98/5.47  tff(c_380, plain, (![A_160, B_22, A_21]: (m1_subset_1(A_160, B_22) | ~r2_hidden(A_160, A_21) | ~r1_tarski(A_21, B_22))), inference(resolution, [status(thm)], [c_42, c_375])).
% 13.98/5.47  tff(c_31927, plain, (![A_136740, D_136741, B_136742]: (m1_subset_1(k1_funct_1(A_136740, D_136741), B_136742) | ~r1_tarski(k2_relat_1(A_136740), B_136742) | ~r2_hidden(D_136741, k1_relat_1(A_136740)) | ~v1_funct_1(A_136740) | ~v1_relat_1(A_136740))), inference(resolution, [status(thm)], [c_588, c_380])).
% 13.98/5.47  tff(c_31940, plain, (![B_137085, D_137086, A_137087]: (m1_subset_1(k1_funct_1(B_137085, D_137086), A_137087) | ~r2_hidden(D_137086, k1_relat_1(B_137085)) | ~v1_funct_1(B_137085) | ~v5_relat_1(B_137085, A_137087) | ~v1_relat_1(B_137085))), inference(resolution, [status(thm)], [c_48, c_31927])).
% 13.98/5.47  tff(c_31984, plain, (![D_137086, A_137087]: (m1_subset_1(k1_funct_1('#skF_11', D_137086), A_137087) | ~r2_hidden(D_137086, '#skF_8') | ~v1_funct_1('#skF_11') | ~v5_relat_1('#skF_11', A_137087) | ~v1_relat_1('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_973, c_31940])).
% 13.98/5.47  tff(c_32010, plain, (![D_137430, A_137431]: (m1_subset_1(k1_funct_1('#skF_11', D_137430), A_137431) | ~r2_hidden(D_137430, '#skF_8') | ~v5_relat_1('#skF_11', A_137431))), inference(demodulation, [status(thm), theory('equality')], [c_255, c_98, c_31984])).
% 13.98/5.47  tff(c_32, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 13.98/5.47  tff(c_159, plain, (![A_110, B_111]: (k1_enumset1(A_110, A_110, B_111)=k2_tarski(A_110, B_111))), inference(cnfTransformation, [status(thm)], [f_52])).
% 13.98/5.47  tff(c_114, plain, (![E_86, B_87, C_88]: (r2_hidden(E_86, k1_enumset1(E_86, B_87, C_88)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.98/5.47  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.98/5.47  tff(c_118, plain, (![E_86, B_87, C_88]: (~v1_xboole_0(k1_enumset1(E_86, B_87, C_88)))), inference(resolution, [status(thm)], [c_114, c_2])).
% 13.98/5.47  tff(c_179, plain, (![A_110, B_111]: (~v1_xboole_0(k2_tarski(A_110, B_111)))), inference(superposition, [status(thm), theory('equality')], [c_159, c_118])).
% 13.98/5.47  tff(c_38, plain, (![A_19, B_20]: (r2_hidden(A_19, B_20) | v1_xboole_0(B_20) | ~m1_subset_1(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_60])).
% 13.98/5.47  tff(c_34, plain, (![A_14, B_15]: (k1_enumset1(A_14, A_14, B_15)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 13.98/5.47  tff(c_502, plain, (![E_200, C_201, B_202, A_203]: (E_200=C_201 | E_200=B_202 | E_200=A_203 | ~r2_hidden(E_200, k1_enumset1(A_203, B_202, C_201)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.98/5.47  tff(c_600, plain, (![E_213, B_214, A_215]: (E_213=B_214 | E_213=A_215 | E_213=A_215 | ~r2_hidden(E_213, k2_tarski(A_215, B_214)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_502])).
% 13.98/5.47  tff(c_604, plain, (![B_214, A_19, A_215]: (B_214=A_19 | A_215=A_19 | v1_xboole_0(k2_tarski(A_215, B_214)) | ~m1_subset_1(A_19, k2_tarski(A_215, B_214)))), inference(resolution, [status(thm)], [c_38, c_600])).
% 13.98/5.47  tff(c_628, plain, (![B_216, A_217, A_218]: (B_216=A_217 | A_218=A_217 | ~m1_subset_1(A_217, k2_tarski(A_218, B_216)))), inference(negUnitSimplification, [status(thm)], [c_179, c_604])).
% 13.98/5.47  tff(c_635, plain, (![A_217, A_13]: (A_217=A_13 | A_217=A_13 | ~m1_subset_1(A_217, k1_tarski(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_628])).
% 13.98/5.47  tff(c_35473, plain, (![D_154768, A_154769]: (k1_funct_1('#skF_11', D_154768)=A_154769 | ~r2_hidden(D_154768, '#skF_8') | ~v5_relat_1('#skF_11', k1_tarski(A_154769)))), inference(resolution, [status(thm)], [c_32010, c_635])).
% 13.98/5.47  tff(c_35560, plain, (![A_155150]: (k1_funct_1('#skF_11', '#skF_10')=A_155150 | ~v5_relat_1('#skF_11', k1_tarski(A_155150)))), inference(resolution, [status(thm)], [c_92, c_35473])).
% 13.98/5.47  tff(c_35576, plain, (k1_funct_1('#skF_11', '#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_358, c_35560])).
% 13.98/5.47  tff(c_35580, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_35576])).
% 13.98/5.47  tff(c_35581, plain, (k1_tarski('#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_972])).
% 13.98/5.47  tff(c_10, plain, (![E_12, A_6, B_7]: (r2_hidden(E_12, k1_enumset1(A_6, B_7, E_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.98/5.47  tff(c_192, plain, (![B_115, A_116]: (r2_hidden(B_115, k2_tarski(A_116, B_115)))), inference(superposition, [status(thm), theory('equality')], [c_159, c_10])).
% 13.98/5.47  tff(c_204, plain, (![A_117]: (r2_hidden(A_117, k1_tarski(A_117)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_192])).
% 13.98/5.47  tff(c_68, plain, (![B_69, A_68]: (~r1_tarski(B_69, A_68) | ~r2_hidden(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_96])).
% 13.98/5.47  tff(c_211, plain, (![A_117]: (~r1_tarski(k1_tarski(A_117), A_117))), inference(resolution, [status(thm)], [c_204, c_68])).
% 13.98/5.47  tff(c_35611, plain, (~r1_tarski(k1_xboole_0, '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_35581, c_211])).
% 13.98/5.47  tff(c_35625, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_35611])).
% 13.98/5.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.98/5.47  
% 13.98/5.47  Inference rules
% 13.98/5.47  ----------------------
% 13.98/5.47  #Ref     : 0
% 13.98/5.47  #Sup     : 3391
% 13.98/5.47  #Fact    : 48
% 13.98/5.47  #Define  : 0
% 13.98/5.47  #Split   : 35
% 13.98/5.47  #Chain   : 0
% 13.98/5.47  #Close   : 0
% 13.98/5.47  
% 13.98/5.47  Ordering : KBO
% 13.98/5.47  
% 13.98/5.47  Simplification rules
% 13.98/5.47  ----------------------
% 13.98/5.47  #Subsume      : 797
% 13.98/5.47  #Demod        : 1534
% 13.98/5.47  #Tautology    : 496
% 13.98/5.47  #SimpNegUnit  : 332
% 13.98/5.47  #BackRed      : 125
% 13.98/5.47  
% 13.98/5.47  #Partial instantiations: 81015
% 13.98/5.47  #Strategies tried      : 1
% 13.98/5.47  
% 13.98/5.47  Timing (in seconds)
% 13.98/5.47  ----------------------
% 13.98/5.47  Preprocessing        : 0.38
% 13.98/5.47  Parsing              : 0.19
% 13.98/5.47  CNF conversion       : 0.03
% 13.98/5.47  Main loop            : 4.25
% 13.98/5.47  Inferencing          : 2.09
% 13.98/5.47  Reduction            : 1.13
% 13.98/5.47  Demodulation         : 0.81
% 13.98/5.47  BG Simplification    : 0.11
% 13.98/5.47  Subsumption          : 0.70
% 13.98/5.47  Abstraction          : 0.14
% 13.98/5.47  MUC search           : 0.00
% 13.98/5.47  Cooper               : 0.00
% 13.98/5.47  Total                : 4.67
% 13.98/5.47  Index Insertion      : 0.00
% 13.98/5.47  Index Deletion       : 0.00
% 13.98/5.47  Index Matching       : 0.00
% 13.98/5.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
