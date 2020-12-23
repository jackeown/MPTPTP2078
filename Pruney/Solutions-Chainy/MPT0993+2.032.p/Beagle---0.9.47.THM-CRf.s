%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:46 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 161 expanded)
%              Number of leaves         :   36 (  70 expanded)
%              Depth                    :   10
%              Number of atoms          :  123 ( 354 expanded)
%              Number of equality atoms :   40 (  89 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_96,axiom,(
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

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_450,plain,(
    ! [A_129,B_130,D_131] :
      ( r2_relset_1(A_129,B_130,D_131,D_131)
      | ~ m1_subset_1(D_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_457,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_450])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_121,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_129,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_121])).

tff(c_24,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k7_relat_1(B_14,A_13),B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_160,plain,(
    ! [A_60,B_61,D_62] :
      ( r2_relset_1(A_60,B_61,D_62,D_62)
      | ~ m1_subset_1(D_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_167,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_160])).

tff(c_52,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_56,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_185,plain,(
    ! [A_72,B_73,C_74] :
      ( k1_relset_1(A_72,B_73,C_74) = k1_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_195,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_185])).

tff(c_297,plain,(
    ! [B_115,A_116,C_117] :
      ( k1_xboole_0 = B_115
      | k1_relset_1(A_116,B_115,C_117) = A_116
      | ~ v1_funct_2(C_117,A_116,B_115)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_116,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_300,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_297])).

tff(c_309,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_195,c_300])).

tff(c_311,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_309])).

tff(c_26,plain,(
    ! [B_16,A_15] :
      ( k7_relat_1(B_16,A_15) = B_16
      | ~ r1_tarski(k1_relat_1(B_16),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_319,plain,(
    ! [A_15] :
      ( k7_relat_1('#skF_5',A_15) = '#skF_5'
      | ~ r1_tarski('#skF_2',A_15)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_26])).

tff(c_349,plain,(
    ! [A_118] :
      ( k7_relat_1('#skF_5',A_118) = '#skF_5'
      | ~ r1_tarski('#skF_2',A_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_319])).

tff(c_359,plain,(
    k7_relat_1('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_52,c_349])).

tff(c_203,plain,(
    ! [A_81,B_82,C_83,D_84] :
      ( k2_partfun1(A_81,B_82,C_83,D_84) = k7_relat_1(C_83,D_84)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82)))
      | ~ v1_funct_1(C_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_205,plain,(
    ! [D_84] :
      ( k2_partfun1('#skF_2','#skF_3','#skF_5',D_84) = k7_relat_1('#skF_5',D_84)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_203])).

tff(c_212,plain,(
    ! [D_84] : k2_partfun1('#skF_2','#skF_3','#skF_5',D_84) = k7_relat_1('#skF_5',D_84) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_205])).

tff(c_50,plain,(
    ~ r2_relset_1('#skF_2','#skF_3',k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_213,plain,(
    ~ r2_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_50])).

tff(c_360,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_213])).

tff(c_363,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_360])).

tff(c_364,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_309])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_382,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_8])).

tff(c_18,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_380,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_364,c_18])).

tff(c_135,plain,(
    ! [C_54,B_55,A_56] :
      ( ~ v1_xboole_0(C_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(C_54))
      | ~ r2_hidden(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_138,plain,(
    ! [A_56] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_56,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_135])).

tff(c_139,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_394,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_139])).

tff(c_398,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_394])).

tff(c_401,plain,(
    ! [A_123] : ~ r2_hidden(A_123,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_407,plain,(
    ! [B_124] : r1_tarski('#skF_5',B_124) ),
    inference(resolution,[status(thm)],[c_6,c_401])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_411,plain,(
    ! [B_125] :
      ( B_125 = '#skF_5'
      | ~ r1_tarski(B_125,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_407,c_10])).

tff(c_419,plain,(
    ! [A_13] :
      ( k7_relat_1('#skF_5',A_13) = '#skF_5'
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_24,c_411])).

tff(c_428,plain,(
    ! [A_13] : k7_relat_1('#skF_5',A_13) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_419])).

tff(c_555,plain,(
    ! [A_155,B_156,C_157,D_158] :
      ( k2_partfun1(A_155,B_156,C_157,D_158) = k7_relat_1(C_157,D_158)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156)))
      | ~ v1_funct_1(C_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_557,plain,(
    ! [D_158] :
      ( k2_partfun1('#skF_2','#skF_3','#skF_5',D_158) = k7_relat_1('#skF_5',D_158)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_555])).

tff(c_564,plain,(
    ! [D_158] : k2_partfun1('#skF_2','#skF_3','#skF_5',D_158) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_428,c_557])).

tff(c_565,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_564,c_50])).

tff(c_568,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_565])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:25:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.39  
% 2.74/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.39  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.74/1.39  
% 2.74/1.39  %Foreground sorts:
% 2.74/1.39  
% 2.74/1.39  
% 2.74/1.39  %Background operators:
% 2.74/1.39  
% 2.74/1.39  
% 2.74/1.39  %Foreground operators:
% 2.74/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.74/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.39  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.74/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.74/1.39  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.74/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.74/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.74/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.74/1.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.74/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.74/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.74/1.39  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.74/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.74/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.74/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.74/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.74/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.39  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.74/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.74/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.74/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.74/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.74/1.39  
% 2.74/1.40  tff(f_113, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_funct_2)).
% 2.74/1.40  tff(f_78, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.74/1.40  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.74/1.40  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 2.74/1.40  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.74/1.40  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.74/1.40  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.74/1.40  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.74/1.40  tff(f_102, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.74/1.40  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.74/1.40  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.74/1.40  tff(f_52, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.74/1.40  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.74/1.40  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.74/1.40  tff(c_450, plain, (![A_129, B_130, D_131]: (r2_relset_1(A_129, B_130, D_131, D_131) | ~m1_subset_1(D_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.74/1.40  tff(c_457, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_450])).
% 2.74/1.40  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.74/1.40  tff(c_121, plain, (![C_47, A_48, B_49]: (v1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.74/1.40  tff(c_129, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_121])).
% 2.74/1.40  tff(c_24, plain, (![B_14, A_13]: (r1_tarski(k7_relat_1(B_14, A_13), B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.74/1.40  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.74/1.40  tff(c_160, plain, (![A_60, B_61, D_62]: (r2_relset_1(A_60, B_61, D_62, D_62) | ~m1_subset_1(D_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.74/1.40  tff(c_167, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_160])).
% 2.74/1.40  tff(c_52, plain, (r1_tarski('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.74/1.40  tff(c_56, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.74/1.40  tff(c_185, plain, (![A_72, B_73, C_74]: (k1_relset_1(A_72, B_73, C_74)=k1_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.74/1.40  tff(c_195, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_185])).
% 2.74/1.40  tff(c_297, plain, (![B_115, A_116, C_117]: (k1_xboole_0=B_115 | k1_relset_1(A_116, B_115, C_117)=A_116 | ~v1_funct_2(C_117, A_116, B_115) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_116, B_115))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.74/1.40  tff(c_300, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_297])).
% 2.74/1.40  tff(c_309, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_195, c_300])).
% 2.74/1.40  tff(c_311, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_309])).
% 2.74/1.40  tff(c_26, plain, (![B_16, A_15]: (k7_relat_1(B_16, A_15)=B_16 | ~r1_tarski(k1_relat_1(B_16), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.74/1.40  tff(c_319, plain, (![A_15]: (k7_relat_1('#skF_5', A_15)='#skF_5' | ~r1_tarski('#skF_2', A_15) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_311, c_26])).
% 2.74/1.40  tff(c_349, plain, (![A_118]: (k7_relat_1('#skF_5', A_118)='#skF_5' | ~r1_tarski('#skF_2', A_118))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_319])).
% 2.74/1.40  tff(c_359, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_52, c_349])).
% 2.74/1.40  tff(c_203, plain, (![A_81, B_82, C_83, D_84]: (k2_partfun1(A_81, B_82, C_83, D_84)=k7_relat_1(C_83, D_84) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))) | ~v1_funct_1(C_83))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.74/1.40  tff(c_205, plain, (![D_84]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_84)=k7_relat_1('#skF_5', D_84) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_203])).
% 2.74/1.40  tff(c_212, plain, (![D_84]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_84)=k7_relat_1('#skF_5', D_84))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_205])).
% 2.74/1.40  tff(c_50, plain, (~r2_relset_1('#skF_2', '#skF_3', k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.74/1.40  tff(c_213, plain, (~r2_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_212, c_50])).
% 2.74/1.40  tff(c_360, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_359, c_213])).
% 2.74/1.40  tff(c_363, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_167, c_360])).
% 2.74/1.40  tff(c_364, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_309])).
% 2.74/1.40  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.74/1.40  tff(c_382, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_364, c_8])).
% 2.74/1.40  tff(c_18, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.74/1.40  tff(c_380, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_364, c_364, c_18])).
% 2.74/1.40  tff(c_135, plain, (![C_54, B_55, A_56]: (~v1_xboole_0(C_54) | ~m1_subset_1(B_55, k1_zfmisc_1(C_54)) | ~r2_hidden(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.74/1.40  tff(c_138, plain, (![A_56]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_56, '#skF_5'))), inference(resolution, [status(thm)], [c_54, c_135])).
% 2.74/1.40  tff(c_139, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_138])).
% 2.74/1.40  tff(c_394, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_380, c_139])).
% 2.74/1.40  tff(c_398, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_382, c_394])).
% 2.74/1.40  tff(c_401, plain, (![A_123]: (~r2_hidden(A_123, '#skF_5'))), inference(splitRight, [status(thm)], [c_138])).
% 2.74/1.40  tff(c_407, plain, (![B_124]: (r1_tarski('#skF_5', B_124))), inference(resolution, [status(thm)], [c_6, c_401])).
% 2.74/1.40  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.74/1.40  tff(c_411, plain, (![B_125]: (B_125='#skF_5' | ~r1_tarski(B_125, '#skF_5'))), inference(resolution, [status(thm)], [c_407, c_10])).
% 2.74/1.40  tff(c_419, plain, (![A_13]: (k7_relat_1('#skF_5', A_13)='#skF_5' | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_24, c_411])).
% 2.74/1.40  tff(c_428, plain, (![A_13]: (k7_relat_1('#skF_5', A_13)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_419])).
% 2.74/1.40  tff(c_555, plain, (![A_155, B_156, C_157, D_158]: (k2_partfun1(A_155, B_156, C_157, D_158)=k7_relat_1(C_157, D_158) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))) | ~v1_funct_1(C_157))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.74/1.40  tff(c_557, plain, (![D_158]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_158)=k7_relat_1('#skF_5', D_158) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_555])).
% 2.74/1.40  tff(c_564, plain, (![D_158]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_158)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_428, c_557])).
% 2.74/1.40  tff(c_565, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_564, c_50])).
% 2.74/1.40  tff(c_568, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_457, c_565])).
% 2.74/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.40  
% 2.74/1.40  Inference rules
% 2.74/1.40  ----------------------
% 2.74/1.40  #Ref     : 0
% 2.74/1.40  #Sup     : 106
% 2.74/1.40  #Fact    : 0
% 2.74/1.40  #Define  : 0
% 2.74/1.40  #Split   : 6
% 2.74/1.40  #Chain   : 0
% 2.74/1.40  #Close   : 0
% 2.74/1.40  
% 2.74/1.40  Ordering : KBO
% 2.74/1.40  
% 2.74/1.40  Simplification rules
% 2.74/1.40  ----------------------
% 2.74/1.40  #Subsume      : 9
% 2.74/1.40  #Demod        : 90
% 2.74/1.40  #Tautology    : 53
% 2.74/1.40  #SimpNegUnit  : 0
% 2.74/1.40  #BackRed      : 23
% 2.74/1.40  
% 2.74/1.40  #Partial instantiations: 0
% 2.74/1.40  #Strategies tried      : 1
% 2.74/1.40  
% 2.74/1.40  Timing (in seconds)
% 2.74/1.40  ----------------------
% 2.74/1.41  Preprocessing        : 0.33
% 2.74/1.41  Parsing              : 0.17
% 2.74/1.41  CNF conversion       : 0.02
% 2.74/1.41  Main loop            : 0.32
% 2.74/1.41  Inferencing          : 0.11
% 2.74/1.41  Reduction            : 0.10
% 2.74/1.41  Demodulation         : 0.07
% 2.74/1.41  BG Simplification    : 0.02
% 2.74/1.41  Subsumption          : 0.07
% 2.74/1.41  Abstraction          : 0.02
% 2.74/1.41  MUC search           : 0.00
% 2.74/1.41  Cooper               : 0.00
% 2.74/1.41  Total                : 0.68
% 2.74/1.41  Index Insertion      : 0.00
% 2.74/1.41  Index Deletion       : 0.00
% 2.74/1.41  Index Matching       : 0.00
% 2.74/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
