%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:09 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 120 expanded)
%              Number of leaves         :   39 (  58 expanded)
%              Depth                    :    7
%              Number of atoms          :  129 ( 232 expanded)
%              Number of equality atoms :   28 (  42 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k3_partfun1,type,(
    k3_partfun1: ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

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

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(C,k1_funct_2(A,B))
         => ( k1_relat_1(C) = A
            & r1_tarski(k2_relat_1(C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_2)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => v1_xboole_0(k1_funct_2(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( r2_hidden(C,k1_funct_2(A,B))
     => ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_89,axiom,(
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

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(c_60,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_536,plain,(
    ! [B_188,A_189] :
      ( r1_tarski(k2_relat_1(B_188),A_189)
      | ~ v5_relat_1(B_188,A_189)
      | ~ v1_relat_1(B_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_54,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | k1_relat_1('#skF_5') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_73,plain,(
    k1_relat_1('#skF_5') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_112,plain,(
    ! [A_45,B_46] :
      ( v1_xboole_0(k1_funct_2(A_45,B_46))
      | ~ v1_xboole_0(B_46)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_56,plain,(
    r2_hidden('#skF_5',k1_funct_2('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_62,plain,(
    ! [B_31,A_32] :
      ( ~ r2_hidden(B_31,A_32)
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ~ v1_xboole_0(k1_funct_2('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_62])).

tff(c_116,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_112,c_66])).

tff(c_117,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_136,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_funct_2(C_60,A_61,B_62)
      | ~ r2_hidden(C_60,k1_funct_2(A_61,B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_150,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_136])).

tff(c_46,plain,(
    ! [C_27,A_25,B_26] :
      ( m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ r2_hidden(C_27,k1_funct_2(A_25,B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_204,plain,(
    ! [A_82,B_83,C_84] :
      ( k1_relset_1(A_82,B_83,C_84) = k1_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_246,plain,(
    ! [A_93,B_94,C_95] :
      ( k1_relset_1(A_93,B_94,C_95) = k1_relat_1(C_95)
      | ~ r2_hidden(C_95,k1_funct_2(A_93,B_94)) ) ),
    inference(resolution,[status(thm)],[c_46,c_204])).

tff(c_260,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_246])).

tff(c_327,plain,(
    ! [B_122,A_123,C_124] :
      ( k1_xboole_0 = B_122
      | k1_relset_1(A_123,B_122,C_124) = A_123
      | ~ v1_funct_2(C_124,A_123,B_122)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_123,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_332,plain,(
    ! [B_125,A_126,C_127] :
      ( k1_xboole_0 = B_125
      | k1_relset_1(A_126,B_125,C_127) = A_126
      | ~ v1_funct_2(C_127,A_126,B_125)
      | ~ r2_hidden(C_127,k1_funct_2(A_126,B_125)) ) ),
    inference(resolution,[status(thm)],[c_46,c_327])).

tff(c_343,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_332])).

tff(c_348,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_260,c_343])).

tff(c_349,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_348])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_359,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_12])).

tff(c_361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_359])).

tff(c_362,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_419,plain,(
    ! [C_157,A_158,B_159] :
      ( m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159)))
      | ~ r2_hidden(C_157,k1_funct_2(A_158,B_159)) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_28,plain,(
    ! [C_16,A_14,B_15] :
      ( v4_relat_1(C_16,A_14)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_434,plain,(
    ! [C_161,A_162,B_163] :
      ( v4_relat_1(C_161,A_162)
      | ~ r2_hidden(C_161,k1_funct_2(A_162,B_163)) ) ),
    inference(resolution,[status(thm)],[c_419,c_28])).

tff(c_448,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_434])).

tff(c_383,plain,(
    ! [B_144,A_145] :
      ( r1_tarski(k1_relat_1(B_144),A_145)
      | ~ v4_relat_1(B_144,A_145)
      | ~ v1_relat_1(B_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r2_xboole_0(A_5,B_6)
      | B_6 = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_97,plain,(
    ! [A_43,B_44] :
      ( r2_hidden('#skF_2'(A_43,B_44),B_44)
      | ~ r2_xboole_0(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_364,plain,(
    ! [B_128,A_129] :
      ( ~ v1_xboole_0(B_128)
      | ~ r2_xboole_0(A_129,B_128) ) ),
    inference(resolution,[status(thm)],[c_97,c_2])).

tff(c_368,plain,(
    ! [B_6,A_5] :
      ( ~ v1_xboole_0(B_6)
      | B_6 = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_6,c_364])).

tff(c_391,plain,(
    ! [A_145,B_144] :
      ( ~ v1_xboole_0(A_145)
      | k1_relat_1(B_144) = A_145
      | ~ v4_relat_1(B_144,A_145)
      | ~ v1_relat_1(B_144) ) ),
    inference(resolution,[status(thm)],[c_383,c_368])).

tff(c_451,plain,
    ( ~ v1_xboole_0('#skF_3')
    | k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_448,c_391])).

tff(c_454,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_362,c_451])).

tff(c_456,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_454])).

tff(c_457,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_542,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_536,c_457])).

tff(c_546,plain,(
    ~ v5_relat_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_542])).

tff(c_590,plain,(
    ! [C_206,A_207,B_208] :
      ( m1_subset_1(C_206,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208)))
      | ~ r2_hidden(C_206,k1_funct_2(A_207,B_208)) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_26,plain,(
    ! [C_16,B_15,A_14] :
      ( v5_relat_1(C_16,B_15)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_640,plain,(
    ! [C_216,B_217,A_218] :
      ( v5_relat_1(C_216,B_217)
      | ~ r2_hidden(C_216,k1_funct_2(A_218,B_217)) ) ),
    inference(resolution,[status(thm)],[c_590,c_26])).

tff(c_651,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_640])).

tff(c_657,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_546,c_651])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:53:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.45  
% 2.66/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.45  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.66/1.45  
% 2.66/1.45  %Foreground sorts:
% 2.66/1.45  
% 2.66/1.45  
% 2.66/1.45  %Background operators:
% 2.66/1.45  
% 2.66/1.45  
% 2.66/1.45  %Foreground operators:
% 2.66/1.45  tff(k3_partfun1, type, k3_partfun1: ($i * $i * $i) > $i).
% 2.66/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.66/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.66/1.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.66/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.66/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.66/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.66/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.66/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.66/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.66/1.45  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.66/1.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.66/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.66/1.45  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.66/1.45  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 2.66/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.66/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.66/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.66/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.66/1.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.66/1.45  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 2.66/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.66/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.66/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.66/1.45  
% 2.66/1.46  tff(f_117, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(C, k1_funct_2(A, B)) => ((k1_relat_1(C) = A) & r1_tarski(k2_relat_1(C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_funct_2)).
% 2.66/1.46  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.66/1.46  tff(f_96, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => v1_xboole_0(k1_funct_2(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_2)).
% 2.66/1.46  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.66/1.46  tff(f_104, axiom, (![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_2)).
% 2.66/1.46  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.66/1.46  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.66/1.46  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.66/1.46  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.66/1.46  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.66/1.46  tff(f_38, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.66/1.46  tff(f_49, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 2.66/1.46  tff(c_60, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.66/1.46  tff(c_536, plain, (![B_188, A_189]: (r1_tarski(k2_relat_1(B_188), A_189) | ~v5_relat_1(B_188, A_189) | ~v1_relat_1(B_188))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.66/1.46  tff(c_54, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | k1_relat_1('#skF_5')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.66/1.46  tff(c_73, plain, (k1_relat_1('#skF_5')!='#skF_3'), inference(splitLeft, [status(thm)], [c_54])).
% 2.66/1.46  tff(c_112, plain, (![A_45, B_46]: (v1_xboole_0(k1_funct_2(A_45, B_46)) | ~v1_xboole_0(B_46) | v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.66/1.46  tff(c_56, plain, (r2_hidden('#skF_5', k1_funct_2('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.66/1.46  tff(c_62, plain, (![B_31, A_32]: (~r2_hidden(B_31, A_32) | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.66/1.46  tff(c_66, plain, (~v1_xboole_0(k1_funct_2('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_56, c_62])).
% 2.66/1.46  tff(c_116, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_112, c_66])).
% 2.66/1.46  tff(c_117, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_116])).
% 2.66/1.46  tff(c_136, plain, (![C_60, A_61, B_62]: (v1_funct_2(C_60, A_61, B_62) | ~r2_hidden(C_60, k1_funct_2(A_61, B_62)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.66/1.46  tff(c_150, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_136])).
% 2.66/1.46  tff(c_46, plain, (![C_27, A_25, B_26]: (m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~r2_hidden(C_27, k1_funct_2(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.66/1.47  tff(c_204, plain, (![A_82, B_83, C_84]: (k1_relset_1(A_82, B_83, C_84)=k1_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.66/1.47  tff(c_246, plain, (![A_93, B_94, C_95]: (k1_relset_1(A_93, B_94, C_95)=k1_relat_1(C_95) | ~r2_hidden(C_95, k1_funct_2(A_93, B_94)))), inference(resolution, [status(thm)], [c_46, c_204])).
% 2.66/1.47  tff(c_260, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_246])).
% 2.66/1.47  tff(c_327, plain, (![B_122, A_123, C_124]: (k1_xboole_0=B_122 | k1_relset_1(A_123, B_122, C_124)=A_123 | ~v1_funct_2(C_124, A_123, B_122) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_123, B_122))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.66/1.47  tff(c_332, plain, (![B_125, A_126, C_127]: (k1_xboole_0=B_125 | k1_relset_1(A_126, B_125, C_127)=A_126 | ~v1_funct_2(C_127, A_126, B_125) | ~r2_hidden(C_127, k1_funct_2(A_126, B_125)))), inference(resolution, [status(thm)], [c_46, c_327])).
% 2.66/1.47  tff(c_343, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_332])).
% 2.66/1.47  tff(c_348, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_150, c_260, c_343])).
% 2.66/1.47  tff(c_349, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_73, c_348])).
% 2.66/1.47  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.66/1.47  tff(c_359, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_349, c_12])).
% 2.66/1.47  tff(c_361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_117, c_359])).
% 2.66/1.47  tff(c_362, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_116])).
% 2.66/1.47  tff(c_419, plain, (![C_157, A_158, B_159]: (m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))) | ~r2_hidden(C_157, k1_funct_2(A_158, B_159)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.66/1.47  tff(c_28, plain, (![C_16, A_14, B_15]: (v4_relat_1(C_16, A_14) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.66/1.47  tff(c_434, plain, (![C_161, A_162, B_163]: (v4_relat_1(C_161, A_162) | ~r2_hidden(C_161, k1_funct_2(A_162, B_163)))), inference(resolution, [status(thm)], [c_419, c_28])).
% 2.66/1.47  tff(c_448, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_434])).
% 2.66/1.47  tff(c_383, plain, (![B_144, A_145]: (r1_tarski(k1_relat_1(B_144), A_145) | ~v4_relat_1(B_144, A_145) | ~v1_relat_1(B_144))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.66/1.47  tff(c_6, plain, (![A_5, B_6]: (r2_xboole_0(A_5, B_6) | B_6=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.66/1.47  tff(c_97, plain, (![A_43, B_44]: (r2_hidden('#skF_2'(A_43, B_44), B_44) | ~r2_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.66/1.47  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.66/1.47  tff(c_364, plain, (![B_128, A_129]: (~v1_xboole_0(B_128) | ~r2_xboole_0(A_129, B_128))), inference(resolution, [status(thm)], [c_97, c_2])).
% 2.66/1.47  tff(c_368, plain, (![B_6, A_5]: (~v1_xboole_0(B_6) | B_6=A_5 | ~r1_tarski(A_5, B_6))), inference(resolution, [status(thm)], [c_6, c_364])).
% 2.66/1.47  tff(c_391, plain, (![A_145, B_144]: (~v1_xboole_0(A_145) | k1_relat_1(B_144)=A_145 | ~v4_relat_1(B_144, A_145) | ~v1_relat_1(B_144))), inference(resolution, [status(thm)], [c_383, c_368])).
% 2.66/1.47  tff(c_451, plain, (~v1_xboole_0('#skF_3') | k1_relat_1('#skF_5')='#skF_3' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_448, c_391])).
% 2.66/1.47  tff(c_454, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_362, c_451])).
% 2.66/1.47  tff(c_456, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_454])).
% 2.66/1.47  tff(c_457, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_54])).
% 2.66/1.47  tff(c_542, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_536, c_457])).
% 2.66/1.47  tff(c_546, plain, (~v5_relat_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_542])).
% 2.66/1.47  tff(c_590, plain, (![C_206, A_207, B_208]: (m1_subset_1(C_206, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))) | ~r2_hidden(C_206, k1_funct_2(A_207, B_208)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.66/1.47  tff(c_26, plain, (![C_16, B_15, A_14]: (v5_relat_1(C_16, B_15) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.66/1.47  tff(c_640, plain, (![C_216, B_217, A_218]: (v5_relat_1(C_216, B_217) | ~r2_hidden(C_216, k1_funct_2(A_218, B_217)))), inference(resolution, [status(thm)], [c_590, c_26])).
% 2.66/1.47  tff(c_651, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_640])).
% 2.66/1.47  tff(c_657, plain, $false, inference(negUnitSimplification, [status(thm)], [c_546, c_651])).
% 2.66/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.47  
% 2.66/1.47  Inference rules
% 2.66/1.47  ----------------------
% 2.66/1.47  #Ref     : 0
% 2.66/1.47  #Sup     : 109
% 2.66/1.47  #Fact    : 0
% 2.66/1.47  #Define  : 0
% 2.66/1.47  #Split   : 3
% 2.66/1.47  #Chain   : 0
% 2.66/1.47  #Close   : 0
% 2.66/1.47  
% 2.66/1.47  Ordering : KBO
% 2.66/1.47  
% 2.66/1.47  Simplification rules
% 2.66/1.47  ----------------------
% 2.66/1.47  #Subsume      : 8
% 2.66/1.47  #Demod        : 44
% 2.66/1.47  #Tautology    : 28
% 2.66/1.47  #SimpNegUnit  : 5
% 2.66/1.47  #BackRed      : 10
% 2.66/1.47  
% 2.66/1.47  #Partial instantiations: 0
% 2.66/1.47  #Strategies tried      : 1
% 2.66/1.47  
% 2.66/1.47  Timing (in seconds)
% 2.66/1.47  ----------------------
% 2.66/1.47  Preprocessing        : 0.34
% 2.66/1.47  Parsing              : 0.18
% 2.66/1.47  CNF conversion       : 0.02
% 2.66/1.47  Main loop            : 0.30
% 2.66/1.47  Inferencing          : 0.12
% 2.66/1.47  Reduction            : 0.08
% 2.66/1.47  Demodulation         : 0.05
% 2.66/1.47  BG Simplification    : 0.02
% 2.66/1.47  Subsumption          : 0.05
% 2.66/1.47  Abstraction          : 0.02
% 2.66/1.47  MUC search           : 0.00
% 2.66/1.47  Cooper               : 0.00
% 2.66/1.47  Total                : 0.68
% 2.66/1.47  Index Insertion      : 0.00
% 2.66/1.47  Index Deletion       : 0.00
% 2.66/1.47  Index Matching       : 0.00
% 2.66/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
