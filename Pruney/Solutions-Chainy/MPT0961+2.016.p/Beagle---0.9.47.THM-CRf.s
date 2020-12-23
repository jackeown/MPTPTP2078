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
% DateTime   : Thu Dec  3 10:10:43 EST 2020

% Result     : Theorem 4.88s
% Output     : CNFRefutation 4.88s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 526 expanded)
%              Number of leaves         :   25 ( 189 expanded)
%              Depth                    :   11
%              Number of atoms          :  168 (1529 expanded)
%              Number of equality atoms :   47 ( 415 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_94,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_64,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_50,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2891,plain,(
    ! [C_228,A_229,B_230] :
      ( m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(A_229,B_230)))
      | ~ r1_tarski(k2_relat_1(C_228),B_230)
      | ~ r1_tarski(k1_relat_1(C_228),A_229)
      | ~ v1_relat_1(C_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [A_11,B_13] :
      ( r1_tarski(k2_relat_1(A_11),k2_relat_1(B_13))
      | ~ r1_tarski(A_11,B_13)
      | ~ v1_relat_1(B_13)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_361,plain,(
    ! [C_61,A_62,B_63] :
      ( m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | ~ r1_tarski(k2_relat_1(C_61),B_63)
      | ~ r1_tarski(k1_relat_1(C_61),A_62)
      | ~ v1_relat_1(C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_30,plain,(
    ! [A_14,B_15,C_16] :
      ( k1_relset_1(A_14,B_15,C_16) = k1_relat_1(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1401,plain,(
    ! [A_137,B_138,C_139] :
      ( k1_relset_1(A_137,B_138,C_139) = k1_relat_1(C_139)
      | ~ r1_tarski(k2_relat_1(C_139),B_138)
      | ~ r1_tarski(k1_relat_1(C_139),A_137)
      | ~ v1_relat_1(C_139) ) ),
    inference(resolution,[status(thm)],[c_361,c_30])).

tff(c_1804,plain,(
    ! [A_170,B_171,A_172] :
      ( k1_relset_1(A_170,k2_relat_1(B_171),A_172) = k1_relat_1(A_172)
      | ~ r1_tarski(k1_relat_1(A_172),A_170)
      | ~ r1_tarski(A_172,B_171)
      | ~ v1_relat_1(B_171)
      | ~ v1_relat_1(A_172) ) ),
    inference(resolution,[status(thm)],[c_22,c_1401])).

tff(c_1834,plain,(
    ! [A_172,B_171] :
      ( k1_relset_1(k1_relat_1(A_172),k2_relat_1(B_171),A_172) = k1_relat_1(A_172)
      | ~ r1_tarski(A_172,B_171)
      | ~ v1_relat_1(B_171)
      | ~ v1_relat_1(A_172) ) ),
    inference(resolution,[status(thm)],[c_6,c_1804])).

tff(c_32,plain,(
    ! [C_19,A_17,B_18] :
      ( m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18)))
      | ~ r1_tarski(k2_relat_1(C_19),B_18)
      | ~ r1_tarski(k1_relat_1(C_19),A_17)
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_488,plain,(
    ! [B_81,C_82,A_83] :
      ( k1_xboole_0 = B_81
      | v1_funct_2(C_82,A_83,B_81)
      | k1_relset_1(A_83,B_81,C_82) != A_83
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_83,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1982,plain,(
    ! [B_180,C_181,A_182] :
      ( k1_xboole_0 = B_180
      | v1_funct_2(C_181,A_182,B_180)
      | k1_relset_1(A_182,B_180,C_181) != A_182
      | ~ r1_tarski(k2_relat_1(C_181),B_180)
      | ~ r1_tarski(k1_relat_1(C_181),A_182)
      | ~ v1_relat_1(C_181) ) ),
    inference(resolution,[status(thm)],[c_32,c_488])).

tff(c_2177,plain,(
    ! [C_190,A_191] :
      ( k2_relat_1(C_190) = k1_xboole_0
      | v1_funct_2(C_190,A_191,k2_relat_1(C_190))
      | k1_relset_1(A_191,k2_relat_1(C_190),C_190) != A_191
      | ~ r1_tarski(k1_relat_1(C_190),A_191)
      | ~ v1_relat_1(C_190) ) ),
    inference(resolution,[status(thm)],[c_6,c_1982])).

tff(c_48,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_46,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_52,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46])).

tff(c_91,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_2193,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2177,c_91])).

tff(c_2213,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_6,c_2193])).

tff(c_2216,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2213])).

tff(c_2219,plain,
    ( ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1834,c_2216])).

tff(c_2229,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_6,c_2219])).

tff(c_2230,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2213])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1087,plain,(
    ! [C_122,A_123,B_124] :
      ( r1_tarski(C_122,k2_zfmisc_1(A_123,B_124))
      | ~ r1_tarski(k2_relat_1(C_122),B_124)
      | ~ r1_tarski(k1_relat_1(C_122),A_123)
      | ~ v1_relat_1(C_122) ) ),
    inference(resolution,[status(thm)],[c_361,c_16])).

tff(c_1111,plain,(
    ! [C_125,A_126] :
      ( r1_tarski(C_125,k2_zfmisc_1(A_126,k2_relat_1(C_125)))
      | ~ r1_tarski(k1_relat_1(C_125),A_126)
      | ~ v1_relat_1(C_125) ) ),
    inference(resolution,[status(thm)],[c_6,c_1087])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1144,plain,(
    ! [A_126,C_125] :
      ( k2_zfmisc_1(A_126,k2_relat_1(C_125)) = C_125
      | ~ r1_tarski(k2_zfmisc_1(A_126,k2_relat_1(C_125)),C_125)
      | ~ r1_tarski(k1_relat_1(C_125),A_126)
      | ~ v1_relat_1(C_125) ) ),
    inference(resolution,[status(thm)],[c_1111,c_2])).

tff(c_2250,plain,(
    ! [A_126] :
      ( k2_zfmisc_1(A_126,k2_relat_1('#skF_1')) = '#skF_1'
      | ~ r1_tarski(k2_zfmisc_1(A_126,k1_xboole_0),'#skF_1')
      | ~ r1_tarski(k1_relat_1('#skF_1'),A_126)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2230,c_1144])).

tff(c_2323,plain,(
    ! [A_126] :
      ( k1_xboole_0 = '#skF_1'
      | ~ r1_tarski(k1_relat_1('#skF_1'),A_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_8,c_12,c_12,c_2230,c_2250])).

tff(c_2368,plain,(
    ! [A_192] : ~ r1_tarski(k1_relat_1('#skF_1'),A_192) ),
    inference(splitLeft,[status(thm)],[c_2323])).

tff(c_2397,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_2368])).

tff(c_2398,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2323])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_138,plain,(
    ! [A_39,B_40,C_41] :
      ( k1_relset_1(A_39,B_40,C_41) = k1_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_421,plain,(
    ! [A_69,B_70,A_71] :
      ( k1_relset_1(A_69,B_70,A_71) = k1_relat_1(A_71)
      | ~ r1_tarski(A_71,k2_zfmisc_1(A_69,B_70)) ) ),
    inference(resolution,[status(thm)],[c_18,c_138])).

tff(c_435,plain,(
    ! [A_69,B_70] : k1_relset_1(A_69,B_70,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_421])).

tff(c_438,plain,(
    ! [A_69,B_70] : k1_relset_1(A_69,B_70,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_435])).

tff(c_34,plain,(
    ! [A_20] :
      ( v1_funct_2(k1_xboole_0,A_20,k1_xboole_0)
      | k1_xboole_0 = A_20
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_20,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_55,plain,(
    ! [A_20] :
      ( v1_funct_2(k1_xboole_0,A_20,k1_xboole_0)
      | k1_xboole_0 = A_20
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_34])).

tff(c_163,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_55])).

tff(c_166,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_163])).

tff(c_170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_166])).

tff(c_172,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_38,plain,(
    ! [C_22,B_21] :
      ( v1_funct_2(C_22,k1_xboole_0,B_21)
      | k1_relset_1(k1_xboole_0,B_21,C_22) != k1_xboole_0
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_448,plain,(
    ! [C_74,B_75] :
      ( v1_funct_2(C_74,k1_xboole_0,B_75)
      | k1_relset_1(k1_xboole_0,B_75,C_74) != k1_xboole_0
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_38])).

tff(c_450,plain,(
    ! [B_75] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_75)
      | k1_relset_1(k1_xboole_0,B_75,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_172,c_448])).

tff(c_456,plain,(
    ! [B_75] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_75) ),
    inference(demodulation,[status(thm),theory(equality)],[c_438,c_450])).

tff(c_2441,plain,(
    ! [B_75] : v1_funct_2('#skF_1','#skF_1',B_75) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2398,c_2398,c_456])).

tff(c_2463,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2398,c_2398,c_28])).

tff(c_2232,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2230,c_91])).

tff(c_2399,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2398,c_2232])).

tff(c_2622,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2441,c_2463,c_2399])).

tff(c_2623,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_2900,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2891,c_2623])).

tff(c_2915,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_6,c_6,c_2900])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 17:30:30 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.88/1.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.88/1.93  
% 4.88/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.88/1.94  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 4.88/1.94  
% 4.88/1.94  %Foreground sorts:
% 4.88/1.94  
% 4.88/1.94  
% 4.88/1.94  %Background operators:
% 4.88/1.94  
% 4.88/1.94  
% 4.88/1.94  %Foreground operators:
% 4.88/1.94  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.88/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.88/1.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.88/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.88/1.94  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.88/1.94  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.88/1.94  tff('#skF_1', type, '#skF_1': $i).
% 4.88/1.94  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.88/1.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.88/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.88/1.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.88/1.94  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.88/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.88/1.94  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.88/1.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.88/1.94  
% 4.88/1.95  tff(f_105, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 4.88/1.95  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.88/1.95  tff(f_76, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 4.88/1.95  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.88/1.95  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.88/1.95  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 4.88/1.95  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.88/1.95  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.88/1.95  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.88/1.95  tff(f_64, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 4.88/1.95  tff(c_50, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.88/1.95  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.88/1.95  tff(c_2891, plain, (![C_228, A_229, B_230]: (m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(A_229, B_230))) | ~r1_tarski(k2_relat_1(C_228), B_230) | ~r1_tarski(k1_relat_1(C_228), A_229) | ~v1_relat_1(C_228))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.88/1.95  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.88/1.95  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.88/1.95  tff(c_22, plain, (![A_11, B_13]: (r1_tarski(k2_relat_1(A_11), k2_relat_1(B_13)) | ~r1_tarski(A_11, B_13) | ~v1_relat_1(B_13) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.88/1.95  tff(c_361, plain, (![C_61, A_62, B_63]: (m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))) | ~r1_tarski(k2_relat_1(C_61), B_63) | ~r1_tarski(k1_relat_1(C_61), A_62) | ~v1_relat_1(C_61))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.88/1.95  tff(c_30, plain, (![A_14, B_15, C_16]: (k1_relset_1(A_14, B_15, C_16)=k1_relat_1(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.88/1.95  tff(c_1401, plain, (![A_137, B_138, C_139]: (k1_relset_1(A_137, B_138, C_139)=k1_relat_1(C_139) | ~r1_tarski(k2_relat_1(C_139), B_138) | ~r1_tarski(k1_relat_1(C_139), A_137) | ~v1_relat_1(C_139))), inference(resolution, [status(thm)], [c_361, c_30])).
% 4.88/1.95  tff(c_1804, plain, (![A_170, B_171, A_172]: (k1_relset_1(A_170, k2_relat_1(B_171), A_172)=k1_relat_1(A_172) | ~r1_tarski(k1_relat_1(A_172), A_170) | ~r1_tarski(A_172, B_171) | ~v1_relat_1(B_171) | ~v1_relat_1(A_172))), inference(resolution, [status(thm)], [c_22, c_1401])).
% 4.88/1.95  tff(c_1834, plain, (![A_172, B_171]: (k1_relset_1(k1_relat_1(A_172), k2_relat_1(B_171), A_172)=k1_relat_1(A_172) | ~r1_tarski(A_172, B_171) | ~v1_relat_1(B_171) | ~v1_relat_1(A_172))), inference(resolution, [status(thm)], [c_6, c_1804])).
% 4.88/1.95  tff(c_32, plain, (![C_19, A_17, B_18]: (m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))) | ~r1_tarski(k2_relat_1(C_19), B_18) | ~r1_tarski(k1_relat_1(C_19), A_17) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.88/1.95  tff(c_488, plain, (![B_81, C_82, A_83]: (k1_xboole_0=B_81 | v1_funct_2(C_82, A_83, B_81) | k1_relset_1(A_83, B_81, C_82)!=A_83 | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_83, B_81))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.88/1.95  tff(c_1982, plain, (![B_180, C_181, A_182]: (k1_xboole_0=B_180 | v1_funct_2(C_181, A_182, B_180) | k1_relset_1(A_182, B_180, C_181)!=A_182 | ~r1_tarski(k2_relat_1(C_181), B_180) | ~r1_tarski(k1_relat_1(C_181), A_182) | ~v1_relat_1(C_181))), inference(resolution, [status(thm)], [c_32, c_488])).
% 4.88/1.95  tff(c_2177, plain, (![C_190, A_191]: (k2_relat_1(C_190)=k1_xboole_0 | v1_funct_2(C_190, A_191, k2_relat_1(C_190)) | k1_relset_1(A_191, k2_relat_1(C_190), C_190)!=A_191 | ~r1_tarski(k1_relat_1(C_190), A_191) | ~v1_relat_1(C_190))), inference(resolution, [status(thm)], [c_6, c_1982])).
% 4.88/1.95  tff(c_48, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.88/1.95  tff(c_46, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.88/1.95  tff(c_52, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46])).
% 4.88/1.95  tff(c_91, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_52])).
% 4.88/1.95  tff(c_2193, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_2177, c_91])).
% 4.88/1.95  tff(c_2213, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_6, c_2193])).
% 4.88/1.95  tff(c_2216, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_2213])).
% 4.88/1.95  tff(c_2219, plain, (~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1834, c_2216])).
% 4.88/1.95  tff(c_2229, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_6, c_2219])).
% 4.88/1.95  tff(c_2230, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2213])).
% 4.88/1.95  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.88/1.95  tff(c_1087, plain, (![C_122, A_123, B_124]: (r1_tarski(C_122, k2_zfmisc_1(A_123, B_124)) | ~r1_tarski(k2_relat_1(C_122), B_124) | ~r1_tarski(k1_relat_1(C_122), A_123) | ~v1_relat_1(C_122))), inference(resolution, [status(thm)], [c_361, c_16])).
% 4.88/1.95  tff(c_1111, plain, (![C_125, A_126]: (r1_tarski(C_125, k2_zfmisc_1(A_126, k2_relat_1(C_125))) | ~r1_tarski(k1_relat_1(C_125), A_126) | ~v1_relat_1(C_125))), inference(resolution, [status(thm)], [c_6, c_1087])).
% 4.88/1.95  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.88/1.95  tff(c_1144, plain, (![A_126, C_125]: (k2_zfmisc_1(A_126, k2_relat_1(C_125))=C_125 | ~r1_tarski(k2_zfmisc_1(A_126, k2_relat_1(C_125)), C_125) | ~r1_tarski(k1_relat_1(C_125), A_126) | ~v1_relat_1(C_125))), inference(resolution, [status(thm)], [c_1111, c_2])).
% 4.88/1.95  tff(c_2250, plain, (![A_126]: (k2_zfmisc_1(A_126, k2_relat_1('#skF_1'))='#skF_1' | ~r1_tarski(k2_zfmisc_1(A_126, k1_xboole_0), '#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), A_126) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2230, c_1144])).
% 4.88/1.95  tff(c_2323, plain, (![A_126]: (k1_xboole_0='#skF_1' | ~r1_tarski(k1_relat_1('#skF_1'), A_126))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_8, c_12, c_12, c_2230, c_2250])).
% 4.88/1.95  tff(c_2368, plain, (![A_192]: (~r1_tarski(k1_relat_1('#skF_1'), A_192))), inference(splitLeft, [status(thm)], [c_2323])).
% 4.88/1.95  tff(c_2397, plain, $false, inference(resolution, [status(thm)], [c_6, c_2368])).
% 4.88/1.95  tff(c_2398, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_2323])).
% 4.88/1.95  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.88/1.95  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.88/1.95  tff(c_138, plain, (![A_39, B_40, C_41]: (k1_relset_1(A_39, B_40, C_41)=k1_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.88/1.95  tff(c_421, plain, (![A_69, B_70, A_71]: (k1_relset_1(A_69, B_70, A_71)=k1_relat_1(A_71) | ~r1_tarski(A_71, k2_zfmisc_1(A_69, B_70)))), inference(resolution, [status(thm)], [c_18, c_138])).
% 4.88/1.95  tff(c_435, plain, (![A_69, B_70]: (k1_relset_1(A_69, B_70, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_421])).
% 4.88/1.95  tff(c_438, plain, (![A_69, B_70]: (k1_relset_1(A_69, B_70, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_435])).
% 4.88/1.95  tff(c_34, plain, (![A_20]: (v1_funct_2(k1_xboole_0, A_20, k1_xboole_0) | k1_xboole_0=A_20 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_20, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.88/1.95  tff(c_55, plain, (![A_20]: (v1_funct_2(k1_xboole_0, A_20, k1_xboole_0) | k1_xboole_0=A_20 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_34])).
% 4.88/1.95  tff(c_163, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_55])).
% 4.88/1.95  tff(c_166, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_163])).
% 4.88/1.95  tff(c_170, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_166])).
% 4.88/1.95  tff(c_172, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_55])).
% 4.88/1.95  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.88/1.95  tff(c_38, plain, (![C_22, B_21]: (v1_funct_2(C_22, k1_xboole_0, B_21) | k1_relset_1(k1_xboole_0, B_21, C_22)!=k1_xboole_0 | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_21))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.88/1.95  tff(c_448, plain, (![C_74, B_75]: (v1_funct_2(C_74, k1_xboole_0, B_75) | k1_relset_1(k1_xboole_0, B_75, C_74)!=k1_xboole_0 | ~m1_subset_1(C_74, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_38])).
% 4.88/1.95  tff(c_450, plain, (![B_75]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_75) | k1_relset_1(k1_xboole_0, B_75, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_172, c_448])).
% 4.88/1.95  tff(c_456, plain, (![B_75]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_75))), inference(demodulation, [status(thm), theory('equality')], [c_438, c_450])).
% 4.88/1.95  tff(c_2441, plain, (![B_75]: (v1_funct_2('#skF_1', '#skF_1', B_75))), inference(demodulation, [status(thm), theory('equality')], [c_2398, c_2398, c_456])).
% 4.88/1.95  tff(c_2463, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2398, c_2398, c_28])).
% 4.88/1.95  tff(c_2232, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2230, c_91])).
% 4.88/1.95  tff(c_2399, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2398, c_2232])).
% 4.88/1.95  tff(c_2622, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2441, c_2463, c_2399])).
% 4.88/1.95  tff(c_2623, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_52])).
% 4.88/1.95  tff(c_2900, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_2891, c_2623])).
% 4.88/1.95  tff(c_2915, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_6, c_6, c_2900])).
% 4.88/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.88/1.95  
% 4.88/1.95  Inference rules
% 4.88/1.95  ----------------------
% 4.88/1.95  #Ref     : 0
% 4.88/1.95  #Sup     : 606
% 4.88/1.95  #Fact    : 0
% 4.88/1.95  #Define  : 0
% 4.88/1.95  #Split   : 7
% 4.88/1.95  #Chain   : 0
% 4.88/1.95  #Close   : 0
% 4.88/1.95  
% 4.88/1.95  Ordering : KBO
% 4.88/1.95  
% 4.88/1.95  Simplification rules
% 4.88/1.95  ----------------------
% 4.88/1.95  #Subsume      : 118
% 4.88/1.95  #Demod        : 834
% 4.88/1.95  #Tautology    : 260
% 4.88/1.95  #SimpNegUnit  : 6
% 4.88/1.95  #BackRed      : 69
% 4.88/1.95  
% 4.88/1.95  #Partial instantiations: 0
% 4.88/1.95  #Strategies tried      : 1
% 4.88/1.95  
% 4.88/1.95  Timing (in seconds)
% 4.88/1.95  ----------------------
% 4.88/1.96  Preprocessing        : 0.33
% 4.88/1.96  Parsing              : 0.18
% 4.88/1.96  CNF conversion       : 0.02
% 4.88/1.96  Main loop            : 0.81
% 4.88/1.96  Inferencing          : 0.25
% 4.88/1.96  Reduction            : 0.25
% 4.88/1.96  Demodulation         : 0.18
% 4.88/1.96  BG Simplification    : 0.03
% 4.88/1.96  Subsumption          : 0.23
% 4.88/1.96  Abstraction          : 0.04
% 4.88/1.96  MUC search           : 0.00
% 4.88/1.96  Cooper               : 0.00
% 4.88/1.96  Total                : 1.18
% 4.88/1.96  Index Insertion      : 0.00
% 4.88/1.96  Index Deletion       : 0.00
% 4.88/1.96  Index Matching       : 0.00
% 4.88/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
