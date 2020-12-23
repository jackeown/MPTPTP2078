%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:17 EST 2020

% Result     : Theorem 5.12s
% Output     : CNFRefutation 5.28s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 403 expanded)
%              Number of leaves         :   37 ( 151 expanded)
%              Depth                    :   11
%              Number of atoms          :  189 (1133 expanded)
%              Number of equality atoms :   60 ( 234 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( m1_subset_1(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_funct_2)).

tff(f_92,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_122,axiom,(
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

tff(f_81,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_68,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_547,plain,(
    ! [C_113,B_114,A_115] :
      ( v1_xboole_0(C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(B_114,A_115)))
      | ~ v1_xboole_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_579,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_547])).

tff(c_586,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_579])).

tff(c_802,plain,(
    ! [A_137,B_138,D_139] :
      ( r2_relset_1(A_137,B_138,D_139,D_139)
      | ~ m1_subset_1(D_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_834,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_802])).

tff(c_62,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_180,plain,(
    ! [C_75,A_76,B_77] :
      ( v1_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_201,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_180])).

tff(c_66,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_64,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_889,plain,(
    ! [A_152,B_153,C_154] :
      ( k1_relset_1(A_152,B_153,C_154) = k1_relat_1(C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_932,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_889])).

tff(c_2050,plain,(
    ! [B_225,A_226,C_227] :
      ( k1_xboole_0 = B_225
      | k1_relset_1(A_226,B_225,C_227) = A_226
      | ~ v1_funct_2(C_227,A_226,B_225)
      | ~ m1_subset_1(C_227,k1_zfmisc_1(k2_zfmisc_1(A_226,B_225))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2080,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_2050])).

tff(c_2102,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_932,c_2080])).

tff(c_2114,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2102])).

tff(c_200,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_180])).

tff(c_72,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_70,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_931,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_889])).

tff(c_2077,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_2050])).

tff(c_2099,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_931,c_2077])).

tff(c_2108,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2099])).

tff(c_2265,plain,(
    ! [A_240,B_241] :
      ( r2_hidden('#skF_3'(A_240,B_241),k1_relat_1(A_240))
      | B_241 = A_240
      | k1_relat_1(B_241) != k1_relat_1(A_240)
      | ~ v1_funct_1(B_241)
      | ~ v1_relat_1(B_241)
      | ~ v1_funct_1(A_240)
      | ~ v1_relat_1(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_28,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,B_16)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2867,plain,(
    ! [A_288,B_289] :
      ( m1_subset_1('#skF_3'(A_288,B_289),k1_relat_1(A_288))
      | B_289 = A_288
      | k1_relat_1(B_289) != k1_relat_1(A_288)
      | ~ v1_funct_1(B_289)
      | ~ v1_relat_1(B_289)
      | ~ v1_funct_1(A_288)
      | ~ v1_relat_1(A_288) ) ),
    inference(resolution,[status(thm)],[c_2265,c_28])).

tff(c_2873,plain,(
    ! [B_289] :
      ( m1_subset_1('#skF_3'('#skF_6',B_289),'#skF_4')
      | B_289 = '#skF_6'
      | k1_relat_1(B_289) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_289)
      | ~ v1_relat_1(B_289)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2108,c_2867])).

tff(c_3277,plain,(
    ! [B_311] :
      ( m1_subset_1('#skF_3'('#skF_6',B_311),'#skF_4')
      | B_311 = '#skF_6'
      | k1_relat_1(B_311) != '#skF_4'
      | ~ v1_funct_1(B_311)
      | ~ v1_relat_1(B_311) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_72,c_2108,c_2873])).

tff(c_60,plain,(
    ! [E_47] :
      ( k1_funct_1('#skF_7',E_47) = k1_funct_1('#skF_6',E_47)
      | ~ m1_subset_1(E_47,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_3284,plain,(
    ! [B_312] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_6',B_312)) = k1_funct_1('#skF_6','#skF_3'('#skF_6',B_312))
      | B_312 = '#skF_6'
      | k1_relat_1(B_312) != '#skF_4'
      | ~ v1_funct_1(B_312)
      | ~ v1_relat_1(B_312) ) ),
    inference(resolution,[status(thm)],[c_3277,c_60])).

tff(c_32,plain,(
    ! [B_24,A_20] :
      ( k1_funct_1(B_24,'#skF_3'(A_20,B_24)) != k1_funct_1(A_20,'#skF_3'(A_20,B_24))
      | B_24 = A_20
      | k1_relat_1(B_24) != k1_relat_1(A_20)
      | ~ v1_funct_1(B_24)
      | ~ v1_relat_1(B_24)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3291,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_7') != '#skF_4'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_3284,c_32])).

tff(c_3298,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_66,c_2114,c_200,c_72,c_2108,c_2114,c_3291])).

tff(c_58,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_3313,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3298,c_58])).

tff(c_3323,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_834,c_3313])).

tff(c_3324,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2102])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3374,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3324,c_12])).

tff(c_3376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_586,c_3374])).

tff(c_3377,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2099])).

tff(c_3427,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3377,c_12])).

tff(c_3429,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_586,c_3427])).

tff(c_3430,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_579])).

tff(c_116,plain,(
    ! [A_59,B_60] :
      ( r2_hidden('#skF_2'(A_59,B_60),A_59)
      | r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_124,plain,(
    ! [A_59,B_60] :
      ( ~ v1_xboole_0(A_59)
      | r1_tarski(A_59,B_60) ) ),
    inference(resolution,[status(thm)],[c_116,c_2])).

tff(c_139,plain,(
    ! [B_66,A_67] :
      ( B_66 = A_67
      | ~ r1_tarski(B_66,A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_149,plain,(
    ! [B_68,A_69] :
      ( B_68 = A_69
      | ~ r1_tarski(B_68,A_69)
      | ~ v1_xboole_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_124,c_139])).

tff(c_159,plain,(
    ! [B_70,A_71] :
      ( B_70 = A_71
      | ~ v1_xboole_0(B_70)
      | ~ v1_xboole_0(A_71) ) ),
    inference(resolution,[status(thm)],[c_124,c_149])).

tff(c_162,plain,(
    ! [A_71] :
      ( k1_xboole_0 = A_71
      | ~ v1_xboole_0(A_71) ) ),
    inference(resolution,[status(thm)],[c_12,c_159])).

tff(c_3437,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3430,c_162])).

tff(c_26,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3593,plain,(
    ! [A_322] : m1_subset_1('#skF_6',k1_zfmisc_1(A_322)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3437,c_26])).

tff(c_42,plain,(
    ! [A_36,B_37,D_39] :
      ( r2_relset_1(A_36,B_37,D_39,D_39)
      | ~ m1_subset_1(D_39,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3609,plain,(
    ! [A_36,B_37] : r2_relset_1(A_36,B_37,'#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_3593,c_42])).

tff(c_3431,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_579])).

tff(c_3444,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3431,c_162])).

tff(c_3488,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3437,c_3444])).

tff(c_580,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_547])).

tff(c_3507,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3430,c_3488,c_580])).

tff(c_156,plain,(
    ! [B_60,A_59] :
      ( B_60 = A_59
      | ~ v1_xboole_0(B_60)
      | ~ v1_xboole_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_124,c_149])).

tff(c_3445,plain,(
    ! [A_59] :
      ( A_59 = '#skF_5'
      | ~ v1_xboole_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_3431,c_156])).

tff(c_3512,plain,(
    ! [A_316] :
      ( A_316 = '#skF_6'
      | ~ v1_xboole_0(A_316) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3488,c_3445])).

tff(c_3519,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3507,c_3512])).

tff(c_3492,plain,(
    ~ r2_relset_1('#skF_4','#skF_6','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3488,c_58])).

tff(c_3567,plain,(
    ~ r2_relset_1('#skF_4','#skF_6','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3519,c_3492])).

tff(c_3693,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3609,c_3567])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:22:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.12/1.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.28/1.97  
% 5.28/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.28/1.97  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 5.28/1.97  
% 5.28/1.97  %Foreground sorts:
% 5.28/1.97  
% 5.28/1.97  
% 5.28/1.97  %Background operators:
% 5.28/1.97  
% 5.28/1.97  
% 5.28/1.97  %Foreground operators:
% 5.28/1.97  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.28/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.28/1.97  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.28/1.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.28/1.97  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.28/1.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.28/1.97  tff('#skF_7', type, '#skF_7': $i).
% 5.28/1.97  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.28/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.28/1.97  tff('#skF_5', type, '#skF_5': $i).
% 5.28/1.97  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.28/1.97  tff('#skF_6', type, '#skF_6': $i).
% 5.28/1.97  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.28/1.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.28/1.97  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.28/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.28/1.97  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.28/1.97  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.28/1.97  tff('#skF_4', type, '#skF_4': $i).
% 5.28/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.28/1.97  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.28/1.97  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.28/1.97  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.28/1.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.28/1.97  
% 5.28/1.99  tff(f_143, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_funct_2)).
% 5.28/1.99  tff(f_92, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 5.28/1.99  tff(f_104, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.28/1.99  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.28/1.99  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.28/1.99  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.28/1.99  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 5.28/1.99  tff(f_57, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 5.28/1.99  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.28/1.99  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.28/1.99  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.28/1.99  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.28/1.99  tff(f_53, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 5.28/1.99  tff(c_68, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.28/1.99  tff(c_547, plain, (![C_113, B_114, A_115]: (v1_xboole_0(C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(B_114, A_115))) | ~v1_xboole_0(A_115))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.28/1.99  tff(c_579, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_68, c_547])).
% 5.28/1.99  tff(c_586, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_579])).
% 5.28/1.99  tff(c_802, plain, (![A_137, B_138, D_139]: (r2_relset_1(A_137, B_138, D_139, D_139) | ~m1_subset_1(D_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.28/1.99  tff(c_834, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_68, c_802])).
% 5.28/1.99  tff(c_62, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.28/1.99  tff(c_180, plain, (![C_75, A_76, B_77]: (v1_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.28/1.99  tff(c_201, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_62, c_180])).
% 5.28/1.99  tff(c_66, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.28/1.99  tff(c_64, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.28/1.99  tff(c_889, plain, (![A_152, B_153, C_154]: (k1_relset_1(A_152, B_153, C_154)=k1_relat_1(C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.28/1.99  tff(c_932, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_62, c_889])).
% 5.28/1.99  tff(c_2050, plain, (![B_225, A_226, C_227]: (k1_xboole_0=B_225 | k1_relset_1(A_226, B_225, C_227)=A_226 | ~v1_funct_2(C_227, A_226, B_225) | ~m1_subset_1(C_227, k1_zfmisc_1(k2_zfmisc_1(A_226, B_225))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.28/1.99  tff(c_2080, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_62, c_2050])).
% 5.28/1.99  tff(c_2102, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_932, c_2080])).
% 5.28/1.99  tff(c_2114, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_2102])).
% 5.28/1.99  tff(c_200, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_68, c_180])).
% 5.28/1.99  tff(c_72, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.28/1.99  tff(c_70, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.28/1.99  tff(c_931, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_68, c_889])).
% 5.28/1.99  tff(c_2077, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_68, c_2050])).
% 5.28/1.99  tff(c_2099, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_931, c_2077])).
% 5.28/1.99  tff(c_2108, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_2099])).
% 5.28/1.99  tff(c_2265, plain, (![A_240, B_241]: (r2_hidden('#skF_3'(A_240, B_241), k1_relat_1(A_240)) | B_241=A_240 | k1_relat_1(B_241)!=k1_relat_1(A_240) | ~v1_funct_1(B_241) | ~v1_relat_1(B_241) | ~v1_funct_1(A_240) | ~v1_relat_1(A_240))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.28/1.99  tff(c_28, plain, (![A_15, B_16]: (m1_subset_1(A_15, B_16) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.28/1.99  tff(c_2867, plain, (![A_288, B_289]: (m1_subset_1('#skF_3'(A_288, B_289), k1_relat_1(A_288)) | B_289=A_288 | k1_relat_1(B_289)!=k1_relat_1(A_288) | ~v1_funct_1(B_289) | ~v1_relat_1(B_289) | ~v1_funct_1(A_288) | ~v1_relat_1(A_288))), inference(resolution, [status(thm)], [c_2265, c_28])).
% 5.28/1.99  tff(c_2873, plain, (![B_289]: (m1_subset_1('#skF_3'('#skF_6', B_289), '#skF_4') | B_289='#skF_6' | k1_relat_1(B_289)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_289) | ~v1_relat_1(B_289) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2108, c_2867])).
% 5.28/1.99  tff(c_3277, plain, (![B_311]: (m1_subset_1('#skF_3'('#skF_6', B_311), '#skF_4') | B_311='#skF_6' | k1_relat_1(B_311)!='#skF_4' | ~v1_funct_1(B_311) | ~v1_relat_1(B_311))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_72, c_2108, c_2873])).
% 5.28/1.99  tff(c_60, plain, (![E_47]: (k1_funct_1('#skF_7', E_47)=k1_funct_1('#skF_6', E_47) | ~m1_subset_1(E_47, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.28/1.99  tff(c_3284, plain, (![B_312]: (k1_funct_1('#skF_7', '#skF_3'('#skF_6', B_312))=k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_312)) | B_312='#skF_6' | k1_relat_1(B_312)!='#skF_4' | ~v1_funct_1(B_312) | ~v1_relat_1(B_312))), inference(resolution, [status(thm)], [c_3277, c_60])).
% 5.28/1.99  tff(c_32, plain, (![B_24, A_20]: (k1_funct_1(B_24, '#skF_3'(A_20, B_24))!=k1_funct_1(A_20, '#skF_3'(A_20, B_24)) | B_24=A_20 | k1_relat_1(B_24)!=k1_relat_1(A_20) | ~v1_funct_1(B_24) | ~v1_relat_1(B_24) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.28/1.99  tff(c_3291, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_7'='#skF_6' | k1_relat_1('#skF_7')!='#skF_4' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_3284, c_32])).
% 5.28/1.99  tff(c_3298, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_201, c_66, c_2114, c_200, c_72, c_2108, c_2114, c_3291])).
% 5.28/1.99  tff(c_58, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.28/1.99  tff(c_3313, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3298, c_58])).
% 5.28/1.99  tff(c_3323, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_834, c_3313])).
% 5.28/1.99  tff(c_3324, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_2102])).
% 5.28/1.99  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.28/1.99  tff(c_3374, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3324, c_12])).
% 5.28/1.99  tff(c_3376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_586, c_3374])).
% 5.28/1.99  tff(c_3377, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_2099])).
% 5.28/1.99  tff(c_3427, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3377, c_12])).
% 5.28/1.99  tff(c_3429, plain, $false, inference(negUnitSimplification, [status(thm)], [c_586, c_3427])).
% 5.28/1.99  tff(c_3430, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_579])).
% 5.28/1.99  tff(c_116, plain, (![A_59, B_60]: (r2_hidden('#skF_2'(A_59, B_60), A_59) | r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.28/1.99  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.28/1.99  tff(c_124, plain, (![A_59, B_60]: (~v1_xboole_0(A_59) | r1_tarski(A_59, B_60))), inference(resolution, [status(thm)], [c_116, c_2])).
% 5.28/1.99  tff(c_139, plain, (![B_66, A_67]: (B_66=A_67 | ~r1_tarski(B_66, A_67) | ~r1_tarski(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.28/1.99  tff(c_149, plain, (![B_68, A_69]: (B_68=A_69 | ~r1_tarski(B_68, A_69) | ~v1_xboole_0(A_69))), inference(resolution, [status(thm)], [c_124, c_139])).
% 5.28/1.99  tff(c_159, plain, (![B_70, A_71]: (B_70=A_71 | ~v1_xboole_0(B_70) | ~v1_xboole_0(A_71))), inference(resolution, [status(thm)], [c_124, c_149])).
% 5.28/1.99  tff(c_162, plain, (![A_71]: (k1_xboole_0=A_71 | ~v1_xboole_0(A_71))), inference(resolution, [status(thm)], [c_12, c_159])).
% 5.28/1.99  tff(c_3437, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_3430, c_162])).
% 5.28/1.99  tff(c_26, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.28/1.99  tff(c_3593, plain, (![A_322]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_322)))), inference(demodulation, [status(thm), theory('equality')], [c_3437, c_26])).
% 5.28/1.99  tff(c_42, plain, (![A_36, B_37, D_39]: (r2_relset_1(A_36, B_37, D_39, D_39) | ~m1_subset_1(D_39, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.28/1.99  tff(c_3609, plain, (![A_36, B_37]: (r2_relset_1(A_36, B_37, '#skF_6', '#skF_6'))), inference(resolution, [status(thm)], [c_3593, c_42])).
% 5.28/1.99  tff(c_3431, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_579])).
% 5.28/1.99  tff(c_3444, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_3431, c_162])).
% 5.28/1.99  tff(c_3488, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3437, c_3444])).
% 5.28/1.99  tff(c_580, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_62, c_547])).
% 5.28/1.99  tff(c_3507, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3430, c_3488, c_580])).
% 5.28/1.99  tff(c_156, plain, (![B_60, A_59]: (B_60=A_59 | ~v1_xboole_0(B_60) | ~v1_xboole_0(A_59))), inference(resolution, [status(thm)], [c_124, c_149])).
% 5.28/1.99  tff(c_3445, plain, (![A_59]: (A_59='#skF_5' | ~v1_xboole_0(A_59))), inference(resolution, [status(thm)], [c_3431, c_156])).
% 5.28/1.99  tff(c_3512, plain, (![A_316]: (A_316='#skF_6' | ~v1_xboole_0(A_316))), inference(demodulation, [status(thm), theory('equality')], [c_3488, c_3445])).
% 5.28/1.99  tff(c_3519, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_3507, c_3512])).
% 5.28/1.99  tff(c_3492, plain, (~r2_relset_1('#skF_4', '#skF_6', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3488, c_58])).
% 5.28/1.99  tff(c_3567, plain, (~r2_relset_1('#skF_4', '#skF_6', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3519, c_3492])).
% 5.28/1.99  tff(c_3693, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3609, c_3567])).
% 5.28/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.28/1.99  
% 5.28/1.99  Inference rules
% 5.28/1.99  ----------------------
% 5.28/1.99  #Ref     : 1
% 5.28/1.99  #Sup     : 763
% 5.28/1.99  #Fact    : 0
% 5.28/1.99  #Define  : 0
% 5.28/1.99  #Split   : 14
% 5.28/1.99  #Chain   : 0
% 5.28/1.99  #Close   : 0
% 5.28/1.99  
% 5.28/1.99  Ordering : KBO
% 5.28/1.99  
% 5.28/1.99  Simplification rules
% 5.28/1.99  ----------------------
% 5.28/1.99  #Subsume      : 181
% 5.28/1.99  #Demod        : 775
% 5.28/1.99  #Tautology    : 359
% 5.28/1.99  #SimpNegUnit  : 35
% 5.28/1.99  #BackRed      : 181
% 5.28/1.99  
% 5.28/1.99  #Partial instantiations: 0
% 5.28/1.99  #Strategies tried      : 1
% 5.28/1.99  
% 5.28/1.99  Timing (in seconds)
% 5.28/1.99  ----------------------
% 5.28/1.99  Preprocessing        : 0.34
% 5.28/1.99  Parsing              : 0.17
% 5.28/1.99  CNF conversion       : 0.03
% 5.28/1.99  Main loop            : 0.85
% 5.28/1.99  Inferencing          : 0.28
% 5.28/1.99  Reduction            : 0.27
% 5.28/1.99  Demodulation         : 0.18
% 5.28/1.99  BG Simplification    : 0.04
% 5.28/1.99  Subsumption          : 0.19
% 5.28/1.99  Abstraction          : 0.04
% 5.28/1.99  MUC search           : 0.00
% 5.28/1.99  Cooper               : 0.00
% 5.28/1.99  Total                : 1.22
% 5.28/1.99  Index Insertion      : 0.00
% 5.28/1.99  Index Deletion       : 0.00
% 5.28/1.99  Index Matching       : 0.00
% 5.28/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
