%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:51 EST 2020

% Result     : Theorem 5.86s
% Output     : CNFRefutation 5.99s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 221 expanded)
%              Number of leaves         :   38 (  91 expanded)
%              Depth                    :   10
%              Number of atoms          :  153 ( 722 expanded)
%              Number of equality atoms :   29 ( 162 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_162,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_relset_1(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_96,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_127,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( v1_partfun1(C,A)
              & v1_partfun1(D,A)
              & r1_partfun1(C,D) )
           => C = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_70,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_64,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_857,plain,(
    ! [A_156,B_157,C_158,D_159] :
      ( r2_relset_1(A_156,B_157,C_158,C_158)
      | ~ m1_subset_1(D_159,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157)))
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_957,plain,(
    ! [C_163] :
      ( r2_relset_1('#skF_4','#skF_5',C_163,C_163)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_64,c_857])).

tff(c_981,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_957])).

tff(c_60,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_77,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_68,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_66,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_713,plain,(
    ! [C_146,A_147,B_148] :
      ( v1_partfun1(C_146,A_147)
      | ~ v1_funct_2(C_146,A_147,B_148)
      | ~ v1_funct_1(C_146)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148)))
      | v1_xboole_0(B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_723,plain,
    ( v1_partfun1('#skF_7','#skF_4')
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_713])).

tff(c_745,plain,
    ( v1_partfun1('#skF_7','#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_723])).

tff(c_752,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_745])).

tff(c_108,plain,(
    ! [A_59] :
      ( r2_hidden('#skF_3'(A_59),A_59)
      | k1_xboole_0 = A_59 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_112,plain,(
    ! [A_59] :
      ( ~ v1_xboole_0(A_59)
      | k1_xboole_0 = A_59 ) ),
    inference(resolution,[status(thm)],[c_108,c_2])).

tff(c_755,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_752,c_112])).

tff(c_759,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_755])).

tff(c_761,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_745])).

tff(c_74,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_72,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_726,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_713])).

tff(c_748,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_726])).

tff(c_762,plain,(
    v1_partfun1('#skF_6','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_761,c_748])).

tff(c_760,plain,(
    v1_partfun1('#skF_7','#skF_4') ),
    inference(splitRight,[status(thm)],[c_745])).

tff(c_62,plain,(
    r1_partfun1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_1023,plain,(
    ! [D_164,C_165,A_166,B_167] :
      ( D_164 = C_165
      | ~ r1_partfun1(C_165,D_164)
      | ~ v1_partfun1(D_164,A_166)
      | ~ v1_partfun1(C_165,A_166)
      | ~ m1_subset_1(D_164,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167)))
      | ~ v1_funct_1(D_164)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167)))
      | ~ v1_funct_1(C_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1025,plain,(
    ! [A_166,B_167] :
      ( '#skF_7' = '#skF_6'
      | ~ v1_partfun1('#skF_7',A_166)
      | ~ v1_partfun1('#skF_6',A_166)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_166,B_167)))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_166,B_167)))
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_62,c_1023])).

tff(c_1028,plain,(
    ! [A_166,B_167] :
      ( '#skF_7' = '#skF_6'
      | ~ v1_partfun1('#skF_7',A_166)
      | ~ v1_partfun1('#skF_6',A_166)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_166,B_167)))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_166,B_167))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_68,c_1025])).

tff(c_3405,plain,(
    ! [A_333,B_334] :
      ( ~ v1_partfun1('#skF_7',A_333)
      | ~ v1_partfun1('#skF_6',A_333)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_333,B_334)))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_333,B_334))) ) ),
    inference(splitLeft,[status(thm)],[c_1028])).

tff(c_3415,plain,
    ( ~ v1_partfun1('#skF_7','#skF_4')
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_64,c_3405])).

tff(c_3429,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_762,c_760,c_3415])).

tff(c_3430,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1028])).

tff(c_58,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_3440,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3430,c_58])).

tff(c_3453,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_981,c_3440])).

tff(c_3454,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_20,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_3467,plain,(
    ! [A_11] : m1_subset_1('#skF_4',k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3454,c_20])).

tff(c_4322,plain,(
    ! [A_442,B_443,C_444,D_445] :
      ( r2_relset_1(A_442,B_443,C_444,C_444)
      | ~ m1_subset_1(D_445,k1_zfmisc_1(k2_zfmisc_1(A_442,B_443)))
      | ~ m1_subset_1(C_444,k1_zfmisc_1(k2_zfmisc_1(A_442,B_443))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4792,plain,(
    ! [A_482,B_483,C_484] :
      ( r2_relset_1(A_482,B_483,C_484,C_484)
      | ~ m1_subset_1(C_484,k1_zfmisc_1(k2_zfmisc_1(A_482,B_483))) ) ),
    inference(resolution,[status(thm)],[c_3467,c_4322])).

tff(c_4828,plain,(
    ! [A_482,B_483] : r2_relset_1(A_482,B_483,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_3467,c_4792])).

tff(c_3510,plain,(
    ! [A_344,B_345] :
      ( r1_tarski(A_344,B_345)
      | ~ m1_subset_1(A_344,k1_zfmisc_1(B_345)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3526,plain,(
    ! [A_11] : r1_tarski('#skF_4',A_11) ),
    inference(resolution,[status(thm)],[c_3467,c_3510])).

tff(c_14,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3469,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3454,c_3454,c_14])).

tff(c_3455,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_3460,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3454,c_3455])).

tff(c_3504,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3469,c_3460,c_70])).

tff(c_3524,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_3504,c_3510])).

tff(c_3535,plain,(
    ! [B_350,A_351] :
      ( B_350 = A_351
      | ~ r1_tarski(B_350,A_351)
      | ~ r1_tarski(A_351,B_350) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3543,plain,
    ( '#skF_6' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_3524,c_3535])).

tff(c_3553,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3526,c_3543])).

tff(c_3503,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3469,c_3460,c_64])).

tff(c_3525,plain,(
    r1_tarski('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_3503,c_3510])).

tff(c_3541,plain,
    ( '#skF_7' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_7') ),
    inference(resolution,[status(thm)],[c_3525,c_3535])).

tff(c_3550,plain,(
    '#skF_7' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3526,c_3541])).

tff(c_3494,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3460,c_58])).

tff(c_3560,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3550,c_3494])).

tff(c_3633,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3553,c_3560])).

tff(c_4832,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4828,c_3633])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:20:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.86/2.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.86/2.11  
% 5.86/2.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.86/2.11  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3
% 5.86/2.11  
% 5.86/2.11  %Foreground sorts:
% 5.86/2.11  
% 5.86/2.11  
% 5.86/2.11  %Background operators:
% 5.86/2.11  
% 5.86/2.11  
% 5.86/2.11  %Foreground operators:
% 5.86/2.11  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.86/2.11  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.86/2.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.86/2.11  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.86/2.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.86/2.11  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.86/2.11  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.86/2.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.86/2.11  tff('#skF_7', type, '#skF_7': $i).
% 5.86/2.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.86/2.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.86/2.11  tff('#skF_5', type, '#skF_5': $i).
% 5.86/2.11  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.86/2.11  tff('#skF_6', type, '#skF_6': $i).
% 5.86/2.11  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.86/2.11  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.86/2.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.86/2.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.86/2.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.86/2.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.86/2.11  tff('#skF_4', type, '#skF_4': $i).
% 5.86/2.11  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.86/2.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.86/2.11  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.86/2.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.86/2.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.86/2.11  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 5.86/2.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.86/2.11  
% 5.99/2.13  tff(f_162, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_2)).
% 5.99/2.13  tff(f_80, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 5.99/2.13  tff(f_110, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 5.99/2.13  tff(f_96, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 5.99/2.13  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.99/2.13  tff(f_127, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_partfun1)).
% 5.99/2.13  tff(f_48, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 5.99/2.13  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.99/2.13  tff(f_43, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.99/2.13  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.99/2.13  tff(c_70, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.99/2.13  tff(c_64, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.99/2.13  tff(c_857, plain, (![A_156, B_157, C_158, D_159]: (r2_relset_1(A_156, B_157, C_158, C_158) | ~m1_subset_1(D_159, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.99/2.13  tff(c_957, plain, (![C_163]: (r2_relset_1('#skF_4', '#skF_5', C_163, C_163) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))))), inference(resolution, [status(thm)], [c_64, c_857])).
% 5.99/2.13  tff(c_981, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_70, c_957])).
% 5.99/2.13  tff(c_60, plain, (k1_xboole_0='#skF_4' | k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.99/2.13  tff(c_77, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_60])).
% 5.99/2.13  tff(c_68, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.99/2.13  tff(c_66, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.99/2.13  tff(c_713, plain, (![C_146, A_147, B_148]: (v1_partfun1(C_146, A_147) | ~v1_funct_2(C_146, A_147, B_148) | ~v1_funct_1(C_146) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))) | v1_xboole_0(B_148))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.99/2.13  tff(c_723, plain, (v1_partfun1('#skF_7', '#skF_4') | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_64, c_713])).
% 5.99/2.13  tff(c_745, plain, (v1_partfun1('#skF_7', '#skF_4') | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_723])).
% 5.99/2.13  tff(c_752, plain, (v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_745])).
% 5.99/2.13  tff(c_108, plain, (![A_59]: (r2_hidden('#skF_3'(A_59), A_59) | k1_xboole_0=A_59)), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.99/2.13  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.99/2.13  tff(c_112, plain, (![A_59]: (~v1_xboole_0(A_59) | k1_xboole_0=A_59)), inference(resolution, [status(thm)], [c_108, c_2])).
% 5.99/2.13  tff(c_755, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_752, c_112])).
% 5.99/2.13  tff(c_759, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_755])).
% 5.99/2.13  tff(c_761, plain, (~v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_745])).
% 5.99/2.13  tff(c_74, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.99/2.13  tff(c_72, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.99/2.13  tff(c_726, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_70, c_713])).
% 5.99/2.13  tff(c_748, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_726])).
% 5.99/2.13  tff(c_762, plain, (v1_partfun1('#skF_6', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_761, c_748])).
% 5.99/2.13  tff(c_760, plain, (v1_partfun1('#skF_7', '#skF_4')), inference(splitRight, [status(thm)], [c_745])).
% 5.99/2.13  tff(c_62, plain, (r1_partfun1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.99/2.13  tff(c_1023, plain, (![D_164, C_165, A_166, B_167]: (D_164=C_165 | ~r1_partfun1(C_165, D_164) | ~v1_partfun1(D_164, A_166) | ~v1_partfun1(C_165, A_166) | ~m1_subset_1(D_164, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))) | ~v1_funct_1(D_164) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))) | ~v1_funct_1(C_165))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.99/2.13  tff(c_1025, plain, (![A_166, B_167]: ('#skF_7'='#skF_6' | ~v1_partfun1('#skF_7', A_166) | ~v1_partfun1('#skF_6', A_166) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_62, c_1023])).
% 5.99/2.13  tff(c_1028, plain, (![A_166, B_167]: ('#skF_7'='#skF_6' | ~v1_partfun1('#skF_7', A_166) | ~v1_partfun1('#skF_6', A_166) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_68, c_1025])).
% 5.99/2.13  tff(c_3405, plain, (![A_333, B_334]: (~v1_partfun1('#skF_7', A_333) | ~v1_partfun1('#skF_6', A_333) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_333, B_334))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_333, B_334))))), inference(splitLeft, [status(thm)], [c_1028])).
% 5.99/2.13  tff(c_3415, plain, (~v1_partfun1('#skF_7', '#skF_4') | ~v1_partfun1('#skF_6', '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_64, c_3405])).
% 5.99/2.13  tff(c_3429, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_762, c_760, c_3415])).
% 5.99/2.13  tff(c_3430, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_1028])).
% 5.99/2.13  tff(c_58, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.99/2.13  tff(c_3440, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3430, c_58])).
% 5.99/2.13  tff(c_3453, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_981, c_3440])).
% 5.99/2.13  tff(c_3454, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_60])).
% 5.99/2.13  tff(c_20, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.99/2.13  tff(c_3467, plain, (![A_11]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_3454, c_20])).
% 5.99/2.13  tff(c_4322, plain, (![A_442, B_443, C_444, D_445]: (r2_relset_1(A_442, B_443, C_444, C_444) | ~m1_subset_1(D_445, k1_zfmisc_1(k2_zfmisc_1(A_442, B_443))) | ~m1_subset_1(C_444, k1_zfmisc_1(k2_zfmisc_1(A_442, B_443))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.99/2.13  tff(c_4792, plain, (![A_482, B_483, C_484]: (r2_relset_1(A_482, B_483, C_484, C_484) | ~m1_subset_1(C_484, k1_zfmisc_1(k2_zfmisc_1(A_482, B_483))))), inference(resolution, [status(thm)], [c_3467, c_4322])).
% 5.99/2.13  tff(c_4828, plain, (![A_482, B_483]: (r2_relset_1(A_482, B_483, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_3467, c_4792])).
% 5.99/2.13  tff(c_3510, plain, (![A_344, B_345]: (r1_tarski(A_344, B_345) | ~m1_subset_1(A_344, k1_zfmisc_1(B_345)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.99/2.13  tff(c_3526, plain, (![A_11]: (r1_tarski('#skF_4', A_11))), inference(resolution, [status(thm)], [c_3467, c_3510])).
% 5.99/2.13  tff(c_14, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.99/2.13  tff(c_3469, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3454, c_3454, c_14])).
% 5.99/2.13  tff(c_3455, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_60])).
% 5.99/2.13  tff(c_3460, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3454, c_3455])).
% 5.99/2.13  tff(c_3504, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3469, c_3460, c_70])).
% 5.99/2.13  tff(c_3524, plain, (r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_3504, c_3510])).
% 5.99/2.13  tff(c_3535, plain, (![B_350, A_351]: (B_350=A_351 | ~r1_tarski(B_350, A_351) | ~r1_tarski(A_351, B_350))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.99/2.13  tff(c_3543, plain, ('#skF_6'='#skF_4' | ~r1_tarski('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_3524, c_3535])).
% 5.99/2.13  tff(c_3553, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3526, c_3543])).
% 5.99/2.13  tff(c_3503, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3469, c_3460, c_64])).
% 5.99/2.13  tff(c_3525, plain, (r1_tarski('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_3503, c_3510])).
% 5.99/2.13  tff(c_3541, plain, ('#skF_7'='#skF_4' | ~r1_tarski('#skF_4', '#skF_7')), inference(resolution, [status(thm)], [c_3525, c_3535])).
% 5.99/2.13  tff(c_3550, plain, ('#skF_7'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3526, c_3541])).
% 5.99/2.13  tff(c_3494, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3460, c_58])).
% 5.99/2.13  tff(c_3560, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3550, c_3494])).
% 5.99/2.13  tff(c_3633, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3553, c_3560])).
% 5.99/2.13  tff(c_4832, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4828, c_3633])).
% 5.99/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.99/2.13  
% 5.99/2.13  Inference rules
% 5.99/2.13  ----------------------
% 5.99/2.13  #Ref     : 0
% 5.99/2.13  #Sup     : 976
% 5.99/2.13  #Fact    : 0
% 5.99/2.13  #Define  : 0
% 5.99/2.13  #Split   : 12
% 5.99/2.13  #Chain   : 0
% 5.99/2.13  #Close   : 0
% 5.99/2.13  
% 5.99/2.13  Ordering : KBO
% 5.99/2.13  
% 5.99/2.13  Simplification rules
% 5.99/2.13  ----------------------
% 5.99/2.13  #Subsume      : 145
% 5.99/2.13  #Demod        : 1185
% 5.99/2.13  #Tautology    : 412
% 5.99/2.13  #SimpNegUnit  : 2
% 5.99/2.13  #BackRed      : 37
% 5.99/2.13  
% 5.99/2.13  #Partial instantiations: 0
% 5.99/2.13  #Strategies tried      : 1
% 5.99/2.13  
% 5.99/2.13  Timing (in seconds)
% 5.99/2.13  ----------------------
% 5.99/2.13  Preprocessing        : 0.35
% 5.99/2.13  Parsing              : 0.19
% 5.99/2.13  CNF conversion       : 0.02
% 5.99/2.13  Main loop            : 1.01
% 5.99/2.13  Inferencing          : 0.34
% 5.99/2.13  Reduction            : 0.36
% 5.99/2.13  Demodulation         : 0.26
% 5.99/2.13  BG Simplification    : 0.03
% 5.99/2.13  Subsumption          : 0.19
% 5.99/2.13  Abstraction          : 0.04
% 5.99/2.13  MUC search           : 0.00
% 5.99/2.13  Cooper               : 0.00
% 5.99/2.13  Total                : 1.39
% 5.99/2.13  Index Insertion      : 0.00
% 5.99/2.13  Index Deletion       : 0.00
% 5.99/2.13  Index Matching       : 0.00
% 5.99/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
