%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:54 EST 2020

% Result     : Theorem 6.34s
% Output     : CNFRefutation 6.45s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 383 expanded)
%              Number of leaves         :   35 ( 137 expanded)
%              Depth                    :   10
%              Number of atoms          :  193 (1271 expanded)
%              Number of equality atoms :   35 ( 369 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_subset_1 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_mcart_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_138,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_84,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_115,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_58,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_52,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_581,plain,(
    ! [A_116,B_117,C_118,D_119] :
      ( r2_relset_1(A_116,B_117,C_118,C_118)
      | ~ m1_subset_1(D_119,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117)))
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_718,plain,(
    ! [C_124] :
      ( r2_relset_1('#skF_4','#skF_5',C_124,C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_52,c_581])).

tff(c_731,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_718])).

tff(c_48,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_56,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_54,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_476,plain,(
    ! [C_105,A_106,B_107] :
      ( v1_partfun1(C_105,A_106)
      | ~ v1_funct_2(C_105,A_106,B_107)
      | ~ v1_funct_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107)))
      | v1_xboole_0(B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_483,plain,
    ( v1_partfun1('#skF_7','#skF_4')
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_476])).

tff(c_500,plain,
    ( v1_partfun1('#skF_7','#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_483])).

tff(c_506,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_500])).

tff(c_34,plain,(
    ! [A_21] :
      ( r2_hidden('#skF_3'(A_21),A_21)
      | k1_xboole_0 = A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_28,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_153,plain,(
    ! [C_68,B_69,A_70] :
      ( ~ v1_xboole_0(C_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(C_68))
      | ~ r2_hidden(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_344,plain,(
    ! [B_85,A_86,A_87] :
      ( ~ v1_xboole_0(B_85)
      | ~ r2_hidden(A_86,A_87)
      | ~ r1_tarski(A_87,B_85) ) ),
    inference(resolution,[status(thm)],[c_28,c_153])).

tff(c_358,plain,(
    ! [B_92,A_93] :
      ( ~ v1_xboole_0(B_92)
      | ~ r1_tarski(A_93,B_92)
      | k1_xboole_0 = A_93 ) ),
    inference(resolution,[status(thm)],[c_34,c_344])).

tff(c_383,plain,(
    ! [B_7] :
      ( ~ v1_xboole_0(B_7)
      | k1_xboole_0 = B_7 ) ),
    inference(resolution,[status(thm)],[c_14,c_358])).

tff(c_514,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_506,c_383])).

tff(c_523,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_514])).

tff(c_525,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_500])).

tff(c_62,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_60,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_486,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_476])).

tff(c_503,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_486])).

tff(c_526,plain,(
    v1_partfun1('#skF_6','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_525,c_503])).

tff(c_524,plain,(
    v1_partfun1('#skF_7','#skF_4') ),
    inference(splitRight,[status(thm)],[c_500])).

tff(c_50,plain,(
    r1_partfun1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_756,plain,(
    ! [D_129,C_130,A_131,B_132] :
      ( D_129 = C_130
      | ~ r1_partfun1(C_130,D_129)
      | ~ v1_partfun1(D_129,A_131)
      | ~ v1_partfun1(C_130,A_131)
      | ~ m1_subset_1(D_129,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132)))
      | ~ v1_funct_1(D_129)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132)))
      | ~ v1_funct_1(C_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_758,plain,(
    ! [A_131,B_132] :
      ( '#skF_7' = '#skF_6'
      | ~ v1_partfun1('#skF_7',A_131)
      | ~ v1_partfun1('#skF_6',A_131)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_131,B_132)))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_131,B_132)))
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_50,c_756])).

tff(c_761,plain,(
    ! [A_131,B_132] :
      ( '#skF_7' = '#skF_6'
      | ~ v1_partfun1('#skF_7',A_131)
      | ~ v1_partfun1('#skF_6',A_131)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_131,B_132)))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_56,c_758])).

tff(c_2065,plain,(
    ! [A_204,B_205] :
      ( ~ v1_partfun1('#skF_7',A_204)
      | ~ v1_partfun1('#skF_6',A_204)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_204,B_205)))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_204,B_205))) ) ),
    inference(splitLeft,[status(thm)],[c_761])).

tff(c_2071,plain,
    ( ~ v1_partfun1('#skF_7','#skF_4')
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_52,c_2065])).

tff(c_2082,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_526,c_524,c_2071])).

tff(c_2083,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_761])).

tff(c_46,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_2089,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2083,c_46])).

tff(c_2099,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_731,c_2089])).

tff(c_2100,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2143,plain,(
    ! [A_21] :
      ( r2_hidden('#skF_3'(A_21),A_21)
      | A_21 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2100,c_34])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2103,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2100,c_8])).

tff(c_20,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2115,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_4',B_9) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2100,c_2100,c_20])).

tff(c_2101,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2108,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2100,c_2101])).

tff(c_2141,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2115,c_2108,c_52])).

tff(c_2288,plain,(
    ! [C_237,B_238,A_239] :
      ( ~ v1_xboole_0(C_237)
      | ~ m1_subset_1(B_238,k1_zfmisc_1(C_237))
      | ~ r2_hidden(A_239,B_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2294,plain,(
    ! [A_239] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_239,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_2141,c_2288])).

tff(c_2305,plain,(
    ! [A_240] : ~ r2_hidden(A_240,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2103,c_2294])).

tff(c_2315,plain,(
    '#skF_7' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2143,c_2305])).

tff(c_2146,plain,(
    ! [A_213,B_214] :
      ( r1_tarski(A_213,B_214)
      | ~ m1_subset_1(A_213,k1_zfmisc_1(B_214)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2161,plain,(
    r1_tarski('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_2141,c_2146])).

tff(c_2165,plain,(
    ! [B_218,A_219] :
      ( B_218 = A_219
      | ~ r1_tarski(B_218,A_219)
      | ~ r1_tarski(A_219,B_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2175,plain,
    ( '#skF_7' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_7') ),
    inference(resolution,[status(thm)],[c_2161,c_2165])).

tff(c_2181,plain,(
    ~ r1_tarski('#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_2175])).

tff(c_2319,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2315,c_2181])).

tff(c_2326,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2319])).

tff(c_2327,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2175])).

tff(c_2342,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2327,c_2141])).

tff(c_18,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2102,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2100,c_2100,c_18])).

tff(c_24,plain,(
    ! [A_10] : m1_subset_1('#skF_2'(A_10),k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2729,plain,(
    ! [A_295,B_296,C_297,D_298] :
      ( r2_relset_1(A_295,B_296,C_297,C_297)
      | ~ m1_subset_1(D_298,k1_zfmisc_1(k2_zfmisc_1(A_295,B_296)))
      | ~ m1_subset_1(C_297,k1_zfmisc_1(k2_zfmisc_1(A_295,B_296))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3182,plain,(
    ! [A_338,B_339,C_340] :
      ( r2_relset_1(A_338,B_339,C_340,C_340)
      | ~ m1_subset_1(C_340,k1_zfmisc_1(k2_zfmisc_1(A_338,B_339))) ) ),
    inference(resolution,[status(thm)],[c_24,c_2729])).

tff(c_3199,plain,(
    ! [A_343,C_344] :
      ( r2_relset_1(A_343,'#skF_4',C_344,C_344)
      | ~ m1_subset_1(C_344,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2102,c_3182])).

tff(c_3208,plain,(
    ! [A_343] : r2_relset_1(A_343,'#skF_4','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_2342,c_3199])).

tff(c_2142,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2115,c_2108,c_58])).

tff(c_2367,plain,(
    ! [C_246,B_247,A_248] :
      ( ~ v1_xboole_0(C_246)
      | ~ m1_subset_1(B_247,k1_zfmisc_1(C_246))
      | ~ r2_hidden(A_248,B_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2373,plain,(
    ! [A_248] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_248,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2142,c_2367])).

tff(c_2384,plain,(
    ! [A_249] : ~ r2_hidden(A_249,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2103,c_2373])).

tff(c_2394,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2143,c_2384])).

tff(c_2160,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_2142,c_2146])).

tff(c_2176,plain,
    ( '#skF_6' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_2160,c_2165])).

tff(c_2358,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2176])).

tff(c_2397,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2394,c_2358])).

tff(c_2405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2397])).

tff(c_2406,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2176])).

tff(c_2139,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2108,c_46])).

tff(c_2343,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2327,c_2139])).

tff(c_2422,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2406,c_2343])).

tff(c_3214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3208,c_2422])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:14:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.34/2.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.45/2.62  
% 6.45/2.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.45/2.63  %$ r2_relset_1 > v1_funct_2 > v1_subset_1 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_mcart_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 6.45/2.63  
% 6.45/2.63  %Foreground sorts:
% 6.45/2.63  
% 6.45/2.63  
% 6.45/2.63  %Background operators:
% 6.45/2.63  
% 6.45/2.63  
% 6.45/2.63  %Foreground operators:
% 6.45/2.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.45/2.63  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.45/2.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.45/2.63  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.45/2.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.45/2.63  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 6.45/2.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.45/2.63  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 6.45/2.63  tff('#skF_7', type, '#skF_7': $i).
% 6.45/2.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.45/2.63  tff('#skF_5', type, '#skF_5': $i).
% 6.45/2.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.45/2.63  tff('#skF_6', type, '#skF_6': $i).
% 6.45/2.63  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.45/2.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.45/2.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.45/2.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.45/2.63  tff('#skF_4', type, '#skF_4': $i).
% 6.45/2.63  tff('#skF_3', type, '#skF_3': $i > $i).
% 6.45/2.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.45/2.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.45/2.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.45/2.63  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 6.45/2.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.45/2.63  
% 6.45/2.65  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.45/2.65  tff(f_138, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_2)).
% 6.45/2.65  tff(f_68, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 6.45/2.65  tff(f_98, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 6.45/2.65  tff(f_84, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 6.45/2.65  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.45/2.65  tff(f_62, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 6.45/2.65  tff(f_115, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 6.45/2.65  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.45/2.65  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.45/2.65  tff(f_51, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_subset_1)).
% 6.45/2.65  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.45/2.65  tff(c_58, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.45/2.65  tff(c_52, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.45/2.65  tff(c_581, plain, (![A_116, B_117, C_118, D_119]: (r2_relset_1(A_116, B_117, C_118, C_118) | ~m1_subset_1(D_119, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.45/2.65  tff(c_718, plain, (![C_124]: (r2_relset_1('#skF_4', '#skF_5', C_124, C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))))), inference(resolution, [status(thm)], [c_52, c_581])).
% 6.45/2.65  tff(c_731, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_58, c_718])).
% 6.45/2.65  tff(c_48, plain, (k1_xboole_0='#skF_4' | k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.45/2.65  tff(c_72, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_48])).
% 6.45/2.65  tff(c_56, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.45/2.65  tff(c_54, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.45/2.65  tff(c_476, plain, (![C_105, A_106, B_107]: (v1_partfun1(C_105, A_106) | ~v1_funct_2(C_105, A_106, B_107) | ~v1_funct_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))) | v1_xboole_0(B_107))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.45/2.65  tff(c_483, plain, (v1_partfun1('#skF_7', '#skF_4') | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_52, c_476])).
% 6.45/2.65  tff(c_500, plain, (v1_partfun1('#skF_7', '#skF_4') | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_483])).
% 6.45/2.65  tff(c_506, plain, (v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_500])).
% 6.45/2.65  tff(c_34, plain, (![A_21]: (r2_hidden('#skF_3'(A_21), A_21) | k1_xboole_0=A_21)), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.45/2.65  tff(c_28, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.45/2.65  tff(c_153, plain, (![C_68, B_69, A_70]: (~v1_xboole_0(C_68) | ~m1_subset_1(B_69, k1_zfmisc_1(C_68)) | ~r2_hidden(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.45/2.65  tff(c_344, plain, (![B_85, A_86, A_87]: (~v1_xboole_0(B_85) | ~r2_hidden(A_86, A_87) | ~r1_tarski(A_87, B_85))), inference(resolution, [status(thm)], [c_28, c_153])).
% 6.45/2.65  tff(c_358, plain, (![B_92, A_93]: (~v1_xboole_0(B_92) | ~r1_tarski(A_93, B_92) | k1_xboole_0=A_93)), inference(resolution, [status(thm)], [c_34, c_344])).
% 6.45/2.65  tff(c_383, plain, (![B_7]: (~v1_xboole_0(B_7) | k1_xboole_0=B_7)), inference(resolution, [status(thm)], [c_14, c_358])).
% 6.45/2.65  tff(c_514, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_506, c_383])).
% 6.45/2.65  tff(c_523, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_514])).
% 6.45/2.65  tff(c_525, plain, (~v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_500])).
% 6.45/2.65  tff(c_62, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.45/2.65  tff(c_60, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.45/2.65  tff(c_486, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_58, c_476])).
% 6.45/2.65  tff(c_503, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_486])).
% 6.45/2.65  tff(c_526, plain, (v1_partfun1('#skF_6', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_525, c_503])).
% 6.45/2.65  tff(c_524, plain, (v1_partfun1('#skF_7', '#skF_4')), inference(splitRight, [status(thm)], [c_500])).
% 6.45/2.65  tff(c_50, plain, (r1_partfun1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.45/2.65  tff(c_756, plain, (![D_129, C_130, A_131, B_132]: (D_129=C_130 | ~r1_partfun1(C_130, D_129) | ~v1_partfun1(D_129, A_131) | ~v1_partfun1(C_130, A_131) | ~m1_subset_1(D_129, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))) | ~v1_funct_1(D_129) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))) | ~v1_funct_1(C_130))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.45/2.65  tff(c_758, plain, (![A_131, B_132]: ('#skF_7'='#skF_6' | ~v1_partfun1('#skF_7', A_131) | ~v1_partfun1('#skF_6', A_131) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_50, c_756])).
% 6.45/2.65  tff(c_761, plain, (![A_131, B_132]: ('#skF_7'='#skF_6' | ~v1_partfun1('#skF_7', A_131) | ~v1_partfun1('#skF_6', A_131) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_56, c_758])).
% 6.45/2.65  tff(c_2065, plain, (![A_204, B_205]: (~v1_partfun1('#skF_7', A_204) | ~v1_partfun1('#skF_6', A_204) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_204, B_205))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_204, B_205))))), inference(splitLeft, [status(thm)], [c_761])).
% 6.45/2.65  tff(c_2071, plain, (~v1_partfun1('#skF_7', '#skF_4') | ~v1_partfun1('#skF_6', '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_52, c_2065])).
% 6.45/2.65  tff(c_2082, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_526, c_524, c_2071])).
% 6.45/2.65  tff(c_2083, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_761])).
% 6.45/2.65  tff(c_46, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.45/2.65  tff(c_2089, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2083, c_46])).
% 6.45/2.65  tff(c_2099, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_731, c_2089])).
% 6.45/2.65  tff(c_2100, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_48])).
% 6.45/2.65  tff(c_2143, plain, (![A_21]: (r2_hidden('#skF_3'(A_21), A_21) | A_21='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2100, c_34])).
% 6.45/2.65  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.45/2.65  tff(c_2103, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2100, c_8])).
% 6.45/2.65  tff(c_20, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.45/2.65  tff(c_2115, plain, (![B_9]: (k2_zfmisc_1('#skF_4', B_9)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2100, c_2100, c_20])).
% 6.45/2.65  tff(c_2101, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_48])).
% 6.45/2.65  tff(c_2108, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2100, c_2101])).
% 6.45/2.65  tff(c_2141, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2115, c_2108, c_52])).
% 6.45/2.65  tff(c_2288, plain, (![C_237, B_238, A_239]: (~v1_xboole_0(C_237) | ~m1_subset_1(B_238, k1_zfmisc_1(C_237)) | ~r2_hidden(A_239, B_238))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.45/2.65  tff(c_2294, plain, (![A_239]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_239, '#skF_7'))), inference(resolution, [status(thm)], [c_2141, c_2288])).
% 6.45/2.65  tff(c_2305, plain, (![A_240]: (~r2_hidden(A_240, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2103, c_2294])).
% 6.45/2.65  tff(c_2315, plain, ('#skF_7'='#skF_4'), inference(resolution, [status(thm)], [c_2143, c_2305])).
% 6.45/2.65  tff(c_2146, plain, (![A_213, B_214]: (r1_tarski(A_213, B_214) | ~m1_subset_1(A_213, k1_zfmisc_1(B_214)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.45/2.65  tff(c_2161, plain, (r1_tarski('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_2141, c_2146])).
% 6.45/2.65  tff(c_2165, plain, (![B_218, A_219]: (B_218=A_219 | ~r1_tarski(B_218, A_219) | ~r1_tarski(A_219, B_218))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.45/2.65  tff(c_2175, plain, ('#skF_7'='#skF_4' | ~r1_tarski('#skF_4', '#skF_7')), inference(resolution, [status(thm)], [c_2161, c_2165])).
% 6.45/2.65  tff(c_2181, plain, (~r1_tarski('#skF_4', '#skF_7')), inference(splitLeft, [status(thm)], [c_2175])).
% 6.45/2.65  tff(c_2319, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2315, c_2181])).
% 6.45/2.65  tff(c_2326, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_2319])).
% 6.45/2.65  tff(c_2327, plain, ('#skF_7'='#skF_4'), inference(splitRight, [status(thm)], [c_2175])).
% 6.45/2.65  tff(c_2342, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2327, c_2141])).
% 6.45/2.65  tff(c_18, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.45/2.65  tff(c_2102, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2100, c_2100, c_18])).
% 6.45/2.65  tff(c_24, plain, (![A_10]: (m1_subset_1('#skF_2'(A_10), k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.45/2.65  tff(c_2729, plain, (![A_295, B_296, C_297, D_298]: (r2_relset_1(A_295, B_296, C_297, C_297) | ~m1_subset_1(D_298, k1_zfmisc_1(k2_zfmisc_1(A_295, B_296))) | ~m1_subset_1(C_297, k1_zfmisc_1(k2_zfmisc_1(A_295, B_296))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.45/2.65  tff(c_3182, plain, (![A_338, B_339, C_340]: (r2_relset_1(A_338, B_339, C_340, C_340) | ~m1_subset_1(C_340, k1_zfmisc_1(k2_zfmisc_1(A_338, B_339))))), inference(resolution, [status(thm)], [c_24, c_2729])).
% 6.45/2.65  tff(c_3199, plain, (![A_343, C_344]: (r2_relset_1(A_343, '#skF_4', C_344, C_344) | ~m1_subset_1(C_344, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2102, c_3182])).
% 6.45/2.65  tff(c_3208, plain, (![A_343]: (r2_relset_1(A_343, '#skF_4', '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_2342, c_3199])).
% 6.45/2.65  tff(c_2142, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2115, c_2108, c_58])).
% 6.45/2.65  tff(c_2367, plain, (![C_246, B_247, A_248]: (~v1_xboole_0(C_246) | ~m1_subset_1(B_247, k1_zfmisc_1(C_246)) | ~r2_hidden(A_248, B_247))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.45/2.65  tff(c_2373, plain, (![A_248]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_248, '#skF_6'))), inference(resolution, [status(thm)], [c_2142, c_2367])).
% 6.45/2.65  tff(c_2384, plain, (![A_249]: (~r2_hidden(A_249, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2103, c_2373])).
% 6.45/2.65  tff(c_2394, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_2143, c_2384])).
% 6.45/2.65  tff(c_2160, plain, (r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_2142, c_2146])).
% 6.45/2.65  tff(c_2176, plain, ('#skF_6'='#skF_4' | ~r1_tarski('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_2160, c_2165])).
% 6.45/2.65  tff(c_2358, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_2176])).
% 6.45/2.65  tff(c_2397, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2394, c_2358])).
% 6.45/2.65  tff(c_2405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_2397])).
% 6.45/2.65  tff(c_2406, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_2176])).
% 6.45/2.65  tff(c_2139, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2108, c_46])).
% 6.45/2.65  tff(c_2343, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2327, c_2139])).
% 6.45/2.65  tff(c_2422, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2406, c_2343])).
% 6.45/2.65  tff(c_3214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3208, c_2422])).
% 6.45/2.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.45/2.65  
% 6.45/2.65  Inference rules
% 6.45/2.65  ----------------------
% 6.45/2.65  #Ref     : 0
% 6.45/2.65  #Sup     : 756
% 6.45/2.65  #Fact    : 0
% 6.45/2.65  #Define  : 0
% 6.45/2.65  #Split   : 9
% 6.45/2.65  #Chain   : 0
% 6.45/2.65  #Close   : 0
% 6.45/2.65  
% 6.45/2.65  Ordering : KBO
% 6.45/2.65  
% 6.45/2.65  Simplification rules
% 6.45/2.65  ----------------------
% 6.45/2.65  #Subsume      : 271
% 6.45/2.66  #Demod        : 427
% 6.45/2.66  #Tautology    : 224
% 6.45/2.66  #SimpNegUnit  : 2
% 6.45/2.66  #BackRed      : 54
% 6.45/2.66  
% 6.45/2.66  #Partial instantiations: 0
% 6.45/2.66  #Strategies tried      : 1
% 6.45/2.66  
% 6.45/2.66  Timing (in seconds)
% 6.45/2.66  ----------------------
% 6.45/2.66  Preprocessing        : 0.52
% 6.45/2.66  Parsing              : 0.27
% 6.45/2.66  CNF conversion       : 0.04
% 6.45/2.66  Main loop            : 1.22
% 6.45/2.66  Inferencing          : 0.42
% 6.45/2.66  Reduction            : 0.39
% 6.45/2.66  Demodulation         : 0.28
% 6.45/2.66  BG Simplification    : 0.05
% 6.45/2.66  Subsumption          : 0.26
% 6.45/2.66  Abstraction          : 0.05
% 6.45/2.66  MUC search           : 0.00
% 6.45/2.66  Cooper               : 0.00
% 6.45/2.66  Total                : 1.80
% 6.45/2.66  Index Insertion      : 0.00
% 6.45/2.66  Index Deletion       : 0.00
% 6.45/2.66  Index Matching       : 0.00
% 6.45/2.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
