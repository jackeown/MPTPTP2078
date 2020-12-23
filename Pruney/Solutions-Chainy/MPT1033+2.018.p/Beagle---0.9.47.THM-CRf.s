%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:53 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 403 expanded)
%              Number of leaves         :   31 ( 144 expanded)
%              Depth                    :   14
%              Number of atoms          :  183 (1081 expanded)
%              Number of equality atoms :   20 ( 149 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_116,negated_conjecture,(
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

tff(f_40,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_93,axiom,(
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

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_14,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_16,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_47,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_126,plain,(
    ! [A_57,B_58,C_59,D_60] :
      ( r2_relset_1(A_57,B_58,C_59,C_59)
      | ~ m1_subset_1(D_60,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58)))
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_152,plain,(
    ! [A_70,B_71,C_72] :
      ( r2_relset_1(A_70,B_71,C_72,C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(resolution,[status(thm)],[c_47,c_126])).

tff(c_160,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_152])).

tff(c_111,plain,(
    ! [C_54,B_55,A_56] :
      ( v1_xboole_0(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(B_55,A_56)))
      | ~ v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_122,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_111])).

tff(c_125,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_44,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_163,plain,(
    ! [C_73,A_74,B_75] :
      ( v1_partfun1(C_73,A_74)
      | ~ v1_funct_2(C_73,A_74,B_75)
      | ~ v1_funct_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75)))
      | v1_xboole_0(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_166,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_163])).

tff(c_176,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_166])).

tff(c_177,plain,(
    v1_partfun1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_176])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_38,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_169,plain,
    ( v1_partfun1('#skF_5','#skF_2')
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_163])).

tff(c_180,plain,
    ( v1_partfun1('#skF_5','#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_169])).

tff(c_181,plain,(
    v1_partfun1('#skF_5','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_180])).

tff(c_34,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_208,plain,(
    ! [D_89,C_90,A_91,B_92] :
      ( D_89 = C_90
      | ~ r1_partfun1(C_90,D_89)
      | ~ v1_partfun1(D_89,A_91)
      | ~ v1_partfun1(C_90,A_91)
      | ~ m1_subset_1(D_89,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | ~ v1_funct_1(D_89)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | ~ v1_funct_1(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_210,plain,(
    ! [A_91,B_92] :
      ( '#skF_5' = '#skF_4'
      | ~ v1_partfun1('#skF_5',A_91)
      | ~ v1_partfun1('#skF_4',A_91)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_208])).

tff(c_213,plain,(
    ! [A_91,B_92] :
      ( '#skF_5' = '#skF_4'
      | ~ v1_partfun1('#skF_5',A_91)
      | ~ v1_partfun1('#skF_4',A_91)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_210])).

tff(c_342,plain,(
    ! [A_111,B_112] :
      ( ~ v1_partfun1('#skF_5',A_111)
      | ~ v1_partfun1('#skF_4',A_111)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_111,B_112)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(splitLeft,[status(thm)],[c_213])).

tff(c_345,plain,
    ( ~ v1_partfun1('#skF_5','#skF_2')
    | ~ v1_partfun1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_36,c_342])).

tff(c_349,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_177,c_181,c_345])).

tff(c_350,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_30,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_354,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_30])).

tff(c_363,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_354])).

tff(c_364,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_459,plain,(
    ! [B_122,A_123] :
      ( v1_xboole_0(k2_zfmisc_1(B_122,A_123))
      | ~ v1_xboole_0(A_123) ) ),
    inference(resolution,[status(thm)],[c_47,c_111])).

tff(c_365,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_76,plain,(
    ! [C_40,B_41,A_42] :
      ( ~ v1_xboole_0(C_40)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(C_40))
      | ~ r2_hidden(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_86,plain,(
    ! [A_43,A_44] :
      ( ~ v1_xboole_0(A_43)
      | ~ r2_hidden(A_44,A_43) ) ),
    inference(resolution,[status(thm)],[c_47,c_76])).

tff(c_90,plain,(
    ! [A_1,B_2] :
      ( ~ v1_xboole_0(A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_86])).

tff(c_91,plain,(
    ! [A_45,B_46] :
      ( ~ v1_xboole_0(A_45)
      | r1_tarski(A_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_6,c_86])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_96,plain,(
    ! [B_47,A_48] :
      ( B_47 = A_48
      | ~ r1_tarski(B_47,A_48)
      | ~ v1_xboole_0(A_48) ) ),
    inference(resolution,[status(thm)],[c_91,c_8])).

tff(c_103,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ v1_xboole_0(B_2)
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_90,c_96])).

tff(c_402,plain,(
    ! [A_116] :
      ( A_116 = '#skF_3'
      | ~ v1_xboole_0(A_116) ) ),
    inference(resolution,[status(thm)],[c_365,c_103])).

tff(c_415,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_364,c_402])).

tff(c_83,plain,(
    ! [A_42] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_42,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_76])).

tff(c_95,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_430,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_95])).

tff(c_462,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_459,c_430])).

tff(c_471,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_462])).

tff(c_473,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_474,plain,(
    ! [A_124] : ~ r2_hidden(A_124,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_480,plain,(
    ! [B_125] : r1_tarski('#skF_4',B_125) ),
    inference(resolution,[status(thm)],[c_6,c_474])).

tff(c_488,plain,(
    ! [B_129] :
      ( B_129 = '#skF_4'
      | ~ r1_tarski(B_129,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_480,c_8])).

tff(c_506,plain,(
    ! [A_130] :
      ( A_130 = '#skF_4'
      | ~ v1_xboole_0(A_130) ) ),
    inference(resolution,[status(thm)],[c_90,c_488])).

tff(c_510,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_473,c_506])).

tff(c_511,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_473])).

tff(c_513,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_36])).

tff(c_18,plain,(
    ! [C_12,B_11,A_10] :
      ( ~ v1_xboole_0(C_12)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(C_12))
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_521,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_10,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_513,c_18])).

tff(c_529,plain,(
    ! [A_131] : ~ r2_hidden(A_131,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_511,c_521])).

tff(c_535,plain,(
    ! [B_132] : r1_tarski('#skF_5',B_132) ),
    inference(resolution,[status(thm)],[c_6,c_529])).

tff(c_483,plain,(
    ! [B_125] :
      ( B_125 = '#skF_4'
      | ~ r1_tarski(B_125,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_480,c_8])).

tff(c_542,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_535,c_483])).

tff(c_547,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_30])).

tff(c_751,plain,(
    ! [A_166,B_167,C_168,D_169] :
      ( r2_relset_1(A_166,B_167,C_168,C_168)
      | ~ m1_subset_1(D_169,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167)))
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_757,plain,(
    ! [C_168,D_169] :
      ( r2_relset_1('#skF_2','#skF_3',C_168,C_168)
      | ~ m1_subset_1(D_169,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_751])).

tff(c_761,plain,(
    ! [C_168,D_169] :
      ( r2_relset_1('#skF_2','#skF_3',C_168,C_168)
      | ~ m1_subset_1(D_169,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(C_168,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_757])).

tff(c_808,plain,(
    ! [D_178] : ~ m1_subset_1(D_178,k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_761])).

tff(c_813,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_47,c_808])).

tff(c_815,plain,(
    ! [C_179] :
      ( r2_relset_1('#skF_2','#skF_3',C_179,C_179)
      | ~ m1_subset_1(C_179,k1_zfmisc_1('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_761])).

tff(c_818,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_47,c_815])).

tff(c_822,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_547,c_818])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n011.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 11:05:42 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.50  
% 2.91/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.50  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.91/1.50  
% 2.91/1.50  %Foreground sorts:
% 2.91/1.50  
% 2.91/1.50  
% 2.91/1.50  %Background operators:
% 2.91/1.50  
% 2.91/1.50  
% 2.91/1.50  %Foreground operators:
% 2.91/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.91/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.50  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.91/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.91/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.91/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.91/1.50  tff('#skF_5', type, '#skF_5': $i).
% 2.91/1.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.91/1.50  tff('#skF_2', type, '#skF_2': $i).
% 2.91/1.50  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.91/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.91/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.91/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.91/1.50  tff('#skF_4', type, '#skF_4': $i).
% 2.91/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.91/1.50  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.91/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.91/1.50  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.91/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.91/1.50  
% 3.12/1.52  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.12/1.52  tff(f_116, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_2)).
% 3.12/1.52  tff(f_40, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.12/1.52  tff(f_42, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.12/1.52  tff(f_62, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 3.12/1.52  tff(f_56, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 3.12/1.52  tff(f_76, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.12/1.52  tff(f_93, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_partfun1)).
% 3.12/1.52  tff(f_49, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.12/1.52  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.12/1.52  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.12/1.52  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.12/1.52  tff(c_14, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.12/1.52  tff(c_16, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.12/1.52  tff(c_47, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 3.12/1.52  tff(c_126, plain, (![A_57, B_58, C_59, D_60]: (r2_relset_1(A_57, B_58, C_59, C_59) | ~m1_subset_1(D_60, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.12/1.52  tff(c_152, plain, (![A_70, B_71, C_72]: (r2_relset_1(A_70, B_71, C_72, C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(resolution, [status(thm)], [c_47, c_126])).
% 3.12/1.52  tff(c_160, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_152])).
% 3.12/1.52  tff(c_111, plain, (![C_54, B_55, A_56]: (v1_xboole_0(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(B_55, A_56))) | ~v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.12/1.52  tff(c_122, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_111])).
% 3.12/1.52  tff(c_125, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_122])).
% 3.12/1.52  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.12/1.52  tff(c_44, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.12/1.52  tff(c_163, plain, (![C_73, A_74, B_75]: (v1_partfun1(C_73, A_74) | ~v1_funct_2(C_73, A_74, B_75) | ~v1_funct_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))) | v1_xboole_0(B_75))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.12/1.52  tff(c_166, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_163])).
% 3.12/1.52  tff(c_176, plain, (v1_partfun1('#skF_4', '#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_166])).
% 3.12/1.52  tff(c_177, plain, (v1_partfun1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_125, c_176])).
% 3.12/1.52  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.12/1.52  tff(c_38, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.12/1.52  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.12/1.52  tff(c_169, plain, (v1_partfun1('#skF_5', '#skF_2') | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_163])).
% 3.12/1.52  tff(c_180, plain, (v1_partfun1('#skF_5', '#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_169])).
% 3.12/1.52  tff(c_181, plain, (v1_partfun1('#skF_5', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_125, c_180])).
% 3.12/1.52  tff(c_34, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.12/1.52  tff(c_208, plain, (![D_89, C_90, A_91, B_92]: (D_89=C_90 | ~r1_partfun1(C_90, D_89) | ~v1_partfun1(D_89, A_91) | ~v1_partfun1(C_90, A_91) | ~m1_subset_1(D_89, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | ~v1_funct_1(D_89) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | ~v1_funct_1(C_90))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.12/1.52  tff(c_210, plain, (![A_91, B_92]: ('#skF_5'='#skF_4' | ~v1_partfun1('#skF_5', A_91) | ~v1_partfun1('#skF_4', A_91) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_208])).
% 3.12/1.52  tff(c_213, plain, (![A_91, B_92]: ('#skF_5'='#skF_4' | ~v1_partfun1('#skF_5', A_91) | ~v1_partfun1('#skF_4', A_91) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_210])).
% 3.12/1.52  tff(c_342, plain, (![A_111, B_112]: (~v1_partfun1('#skF_5', A_111) | ~v1_partfun1('#skF_4', A_111) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(splitLeft, [status(thm)], [c_213])).
% 3.12/1.52  tff(c_345, plain, (~v1_partfun1('#skF_5', '#skF_2') | ~v1_partfun1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_36, c_342])).
% 3.12/1.52  tff(c_349, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_177, c_181, c_345])).
% 3.12/1.52  tff(c_350, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_213])).
% 3.12/1.52  tff(c_30, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.12/1.52  tff(c_354, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_350, c_30])).
% 3.12/1.52  tff(c_363, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_160, c_354])).
% 3.12/1.52  tff(c_364, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_122])).
% 3.12/1.52  tff(c_459, plain, (![B_122, A_123]: (v1_xboole_0(k2_zfmisc_1(B_122, A_123)) | ~v1_xboole_0(A_123))), inference(resolution, [status(thm)], [c_47, c_111])).
% 3.12/1.52  tff(c_365, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_122])).
% 3.12/1.52  tff(c_76, plain, (![C_40, B_41, A_42]: (~v1_xboole_0(C_40) | ~m1_subset_1(B_41, k1_zfmisc_1(C_40)) | ~r2_hidden(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.12/1.52  tff(c_86, plain, (![A_43, A_44]: (~v1_xboole_0(A_43) | ~r2_hidden(A_44, A_43))), inference(resolution, [status(thm)], [c_47, c_76])).
% 3.12/1.52  tff(c_90, plain, (![A_1, B_2]: (~v1_xboole_0(A_1) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_86])).
% 3.12/1.52  tff(c_91, plain, (![A_45, B_46]: (~v1_xboole_0(A_45) | r1_tarski(A_45, B_46))), inference(resolution, [status(thm)], [c_6, c_86])).
% 3.12/1.52  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.12/1.52  tff(c_96, plain, (![B_47, A_48]: (B_47=A_48 | ~r1_tarski(B_47, A_48) | ~v1_xboole_0(A_48))), inference(resolution, [status(thm)], [c_91, c_8])).
% 3.12/1.52  tff(c_103, plain, (![B_2, A_1]: (B_2=A_1 | ~v1_xboole_0(B_2) | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_90, c_96])).
% 3.12/1.52  tff(c_402, plain, (![A_116]: (A_116='#skF_3' | ~v1_xboole_0(A_116))), inference(resolution, [status(thm)], [c_365, c_103])).
% 3.12/1.52  tff(c_415, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_364, c_402])).
% 3.12/1.52  tff(c_83, plain, (![A_42]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_42, '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_76])).
% 3.12/1.52  tff(c_95, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_83])).
% 3.12/1.52  tff(c_430, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_415, c_95])).
% 3.12/1.52  tff(c_462, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_459, c_430])).
% 3.12/1.52  tff(c_471, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_364, c_462])).
% 3.12/1.52  tff(c_473, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_83])).
% 3.12/1.52  tff(c_474, plain, (![A_124]: (~r2_hidden(A_124, '#skF_4'))), inference(splitRight, [status(thm)], [c_83])).
% 3.12/1.52  tff(c_480, plain, (![B_125]: (r1_tarski('#skF_4', B_125))), inference(resolution, [status(thm)], [c_6, c_474])).
% 3.12/1.52  tff(c_488, plain, (![B_129]: (B_129='#skF_4' | ~r1_tarski(B_129, '#skF_4'))), inference(resolution, [status(thm)], [c_480, c_8])).
% 3.12/1.52  tff(c_506, plain, (![A_130]: (A_130='#skF_4' | ~v1_xboole_0(A_130))), inference(resolution, [status(thm)], [c_90, c_488])).
% 3.12/1.52  tff(c_510, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_473, c_506])).
% 3.12/1.52  tff(c_511, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_510, c_473])).
% 3.12/1.52  tff(c_513, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_510, c_36])).
% 3.12/1.52  tff(c_18, plain, (![C_12, B_11, A_10]: (~v1_xboole_0(C_12) | ~m1_subset_1(B_11, k1_zfmisc_1(C_12)) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.12/1.52  tff(c_521, plain, (![A_10]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_10, '#skF_5'))), inference(resolution, [status(thm)], [c_513, c_18])).
% 3.12/1.52  tff(c_529, plain, (![A_131]: (~r2_hidden(A_131, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_511, c_521])).
% 3.12/1.52  tff(c_535, plain, (![B_132]: (r1_tarski('#skF_5', B_132))), inference(resolution, [status(thm)], [c_6, c_529])).
% 3.12/1.52  tff(c_483, plain, (![B_125]: (B_125='#skF_4' | ~r1_tarski(B_125, '#skF_4'))), inference(resolution, [status(thm)], [c_480, c_8])).
% 3.12/1.52  tff(c_542, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_535, c_483])).
% 3.12/1.52  tff(c_547, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_542, c_30])).
% 3.12/1.52  tff(c_751, plain, (![A_166, B_167, C_168, D_169]: (r2_relset_1(A_166, B_167, C_168, C_168) | ~m1_subset_1(D_169, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.12/1.52  tff(c_757, plain, (![C_168, D_169]: (r2_relset_1('#skF_2', '#skF_3', C_168, C_168) | ~m1_subset_1(D_169, k1_zfmisc_1('#skF_4')) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_510, c_751])).
% 3.12/1.52  tff(c_761, plain, (![C_168, D_169]: (r2_relset_1('#skF_2', '#skF_3', C_168, C_168) | ~m1_subset_1(D_169, k1_zfmisc_1('#skF_4')) | ~m1_subset_1(C_168, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_510, c_757])).
% 3.12/1.52  tff(c_808, plain, (![D_178]: (~m1_subset_1(D_178, k1_zfmisc_1('#skF_4')))), inference(splitLeft, [status(thm)], [c_761])).
% 3.12/1.52  tff(c_813, plain, $false, inference(resolution, [status(thm)], [c_47, c_808])).
% 3.12/1.52  tff(c_815, plain, (![C_179]: (r2_relset_1('#skF_2', '#skF_3', C_179, C_179) | ~m1_subset_1(C_179, k1_zfmisc_1('#skF_4')))), inference(splitRight, [status(thm)], [c_761])).
% 3.12/1.52  tff(c_818, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_47, c_815])).
% 3.12/1.52  tff(c_822, plain, $false, inference(negUnitSimplification, [status(thm)], [c_547, c_818])).
% 3.12/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.52  
% 3.12/1.52  Inference rules
% 3.12/1.52  ----------------------
% 3.12/1.52  #Ref     : 0
% 3.12/1.52  #Sup     : 168
% 3.12/1.52  #Fact    : 0
% 3.12/1.52  #Define  : 0
% 3.12/1.52  #Split   : 9
% 3.12/1.52  #Chain   : 0
% 3.12/1.52  #Close   : 0
% 3.12/1.52  
% 3.12/1.52  Ordering : KBO
% 3.12/1.52  
% 3.12/1.52  Simplification rules
% 3.12/1.52  ----------------------
% 3.12/1.52  #Subsume      : 58
% 3.12/1.52  #Demod        : 116
% 3.12/1.52  #Tautology    : 63
% 3.12/1.52  #SimpNegUnit  : 8
% 3.12/1.52  #BackRed      : 37
% 3.12/1.52  
% 3.12/1.52  #Partial instantiations: 0
% 3.12/1.52  #Strategies tried      : 1
% 3.12/1.52  
% 3.12/1.52  Timing (in seconds)
% 3.12/1.52  ----------------------
% 3.12/1.52  Preprocessing        : 0.37
% 3.12/1.52  Parsing              : 0.21
% 3.12/1.52  CNF conversion       : 0.03
% 3.12/1.52  Main loop            : 0.36
% 3.12/1.52  Inferencing          : 0.13
% 3.12/1.52  Reduction            : 0.10
% 3.12/1.52  Demodulation         : 0.07
% 3.12/1.52  BG Simplification    : 0.02
% 3.12/1.52  Subsumption          : 0.08
% 3.12/1.52  Abstraction          : 0.01
% 3.12/1.53  MUC search           : 0.00
% 3.12/1.53  Cooper               : 0.00
% 3.12/1.53  Total                : 0.76
% 3.12/1.53  Index Insertion      : 0.00
% 3.12/1.53  Index Deletion       : 0.00
% 3.12/1.53  Index Matching       : 0.00
% 3.12/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
