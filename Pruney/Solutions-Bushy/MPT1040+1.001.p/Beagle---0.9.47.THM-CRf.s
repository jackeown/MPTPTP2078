%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1040+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:18 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 211 expanded)
%              Number of leaves         :   27 (  81 expanded)
%              Depth                    :   11
%              Number of atoms          :  148 ( 733 expanded)
%              Number of equality atoms :   13 ( 182 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_hidden(D,k5_partfun1(A,B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( D = k5_partfun1(A,B,C)
        <=> ! [E] :
              ( r2_hidden(E,D)
            <=> ? [F] :
                  ( v1_funct_1(F)
                  & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(A,B)))
                  & F = E
                  & v1_partfun1(F,A)
                  & r1_partfun1(C,F) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_partfun1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(c_46,plain,(
    ~ r2_hidden('#skF_8',k5_partfun1('#skF_5','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_60,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_50,plain,(
    r1_partfun1('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_58,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_56,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_48,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_54,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_52,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_73,plain,(
    ! [C_57,A_58,B_59] :
      ( v1_partfun1(C_57,A_58)
      | ~ v1_funct_2(C_57,A_58,B_59)
      | ~ v1_funct_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59)))
      | v1_xboole_0(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_76,plain,
    ( v1_partfun1('#skF_8','#skF_5')
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_8')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_73])).

tff(c_82,plain,
    ( v1_partfun1('#skF_8','#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_76])).

tff(c_87,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_44,plain,(
    ! [A_51] :
      ( k1_xboole_0 = A_51
      | ~ v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_90,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_87,c_44])).

tff(c_94,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_90])).

tff(c_95,plain,(
    v1_partfun1('#skF_8','#skF_5') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_226,plain,(
    ! [F_105,A_106,B_107,C_108] :
      ( r2_hidden(F_105,k5_partfun1(A_106,B_107,C_108))
      | ~ r1_partfun1(C_108,F_105)
      | ~ v1_partfun1(F_105,A_106)
      | ~ m1_subset_1(F_105,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107)))
      | ~ v1_funct_1(F_105)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107)))
      | ~ v1_funct_1(C_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_228,plain,(
    ! [C_108] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_5','#skF_6',C_108))
      | ~ r1_partfun1(C_108,'#skF_8')
      | ~ v1_partfun1('#skF_8','#skF_5')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ v1_funct_1(C_108) ) ),
    inference(resolution,[status(thm)],[c_52,c_226])).

tff(c_237,plain,(
    ! [C_109] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_5','#skF_6',C_109))
      | ~ r1_partfun1(C_109,'#skF_8')
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ v1_funct_1(C_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_95,c_228])).

tff(c_243,plain,
    ( r2_hidden('#skF_8',k5_partfun1('#skF_5','#skF_6','#skF_7'))
    | ~ r1_partfun1('#skF_7','#skF_8')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_237])).

tff(c_249,plain,(
    r2_hidden('#skF_8',k5_partfun1('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_243])).

tff(c_251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_249])).

tff(c_253,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_252,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_259,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_252])).

tff(c_271,plain,(
    ~ r2_hidden('#skF_8',k5_partfun1('#skF_6','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_46])).

tff(c_272,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_58])).

tff(c_273,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_52])).

tff(c_274,plain,(
    ! [C_111,A_112,B_113] :
      ( v1_partfun1(C_111,A_112)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113)))
      | ~ v1_xboole_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_281,plain,
    ( v1_partfun1('#skF_8','#skF_6')
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_273,c_274])).

tff(c_283,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_281])).

tff(c_264,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_54])).

tff(c_284,plain,(
    ! [C_114,A_115,B_116] :
      ( v1_partfun1(C_114,A_115)
      | ~ v1_funct_2(C_114,A_115,B_116)
      | ~ v1_funct_1(C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116)))
      | v1_xboole_0(B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_287,plain,
    ( v1_partfun1('#skF_8','#skF_6')
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_6')
    | ~ v1_funct_1('#skF_8')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_273,c_284])).

tff(c_293,plain,
    ( v1_partfun1('#skF_8','#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_264,c_287])).

tff(c_294,plain,(
    v1_partfun1('#skF_8','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_283,c_293])).

tff(c_424,plain,(
    ! [F_163,A_164,B_165,C_166] :
      ( r2_hidden(F_163,k5_partfun1(A_164,B_165,C_166))
      | ~ r1_partfun1(C_166,F_163)
      | ~ v1_partfun1(F_163,A_164)
      | ~ m1_subset_1(F_163,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165)))
      | ~ v1_funct_1(F_163)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165)))
      | ~ v1_funct_1(C_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_428,plain,(
    ! [C_166] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_6','#skF_6',C_166))
      | ~ r1_partfun1(C_166,'#skF_8')
      | ~ v1_partfun1('#skF_8','#skF_6')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6')))
      | ~ v1_funct_1(C_166) ) ),
    inference(resolution,[status(thm)],[c_273,c_424])).

tff(c_438,plain,(
    ! [C_167] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_6','#skF_6',C_167))
      | ~ r1_partfun1(C_167,'#skF_8')
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6')))
      | ~ v1_funct_1(C_167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_294,c_428])).

tff(c_448,plain,
    ( r2_hidden('#skF_8',k5_partfun1('#skF_6','#skF_6','#skF_7'))
    | ~ r1_partfun1('#skF_7','#skF_8')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_272,c_438])).

tff(c_455,plain,(
    r2_hidden('#skF_8',k5_partfun1('#skF_6','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_448])).

tff(c_457,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_271,c_455])).

tff(c_458,plain,(
    v1_partfun1('#skF_8','#skF_6') ),
    inference(splitRight,[status(thm)],[c_281])).

tff(c_644,plain,(
    ! [F_220,A_221,B_222,C_223] :
      ( r2_hidden(F_220,k5_partfun1(A_221,B_222,C_223))
      | ~ r1_partfun1(C_223,F_220)
      | ~ v1_partfun1(F_220,A_221)
      | ~ m1_subset_1(F_220,k1_zfmisc_1(k2_zfmisc_1(A_221,B_222)))
      | ~ v1_funct_1(F_220)
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1(A_221,B_222)))
      | ~ v1_funct_1(C_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_648,plain,(
    ! [C_223] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_6','#skF_6',C_223))
      | ~ r1_partfun1(C_223,'#skF_8')
      | ~ v1_partfun1('#skF_8','#skF_6')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6')))
      | ~ v1_funct_1(C_223) ) ),
    inference(resolution,[status(thm)],[c_273,c_644])).

tff(c_658,plain,(
    ! [C_224] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_6','#skF_6',C_224))
      | ~ r1_partfun1(C_224,'#skF_8')
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6')))
      | ~ v1_funct_1(C_224) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_458,c_648])).

tff(c_668,plain,
    ( r2_hidden('#skF_8',k5_partfun1('#skF_6','#skF_6','#skF_7'))
    | ~ r1_partfun1('#skF_7','#skF_8')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_272,c_658])).

tff(c_675,plain,(
    r2_hidden('#skF_8',k5_partfun1('#skF_6','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_668])).

tff(c_677,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_271,c_675])).

%------------------------------------------------------------------------------
