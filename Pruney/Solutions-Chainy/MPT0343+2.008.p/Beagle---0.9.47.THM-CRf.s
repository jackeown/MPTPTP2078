%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:18 EST 2020

% Result     : Theorem 8.16s
% Output     : CNFRefutation 8.53s
% Verified   : 
% Statistics : Number of formulae       :  278 (1710 expanded)
%              Number of leaves         :   24 ( 532 expanded)
%              Depth                    :   18
%              Number of atoms          :  524 (4713 expanded)
%              Number of equality atoms :   26 ( 254 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_8 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ! [D] :
                  ( m1_subset_1(D,A)
                 => ( r2_hidden(D,B)
                  <=> r2_hidden(D,C) ) )
             => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(c_11904,plain,(
    ! [A_944,B_945] :
      ( r2_hidden('#skF_2'(A_944,B_945),A_944)
      | r1_tarski(A_944,B_945) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_11919,plain,(
    ! [A_946,B_947] :
      ( ~ v1_xboole_0(A_946)
      | r1_tarski(A_946,B_947) ) ),
    inference(resolution,[status(thm)],[c_11904,c_2])).

tff(c_42,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_38,plain,(
    ! [B_21,A_20] :
      ( m1_subset_1(B_21,A_20)
      | ~ v1_xboole_0(B_21)
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r2_xboole_0(A_10,B_11)
      | B_11 = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_151,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_3'(A_54,B_55),B_55)
      | ~ r2_xboole_0(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_50,plain,(
    ! [D_26] :
      ( r2_hidden(D_26,'#skF_8')
      | ~ r2_hidden(D_26,'#skF_7')
      | ~ m1_subset_1(D_26,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3060,plain,(
    ! [A_283] :
      ( r2_hidden('#skF_3'(A_283,'#skF_7'),'#skF_8')
      | ~ m1_subset_1('#skF_3'(A_283,'#skF_7'),'#skF_6')
      | ~ r2_xboole_0(A_283,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_151,c_50])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( ~ r2_hidden('#skF_3'(A_12,B_13),A_12)
      | ~ r2_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3086,plain,
    ( ~ m1_subset_1('#skF_3'('#skF_8','#skF_7'),'#skF_6')
    | ~ r2_xboole_0('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_3060,c_18])).

tff(c_3091,plain,(
    ~ r2_xboole_0('#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_3086])).

tff(c_3094,plain,
    ( '#skF_7' = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_12,c_3091])).

tff(c_3097,plain,(
    ~ r1_tarski('#skF_8','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_3094])).

tff(c_123,plain,(
    ! [D_50] :
      ( r2_hidden(D_50,'#skF_7')
      | ~ r2_hidden(D_50,'#skF_8')
      | ~ m1_subset_1(D_50,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_136,plain,(
    ! [D_50] :
      ( ~ v1_xboole_0('#skF_7')
      | ~ r2_hidden(D_50,'#skF_8')
      | ~ m1_subset_1(D_50,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_123,c_2])).

tff(c_224,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_225,plain,(
    ! [B_67,A_68] :
      ( r2_hidden(B_67,A_68)
      | ~ m1_subset_1(B_67,A_68)
      | v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_244,plain,(
    ! [B_67] :
      ( r2_hidden(B_67,'#skF_8')
      | ~ m1_subset_1(B_67,'#skF_6')
      | ~ m1_subset_1(B_67,'#skF_7')
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_225,c_50])).

tff(c_345,plain,(
    ! [B_79] :
      ( r2_hidden(B_79,'#skF_8')
      | ~ m1_subset_1(B_79,'#skF_6')
      | ~ m1_subset_1(B_79,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_244])).

tff(c_366,plain,(
    ! [B_79] :
      ( ~ v1_xboole_0('#skF_8')
      | ~ m1_subset_1(B_79,'#skF_6')
      | ~ m1_subset_1(B_79,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_345,c_2])).

tff(c_367,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_366])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_181,plain,(
    ! [B_60,A_61] :
      ( m1_subset_1(B_60,A_61)
      | ~ r2_hidden(B_60,A_61)
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_199,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1('#skF_2'(A_5,B_6),A_5)
      | v1_xboole_0(A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_181])).

tff(c_69,plain,(
    ! [D_35] :
      ( r2_hidden(D_35,'#skF_8')
      | ~ r2_hidden(D_35,'#skF_7')
      | ~ m1_subset_1(D_35,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_74,plain,
    ( r2_hidden('#skF_1'('#skF_7'),'#skF_8')
    | ~ m1_subset_1('#skF_1'('#skF_7'),'#skF_6')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_4,c_69])).

tff(c_368,plain,
    ( r2_hidden('#skF_1'('#skF_7'),'#skF_8')
    | ~ m1_subset_1('#skF_1'('#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_74])).

tff(c_369,plain,(
    ~ m1_subset_1('#skF_1'('#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_368])).

tff(c_201,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_181])).

tff(c_373,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_7'))
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_369])).

tff(c_374,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_373])).

tff(c_44,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_59,plain,(
    ! [B_33,A_34] :
      ( v1_xboole_0(B_33)
      | ~ m1_subset_1(B_33,A_34)
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_66,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_44,c_59])).

tff(c_68,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_22,plain,(
    ! [C_19,A_15] :
      ( r1_tarski(C_19,A_15)
      | ~ r2_hidden(C_19,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_636,plain,(
    ! [B_109,A_110] :
      ( r1_tarski(B_109,A_110)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(A_110))
      | v1_xboole_0(k1_zfmisc_1(A_110)) ) ),
    inference(resolution,[status(thm)],[c_225,c_22])).

tff(c_657,plain,
    ( r1_tarski('#skF_7','#skF_6')
    | v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_46,c_636])).

tff(c_668,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_657])).

tff(c_36,plain,(
    ! [B_21,A_20] :
      ( r2_hidden(B_21,A_20)
      | ~ m1_subset_1(B_21,A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_261,plain,(
    ! [C_70,B_71,A_72] :
      ( r2_hidden(C_70,B_71)
      | ~ r2_hidden(C_70,A_72)
      | ~ r1_tarski(A_72,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1130,plain,(
    ! [B_152,B_153,A_154] :
      ( r2_hidden(B_152,B_153)
      | ~ r1_tarski(A_154,B_153)
      | ~ m1_subset_1(B_152,A_154)
      | v1_xboole_0(A_154) ) ),
    inference(resolution,[status(thm)],[c_36,c_261])).

tff(c_1140,plain,(
    ! [B_152] :
      ( r2_hidden(B_152,'#skF_6')
      | ~ m1_subset_1(B_152,'#skF_7')
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_668,c_1130])).

tff(c_1168,plain,(
    ! [B_155] :
      ( r2_hidden(B_155,'#skF_6')
      | ~ m1_subset_1(B_155,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_1140])).

tff(c_34,plain,(
    ! [B_21,A_20] :
      ( m1_subset_1(B_21,A_20)
      | ~ r2_hidden(B_21,A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1180,plain,(
    ! [B_155] :
      ( m1_subset_1(B_155,'#skF_6')
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(B_155,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1168,c_34])).

tff(c_1224,plain,(
    ! [B_157] :
      ( m1_subset_1(B_157,'#skF_6')
      | ~ m1_subset_1(B_157,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_374,c_1180])).

tff(c_1239,plain,
    ( m1_subset_1('#skF_1'('#skF_7'),'#skF_6')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_201,c_1224])).

tff(c_1254,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_369,c_1239])).

tff(c_1256,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_373])).

tff(c_1614,plain,(
    ! [B_179,A_180] :
      ( r1_tarski(B_179,A_180)
      | ~ m1_subset_1(B_179,k1_zfmisc_1(A_180))
      | v1_xboole_0(k1_zfmisc_1(A_180)) ) ),
    inference(resolution,[status(thm)],[c_225,c_22])).

tff(c_1631,plain,
    ( r1_tarski('#skF_8','#skF_6')
    | v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_44,c_1614])).

tff(c_1644,plain,(
    r1_tarski('#skF_8','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1631])).

tff(c_280,plain,(
    ! [A_73,B_74] :
      ( r2_hidden('#skF_1'(A_73),B_74)
      | ~ r1_tarski(A_73,B_74)
      | v1_xboole_0(A_73) ) ),
    inference(resolution,[status(thm)],[c_4,c_261])).

tff(c_301,plain,(
    ! [B_74,A_73] :
      ( ~ v1_xboole_0(B_74)
      | ~ r1_tarski(A_73,B_74)
      | v1_xboole_0(A_73) ) ),
    inference(resolution,[status(thm)],[c_280,c_2])).

tff(c_1650,plain,
    ( ~ v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_1644,c_301])).

tff(c_1656,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1256,c_1650])).

tff(c_1658,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_367,c_1656])).

tff(c_1660,plain,(
    m1_subset_1('#skF_1'('#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_368])).

tff(c_40,plain,(
    ! [B_21,A_20] :
      ( v1_xboole_0(B_21)
      | ~ m1_subset_1(B_21,A_20)
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1721,plain,
    ( v1_xboole_0('#skF_1'('#skF_7'))
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1660,c_40])).

tff(c_1726,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1721])).

tff(c_3278,plain,(
    ! [B_304,A_305] :
      ( r1_tarski(B_304,A_305)
      | ~ m1_subset_1(B_304,k1_zfmisc_1(A_305))
      | v1_xboole_0(k1_zfmisc_1(A_305)) ) ),
    inference(resolution,[status(thm)],[c_225,c_22])).

tff(c_3315,plain,
    ( r1_tarski('#skF_8','#skF_6')
    | v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_44,c_3278])).

tff(c_3331,plain,(
    r1_tarski('#skF_8','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3315])).

tff(c_3863,plain,(
    ! [B_347,B_348,A_349] :
      ( r2_hidden(B_347,B_348)
      | ~ r1_tarski(A_349,B_348)
      | ~ m1_subset_1(B_347,A_349)
      | v1_xboole_0(A_349) ) ),
    inference(resolution,[status(thm)],[c_36,c_261])).

tff(c_3871,plain,(
    ! [B_347] :
      ( r2_hidden(B_347,'#skF_6')
      | ~ m1_subset_1(B_347,'#skF_8')
      | v1_xboole_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_3331,c_3863])).

tff(c_3941,plain,(
    ! [B_351] :
      ( r2_hidden(B_351,'#skF_6')
      | ~ m1_subset_1(B_351,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_367,c_3871])).

tff(c_3953,plain,(
    ! [B_351] :
      ( m1_subset_1(B_351,'#skF_6')
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(B_351,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_3941,c_34])).

tff(c_4091,plain,(
    ! [B_354] :
      ( m1_subset_1(B_354,'#skF_6')
      | ~ m1_subset_1(B_354,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1726,c_3953])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2896,plain,(
    ! [A_265] :
      ( r1_tarski(A_265,'#skF_7')
      | ~ r2_hidden('#skF_2'(A_265,'#skF_7'),'#skF_8')
      | ~ m1_subset_1('#skF_2'(A_265,'#skF_7'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_123,c_8])).

tff(c_2911,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_8','#skF_7'),'#skF_6')
    | r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_10,c_2896])).

tff(c_2912,plain,(
    ~ m1_subset_1('#skF_2'('#skF_8','#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2911])).

tff(c_4116,plain,(
    ~ m1_subset_1('#skF_2'('#skF_8','#skF_7'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_4091,c_2912])).

tff(c_4124,plain,
    ( v1_xboole_0('#skF_8')
    | r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_199,c_4116])).

tff(c_4131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3097,c_367,c_4124])).

tff(c_4133,plain,(
    r2_xboole_0('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_3086])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_3'(A_12,B_13),B_13)
      | ~ r2_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_197,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1('#skF_3'(A_12,B_13),B_13)
      | v1_xboole_0(B_13)
      | ~ r2_xboole_0(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_20,c_181])).

tff(c_4302,plain,(
    ! [B_368,A_369] :
      ( r1_tarski(B_368,A_369)
      | ~ m1_subset_1(B_368,k1_zfmisc_1(A_369))
      | v1_xboole_0(k1_zfmisc_1(A_369)) ) ),
    inference(resolution,[status(thm)],[c_225,c_22])).

tff(c_4338,plain,
    ( r1_tarski('#skF_7','#skF_6')
    | v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_46,c_4302])).

tff(c_4353,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_4338])).

tff(c_4763,plain,(
    ! [B_403,B_404,A_405] :
      ( r2_hidden(B_403,B_404)
      | ~ r1_tarski(A_405,B_404)
      | ~ m1_subset_1(B_403,A_405)
      | v1_xboole_0(A_405) ) ),
    inference(resolution,[status(thm)],[c_36,c_261])).

tff(c_4777,plain,(
    ! [B_403] :
      ( r2_hidden(B_403,'#skF_6')
      | ~ m1_subset_1(B_403,'#skF_7')
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_4353,c_4763])).

tff(c_4824,plain,(
    ! [B_406] :
      ( r2_hidden(B_406,'#skF_6')
      | ~ m1_subset_1(B_406,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_4777])).

tff(c_4836,plain,(
    ! [B_406] :
      ( m1_subset_1(B_406,'#skF_6')
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(B_406,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_4824,c_34])).

tff(c_4880,plain,(
    ! [B_408] :
      ( m1_subset_1(B_408,'#skF_6')
      | ~ m1_subset_1(B_408,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1726,c_4836])).

tff(c_4888,plain,(
    ! [A_12] :
      ( m1_subset_1('#skF_3'(A_12,'#skF_7'),'#skF_6')
      | v1_xboole_0('#skF_7')
      | ~ r2_xboole_0(A_12,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_197,c_4880])).

tff(c_5379,plain,(
    ! [A_432] :
      ( m1_subset_1('#skF_3'(A_432,'#skF_7'),'#skF_6')
      | ~ r2_xboole_0(A_432,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_4888])).

tff(c_4132,plain,(
    ~ m1_subset_1('#skF_3'('#skF_8','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_3086])).

tff(c_5382,plain,(
    ~ r2_xboole_0('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_5379,c_4132])).

tff(c_5393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4133,c_5382])).

tff(c_5394,plain,(
    r1_tarski('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_2911])).

tff(c_5441,plain,(
    ! [A_437] :
      ( r2_hidden('#skF_3'(A_437,'#skF_7'),'#skF_8')
      | ~ m1_subset_1('#skF_3'(A_437,'#skF_7'),'#skF_6')
      | ~ r2_xboole_0(A_437,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_151,c_50])).

tff(c_5462,plain,
    ( ~ m1_subset_1('#skF_3'('#skF_8','#skF_7'),'#skF_6')
    | ~ r2_xboole_0('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_5441,c_18])).

tff(c_5467,plain,(
    ~ r2_xboole_0('#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_5462])).

tff(c_5470,plain,
    ( '#skF_7' = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_12,c_5467])).

tff(c_5473,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5394,c_5470])).

tff(c_5475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_5473])).

tff(c_5477,plain,(
    r2_xboole_0('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_5462])).

tff(c_5676,plain,(
    ! [B_456,A_457] :
      ( r1_tarski(B_456,A_457)
      | ~ m1_subset_1(B_456,k1_zfmisc_1(A_457))
      | v1_xboole_0(k1_zfmisc_1(A_457)) ) ),
    inference(resolution,[status(thm)],[c_225,c_22])).

tff(c_5702,plain,
    ( r1_tarski('#skF_7','#skF_6')
    | v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_46,c_5676])).

tff(c_5713,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_5702])).

tff(c_6501,plain,(
    ! [B_521,B_522,A_523] :
      ( r2_hidden(B_521,B_522)
      | ~ r1_tarski(A_523,B_522)
      | ~ m1_subset_1(B_521,A_523)
      | v1_xboole_0(A_523) ) ),
    inference(resolution,[status(thm)],[c_36,c_261])).

tff(c_6513,plain,(
    ! [B_521] :
      ( r2_hidden(B_521,'#skF_6')
      | ~ m1_subset_1(B_521,'#skF_7')
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_5713,c_6501])).

tff(c_6572,plain,(
    ! [B_524] :
      ( r2_hidden(B_524,'#skF_6')
      | ~ m1_subset_1(B_524,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_6513])).

tff(c_6584,plain,(
    ! [B_524] :
      ( m1_subset_1(B_524,'#skF_6')
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(B_524,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_6572,c_34])).

tff(c_6742,plain,(
    ! [B_529] :
      ( m1_subset_1(B_529,'#skF_6')
      | ~ m1_subset_1(B_529,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1726,c_6584])).

tff(c_6750,plain,(
    ! [A_12] :
      ( m1_subset_1('#skF_3'(A_12,'#skF_7'),'#skF_6')
      | v1_xboole_0('#skF_7')
      | ~ r2_xboole_0(A_12,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_197,c_6742])).

tff(c_7091,plain,(
    ! [A_544] :
      ( m1_subset_1('#skF_3'(A_544,'#skF_7'),'#skF_6')
      | ~ r2_xboole_0(A_544,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_6750])).

tff(c_5476,plain,(
    ~ m1_subset_1('#skF_3'('#skF_8','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_5462])).

tff(c_7098,plain,(
    ~ r2_xboole_0('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_7091,c_5476])).

tff(c_7107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5477,c_7098])).

tff(c_7109,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1721])).

tff(c_112,plain,(
    ! [A_48,B_49] :
      ( ~ r2_hidden('#skF_2'(A_48,B_49),B_49)
      | r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_121,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_112])).

tff(c_86,plain,(
    ! [C_42,A_43] :
      ( r1_tarski(C_42,A_43)
      | ~ r2_hidden(C_42,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_95,plain,(
    ! [A_43] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(A_43)),A_43)
      | v1_xboole_0(k1_zfmisc_1(A_43)) ) ),
    inference(resolution,[status(thm)],[c_4,c_86])).

tff(c_328,plain,(
    ! [B_77,A_78] :
      ( ~ v1_xboole_0(B_77)
      | ~ r1_tarski(A_78,B_77)
      | v1_xboole_0(A_78) ) ),
    inference(resolution,[status(thm)],[c_280,c_2])).

tff(c_7589,plain,(
    ! [A_571] :
      ( ~ v1_xboole_0(A_571)
      | v1_xboole_0('#skF_1'(k1_zfmisc_1(A_571)))
      | v1_xboole_0(k1_zfmisc_1(A_571)) ) ),
    inference(resolution,[status(thm)],[c_95,c_328])).

tff(c_96,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_2'(A_44,B_45),A_44)
      | r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_110,plain,(
    ! [A_44,B_45] :
      ( ~ v1_xboole_0(A_44)
      | r1_tarski(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_96,c_2])).

tff(c_166,plain,(
    ! [B_56,A_57] :
      ( ~ v1_xboole_0(B_56)
      | ~ r2_xboole_0(A_57,B_56) ) ),
    inference(resolution,[status(thm)],[c_151,c_2])).

tff(c_171,plain,(
    ! [B_58,A_59] :
      ( ~ v1_xboole_0(B_58)
      | B_58 = A_59
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(resolution,[status(thm)],[c_12,c_166])).

tff(c_180,plain,(
    ! [B_45,A_44] :
      ( ~ v1_xboole_0(B_45)
      | B_45 = A_44
      | ~ v1_xboole_0(A_44) ) ),
    inference(resolution,[status(thm)],[c_110,c_171])).

tff(c_7112,plain,(
    ! [A_44] :
      ( A_44 = '#skF_6'
      | ~ v1_xboole_0(A_44) ) ),
    inference(resolution,[status(thm)],[c_7109,c_180])).

tff(c_7705,plain,(
    ! [A_578] :
      ( '#skF_1'(k1_zfmisc_1(A_578)) = '#skF_6'
      | ~ v1_xboole_0(A_578)
      | v1_xboole_0(k1_zfmisc_1(A_578)) ) ),
    inference(resolution,[status(thm)],[c_7589,c_7112])).

tff(c_80,plain,(
    ! [C_38,A_39] :
      ( r2_hidden(C_38,k1_zfmisc_1(A_39))
      | ~ r1_tarski(C_38,A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_84,plain,(
    ! [A_39,C_38] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_39))
      | ~ r1_tarski(C_38,A_39) ) ),
    inference(resolution,[status(thm)],[c_80,c_2])).

tff(c_7784,plain,(
    ! [C_582,A_583] :
      ( ~ r1_tarski(C_582,A_583)
      | '#skF_1'(k1_zfmisc_1(A_583)) = '#skF_6'
      | ~ v1_xboole_0(A_583) ) ),
    inference(resolution,[status(thm)],[c_7705,c_84])).

tff(c_7813,plain,(
    ! [A_586] :
      ( '#skF_1'(k1_zfmisc_1(A_586)) = '#skF_6'
      | ~ v1_xboole_0(A_586) ) ),
    inference(resolution,[status(thm)],[c_121,c_7784])).

tff(c_7856,plain,(
    ! [A_587] :
      ( r1_tarski('#skF_6',A_587)
      | v1_xboole_0(k1_zfmisc_1(A_587))
      | ~ v1_xboole_0(A_587) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7813,c_95])).

tff(c_7923,plain,(
    ! [C_590,A_591] :
      ( ~ r1_tarski(C_590,A_591)
      | r1_tarski('#skF_6',A_591)
      | ~ v1_xboole_0(A_591) ) ),
    inference(resolution,[status(thm)],[c_7856,c_84])).

tff(c_7940,plain,(
    ! [A_5] :
      ( r1_tarski('#skF_6',A_5)
      | ~ v1_xboole_0(A_5) ) ),
    inference(resolution,[status(thm)],[c_121,c_7923])).

tff(c_7108,plain,(
    v1_xboole_0('#skF_1'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1721])).

tff(c_7116,plain,(
    ! [A_545] :
      ( A_545 = '#skF_6'
      | ~ v1_xboole_0(A_545) ) ),
    inference(resolution,[status(thm)],[c_7109,c_180])).

tff(c_7123,plain,(
    '#skF_1'('#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_7108,c_7116])).

tff(c_1659,plain,(
    r2_hidden('#skF_1'('#skF_7'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_368])).

tff(c_7129,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7123,c_1659])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_7351,plain,(
    ! [B_555] :
      ( r2_hidden('#skF_6',B_555)
      | ~ r1_tarski('#skF_8',B_555) ) ),
    inference(resolution,[status(thm)],[c_7129,c_6])).

tff(c_7967,plain,(
    ! [B_595,B_596] :
      ( r2_hidden('#skF_6',B_595)
      | ~ r1_tarski(B_596,B_595)
      | ~ r1_tarski('#skF_8',B_596) ) ),
    inference(resolution,[status(thm)],[c_7351,c_6])).

tff(c_7980,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_6',A_5)
      | ~ r1_tarski('#skF_8','#skF_6')
      | ~ v1_xboole_0(A_5) ) ),
    inference(resolution,[status(thm)],[c_7940,c_7967])).

tff(c_7986,plain,(
    ~ r1_tarski('#skF_8','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_7980])).

tff(c_8095,plain,(
    ! [B_611,A_612] :
      ( r1_tarski(B_611,A_612)
      | ~ m1_subset_1(B_611,k1_zfmisc_1(A_612))
      | v1_xboole_0(k1_zfmisc_1(A_612)) ) ),
    inference(resolution,[status(thm)],[c_225,c_22])).

tff(c_8126,plain,
    ( r1_tarski('#skF_8','#skF_6')
    | v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_44,c_8095])).

tff(c_8144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_7986,c_8126])).

tff(c_8146,plain,(
    r1_tarski('#skF_8','#skF_6') ),
    inference(splitRight,[status(thm)],[c_7980])).

tff(c_7387,plain,(
    ! [B_555] :
      ( ~ v1_xboole_0(B_555)
      | ~ r1_tarski('#skF_8',B_555) ) ),
    inference(resolution,[status(thm)],[c_7351,c_2])).

tff(c_8154,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_8146,c_7387])).

tff(c_8169,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7109,c_8154])).

tff(c_8171,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_366])).

tff(c_8198,plain,(
    ! [B_616] :
      ( ~ m1_subset_1(B_616,'#skF_6')
      | ~ m1_subset_1(B_616,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_366])).

tff(c_8202,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_7'),'#skF_6')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_201,c_8198])).

tff(c_8209,plain,(
    ~ m1_subset_1('#skF_1'('#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_8202])).

tff(c_8214,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_7'))
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_8209])).

tff(c_8216,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_8214])).

tff(c_8587,plain,(
    ! [B_646,A_647] :
      ( r1_tarski(B_646,A_647)
      | ~ m1_subset_1(B_646,k1_zfmisc_1(A_647))
      | v1_xboole_0(k1_zfmisc_1(A_647)) ) ),
    inference(resolution,[status(thm)],[c_225,c_22])).

tff(c_8607,plain,
    ( r1_tarski('#skF_7','#skF_6')
    | v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_46,c_8587])).

tff(c_8618,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_8607])).

tff(c_9017,plain,(
    ! [B_691,B_692,A_693] :
      ( r2_hidden(B_691,B_692)
      | ~ r1_tarski(A_693,B_692)
      | ~ m1_subset_1(B_691,A_693)
      | v1_xboole_0(A_693) ) ),
    inference(resolution,[status(thm)],[c_36,c_261])).

tff(c_9031,plain,(
    ! [B_691] :
      ( r2_hidden(B_691,'#skF_6')
      | ~ m1_subset_1(B_691,'#skF_7')
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_8618,c_9017])).

tff(c_9059,plain,(
    ! [B_696] :
      ( r2_hidden(B_696,'#skF_6')
      | ~ m1_subset_1(B_696,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_9031])).

tff(c_9071,plain,(
    ! [B_696] :
      ( m1_subset_1(B_696,'#skF_6')
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(B_696,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_9059,c_34])).

tff(c_9087,plain,(
    ! [B_697] :
      ( m1_subset_1(B_697,'#skF_6')
      | ~ m1_subset_1(B_697,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_8216,c_9071])).

tff(c_9099,plain,
    ( m1_subset_1('#skF_1'('#skF_7'),'#skF_6')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_201,c_9087])).

tff(c_9113,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_8209,c_9099])).

tff(c_9115,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_8214])).

tff(c_8174,plain,(
    ! [A_44] :
      ( A_44 = '#skF_8'
      | ~ v1_xboole_0(A_44) ) ),
    inference(resolution,[status(thm)],[c_8171,c_180])).

tff(c_9155,plain,(
    '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_9115,c_8174])).

tff(c_9162,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9155,c_68])).

tff(c_48,plain,(
    ! [D_26] :
      ( r2_hidden(D_26,'#skF_7')
      | ~ r2_hidden(D_26,'#skF_8')
      | ~ m1_subset_1(D_26,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_208,plain,(
    ! [A_65,B_66] :
      ( ~ r2_hidden('#skF_3'(A_65,B_66),A_65)
      | ~ r2_xboole_0(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_222,plain,(
    ! [B_66] :
      ( ~ r2_xboole_0('#skF_7',B_66)
      | ~ r2_hidden('#skF_3'('#skF_7',B_66),'#skF_8')
      | ~ m1_subset_1('#skF_3'('#skF_7',B_66),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_48,c_208])).

tff(c_9748,plain,(
    ! [B_735] :
      ( ~ r2_xboole_0('#skF_7',B_735)
      | ~ r2_hidden('#skF_3'('#skF_7',B_735),'#skF_8')
      | ~ m1_subset_1('#skF_3'('#skF_7',B_735),'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9155,c_222])).

tff(c_9763,plain,
    ( ~ m1_subset_1('#skF_3'('#skF_7','#skF_8'),'#skF_8')
    | ~ r2_xboole_0('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_20,c_9748])).

tff(c_9772,plain,(
    ~ r2_xboole_0('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_9763])).

tff(c_9775,plain,
    ( '#skF_7' = '#skF_8'
    | ~ r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_12,c_9772])).

tff(c_9778,plain,(
    ~ r1_tarski('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_9775])).

tff(c_9165,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9155,c_46])).

tff(c_9860,plain,(
    ! [B_754,A_755] :
      ( r1_tarski(B_754,A_755)
      | ~ m1_subset_1(B_754,k1_zfmisc_1(A_755))
      | v1_xboole_0(k1_zfmisc_1(A_755)) ) ),
    inference(resolution,[status(thm)],[c_225,c_22])).

tff(c_9880,plain,
    ( r1_tarski('#skF_7','#skF_8')
    | v1_xboole_0(k1_zfmisc_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_9165,c_9860])).

tff(c_9900,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9162,c_9778,c_9880])).

tff(c_9902,plain,(
    r2_xboole_0('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_9763])).

tff(c_165,plain,(
    ! [B_55,A_54] :
      ( ~ v1_xboole_0(B_55)
      | ~ r2_xboole_0(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_151,c_2])).

tff(c_9906,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_9902,c_165])).

tff(c_9913,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8171,c_9906])).

tff(c_9925,plain,(
    ! [D_757] :
      ( ~ r2_hidden(D_757,'#skF_8')
      | ~ m1_subset_1(D_757,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_9940,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_8'),'#skF_6')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_4,c_9925])).

tff(c_9941,plain,(
    ~ m1_subset_1('#skF_1'('#skF_8'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_9940])).

tff(c_9980,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_8'))
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_9941])).

tff(c_9981,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_9980])).

tff(c_9942,plain,(
    ! [B_758,A_759] :
      ( r2_hidden(B_758,A_759)
      | ~ m1_subset_1(B_758,A_759)
      | v1_xboole_0(A_759) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_9914,plain,(
    ! [D_50] :
      ( ~ r2_hidden(D_50,'#skF_8')
      | ~ m1_subset_1(D_50,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_9969,plain,(
    ! [B_758] :
      ( ~ m1_subset_1(B_758,'#skF_6')
      | ~ m1_subset_1(B_758,'#skF_8')
      | v1_xboole_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_9942,c_9914])).

tff(c_9989,plain,(
    ! [B_761] :
      ( ~ m1_subset_1(B_761,'#skF_6')
      | ~ m1_subset_1(B_761,'#skF_8') ) ),
    inference(splitLeft,[status(thm)],[c_9969])).

tff(c_9993,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6'),'#skF_8')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_201,c_9989])).

tff(c_10000,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_9981,c_9993])).

tff(c_10005,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_6'))
    | ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_10000])).

tff(c_10006,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_10005])).

tff(c_10523,plain,(
    ! [B_811,A_812] :
      ( r1_tarski(B_811,A_812)
      | ~ m1_subset_1(B_811,k1_zfmisc_1(A_812))
      | v1_xboole_0(k1_zfmisc_1(A_812)) ) ),
    inference(resolution,[status(thm)],[c_9942,c_22])).

tff(c_10543,plain,
    ( r1_tarski('#skF_8','#skF_6')
    | v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_44,c_10523])).

tff(c_10555,plain,(
    r1_tarski('#skF_8','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_10543])).

tff(c_10007,plain,(
    ! [C_762,B_763,A_764] :
      ( r2_hidden(C_762,B_763)
      | ~ r2_hidden(C_762,A_764)
      | ~ r1_tarski(A_764,B_763) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10797,plain,(
    ! [B_842,B_843,A_844] :
      ( r2_hidden(B_842,B_843)
      | ~ r1_tarski(A_844,B_843)
      | ~ m1_subset_1(B_842,A_844)
      | v1_xboole_0(A_844) ) ),
    inference(resolution,[status(thm)],[c_36,c_10007])).

tff(c_10803,plain,(
    ! [B_842] :
      ( r2_hidden(B_842,'#skF_6')
      | ~ m1_subset_1(B_842,'#skF_8')
      | v1_xboole_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_10555,c_10797])).

tff(c_10840,plain,(
    ! [B_847] :
      ( r2_hidden(B_847,'#skF_6')
      | ~ m1_subset_1(B_847,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_10006,c_10803])).

tff(c_10852,plain,(
    ! [B_847] :
      ( m1_subset_1(B_847,'#skF_6')
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(B_847,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_10840,c_34])).

tff(c_10868,plain,(
    ! [B_848] :
      ( m1_subset_1(B_848,'#skF_6')
      | ~ m1_subset_1(B_848,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_9981,c_10852])).

tff(c_9988,plain,(
    ! [B_758] :
      ( ~ m1_subset_1(B_758,'#skF_6')
      | ~ m1_subset_1(B_758,'#skF_8') ) ),
    inference(splitLeft,[status(thm)],[c_9969])).

tff(c_10946,plain,(
    ! [B_851] : ~ m1_subset_1(B_851,'#skF_8') ),
    inference(resolution,[status(thm)],[c_10868,c_9988])).

tff(c_10958,plain,(
    v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_201,c_10946])).

tff(c_10972,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10006,c_10958])).

tff(c_10974,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_10005])).

tff(c_9915,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_9918,plain,(
    ! [A_44] :
      ( A_44 = '#skF_7'
      | ~ v1_xboole_0(A_44) ) ),
    inference(resolution,[status(thm)],[c_9915,c_180])).

tff(c_10977,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_10974,c_9918])).

tff(c_10983,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_10977])).

tff(c_10984,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_9969])).

tff(c_10987,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_10984,c_9918])).

tff(c_10993,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_10987])).

tff(c_10995,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_9980])).

tff(c_11001,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_10995,c_9918])).

tff(c_11007,plain,(
    '#skF_6' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11001,c_42])).

tff(c_11046,plain,(
    ! [B_857] :
      ( ~ m1_subset_1(B_857,'#skF_6')
      | ~ m1_subset_1(B_857,'#skF_8') ) ),
    inference(splitLeft,[status(thm)],[c_9969])).

tff(c_11054,plain,(
    ! [B_21] :
      ( ~ m1_subset_1(B_21,'#skF_8')
      | ~ v1_xboole_0(B_21)
      | ~ v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_38,c_11046])).

tff(c_11060,plain,(
    ! [B_858] :
      ( ~ m1_subset_1(B_858,'#skF_8')
      | ~ v1_xboole_0(B_858) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10995,c_11054])).

tff(c_11070,plain,(
    ! [B_21] :
      ( ~ v1_xboole_0(B_21)
      | ~ v1_xboole_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_38,c_11060])).

tff(c_11097,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_11070])).

tff(c_11793,plain,(
    ! [B_931,A_932] :
      ( r1_tarski(B_931,A_932)
      | ~ m1_subset_1(B_931,k1_zfmisc_1(A_932))
      | v1_xboole_0(k1_zfmisc_1(A_932)) ) ),
    inference(resolution,[status(thm)],[c_9942,c_22])).

tff(c_11824,plain,
    ( r1_tarski('#skF_8','#skF_6')
    | v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_44,c_11793])).

tff(c_11838,plain,(
    r1_tarski('#skF_8','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_11824])).

tff(c_11013,plain,(
    ! [C_852,B_853,A_854] :
      ( r2_hidden(C_852,B_853)
      | ~ r2_hidden(C_852,A_854)
      | ~ r1_tarski(A_854,B_853) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_11142,plain,(
    ! [A_866,B_867] :
      ( r2_hidden('#skF_1'(A_866),B_867)
      | ~ r1_tarski(A_866,B_867)
      | v1_xboole_0(A_866) ) ),
    inference(resolution,[status(thm)],[c_4,c_11013])).

tff(c_11168,plain,(
    ! [B_867,A_866] :
      ( ~ v1_xboole_0(B_867)
      | ~ r1_tarski(A_866,B_867)
      | v1_xboole_0(A_866) ) ),
    inference(resolution,[status(thm)],[c_11142,c_2])).

tff(c_11841,plain,
    ( ~ v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_11838,c_11168])).

tff(c_11847,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10995,c_11841])).

tff(c_11849,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11097,c_11847])).

tff(c_11851,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_11070])).

tff(c_11002,plain,(
    ! [A_44] :
      ( A_44 = '#skF_6'
      | ~ v1_xboole_0(A_44) ) ),
    inference(resolution,[status(thm)],[c_10995,c_180])).

tff(c_11854,plain,(
    '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_11851,c_11002])).

tff(c_11860,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11007,c_11854])).

tff(c_11862,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_11863,plain,(
    ! [C_933,A_934] :
      ( r2_hidden(C_933,k1_zfmisc_1(A_934))
      | ~ r1_tarski(C_933,A_934) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_11877,plain,(
    ! [A_936,C_937] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_936))
      | ~ r1_tarski(C_937,A_936) ) ),
    inference(resolution,[status(thm)],[c_11863,c_2])).

tff(c_11880,plain,(
    ! [C_937] : ~ r1_tarski(C_937,'#skF_6') ),
    inference(resolution,[status(thm)],[c_11862,c_11877])).

tff(c_11923,plain,(
    ! [A_946] : ~ v1_xboole_0(A_946) ),
    inference(resolution,[status(thm)],[c_11919,c_11880])).

tff(c_67,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_46,c_59])).

tff(c_11869,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11862,c_67])).

tff(c_11929,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11923,c_11869])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:49:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.16/2.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.16/2.84  
% 8.16/2.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.16/2.84  %$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_8 > #skF_2 > #skF_5 > #skF_4
% 8.16/2.84  
% 8.16/2.84  %Foreground sorts:
% 8.16/2.84  
% 8.16/2.84  
% 8.16/2.84  %Background operators:
% 8.16/2.84  
% 8.16/2.84  
% 8.16/2.84  %Foreground operators:
% 8.16/2.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.16/2.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.16/2.84  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.16/2.84  tff('#skF_7', type, '#skF_7': $i).
% 8.16/2.84  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.16/2.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.16/2.84  tff('#skF_6', type, '#skF_6': $i).
% 8.16/2.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.16/2.84  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 8.16/2.84  tff('#skF_8', type, '#skF_8': $i).
% 8.16/2.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.16/2.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.16/2.84  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.16/2.84  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.16/2.84  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 8.16/2.84  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.16/2.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.16/2.84  
% 8.53/2.88  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.53/2.88  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.53/2.88  tff(f_90, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_subset_1)).
% 8.53/2.88  tff(f_75, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 8.53/2.88  tff(f_45, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 8.53/2.88  tff(f_55, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 8.53/2.88  tff(f_62, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 8.53/2.88  tff(c_11904, plain, (![A_944, B_945]: (r2_hidden('#skF_2'(A_944, B_945), A_944) | r1_tarski(A_944, B_945))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.53/2.88  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.53/2.88  tff(c_11919, plain, (![A_946, B_947]: (~v1_xboole_0(A_946) | r1_tarski(A_946, B_947))), inference(resolution, [status(thm)], [c_11904, c_2])).
% 8.53/2.88  tff(c_42, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.53/2.88  tff(c_38, plain, (![B_21, A_20]: (m1_subset_1(B_21, A_20) | ~v1_xboole_0(B_21) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.53/2.88  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.53/2.88  tff(c_12, plain, (![A_10, B_11]: (r2_xboole_0(A_10, B_11) | B_11=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.53/2.88  tff(c_151, plain, (![A_54, B_55]: (r2_hidden('#skF_3'(A_54, B_55), B_55) | ~r2_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.53/2.88  tff(c_50, plain, (![D_26]: (r2_hidden(D_26, '#skF_8') | ~r2_hidden(D_26, '#skF_7') | ~m1_subset_1(D_26, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.53/2.88  tff(c_3060, plain, (![A_283]: (r2_hidden('#skF_3'(A_283, '#skF_7'), '#skF_8') | ~m1_subset_1('#skF_3'(A_283, '#skF_7'), '#skF_6') | ~r2_xboole_0(A_283, '#skF_7'))), inference(resolution, [status(thm)], [c_151, c_50])).
% 8.53/2.88  tff(c_18, plain, (![A_12, B_13]: (~r2_hidden('#skF_3'(A_12, B_13), A_12) | ~r2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.53/2.88  tff(c_3086, plain, (~m1_subset_1('#skF_3'('#skF_8', '#skF_7'), '#skF_6') | ~r2_xboole_0('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_3060, c_18])).
% 8.53/2.88  tff(c_3091, plain, (~r2_xboole_0('#skF_8', '#skF_7')), inference(splitLeft, [status(thm)], [c_3086])).
% 8.53/2.88  tff(c_3094, plain, ('#skF_7'='#skF_8' | ~r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_12, c_3091])).
% 8.53/2.88  tff(c_3097, plain, (~r1_tarski('#skF_8', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_42, c_3094])).
% 8.53/2.88  tff(c_123, plain, (![D_50]: (r2_hidden(D_50, '#skF_7') | ~r2_hidden(D_50, '#skF_8') | ~m1_subset_1(D_50, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.53/2.88  tff(c_136, plain, (![D_50]: (~v1_xboole_0('#skF_7') | ~r2_hidden(D_50, '#skF_8') | ~m1_subset_1(D_50, '#skF_6'))), inference(resolution, [status(thm)], [c_123, c_2])).
% 8.53/2.88  tff(c_224, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_136])).
% 8.53/2.88  tff(c_225, plain, (![B_67, A_68]: (r2_hidden(B_67, A_68) | ~m1_subset_1(B_67, A_68) | v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.53/2.88  tff(c_244, plain, (![B_67]: (r2_hidden(B_67, '#skF_8') | ~m1_subset_1(B_67, '#skF_6') | ~m1_subset_1(B_67, '#skF_7') | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_225, c_50])).
% 8.53/2.88  tff(c_345, plain, (![B_79]: (r2_hidden(B_79, '#skF_8') | ~m1_subset_1(B_79, '#skF_6') | ~m1_subset_1(B_79, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_224, c_244])).
% 8.53/2.88  tff(c_366, plain, (![B_79]: (~v1_xboole_0('#skF_8') | ~m1_subset_1(B_79, '#skF_6') | ~m1_subset_1(B_79, '#skF_7'))), inference(resolution, [status(thm)], [c_345, c_2])).
% 8.53/2.88  tff(c_367, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_366])).
% 8.53/2.88  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.53/2.88  tff(c_181, plain, (![B_60, A_61]: (m1_subset_1(B_60, A_61) | ~r2_hidden(B_60, A_61) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.53/2.88  tff(c_199, plain, (![A_5, B_6]: (m1_subset_1('#skF_2'(A_5, B_6), A_5) | v1_xboole_0(A_5) | r1_tarski(A_5, B_6))), inference(resolution, [status(thm)], [c_10, c_181])).
% 8.53/2.88  tff(c_69, plain, (![D_35]: (r2_hidden(D_35, '#skF_8') | ~r2_hidden(D_35, '#skF_7') | ~m1_subset_1(D_35, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.53/2.88  tff(c_74, plain, (r2_hidden('#skF_1'('#skF_7'), '#skF_8') | ~m1_subset_1('#skF_1'('#skF_7'), '#skF_6') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_4, c_69])).
% 8.53/2.88  tff(c_368, plain, (r2_hidden('#skF_1'('#skF_7'), '#skF_8') | ~m1_subset_1('#skF_1'('#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_224, c_74])).
% 8.53/2.88  tff(c_369, plain, (~m1_subset_1('#skF_1'('#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_368])).
% 8.53/2.88  tff(c_201, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_181])).
% 8.53/2.88  tff(c_373, plain, (~v1_xboole_0('#skF_1'('#skF_7')) | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_38, c_369])).
% 8.53/2.88  tff(c_374, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_373])).
% 8.53/2.88  tff(c_44, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.53/2.88  tff(c_59, plain, (![B_33, A_34]: (v1_xboole_0(B_33) | ~m1_subset_1(B_33, A_34) | ~v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.53/2.88  tff(c_66, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_44, c_59])).
% 8.53/2.88  tff(c_68, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_66])).
% 8.53/2.88  tff(c_46, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.53/2.88  tff(c_22, plain, (![C_19, A_15]: (r1_tarski(C_19, A_15) | ~r2_hidden(C_19, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.53/2.88  tff(c_636, plain, (![B_109, A_110]: (r1_tarski(B_109, A_110) | ~m1_subset_1(B_109, k1_zfmisc_1(A_110)) | v1_xboole_0(k1_zfmisc_1(A_110)))), inference(resolution, [status(thm)], [c_225, c_22])).
% 8.53/2.88  tff(c_657, plain, (r1_tarski('#skF_7', '#skF_6') | v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_46, c_636])).
% 8.53/2.88  tff(c_668, plain, (r1_tarski('#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_68, c_657])).
% 8.53/2.88  tff(c_36, plain, (![B_21, A_20]: (r2_hidden(B_21, A_20) | ~m1_subset_1(B_21, A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.53/2.88  tff(c_261, plain, (![C_70, B_71, A_72]: (r2_hidden(C_70, B_71) | ~r2_hidden(C_70, A_72) | ~r1_tarski(A_72, B_71))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.53/2.88  tff(c_1130, plain, (![B_152, B_153, A_154]: (r2_hidden(B_152, B_153) | ~r1_tarski(A_154, B_153) | ~m1_subset_1(B_152, A_154) | v1_xboole_0(A_154))), inference(resolution, [status(thm)], [c_36, c_261])).
% 8.53/2.88  tff(c_1140, plain, (![B_152]: (r2_hidden(B_152, '#skF_6') | ~m1_subset_1(B_152, '#skF_7') | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_668, c_1130])).
% 8.53/2.88  tff(c_1168, plain, (![B_155]: (r2_hidden(B_155, '#skF_6') | ~m1_subset_1(B_155, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_224, c_1140])).
% 8.53/2.88  tff(c_34, plain, (![B_21, A_20]: (m1_subset_1(B_21, A_20) | ~r2_hidden(B_21, A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.53/2.88  tff(c_1180, plain, (![B_155]: (m1_subset_1(B_155, '#skF_6') | v1_xboole_0('#skF_6') | ~m1_subset_1(B_155, '#skF_7'))), inference(resolution, [status(thm)], [c_1168, c_34])).
% 8.53/2.88  tff(c_1224, plain, (![B_157]: (m1_subset_1(B_157, '#skF_6') | ~m1_subset_1(B_157, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_374, c_1180])).
% 8.53/2.88  tff(c_1239, plain, (m1_subset_1('#skF_1'('#skF_7'), '#skF_6') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_201, c_1224])).
% 8.53/2.88  tff(c_1254, plain, $false, inference(negUnitSimplification, [status(thm)], [c_224, c_369, c_1239])).
% 8.53/2.88  tff(c_1256, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_373])).
% 8.53/2.88  tff(c_1614, plain, (![B_179, A_180]: (r1_tarski(B_179, A_180) | ~m1_subset_1(B_179, k1_zfmisc_1(A_180)) | v1_xboole_0(k1_zfmisc_1(A_180)))), inference(resolution, [status(thm)], [c_225, c_22])).
% 8.53/2.88  tff(c_1631, plain, (r1_tarski('#skF_8', '#skF_6') | v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_44, c_1614])).
% 8.53/2.88  tff(c_1644, plain, (r1_tarski('#skF_8', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_68, c_1631])).
% 8.53/2.88  tff(c_280, plain, (![A_73, B_74]: (r2_hidden('#skF_1'(A_73), B_74) | ~r1_tarski(A_73, B_74) | v1_xboole_0(A_73))), inference(resolution, [status(thm)], [c_4, c_261])).
% 8.53/2.88  tff(c_301, plain, (![B_74, A_73]: (~v1_xboole_0(B_74) | ~r1_tarski(A_73, B_74) | v1_xboole_0(A_73))), inference(resolution, [status(thm)], [c_280, c_2])).
% 8.53/2.88  tff(c_1650, plain, (~v1_xboole_0('#skF_6') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_1644, c_301])).
% 8.53/2.88  tff(c_1656, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1256, c_1650])).
% 8.53/2.88  tff(c_1658, plain, $false, inference(negUnitSimplification, [status(thm)], [c_367, c_1656])).
% 8.53/2.88  tff(c_1660, plain, (m1_subset_1('#skF_1'('#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_368])).
% 8.53/2.88  tff(c_40, plain, (![B_21, A_20]: (v1_xboole_0(B_21) | ~m1_subset_1(B_21, A_20) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.53/2.88  tff(c_1721, plain, (v1_xboole_0('#skF_1'('#skF_7')) | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_1660, c_40])).
% 8.53/2.88  tff(c_1726, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_1721])).
% 8.53/2.88  tff(c_3278, plain, (![B_304, A_305]: (r1_tarski(B_304, A_305) | ~m1_subset_1(B_304, k1_zfmisc_1(A_305)) | v1_xboole_0(k1_zfmisc_1(A_305)))), inference(resolution, [status(thm)], [c_225, c_22])).
% 8.53/2.88  tff(c_3315, plain, (r1_tarski('#skF_8', '#skF_6') | v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_44, c_3278])).
% 8.53/2.88  tff(c_3331, plain, (r1_tarski('#skF_8', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_68, c_3315])).
% 8.53/2.88  tff(c_3863, plain, (![B_347, B_348, A_349]: (r2_hidden(B_347, B_348) | ~r1_tarski(A_349, B_348) | ~m1_subset_1(B_347, A_349) | v1_xboole_0(A_349))), inference(resolution, [status(thm)], [c_36, c_261])).
% 8.53/2.88  tff(c_3871, plain, (![B_347]: (r2_hidden(B_347, '#skF_6') | ~m1_subset_1(B_347, '#skF_8') | v1_xboole_0('#skF_8'))), inference(resolution, [status(thm)], [c_3331, c_3863])).
% 8.53/2.88  tff(c_3941, plain, (![B_351]: (r2_hidden(B_351, '#skF_6') | ~m1_subset_1(B_351, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_367, c_3871])).
% 8.53/2.88  tff(c_3953, plain, (![B_351]: (m1_subset_1(B_351, '#skF_6') | v1_xboole_0('#skF_6') | ~m1_subset_1(B_351, '#skF_8'))), inference(resolution, [status(thm)], [c_3941, c_34])).
% 8.53/2.88  tff(c_4091, plain, (![B_354]: (m1_subset_1(B_354, '#skF_6') | ~m1_subset_1(B_354, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_1726, c_3953])).
% 8.53/2.88  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.53/2.88  tff(c_2896, plain, (![A_265]: (r1_tarski(A_265, '#skF_7') | ~r2_hidden('#skF_2'(A_265, '#skF_7'), '#skF_8') | ~m1_subset_1('#skF_2'(A_265, '#skF_7'), '#skF_6'))), inference(resolution, [status(thm)], [c_123, c_8])).
% 8.53/2.88  tff(c_2911, plain, (~m1_subset_1('#skF_2'('#skF_8', '#skF_7'), '#skF_6') | r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_10, c_2896])).
% 8.53/2.88  tff(c_2912, plain, (~m1_subset_1('#skF_2'('#skF_8', '#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_2911])).
% 8.53/2.88  tff(c_4116, plain, (~m1_subset_1('#skF_2'('#skF_8', '#skF_7'), '#skF_8')), inference(resolution, [status(thm)], [c_4091, c_2912])).
% 8.53/2.88  tff(c_4124, plain, (v1_xboole_0('#skF_8') | r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_199, c_4116])).
% 8.53/2.88  tff(c_4131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3097, c_367, c_4124])).
% 8.53/2.88  tff(c_4133, plain, (r2_xboole_0('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_3086])).
% 8.53/2.88  tff(c_20, plain, (![A_12, B_13]: (r2_hidden('#skF_3'(A_12, B_13), B_13) | ~r2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.53/2.88  tff(c_197, plain, (![A_12, B_13]: (m1_subset_1('#skF_3'(A_12, B_13), B_13) | v1_xboole_0(B_13) | ~r2_xboole_0(A_12, B_13))), inference(resolution, [status(thm)], [c_20, c_181])).
% 8.53/2.88  tff(c_4302, plain, (![B_368, A_369]: (r1_tarski(B_368, A_369) | ~m1_subset_1(B_368, k1_zfmisc_1(A_369)) | v1_xboole_0(k1_zfmisc_1(A_369)))), inference(resolution, [status(thm)], [c_225, c_22])).
% 8.53/2.88  tff(c_4338, plain, (r1_tarski('#skF_7', '#skF_6') | v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_46, c_4302])).
% 8.53/2.88  tff(c_4353, plain, (r1_tarski('#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_68, c_4338])).
% 8.53/2.88  tff(c_4763, plain, (![B_403, B_404, A_405]: (r2_hidden(B_403, B_404) | ~r1_tarski(A_405, B_404) | ~m1_subset_1(B_403, A_405) | v1_xboole_0(A_405))), inference(resolution, [status(thm)], [c_36, c_261])).
% 8.53/2.88  tff(c_4777, plain, (![B_403]: (r2_hidden(B_403, '#skF_6') | ~m1_subset_1(B_403, '#skF_7') | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_4353, c_4763])).
% 8.53/2.88  tff(c_4824, plain, (![B_406]: (r2_hidden(B_406, '#skF_6') | ~m1_subset_1(B_406, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_224, c_4777])).
% 8.53/2.88  tff(c_4836, plain, (![B_406]: (m1_subset_1(B_406, '#skF_6') | v1_xboole_0('#skF_6') | ~m1_subset_1(B_406, '#skF_7'))), inference(resolution, [status(thm)], [c_4824, c_34])).
% 8.53/2.88  tff(c_4880, plain, (![B_408]: (m1_subset_1(B_408, '#skF_6') | ~m1_subset_1(B_408, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_1726, c_4836])).
% 8.53/2.88  tff(c_4888, plain, (![A_12]: (m1_subset_1('#skF_3'(A_12, '#skF_7'), '#skF_6') | v1_xboole_0('#skF_7') | ~r2_xboole_0(A_12, '#skF_7'))), inference(resolution, [status(thm)], [c_197, c_4880])).
% 8.53/2.88  tff(c_5379, plain, (![A_432]: (m1_subset_1('#skF_3'(A_432, '#skF_7'), '#skF_6') | ~r2_xboole_0(A_432, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_224, c_4888])).
% 8.53/2.88  tff(c_4132, plain, (~m1_subset_1('#skF_3'('#skF_8', '#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_3086])).
% 8.53/2.88  tff(c_5382, plain, (~r2_xboole_0('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_5379, c_4132])).
% 8.53/2.88  tff(c_5393, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4133, c_5382])).
% 8.53/2.88  tff(c_5394, plain, (r1_tarski('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_2911])).
% 8.53/2.88  tff(c_5441, plain, (![A_437]: (r2_hidden('#skF_3'(A_437, '#skF_7'), '#skF_8') | ~m1_subset_1('#skF_3'(A_437, '#skF_7'), '#skF_6') | ~r2_xboole_0(A_437, '#skF_7'))), inference(resolution, [status(thm)], [c_151, c_50])).
% 8.53/2.88  tff(c_5462, plain, (~m1_subset_1('#skF_3'('#skF_8', '#skF_7'), '#skF_6') | ~r2_xboole_0('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_5441, c_18])).
% 8.53/2.88  tff(c_5467, plain, (~r2_xboole_0('#skF_8', '#skF_7')), inference(splitLeft, [status(thm)], [c_5462])).
% 8.53/2.88  tff(c_5470, plain, ('#skF_7'='#skF_8' | ~r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_12, c_5467])).
% 8.53/2.88  tff(c_5473, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_5394, c_5470])).
% 8.53/2.88  tff(c_5475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_5473])).
% 8.53/2.88  tff(c_5477, plain, (r2_xboole_0('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_5462])).
% 8.53/2.88  tff(c_5676, plain, (![B_456, A_457]: (r1_tarski(B_456, A_457) | ~m1_subset_1(B_456, k1_zfmisc_1(A_457)) | v1_xboole_0(k1_zfmisc_1(A_457)))), inference(resolution, [status(thm)], [c_225, c_22])).
% 8.53/2.88  tff(c_5702, plain, (r1_tarski('#skF_7', '#skF_6') | v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_46, c_5676])).
% 8.53/2.88  tff(c_5713, plain, (r1_tarski('#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_68, c_5702])).
% 8.53/2.88  tff(c_6501, plain, (![B_521, B_522, A_523]: (r2_hidden(B_521, B_522) | ~r1_tarski(A_523, B_522) | ~m1_subset_1(B_521, A_523) | v1_xboole_0(A_523))), inference(resolution, [status(thm)], [c_36, c_261])).
% 8.53/2.88  tff(c_6513, plain, (![B_521]: (r2_hidden(B_521, '#skF_6') | ~m1_subset_1(B_521, '#skF_7') | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_5713, c_6501])).
% 8.53/2.88  tff(c_6572, plain, (![B_524]: (r2_hidden(B_524, '#skF_6') | ~m1_subset_1(B_524, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_224, c_6513])).
% 8.53/2.88  tff(c_6584, plain, (![B_524]: (m1_subset_1(B_524, '#skF_6') | v1_xboole_0('#skF_6') | ~m1_subset_1(B_524, '#skF_7'))), inference(resolution, [status(thm)], [c_6572, c_34])).
% 8.53/2.88  tff(c_6742, plain, (![B_529]: (m1_subset_1(B_529, '#skF_6') | ~m1_subset_1(B_529, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_1726, c_6584])).
% 8.53/2.88  tff(c_6750, plain, (![A_12]: (m1_subset_1('#skF_3'(A_12, '#skF_7'), '#skF_6') | v1_xboole_0('#skF_7') | ~r2_xboole_0(A_12, '#skF_7'))), inference(resolution, [status(thm)], [c_197, c_6742])).
% 8.53/2.88  tff(c_7091, plain, (![A_544]: (m1_subset_1('#skF_3'(A_544, '#skF_7'), '#skF_6') | ~r2_xboole_0(A_544, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_224, c_6750])).
% 8.53/2.88  tff(c_5476, plain, (~m1_subset_1('#skF_3'('#skF_8', '#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_5462])).
% 8.53/2.88  tff(c_7098, plain, (~r2_xboole_0('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_7091, c_5476])).
% 8.53/2.88  tff(c_7107, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5477, c_7098])).
% 8.53/2.88  tff(c_7109, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_1721])).
% 8.53/2.88  tff(c_112, plain, (![A_48, B_49]: (~r2_hidden('#skF_2'(A_48, B_49), B_49) | r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.53/2.88  tff(c_121, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_112])).
% 8.53/2.88  tff(c_86, plain, (![C_42, A_43]: (r1_tarski(C_42, A_43) | ~r2_hidden(C_42, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.53/2.88  tff(c_95, plain, (![A_43]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_43)), A_43) | v1_xboole_0(k1_zfmisc_1(A_43)))), inference(resolution, [status(thm)], [c_4, c_86])).
% 8.53/2.88  tff(c_328, plain, (![B_77, A_78]: (~v1_xboole_0(B_77) | ~r1_tarski(A_78, B_77) | v1_xboole_0(A_78))), inference(resolution, [status(thm)], [c_280, c_2])).
% 8.53/2.88  tff(c_7589, plain, (![A_571]: (~v1_xboole_0(A_571) | v1_xboole_0('#skF_1'(k1_zfmisc_1(A_571))) | v1_xboole_0(k1_zfmisc_1(A_571)))), inference(resolution, [status(thm)], [c_95, c_328])).
% 8.53/2.88  tff(c_96, plain, (![A_44, B_45]: (r2_hidden('#skF_2'(A_44, B_45), A_44) | r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.53/2.88  tff(c_110, plain, (![A_44, B_45]: (~v1_xboole_0(A_44) | r1_tarski(A_44, B_45))), inference(resolution, [status(thm)], [c_96, c_2])).
% 8.53/2.88  tff(c_166, plain, (![B_56, A_57]: (~v1_xboole_0(B_56) | ~r2_xboole_0(A_57, B_56))), inference(resolution, [status(thm)], [c_151, c_2])).
% 8.53/2.88  tff(c_171, plain, (![B_58, A_59]: (~v1_xboole_0(B_58) | B_58=A_59 | ~r1_tarski(A_59, B_58))), inference(resolution, [status(thm)], [c_12, c_166])).
% 8.53/2.88  tff(c_180, plain, (![B_45, A_44]: (~v1_xboole_0(B_45) | B_45=A_44 | ~v1_xboole_0(A_44))), inference(resolution, [status(thm)], [c_110, c_171])).
% 8.53/2.88  tff(c_7112, plain, (![A_44]: (A_44='#skF_6' | ~v1_xboole_0(A_44))), inference(resolution, [status(thm)], [c_7109, c_180])).
% 8.53/2.88  tff(c_7705, plain, (![A_578]: ('#skF_1'(k1_zfmisc_1(A_578))='#skF_6' | ~v1_xboole_0(A_578) | v1_xboole_0(k1_zfmisc_1(A_578)))), inference(resolution, [status(thm)], [c_7589, c_7112])).
% 8.53/2.88  tff(c_80, plain, (![C_38, A_39]: (r2_hidden(C_38, k1_zfmisc_1(A_39)) | ~r1_tarski(C_38, A_39))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.53/2.88  tff(c_84, plain, (![A_39, C_38]: (~v1_xboole_0(k1_zfmisc_1(A_39)) | ~r1_tarski(C_38, A_39))), inference(resolution, [status(thm)], [c_80, c_2])).
% 8.53/2.88  tff(c_7784, plain, (![C_582, A_583]: (~r1_tarski(C_582, A_583) | '#skF_1'(k1_zfmisc_1(A_583))='#skF_6' | ~v1_xboole_0(A_583))), inference(resolution, [status(thm)], [c_7705, c_84])).
% 8.53/2.88  tff(c_7813, plain, (![A_586]: ('#skF_1'(k1_zfmisc_1(A_586))='#skF_6' | ~v1_xboole_0(A_586))), inference(resolution, [status(thm)], [c_121, c_7784])).
% 8.53/2.88  tff(c_7856, plain, (![A_587]: (r1_tarski('#skF_6', A_587) | v1_xboole_0(k1_zfmisc_1(A_587)) | ~v1_xboole_0(A_587))), inference(superposition, [status(thm), theory('equality')], [c_7813, c_95])).
% 8.53/2.88  tff(c_7923, plain, (![C_590, A_591]: (~r1_tarski(C_590, A_591) | r1_tarski('#skF_6', A_591) | ~v1_xboole_0(A_591))), inference(resolution, [status(thm)], [c_7856, c_84])).
% 8.53/2.88  tff(c_7940, plain, (![A_5]: (r1_tarski('#skF_6', A_5) | ~v1_xboole_0(A_5))), inference(resolution, [status(thm)], [c_121, c_7923])).
% 8.53/2.88  tff(c_7108, plain, (v1_xboole_0('#skF_1'('#skF_7'))), inference(splitRight, [status(thm)], [c_1721])).
% 8.53/2.88  tff(c_7116, plain, (![A_545]: (A_545='#skF_6' | ~v1_xboole_0(A_545))), inference(resolution, [status(thm)], [c_7109, c_180])).
% 8.53/2.88  tff(c_7123, plain, ('#skF_1'('#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_7108, c_7116])).
% 8.53/2.88  tff(c_1659, plain, (r2_hidden('#skF_1'('#skF_7'), '#skF_8')), inference(splitRight, [status(thm)], [c_368])).
% 8.53/2.88  tff(c_7129, plain, (r2_hidden('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_7123, c_1659])).
% 8.53/2.88  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.53/2.88  tff(c_7351, plain, (![B_555]: (r2_hidden('#skF_6', B_555) | ~r1_tarski('#skF_8', B_555))), inference(resolution, [status(thm)], [c_7129, c_6])).
% 8.53/2.88  tff(c_7967, plain, (![B_595, B_596]: (r2_hidden('#skF_6', B_595) | ~r1_tarski(B_596, B_595) | ~r1_tarski('#skF_8', B_596))), inference(resolution, [status(thm)], [c_7351, c_6])).
% 8.53/2.88  tff(c_7980, plain, (![A_5]: (r2_hidden('#skF_6', A_5) | ~r1_tarski('#skF_8', '#skF_6') | ~v1_xboole_0(A_5))), inference(resolution, [status(thm)], [c_7940, c_7967])).
% 8.53/2.88  tff(c_7986, plain, (~r1_tarski('#skF_8', '#skF_6')), inference(splitLeft, [status(thm)], [c_7980])).
% 8.53/2.88  tff(c_8095, plain, (![B_611, A_612]: (r1_tarski(B_611, A_612) | ~m1_subset_1(B_611, k1_zfmisc_1(A_612)) | v1_xboole_0(k1_zfmisc_1(A_612)))), inference(resolution, [status(thm)], [c_225, c_22])).
% 8.53/2.88  tff(c_8126, plain, (r1_tarski('#skF_8', '#skF_6') | v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_44, c_8095])).
% 8.53/2.88  tff(c_8144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_7986, c_8126])).
% 8.53/2.88  tff(c_8146, plain, (r1_tarski('#skF_8', '#skF_6')), inference(splitRight, [status(thm)], [c_7980])).
% 8.53/2.88  tff(c_7387, plain, (![B_555]: (~v1_xboole_0(B_555) | ~r1_tarski('#skF_8', B_555))), inference(resolution, [status(thm)], [c_7351, c_2])).
% 8.53/2.88  tff(c_8154, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_8146, c_7387])).
% 8.53/2.88  tff(c_8169, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7109, c_8154])).
% 8.53/2.88  tff(c_8171, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_366])).
% 8.53/2.88  tff(c_8198, plain, (![B_616]: (~m1_subset_1(B_616, '#skF_6') | ~m1_subset_1(B_616, '#skF_7'))), inference(splitRight, [status(thm)], [c_366])).
% 8.53/2.88  tff(c_8202, plain, (~m1_subset_1('#skF_1'('#skF_7'), '#skF_6') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_201, c_8198])).
% 8.53/2.88  tff(c_8209, plain, (~m1_subset_1('#skF_1'('#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_224, c_8202])).
% 8.53/2.88  tff(c_8214, plain, (~v1_xboole_0('#skF_1'('#skF_7')) | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_38, c_8209])).
% 8.53/2.88  tff(c_8216, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_8214])).
% 8.53/2.88  tff(c_8587, plain, (![B_646, A_647]: (r1_tarski(B_646, A_647) | ~m1_subset_1(B_646, k1_zfmisc_1(A_647)) | v1_xboole_0(k1_zfmisc_1(A_647)))), inference(resolution, [status(thm)], [c_225, c_22])).
% 8.53/2.88  tff(c_8607, plain, (r1_tarski('#skF_7', '#skF_6') | v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_46, c_8587])).
% 8.53/2.88  tff(c_8618, plain, (r1_tarski('#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_68, c_8607])).
% 8.53/2.88  tff(c_9017, plain, (![B_691, B_692, A_693]: (r2_hidden(B_691, B_692) | ~r1_tarski(A_693, B_692) | ~m1_subset_1(B_691, A_693) | v1_xboole_0(A_693))), inference(resolution, [status(thm)], [c_36, c_261])).
% 8.53/2.88  tff(c_9031, plain, (![B_691]: (r2_hidden(B_691, '#skF_6') | ~m1_subset_1(B_691, '#skF_7') | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_8618, c_9017])).
% 8.53/2.88  tff(c_9059, plain, (![B_696]: (r2_hidden(B_696, '#skF_6') | ~m1_subset_1(B_696, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_224, c_9031])).
% 8.53/2.88  tff(c_9071, plain, (![B_696]: (m1_subset_1(B_696, '#skF_6') | v1_xboole_0('#skF_6') | ~m1_subset_1(B_696, '#skF_7'))), inference(resolution, [status(thm)], [c_9059, c_34])).
% 8.53/2.88  tff(c_9087, plain, (![B_697]: (m1_subset_1(B_697, '#skF_6') | ~m1_subset_1(B_697, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_8216, c_9071])).
% 8.53/2.88  tff(c_9099, plain, (m1_subset_1('#skF_1'('#skF_7'), '#skF_6') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_201, c_9087])).
% 8.53/2.88  tff(c_9113, plain, $false, inference(negUnitSimplification, [status(thm)], [c_224, c_8209, c_9099])).
% 8.53/2.88  tff(c_9115, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_8214])).
% 8.53/2.88  tff(c_8174, plain, (![A_44]: (A_44='#skF_8' | ~v1_xboole_0(A_44))), inference(resolution, [status(thm)], [c_8171, c_180])).
% 8.53/2.88  tff(c_9155, plain, ('#skF_6'='#skF_8'), inference(resolution, [status(thm)], [c_9115, c_8174])).
% 8.53/2.88  tff(c_9162, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_9155, c_68])).
% 8.53/2.88  tff(c_48, plain, (![D_26]: (r2_hidden(D_26, '#skF_7') | ~r2_hidden(D_26, '#skF_8') | ~m1_subset_1(D_26, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.53/2.88  tff(c_208, plain, (![A_65, B_66]: (~r2_hidden('#skF_3'(A_65, B_66), A_65) | ~r2_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.53/2.88  tff(c_222, plain, (![B_66]: (~r2_xboole_0('#skF_7', B_66) | ~r2_hidden('#skF_3'('#skF_7', B_66), '#skF_8') | ~m1_subset_1('#skF_3'('#skF_7', B_66), '#skF_6'))), inference(resolution, [status(thm)], [c_48, c_208])).
% 8.53/2.88  tff(c_9748, plain, (![B_735]: (~r2_xboole_0('#skF_7', B_735) | ~r2_hidden('#skF_3'('#skF_7', B_735), '#skF_8') | ~m1_subset_1('#skF_3'('#skF_7', B_735), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_9155, c_222])).
% 8.53/2.88  tff(c_9763, plain, (~m1_subset_1('#skF_3'('#skF_7', '#skF_8'), '#skF_8') | ~r2_xboole_0('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_20, c_9748])).
% 8.53/2.88  tff(c_9772, plain, (~r2_xboole_0('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_9763])).
% 8.53/2.88  tff(c_9775, plain, ('#skF_7'='#skF_8' | ~r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_12, c_9772])).
% 8.53/2.88  tff(c_9778, plain, (~r1_tarski('#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_42, c_9775])).
% 8.53/2.88  tff(c_9165, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_9155, c_46])).
% 8.53/2.88  tff(c_9860, plain, (![B_754, A_755]: (r1_tarski(B_754, A_755) | ~m1_subset_1(B_754, k1_zfmisc_1(A_755)) | v1_xboole_0(k1_zfmisc_1(A_755)))), inference(resolution, [status(thm)], [c_225, c_22])).
% 8.53/2.88  tff(c_9880, plain, (r1_tarski('#skF_7', '#skF_8') | v1_xboole_0(k1_zfmisc_1('#skF_8'))), inference(resolution, [status(thm)], [c_9165, c_9860])).
% 8.53/2.88  tff(c_9900, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9162, c_9778, c_9880])).
% 8.53/2.88  tff(c_9902, plain, (r2_xboole_0('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_9763])).
% 8.53/2.88  tff(c_165, plain, (![B_55, A_54]: (~v1_xboole_0(B_55) | ~r2_xboole_0(A_54, B_55))), inference(resolution, [status(thm)], [c_151, c_2])).
% 8.53/2.88  tff(c_9906, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_9902, c_165])).
% 8.53/2.88  tff(c_9913, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8171, c_9906])).
% 8.53/2.88  tff(c_9925, plain, (![D_757]: (~r2_hidden(D_757, '#skF_8') | ~m1_subset_1(D_757, '#skF_6'))), inference(splitRight, [status(thm)], [c_136])).
% 8.53/2.88  tff(c_9940, plain, (~m1_subset_1('#skF_1'('#skF_8'), '#skF_6') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_4, c_9925])).
% 8.53/2.88  tff(c_9941, plain, (~m1_subset_1('#skF_1'('#skF_8'), '#skF_6')), inference(splitLeft, [status(thm)], [c_9940])).
% 8.53/2.88  tff(c_9980, plain, (~v1_xboole_0('#skF_1'('#skF_8')) | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_38, c_9941])).
% 8.53/2.88  tff(c_9981, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_9980])).
% 8.53/2.88  tff(c_9942, plain, (![B_758, A_759]: (r2_hidden(B_758, A_759) | ~m1_subset_1(B_758, A_759) | v1_xboole_0(A_759))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.53/2.88  tff(c_9914, plain, (![D_50]: (~r2_hidden(D_50, '#skF_8') | ~m1_subset_1(D_50, '#skF_6'))), inference(splitRight, [status(thm)], [c_136])).
% 8.53/2.88  tff(c_9969, plain, (![B_758]: (~m1_subset_1(B_758, '#skF_6') | ~m1_subset_1(B_758, '#skF_8') | v1_xboole_0('#skF_8'))), inference(resolution, [status(thm)], [c_9942, c_9914])).
% 8.53/2.88  tff(c_9989, plain, (![B_761]: (~m1_subset_1(B_761, '#skF_6') | ~m1_subset_1(B_761, '#skF_8'))), inference(splitLeft, [status(thm)], [c_9969])).
% 8.53/2.88  tff(c_9993, plain, (~m1_subset_1('#skF_1'('#skF_6'), '#skF_8') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_201, c_9989])).
% 8.53/2.88  tff(c_10000, plain, (~m1_subset_1('#skF_1'('#skF_6'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_9981, c_9993])).
% 8.53/2.88  tff(c_10005, plain, (~v1_xboole_0('#skF_1'('#skF_6')) | ~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_38, c_10000])).
% 8.53/2.88  tff(c_10006, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_10005])).
% 8.53/2.88  tff(c_10523, plain, (![B_811, A_812]: (r1_tarski(B_811, A_812) | ~m1_subset_1(B_811, k1_zfmisc_1(A_812)) | v1_xboole_0(k1_zfmisc_1(A_812)))), inference(resolution, [status(thm)], [c_9942, c_22])).
% 8.53/2.88  tff(c_10543, plain, (r1_tarski('#skF_8', '#skF_6') | v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_44, c_10523])).
% 8.53/2.88  tff(c_10555, plain, (r1_tarski('#skF_8', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_68, c_10543])).
% 8.53/2.88  tff(c_10007, plain, (![C_762, B_763, A_764]: (r2_hidden(C_762, B_763) | ~r2_hidden(C_762, A_764) | ~r1_tarski(A_764, B_763))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.53/2.88  tff(c_10797, plain, (![B_842, B_843, A_844]: (r2_hidden(B_842, B_843) | ~r1_tarski(A_844, B_843) | ~m1_subset_1(B_842, A_844) | v1_xboole_0(A_844))), inference(resolution, [status(thm)], [c_36, c_10007])).
% 8.53/2.88  tff(c_10803, plain, (![B_842]: (r2_hidden(B_842, '#skF_6') | ~m1_subset_1(B_842, '#skF_8') | v1_xboole_0('#skF_8'))), inference(resolution, [status(thm)], [c_10555, c_10797])).
% 8.53/2.88  tff(c_10840, plain, (![B_847]: (r2_hidden(B_847, '#skF_6') | ~m1_subset_1(B_847, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_10006, c_10803])).
% 8.53/2.88  tff(c_10852, plain, (![B_847]: (m1_subset_1(B_847, '#skF_6') | v1_xboole_0('#skF_6') | ~m1_subset_1(B_847, '#skF_8'))), inference(resolution, [status(thm)], [c_10840, c_34])).
% 8.53/2.88  tff(c_10868, plain, (![B_848]: (m1_subset_1(B_848, '#skF_6') | ~m1_subset_1(B_848, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_9981, c_10852])).
% 8.53/2.88  tff(c_9988, plain, (![B_758]: (~m1_subset_1(B_758, '#skF_6') | ~m1_subset_1(B_758, '#skF_8'))), inference(splitLeft, [status(thm)], [c_9969])).
% 8.53/2.88  tff(c_10946, plain, (![B_851]: (~m1_subset_1(B_851, '#skF_8'))), inference(resolution, [status(thm)], [c_10868, c_9988])).
% 8.53/2.88  tff(c_10958, plain, (v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_201, c_10946])).
% 8.53/2.88  tff(c_10972, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10006, c_10958])).
% 8.53/2.88  tff(c_10974, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_10005])).
% 8.53/2.88  tff(c_9915, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_136])).
% 8.53/2.88  tff(c_9918, plain, (![A_44]: (A_44='#skF_7' | ~v1_xboole_0(A_44))), inference(resolution, [status(thm)], [c_9915, c_180])).
% 8.53/2.88  tff(c_10977, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_10974, c_9918])).
% 8.53/2.88  tff(c_10983, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_10977])).
% 8.53/2.88  tff(c_10984, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_9969])).
% 8.53/2.88  tff(c_10987, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_10984, c_9918])).
% 8.53/2.88  tff(c_10993, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_10987])).
% 8.53/2.88  tff(c_10995, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_9980])).
% 8.53/2.88  tff(c_11001, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_10995, c_9918])).
% 8.53/2.88  tff(c_11007, plain, ('#skF_6'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_11001, c_42])).
% 8.53/2.88  tff(c_11046, plain, (![B_857]: (~m1_subset_1(B_857, '#skF_6') | ~m1_subset_1(B_857, '#skF_8'))), inference(splitLeft, [status(thm)], [c_9969])).
% 8.53/2.88  tff(c_11054, plain, (![B_21]: (~m1_subset_1(B_21, '#skF_8') | ~v1_xboole_0(B_21) | ~v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_38, c_11046])).
% 8.53/2.88  tff(c_11060, plain, (![B_858]: (~m1_subset_1(B_858, '#skF_8') | ~v1_xboole_0(B_858))), inference(demodulation, [status(thm), theory('equality')], [c_10995, c_11054])).
% 8.53/2.88  tff(c_11070, plain, (![B_21]: (~v1_xboole_0(B_21) | ~v1_xboole_0('#skF_8'))), inference(resolution, [status(thm)], [c_38, c_11060])).
% 8.53/2.88  tff(c_11097, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_11070])).
% 8.53/2.88  tff(c_11793, plain, (![B_931, A_932]: (r1_tarski(B_931, A_932) | ~m1_subset_1(B_931, k1_zfmisc_1(A_932)) | v1_xboole_0(k1_zfmisc_1(A_932)))), inference(resolution, [status(thm)], [c_9942, c_22])).
% 8.53/2.88  tff(c_11824, plain, (r1_tarski('#skF_8', '#skF_6') | v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_44, c_11793])).
% 8.53/2.88  tff(c_11838, plain, (r1_tarski('#skF_8', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_68, c_11824])).
% 8.53/2.88  tff(c_11013, plain, (![C_852, B_853, A_854]: (r2_hidden(C_852, B_853) | ~r2_hidden(C_852, A_854) | ~r1_tarski(A_854, B_853))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.53/2.88  tff(c_11142, plain, (![A_866, B_867]: (r2_hidden('#skF_1'(A_866), B_867) | ~r1_tarski(A_866, B_867) | v1_xboole_0(A_866))), inference(resolution, [status(thm)], [c_4, c_11013])).
% 8.53/2.88  tff(c_11168, plain, (![B_867, A_866]: (~v1_xboole_0(B_867) | ~r1_tarski(A_866, B_867) | v1_xboole_0(A_866))), inference(resolution, [status(thm)], [c_11142, c_2])).
% 8.53/2.88  tff(c_11841, plain, (~v1_xboole_0('#skF_6') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_11838, c_11168])).
% 8.53/2.88  tff(c_11847, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_10995, c_11841])).
% 8.53/2.88  tff(c_11849, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11097, c_11847])).
% 8.53/2.88  tff(c_11851, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_11070])).
% 8.53/2.88  tff(c_11002, plain, (![A_44]: (A_44='#skF_6' | ~v1_xboole_0(A_44))), inference(resolution, [status(thm)], [c_10995, c_180])).
% 8.53/2.88  tff(c_11854, plain, ('#skF_6'='#skF_8'), inference(resolution, [status(thm)], [c_11851, c_11002])).
% 8.53/2.88  tff(c_11860, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11007, c_11854])).
% 8.53/2.88  tff(c_11862, plain, (v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(splitRight, [status(thm)], [c_66])).
% 8.53/2.88  tff(c_11863, plain, (![C_933, A_934]: (r2_hidden(C_933, k1_zfmisc_1(A_934)) | ~r1_tarski(C_933, A_934))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.53/2.88  tff(c_11877, plain, (![A_936, C_937]: (~v1_xboole_0(k1_zfmisc_1(A_936)) | ~r1_tarski(C_937, A_936))), inference(resolution, [status(thm)], [c_11863, c_2])).
% 8.53/2.88  tff(c_11880, plain, (![C_937]: (~r1_tarski(C_937, '#skF_6'))), inference(resolution, [status(thm)], [c_11862, c_11877])).
% 8.53/2.88  tff(c_11923, plain, (![A_946]: (~v1_xboole_0(A_946))), inference(resolution, [status(thm)], [c_11919, c_11880])).
% 8.53/2.88  tff(c_67, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_46, c_59])).
% 8.53/2.88  tff(c_11869, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_11862, c_67])).
% 8.53/2.88  tff(c_11929, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11923, c_11869])).
% 8.53/2.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.53/2.88  
% 8.53/2.88  Inference rules
% 8.53/2.88  ----------------------
% 8.53/2.88  #Ref     : 0
% 8.53/2.88  #Sup     : 2625
% 8.53/2.88  #Fact    : 0
% 8.53/2.88  #Define  : 0
% 8.53/2.88  #Split   : 57
% 8.53/2.88  #Chain   : 0
% 8.53/2.88  #Close   : 0
% 8.53/2.88  
% 8.53/2.88  Ordering : KBO
% 8.53/2.88  
% 8.53/2.88  Simplification rules
% 8.53/2.88  ----------------------
% 8.53/2.88  #Subsume      : 861
% 8.53/2.88  #Demod        : 424
% 8.53/2.88  #Tautology    : 381
% 8.53/2.88  #SimpNegUnit  : 337
% 8.53/2.88  #BackRed      : 35
% 8.53/2.88  
% 8.53/2.88  #Partial instantiations: 0
% 8.53/2.88  #Strategies tried      : 1
% 8.53/2.88  
% 8.53/2.88  Timing (in seconds)
% 8.53/2.88  ----------------------
% 8.53/2.88  Preprocessing        : 0.30
% 8.53/2.88  Parsing              : 0.15
% 8.53/2.88  CNF conversion       : 0.03
% 8.53/2.88  Main loop            : 1.75
% 8.53/2.88  Inferencing          : 0.61
% 8.53/2.88  Reduction            : 0.45
% 8.53/2.88  Demodulation         : 0.27
% 8.53/2.89  BG Simplification    : 0.06
% 8.53/2.89  Subsumption          : 0.47
% 8.53/2.89  Abstraction          : 0.07
% 8.53/2.89  MUC search           : 0.00
% 8.53/2.89  Cooper               : 0.00
% 8.53/2.89  Total                : 2.14
% 8.53/2.89  Index Insertion      : 0.00
% 8.53/2.89  Index Deletion       : 0.00
% 8.53/2.89  Index Matching       : 0.00
% 8.53/2.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
