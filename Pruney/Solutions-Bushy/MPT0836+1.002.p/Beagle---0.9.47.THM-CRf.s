%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0836+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:55 EST 2020

% Result     : Theorem 7.54s
% Output     : CNFRefutation 7.54s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 276 expanded)
%              Number of leaves         :   30 ( 102 expanded)
%              Depth                    :    9
%              Number of atoms          :  189 ( 687 expanded)
%              Number of equality atoms :    8 (  26 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ! [D] :
                    ( m1_subset_1(D,A)
                   => ( r2_hidden(D,k1_relset_1(A,B,C))
                    <=> ? [E] :
                          ( m1_subset_1(E,B)
                          & r2_hidden(k4_tarski(D,E),C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_35,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_6304,plain,(
    ! [A_529,B_530,C_531] :
      ( k1_relset_1(A_529,B_530,C_531) = k1_relat_1(C_531)
      | ~ m1_subset_1(C_531,k1_zfmisc_1(k2_zfmisc_1(A_529,B_530))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6312,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_34,c_6304])).

tff(c_3625,plain,(
    ! [A_317,B_318,C_319] :
      ( k1_relset_1(A_317,B_318,C_319) = k1_relat_1(C_319)
      | ~ m1_subset_1(C_319,k1_zfmisc_1(k2_zfmisc_1(A_317,B_318))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3633,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_34,c_3625])).

tff(c_50,plain,
    ( r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8'))
    | m1_subset_1('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_63,plain,(
    m1_subset_1('#skF_10','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_46,plain,
    ( r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8'))
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_3392,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_4,plain,(
    ! [C_16,A_1,D_19] :
      ( r2_hidden(C_16,k1_relat_1(A_1))
      | ~ r2_hidden(k4_tarski(C_16,D_19),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3402,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_3392,c_4])).

tff(c_3413,plain,(
    ! [A_290,B_291,C_292] :
      ( k1_relset_1(A_290,B_291,C_292) = k1_relat_1(C_292)
      | ~ m1_subset_1(C_292,k1_zfmisc_1(k2_zfmisc_1(A_290,B_291))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3421,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_34,c_3413])).

tff(c_40,plain,(
    ! [E_79] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_79),'#skF_8')
      | ~ m1_subset_1(E_79,'#skF_7')
      | ~ r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8')) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_3592,plain,(
    ! [E_316] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_316),'#skF_8')
      | ~ m1_subset_1(E_316,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3402,c_3421,c_40])).

tff(c_3599,plain,(
    ~ m1_subset_1('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_3392,c_3592])).

tff(c_3609,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_3599])).

tff(c_3610,plain,(
    r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_3637,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3633,c_3610])).

tff(c_2,plain,(
    ! [C_16,A_1] :
      ( r2_hidden(k4_tarski(C_16,'#skF_4'(A_1,k1_relat_1(A_1),C_16)),A_1)
      | ~ r2_hidden(C_16,k1_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_26,plain,(
    ! [A_31,B_32] :
      ( r2_hidden(A_31,B_32)
      | v1_xboole_0(B_32)
      | ~ m1_subset_1(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_38,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_3367,plain,(
    ! [A_276,C_277,B_278] :
      ( m1_subset_1(A_276,C_277)
      | ~ m1_subset_1(B_278,k1_zfmisc_1(C_277))
      | ~ r2_hidden(A_276,B_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3373,plain,(
    ! [A_276] :
      ( m1_subset_1(A_276,k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ r2_hidden(A_276,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_34,c_3367])).

tff(c_3361,plain,(
    ! [C_273,A_274,D_275] :
      ( r2_hidden(C_273,k1_relat_1(A_274))
      | ~ r2_hidden(k4_tarski(C_273,D_275),A_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3681,plain,(
    ! [C_330,B_331,D_332] :
      ( r2_hidden(C_330,k1_relat_1(B_331))
      | v1_xboole_0(B_331)
      | ~ m1_subset_1(k4_tarski(C_330,D_332),B_331) ) ),
    inference(resolution,[status(thm)],[c_26,c_3361])).

tff(c_3685,plain,(
    ! [C_330,D_332] :
      ( r2_hidden(C_330,k1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ r2_hidden(k4_tarski(C_330,D_332),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_3373,c_3681])).

tff(c_3821,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_3685])).

tff(c_3659,plain,(
    ! [A_322,B_323,C_324,D_325] :
      ( r2_hidden(k4_tarski(A_322,B_323),k2_zfmisc_1(C_324,D_325))
      | ~ r2_hidden(B_323,D_325)
      | ~ r2_hidden(A_322,C_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_30,plain,(
    ! [B_37,A_36] :
      ( ~ v1_xboole_0(B_37)
      | ~ r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3679,plain,(
    ! [C_324,D_325,B_323,A_322] :
      ( ~ v1_xboole_0(k2_zfmisc_1(C_324,D_325))
      | ~ r2_hidden(B_323,D_325)
      | ~ r2_hidden(A_322,C_324) ) ),
    inference(resolution,[status(thm)],[c_3659,c_30])).

tff(c_3824,plain,(
    ! [B_323,A_322] :
      ( ~ r2_hidden(B_323,'#skF_7')
      | ~ r2_hidden(A_322,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_3821,c_3679])).

tff(c_3826,plain,(
    ! [A_352] : ~ r2_hidden(A_352,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_3824])).

tff(c_3838,plain,(
    ! [A_31] :
      ( v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_31,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_26,c_3826])).

tff(c_3843,plain,(
    ! [A_31] : ~ m1_subset_1(A_31,'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_3838])).

tff(c_32,plain,(
    m1_subset_1('#skF_9','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_3845,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3843,c_32])).

tff(c_3847,plain,(
    ! [B_353] : ~ r2_hidden(B_353,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_3824])).

tff(c_3859,plain,(
    ! [A_31] :
      ( v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_31,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_26,c_3847])).

tff(c_3864,plain,(
    ! [A_31] : ~ m1_subset_1(A_31,'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_3859])).

tff(c_3875,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3864,c_63])).

tff(c_3877,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_3685])).

tff(c_3387,plain,(
    ! [B_286,D_287,A_288,C_289] :
      ( r2_hidden(B_286,D_287)
      | ~ r2_hidden(k4_tarski(A_288,B_286),k2_zfmisc_1(C_289,D_287)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6142,plain,(
    ! [B_493,D_494,C_495,A_496] :
      ( r2_hidden(B_493,D_494)
      | v1_xboole_0(k2_zfmisc_1(C_495,D_494))
      | ~ m1_subset_1(k4_tarski(A_496,B_493),k2_zfmisc_1(C_495,D_494)) ) ),
    inference(resolution,[status(thm)],[c_26,c_3387])).

tff(c_6153,plain,(
    ! [B_493,A_496] :
      ( r2_hidden(B_493,'#skF_7')
      | v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ r2_hidden(k4_tarski(A_496,B_493),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_3373,c_6142])).

tff(c_6159,plain,(
    ! [B_497,A_498] :
      ( r2_hidden(B_497,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_498,B_497),'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_3877,c_6153])).

tff(c_6206,plain,(
    ! [C_503] :
      ( r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_8'),C_503),'#skF_7')
      | ~ r2_hidden(C_503,k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_2,c_6159])).

tff(c_24,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(A_29,B_30)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6241,plain,(
    ! [C_506] :
      ( m1_subset_1('#skF_4'('#skF_8',k1_relat_1('#skF_8'),C_506),'#skF_7')
      | ~ r2_hidden(C_506,k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_6206,c_24])).

tff(c_3759,plain,(
    ! [C_348,A_349] :
      ( r2_hidden(k4_tarski(C_348,'#skF_4'(A_349,k1_relat_1(A_349),C_348)),A_349)
      | ~ r2_hidden(C_348,k1_relat_1(A_349)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3611,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_44,plain,(
    ! [E_79] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_79),'#skF_8')
      | ~ m1_subset_1(E_79,'#skF_7')
      | r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_3642,plain,(
    ! [E_79] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_79),'#skF_8')
      | ~ m1_subset_1(E_79,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_3611,c_44])).

tff(c_3765,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_9'),'#skF_7')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_3759,c_3642])).

tff(c_3790,plain,(
    ~ m1_subset_1('#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_9'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3637,c_3765])).

tff(c_6244,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6241,c_3790])).

tff(c_6248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3637,c_6244])).

tff(c_6249,plain,(
    r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_6316,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6312,c_6249])).

tff(c_14,plain,(
    ! [A_20] : m1_subset_1('#skF_5'(A_20),A_20) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6271,plain,(
    ! [A_511,C_512,B_513] :
      ( m1_subset_1(A_511,C_512)
      | ~ m1_subset_1(B_513,k1_zfmisc_1(C_512))
      | ~ r2_hidden(A_511,B_513) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6277,plain,(
    ! [A_511] :
      ( m1_subset_1(A_511,k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ r2_hidden(A_511,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_34,c_6271])).

tff(c_6259,plain,(
    ! [C_507,A_508,D_509] :
      ( r2_hidden(C_507,k1_relat_1(A_508))
      | ~ r2_hidden(k4_tarski(C_507,D_509),A_508) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6299,plain,(
    ! [C_526,B_527,D_528] :
      ( r2_hidden(C_526,k1_relat_1(B_527))
      | v1_xboole_0(B_527)
      | ~ m1_subset_1(k4_tarski(C_526,D_528),B_527) ) ),
    inference(resolution,[status(thm)],[c_26,c_6259])).

tff(c_6303,plain,(
    ! [C_526,D_528] :
      ( r2_hidden(C_526,k1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ r2_hidden(k4_tarski(C_526,D_528),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_6277,c_6299])).

tff(c_6511,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_6303])).

tff(c_6454,plain,(
    ! [A_545,B_546,C_547,D_548] :
      ( r2_hidden(k4_tarski(A_545,B_546),k2_zfmisc_1(C_547,D_548))
      | ~ r2_hidden(B_546,D_548)
      | ~ r2_hidden(A_545,C_547) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6528,plain,(
    ! [C_557,D_558,B_559,A_560] :
      ( ~ v1_xboole_0(k2_zfmisc_1(C_557,D_558))
      | ~ r2_hidden(B_559,D_558)
      | ~ r2_hidden(A_560,C_557) ) ),
    inference(resolution,[status(thm)],[c_6454,c_30])).

tff(c_6531,plain,(
    ! [B_559,A_560] :
      ( ~ r2_hidden(B_559,'#skF_7')
      | ~ r2_hidden(A_560,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_6511,c_6528])).

tff(c_6533,plain,(
    ! [A_561] : ~ r2_hidden(A_561,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_6531])).

tff(c_6545,plain,(
    ! [A_31] :
      ( v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_31,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_26,c_6533])).

tff(c_6550,plain,(
    ! [A_31] : ~ m1_subset_1(A_31,'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_6545])).

tff(c_6557,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6550,c_32])).

tff(c_6559,plain,(
    ! [B_565] : ~ r2_hidden(B_565,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_6531])).

tff(c_6571,plain,(
    ! [A_31] :
      ( v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_31,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_26,c_6559])).

tff(c_6577,plain,(
    ! [A_566] : ~ m1_subset_1(A_566,'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_6571])).

tff(c_6587,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_14,c_6577])).

tff(c_6589,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_6303])).

tff(c_6286,plain,(
    ! [B_517,D_518,A_519,C_520] :
      ( r2_hidden(B_517,D_518)
      | ~ r2_hidden(k4_tarski(A_519,B_517),k2_zfmisc_1(C_520,D_518)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_9734,plain,(
    ! [B_704,D_705,C_706,A_707] :
      ( r2_hidden(B_704,D_705)
      | v1_xboole_0(k2_zfmisc_1(C_706,D_705))
      | ~ m1_subset_1(k4_tarski(A_707,B_704),k2_zfmisc_1(C_706,D_705)) ) ),
    inference(resolution,[status(thm)],[c_26,c_6286])).

tff(c_9745,plain,(
    ! [B_704,A_707] :
      ( r2_hidden(B_704,'#skF_7')
      | v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ r2_hidden(k4_tarski(A_707,B_704),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_6277,c_9734])).

tff(c_9751,plain,(
    ! [B_708,A_709] :
      ( r2_hidden(B_708,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_709,B_708),'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_6589,c_9745])).

tff(c_9774,plain,(
    ! [C_712] :
      ( r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_8'),C_712),'#skF_7')
      | ~ r2_hidden(C_712,k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_2,c_9751])).

tff(c_9866,plain,(
    ! [C_716] :
      ( m1_subset_1('#skF_4'('#skF_8',k1_relat_1('#skF_8'),C_716),'#skF_7')
      | ~ r2_hidden(C_716,k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_9774,c_24])).

tff(c_6365,plain,(
    ! [C_537,A_538] :
      ( r2_hidden(k4_tarski(C_537,'#skF_4'(A_538,k1_relat_1(A_538),C_537)),A_538)
      | ~ r2_hidden(C_537,k1_relat_1(A_538)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6250,plain,(
    ~ m1_subset_1('#skF_10','#skF_7') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,(
    ! [E_79] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_79),'#skF_8')
      | ~ m1_subset_1(E_79,'#skF_7')
      | m1_subset_1('#skF_10','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_6265,plain,(
    ! [E_79] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_79),'#skF_8')
      | ~ m1_subset_1(E_79,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_6250,c_48])).

tff(c_6381,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_9'),'#skF_7')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6365,c_6265])).

tff(c_6396,plain,(
    ~ m1_subset_1('#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_9'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6316,c_6381])).

tff(c_9869,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_9866,c_6396])).

tff(c_9873,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6316,c_9869])).

%------------------------------------------------------------------------------
