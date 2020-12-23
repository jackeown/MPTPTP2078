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
% DateTime   : Thu Dec  3 09:55:18 EST 2020

% Result     : Theorem 6.65s
% Output     : CNFRefutation 6.97s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 580 expanded)
%              Number of leaves         :   25 ( 196 expanded)
%              Depth                    :   13
%              Number of atoms          :  279 (1472 expanded)
%              Number of equality atoms :   20 ( 120 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ! [D] :
                  ( m1_subset_1(D,A)
                 => ( r2_hidden(D,B)
                  <=> r2_hidden(D,C) ) )
             => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_77,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_61,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(c_36,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r2_xboole_0(A_10,B_11)
      | B_11 = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_3'(A_12,B_13),B_13)
      | ~ r2_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_42,plain,(
    ! [D_25] :
      ( r2_hidden(D_25,'#skF_5')
      | ~ r2_hidden(D_25,'#skF_6')
      | ~ m1_subset_1(D_25,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_152,plain,(
    ! [A_53,B_54] :
      ( ~ r2_hidden('#skF_3'(A_53,B_54),A_53)
      | ~ r2_xboole_0(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1494,plain,(
    ! [B_165] :
      ( ~ r2_xboole_0('#skF_5',B_165)
      | ~ r2_hidden('#skF_3'('#skF_5',B_165),'#skF_6')
      | ~ m1_subset_1('#skF_3'('#skF_5',B_165),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_152])).

tff(c_1511,plain,
    ( ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),'#skF_4')
    | ~ r2_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_1494])).

tff(c_1516,plain,(
    ~ r2_xboole_0('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1511])).

tff(c_1519,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_12,c_1516])).

tff(c_1522,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1519])).

tff(c_127,plain,(
    ! [D_48] :
      ( r2_hidden(D_48,'#skF_5')
      | ~ r2_hidden(D_48,'#skF_6')
      | ~ m1_subset_1(D_48,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,(
    ! [D_48] :
      ( ~ v1_xboole_0('#skF_5')
      | ~ r2_hidden(D_48,'#skF_6')
      | ~ m1_subset_1(D_48,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_127,c_2])).

tff(c_221,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_268,plain,(
    ! [B_70,A_71] :
      ( m1_subset_1(B_70,A_71)
      | ~ r2_hidden(B_70,A_71)
      | v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_291,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1('#skF_2'(A_5,B_6),A_5)
      | v1_xboole_0(A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_268])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_34,plain,(
    ! [A_20] : ~ v1_xboole_0(k1_zfmisc_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_96,plain,(
    ! [B_44,A_45] :
      ( r2_hidden(B_44,A_45)
      | ~ m1_subset_1(B_44,A_45)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24,plain,(
    ! [A_17] : k3_tarski(k1_zfmisc_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_69,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(A_35,k3_tarski(B_36))
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_72,plain,(
    ! [A_35,A_17] :
      ( r1_tarski(A_35,A_17)
      | ~ r2_hidden(A_35,k1_zfmisc_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_69])).

tff(c_100,plain,(
    ! [B_44,A_17] :
      ( r1_tarski(B_44,A_17)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_17))
      | v1_xboole_0(k1_zfmisc_1(A_17)) ) ),
    inference(resolution,[status(thm)],[c_96,c_72])).

tff(c_113,plain,(
    ! [B_46,A_47] :
      ( r1_tarski(B_46,A_47)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_100])).

tff(c_126,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_113])).

tff(c_184,plain,(
    ! [A_59,B_60] :
      ( r2_xboole_0(A_59,B_60)
      | B_60 = A_59
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_163,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_3'(A_55,B_56),B_56)
      | ~ r2_xboole_0(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_182,plain,(
    ! [B_56,A_55] :
      ( ~ v1_xboole_0(B_56)
      | ~ r2_xboole_0(A_55,B_56) ) ),
    inference(resolution,[status(thm)],[c_163,c_2])).

tff(c_199,plain,(
    ! [B_61,A_62] :
      ( ~ v1_xboole_0(B_61)
      | B_61 = A_62
      | ~ r1_tarski(A_62,B_61) ) ),
    inference(resolution,[status(thm)],[c_184,c_182])).

tff(c_216,plain,
    ( ~ v1_xboole_0('#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_126,c_199])).

tff(c_220,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_216])).

tff(c_28,plain,(
    ! [B_19,A_18] :
      ( r2_hidden(B_19,A_18)
      | ~ m1_subset_1(B_19,A_18)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1120,plain,(
    ! [C_143,B_144,A_145] :
      ( r2_hidden(C_143,B_144)
      | ~ r2_hidden(C_143,A_145)
      | ~ r1_tarski(A_145,B_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3012,plain,(
    ! [B_276,B_277,A_278] :
      ( r2_hidden(B_276,B_277)
      | ~ r1_tarski(A_278,B_277)
      | ~ m1_subset_1(B_276,A_278)
      | v1_xboole_0(A_278) ) ),
    inference(resolution,[status(thm)],[c_28,c_1120])).

tff(c_3024,plain,(
    ! [B_276] :
      ( r2_hidden(B_276,'#skF_4')
      | ~ m1_subset_1(B_276,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_126,c_3012])).

tff(c_3044,plain,(
    ! [B_279] :
      ( r2_hidden(B_279,'#skF_4')
      | ~ m1_subset_1(B_279,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_3024])).

tff(c_26,plain,(
    ! [B_19,A_18] :
      ( m1_subset_1(B_19,A_18)
      | ~ r2_hidden(B_19,A_18)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_3049,plain,(
    ! [B_279] :
      ( m1_subset_1(B_279,'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(B_279,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3044,c_26])).

tff(c_3092,plain,(
    ! [B_281] :
      ( m1_subset_1(B_281,'#skF_4')
      | ~ m1_subset_1(B_281,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_220,c_3049])).

tff(c_3096,plain,(
    ! [B_6] :
      ( m1_subset_1('#skF_2'('#skF_5',B_6),'#skF_4')
      | v1_xboole_0('#skF_5')
      | r1_tarski('#skF_5',B_6) ) ),
    inference(resolution,[status(thm)],[c_291,c_3092])).

tff(c_3336,plain,(
    ! [B_293] :
      ( m1_subset_1('#skF_2'('#skF_5',B_293),'#skF_4')
      | r1_tarski('#skF_5',B_293) ) ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_3096])).

tff(c_136,plain,(
    ! [A_49,B_50] :
      ( r2_hidden('#skF_2'(A_49,B_50),A_49)
      | r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_44,plain,(
    ! [D_25] :
      ( r2_hidden(D_25,'#skF_6')
      | ~ r2_hidden(D_25,'#skF_5')
      | ~ m1_subset_1(D_25,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2302,plain,(
    ! [B_221] :
      ( r2_hidden('#skF_2'('#skF_5',B_221),'#skF_6')
      | ~ m1_subset_1('#skF_2'('#skF_5',B_221),'#skF_4')
      | r1_tarski('#skF_5',B_221) ) ),
    inference(resolution,[status(thm)],[c_136,c_44])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2316,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_5','#skF_6'),'#skF_4')
    | r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_2302,c_8])).

tff(c_2328,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5','#skF_6'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1522,c_1522,c_2316])).

tff(c_3343,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_3336,c_2328])).

tff(c_3356,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1522,c_3343])).

tff(c_3358,plain,(
    r2_xboole_0('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_1511])).

tff(c_246,plain,(
    ! [A_67,B_68] :
      ( ~ r2_hidden('#skF_2'(A_67,B_68),B_68)
      | r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_259,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_246])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_63,plain,(
    ! [D_34] :
      ( r2_hidden(D_34,'#skF_6')
      | ~ r2_hidden(D_34,'#skF_5')
      | ~ m1_subset_1(D_34,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_68,plain,
    ( r2_hidden('#skF_1'('#skF_5'),'#skF_6')
    | ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_63])).

tff(c_313,plain,
    ( r2_hidden('#skF_1'('#skF_5'),'#skF_6')
    | ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_68])).

tff(c_314,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_313])).

tff(c_296,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_268])).

tff(c_329,plain,(
    ! [C_74,B_75,A_76] :
      ( r2_hidden(C_74,B_75)
      | ~ r2_hidden(C_74,A_76)
      | ~ r1_tarski(A_76,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_970,plain,(
    ! [B_135,B_136,A_137] :
      ( r2_hidden(B_135,B_136)
      | ~ r1_tarski(A_137,B_136)
      | ~ m1_subset_1(B_135,A_137)
      | v1_xboole_0(A_137) ) ),
    inference(resolution,[status(thm)],[c_28,c_329])).

tff(c_978,plain,(
    ! [B_135] :
      ( r2_hidden(B_135,'#skF_4')
      | ~ m1_subset_1(B_135,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_126,c_970])).

tff(c_996,plain,(
    ! [B_138] :
      ( r2_hidden(B_138,'#skF_4')
      | ~ m1_subset_1(B_138,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_978])).

tff(c_1001,plain,(
    ! [B_138] :
      ( m1_subset_1(B_138,'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(B_138,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_996,c_26])).

tff(c_1044,plain,(
    ! [B_140] :
      ( m1_subset_1(B_140,'#skF_4')
      | ~ m1_subset_1(B_140,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_220,c_1001])).

tff(c_1056,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_296,c_1044])).

tff(c_1070,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_314,c_1056])).

tff(c_1071,plain,(
    r2_hidden('#skF_1'('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_313])).

tff(c_1100,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1071,c_2])).

tff(c_290,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1('#skF_3'(A_12,B_13),B_13)
      | v1_xboole_0(B_13)
      | ~ r2_xboole_0(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_20,c_268])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_125,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_113])).

tff(c_5364,plain,(
    ! [B_447,B_448,A_449] :
      ( r2_hidden(B_447,B_448)
      | ~ r1_tarski(A_449,B_448)
      | ~ m1_subset_1(B_447,A_449)
      | v1_xboole_0(A_449) ) ),
    inference(resolution,[status(thm)],[c_28,c_1120])).

tff(c_5380,plain,(
    ! [B_447] :
      ( r2_hidden(B_447,'#skF_4')
      | ~ m1_subset_1(B_447,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_125,c_5364])).

tff(c_5464,plain,(
    ! [B_452] :
      ( r2_hidden(B_452,'#skF_4')
      | ~ m1_subset_1(B_452,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1100,c_5380])).

tff(c_5469,plain,(
    ! [B_452] :
      ( m1_subset_1(B_452,'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(B_452,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_5464,c_26])).

tff(c_5555,plain,(
    ! [B_455] :
      ( m1_subset_1(B_455,'#skF_4')
      | ~ m1_subset_1(B_455,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_220,c_5469])).

tff(c_5571,plain,(
    ! [A_12] :
      ( m1_subset_1('#skF_3'(A_12,'#skF_6'),'#skF_4')
      | v1_xboole_0('#skF_6')
      | ~ r2_xboole_0(A_12,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_290,c_5555])).

tff(c_5839,plain,(
    ! [A_469] :
      ( m1_subset_1('#skF_3'(A_469,'#skF_6'),'#skF_4')
      | ~ r2_xboole_0(A_469,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1100,c_5571])).

tff(c_5184,plain,(
    ! [A_433,B_434,B_435] :
      ( r2_hidden('#skF_3'(A_433,B_434),B_435)
      | ~ r1_tarski(B_434,B_435)
      | ~ r2_xboole_0(A_433,B_434) ) ),
    inference(resolution,[status(thm)],[c_20,c_1120])).

tff(c_161,plain,(
    ! [B_54] :
      ( ~ r2_xboole_0('#skF_5',B_54)
      | ~ r2_hidden('#skF_3'('#skF_5',B_54),'#skF_6')
      | ~ m1_subset_1('#skF_3'('#skF_5',B_54),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_152])).

tff(c_5230,plain,(
    ! [B_434] :
      ( ~ m1_subset_1('#skF_3'('#skF_5',B_434),'#skF_4')
      | ~ r1_tarski(B_434,'#skF_6')
      | ~ r2_xboole_0('#skF_5',B_434) ) ),
    inference(resolution,[status(thm)],[c_5184,c_161])).

tff(c_5843,plain,
    ( ~ r1_tarski('#skF_6','#skF_6')
    | ~ r2_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_5839,c_5230])).

tff(c_5857,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3358,c_259,c_5843])).

tff(c_5859,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_30,plain,(
    ! [B_19,A_18] :
      ( m1_subset_1(B_19,A_18)
      | ~ v1_xboole_0(B_19)
      | ~ v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_5861,plain,(
    ! [D_470] :
      ( ~ r2_hidden(D_470,'#skF_6')
      | ~ m1_subset_1(D_470,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_5880,plain,(
    ! [B_19] :
      ( ~ m1_subset_1(B_19,'#skF_4')
      | ~ m1_subset_1(B_19,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_28,c_5861])).

tff(c_6015,plain,(
    ! [B_488] :
      ( ~ m1_subset_1(B_488,'#skF_4')
      | ~ m1_subset_1(B_488,'#skF_6') ) ),
    inference(splitLeft,[status(thm)],[c_5880])).

tff(c_6025,plain,(
    ! [B_19] :
      ( ~ m1_subset_1(B_19,'#skF_4')
      | ~ v1_xboole_0(B_19)
      | ~ v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_30,c_6015])).

tff(c_6026,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_6025])).

tff(c_5881,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6'),'#skF_4')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_5861])).

tff(c_5882,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5881])).

tff(c_5907,plain,(
    ! [B_474,A_475] :
      ( m1_subset_1(B_474,A_475)
      | ~ r2_hidden(B_474,A_475)
      | v1_xboole_0(A_475) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_5923,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_5907])).

tff(c_5993,plain,(
    ! [C_484,B_485,A_486] :
      ( r2_hidden(C_484,B_485)
      | ~ r2_hidden(C_484,A_486)
      | ~ r1_tarski(A_486,B_485) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_7106,plain,(
    ! [B_567,B_568,A_569] :
      ( r2_hidden(B_567,B_568)
      | ~ r1_tarski(A_569,B_568)
      | ~ m1_subset_1(B_567,A_569)
      | v1_xboole_0(A_569) ) ),
    inference(resolution,[status(thm)],[c_28,c_5993])).

tff(c_7118,plain,(
    ! [B_567] :
      ( r2_hidden(B_567,'#skF_4')
      | ~ m1_subset_1(B_567,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_125,c_7106])).

tff(c_7134,plain,(
    ! [B_570] :
      ( r2_hidden(B_570,'#skF_4')
      | ~ m1_subset_1(B_570,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_6026,c_7118])).

tff(c_7143,plain,(
    ! [B_570] :
      ( m1_subset_1(B_570,'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(B_570,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_7134,c_26])).

tff(c_7158,plain,(
    ! [B_571] :
      ( m1_subset_1(B_571,'#skF_4')
      | ~ m1_subset_1(B_571,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_220,c_7143])).

tff(c_7170,plain,
    ( m1_subset_1('#skF_1'('#skF_6'),'#skF_4')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_5923,c_7158])).

tff(c_7184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6026,c_5882,c_7170])).

tff(c_7186,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_6025])).

tff(c_150,plain,(
    ! [A_49,B_50] :
      ( ~ v1_xboole_0(A_49)
      | r1_tarski(A_49,B_50) ) ),
    inference(resolution,[status(thm)],[c_136,c_2])).

tff(c_5903,plain,(
    ! [B_472,A_473] :
      ( ~ v1_xboole_0(B_472)
      | B_472 = A_473
      | ~ v1_xboole_0(A_473) ) ),
    inference(resolution,[status(thm)],[c_150,c_199])).

tff(c_5906,plain,(
    ! [A_473] :
      ( A_473 = '#skF_5'
      | ~ v1_xboole_0(A_473) ) ),
    inference(resolution,[status(thm)],[c_5859,c_5903])).

tff(c_7189,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_7186,c_5906])).

tff(c_7195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_7189])).

tff(c_7196,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_5881])).

tff(c_7219,plain,(
    ! [B_573,A_574] :
      ( ~ v1_xboole_0(B_573)
      | B_573 = A_574
      | ~ v1_xboole_0(A_574) ) ),
    inference(resolution,[status(thm)],[c_150,c_199])).

tff(c_7226,plain,(
    ! [A_575] :
      ( A_575 = '#skF_6'
      | ~ v1_xboole_0(A_575) ) ),
    inference(resolution,[status(thm)],[c_7196,c_7219])).

tff(c_7232,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_5859,c_7226])).

tff(c_7238,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_7232])).

tff(c_7239,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_7261,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7239,c_36])).

tff(c_7240,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_217,plain,
    ( ~ v1_xboole_0('#skF_4')
    | '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_125,c_199])).

tff(c_7284,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7240,c_217])).

tff(c_7285,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7261,c_7284])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:11:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.65/2.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.65/2.36  
% 6.65/2.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.65/2.36  %$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 6.65/2.36  
% 6.65/2.36  %Foreground sorts:
% 6.65/2.36  
% 6.65/2.36  
% 6.65/2.36  %Background operators:
% 6.65/2.36  
% 6.65/2.36  
% 6.65/2.36  %Foreground operators:
% 6.65/2.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.65/2.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.65/2.36  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.65/2.36  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.65/2.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.65/2.36  tff('#skF_5', type, '#skF_5': $i).
% 6.65/2.36  tff('#skF_6', type, '#skF_6': $i).
% 6.65/2.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.65/2.36  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 6.65/2.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.65/2.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.65/2.36  tff('#skF_4', type, '#skF_4': $i).
% 6.65/2.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.65/2.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.65/2.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.65/2.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.65/2.36  
% 6.97/2.38  tff(f_92, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_subset_1)).
% 6.97/2.38  tff(f_45, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 6.97/2.38  tff(f_55, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_0)).
% 6.97/2.38  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.97/2.38  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.97/2.38  tff(f_74, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 6.97/2.38  tff(f_77, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 6.97/2.38  tff(f_61, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 6.97/2.38  tff(f_59, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 6.97/2.38  tff(c_36, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.97/2.38  tff(c_12, plain, (![A_10, B_11]: (r2_xboole_0(A_10, B_11) | B_11=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.97/2.38  tff(c_20, plain, (![A_12, B_13]: (r2_hidden('#skF_3'(A_12, B_13), B_13) | ~r2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.97/2.38  tff(c_42, plain, (![D_25]: (r2_hidden(D_25, '#skF_5') | ~r2_hidden(D_25, '#skF_6') | ~m1_subset_1(D_25, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.97/2.38  tff(c_152, plain, (![A_53, B_54]: (~r2_hidden('#skF_3'(A_53, B_54), A_53) | ~r2_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.97/2.38  tff(c_1494, plain, (![B_165]: (~r2_xboole_0('#skF_5', B_165) | ~r2_hidden('#skF_3'('#skF_5', B_165), '#skF_6') | ~m1_subset_1('#skF_3'('#skF_5', B_165), '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_152])).
% 6.97/2.38  tff(c_1511, plain, (~m1_subset_1('#skF_3'('#skF_5', '#skF_6'), '#skF_4') | ~r2_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_20, c_1494])).
% 6.97/2.38  tff(c_1516, plain, (~r2_xboole_0('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_1511])).
% 6.97/2.38  tff(c_1519, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_12, c_1516])).
% 6.97/2.38  tff(c_1522, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_36, c_1519])).
% 6.97/2.38  tff(c_127, plain, (![D_48]: (r2_hidden(D_48, '#skF_5') | ~r2_hidden(D_48, '#skF_6') | ~m1_subset_1(D_48, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.97/2.38  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.97/2.38  tff(c_135, plain, (![D_48]: (~v1_xboole_0('#skF_5') | ~r2_hidden(D_48, '#skF_6') | ~m1_subset_1(D_48, '#skF_4'))), inference(resolution, [status(thm)], [c_127, c_2])).
% 6.97/2.38  tff(c_221, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_135])).
% 6.97/2.38  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.97/2.38  tff(c_268, plain, (![B_70, A_71]: (m1_subset_1(B_70, A_71) | ~r2_hidden(B_70, A_71) | v1_xboole_0(A_71))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.97/2.38  tff(c_291, plain, (![A_5, B_6]: (m1_subset_1('#skF_2'(A_5, B_6), A_5) | v1_xboole_0(A_5) | r1_tarski(A_5, B_6))), inference(resolution, [status(thm)], [c_10, c_268])).
% 6.97/2.38  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.97/2.38  tff(c_34, plain, (![A_20]: (~v1_xboole_0(k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.97/2.38  tff(c_96, plain, (![B_44, A_45]: (r2_hidden(B_44, A_45) | ~m1_subset_1(B_44, A_45) | v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.97/2.38  tff(c_24, plain, (![A_17]: (k3_tarski(k1_zfmisc_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.97/2.38  tff(c_69, plain, (![A_35, B_36]: (r1_tarski(A_35, k3_tarski(B_36)) | ~r2_hidden(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.97/2.38  tff(c_72, plain, (![A_35, A_17]: (r1_tarski(A_35, A_17) | ~r2_hidden(A_35, k1_zfmisc_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_69])).
% 6.97/2.38  tff(c_100, plain, (![B_44, A_17]: (r1_tarski(B_44, A_17) | ~m1_subset_1(B_44, k1_zfmisc_1(A_17)) | v1_xboole_0(k1_zfmisc_1(A_17)))), inference(resolution, [status(thm)], [c_96, c_72])).
% 6.97/2.38  tff(c_113, plain, (![B_46, A_47]: (r1_tarski(B_46, A_47) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)))), inference(negUnitSimplification, [status(thm)], [c_34, c_100])).
% 6.97/2.38  tff(c_126, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_113])).
% 6.97/2.38  tff(c_184, plain, (![A_59, B_60]: (r2_xboole_0(A_59, B_60) | B_60=A_59 | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.97/2.38  tff(c_163, plain, (![A_55, B_56]: (r2_hidden('#skF_3'(A_55, B_56), B_56) | ~r2_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.97/2.38  tff(c_182, plain, (![B_56, A_55]: (~v1_xboole_0(B_56) | ~r2_xboole_0(A_55, B_56))), inference(resolution, [status(thm)], [c_163, c_2])).
% 6.97/2.38  tff(c_199, plain, (![B_61, A_62]: (~v1_xboole_0(B_61) | B_61=A_62 | ~r1_tarski(A_62, B_61))), inference(resolution, [status(thm)], [c_184, c_182])).
% 6.97/2.38  tff(c_216, plain, (~v1_xboole_0('#skF_4') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_126, c_199])).
% 6.97/2.38  tff(c_220, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_216])).
% 6.97/2.38  tff(c_28, plain, (![B_19, A_18]: (r2_hidden(B_19, A_18) | ~m1_subset_1(B_19, A_18) | v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.97/2.38  tff(c_1120, plain, (![C_143, B_144, A_145]: (r2_hidden(C_143, B_144) | ~r2_hidden(C_143, A_145) | ~r1_tarski(A_145, B_144))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.97/2.38  tff(c_3012, plain, (![B_276, B_277, A_278]: (r2_hidden(B_276, B_277) | ~r1_tarski(A_278, B_277) | ~m1_subset_1(B_276, A_278) | v1_xboole_0(A_278))), inference(resolution, [status(thm)], [c_28, c_1120])).
% 6.97/2.38  tff(c_3024, plain, (![B_276]: (r2_hidden(B_276, '#skF_4') | ~m1_subset_1(B_276, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_126, c_3012])).
% 6.97/2.38  tff(c_3044, plain, (![B_279]: (r2_hidden(B_279, '#skF_4') | ~m1_subset_1(B_279, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_221, c_3024])).
% 6.97/2.38  tff(c_26, plain, (![B_19, A_18]: (m1_subset_1(B_19, A_18) | ~r2_hidden(B_19, A_18) | v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.97/2.38  tff(c_3049, plain, (![B_279]: (m1_subset_1(B_279, '#skF_4') | v1_xboole_0('#skF_4') | ~m1_subset_1(B_279, '#skF_5'))), inference(resolution, [status(thm)], [c_3044, c_26])).
% 6.97/2.38  tff(c_3092, plain, (![B_281]: (m1_subset_1(B_281, '#skF_4') | ~m1_subset_1(B_281, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_220, c_3049])).
% 6.97/2.38  tff(c_3096, plain, (![B_6]: (m1_subset_1('#skF_2'('#skF_5', B_6), '#skF_4') | v1_xboole_0('#skF_5') | r1_tarski('#skF_5', B_6))), inference(resolution, [status(thm)], [c_291, c_3092])).
% 6.97/2.38  tff(c_3336, plain, (![B_293]: (m1_subset_1('#skF_2'('#skF_5', B_293), '#skF_4') | r1_tarski('#skF_5', B_293))), inference(negUnitSimplification, [status(thm)], [c_221, c_3096])).
% 6.97/2.38  tff(c_136, plain, (![A_49, B_50]: (r2_hidden('#skF_2'(A_49, B_50), A_49) | r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.97/2.38  tff(c_44, plain, (![D_25]: (r2_hidden(D_25, '#skF_6') | ~r2_hidden(D_25, '#skF_5') | ~m1_subset_1(D_25, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.97/2.38  tff(c_2302, plain, (![B_221]: (r2_hidden('#skF_2'('#skF_5', B_221), '#skF_6') | ~m1_subset_1('#skF_2'('#skF_5', B_221), '#skF_4') | r1_tarski('#skF_5', B_221))), inference(resolution, [status(thm)], [c_136, c_44])).
% 6.97/2.38  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.97/2.38  tff(c_2316, plain, (~m1_subset_1('#skF_2'('#skF_5', '#skF_6'), '#skF_4') | r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_2302, c_8])).
% 6.97/2.38  tff(c_2328, plain, (~m1_subset_1('#skF_2'('#skF_5', '#skF_6'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1522, c_1522, c_2316])).
% 6.97/2.38  tff(c_3343, plain, (r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_3336, c_2328])).
% 6.97/2.38  tff(c_3356, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1522, c_3343])).
% 6.97/2.38  tff(c_3358, plain, (r2_xboole_0('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_1511])).
% 6.97/2.38  tff(c_246, plain, (![A_67, B_68]: (~r2_hidden('#skF_2'(A_67, B_68), B_68) | r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.97/2.38  tff(c_259, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_246])).
% 6.97/2.38  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.97/2.38  tff(c_63, plain, (![D_34]: (r2_hidden(D_34, '#skF_6') | ~r2_hidden(D_34, '#skF_5') | ~m1_subset_1(D_34, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.97/2.38  tff(c_68, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_6') | ~m1_subset_1('#skF_1'('#skF_5'), '#skF_4') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_63])).
% 6.97/2.38  tff(c_313, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_6') | ~m1_subset_1('#skF_1'('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_221, c_68])).
% 6.97/2.38  tff(c_314, plain, (~m1_subset_1('#skF_1'('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_313])).
% 6.97/2.38  tff(c_296, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_268])).
% 6.97/2.38  tff(c_329, plain, (![C_74, B_75, A_76]: (r2_hidden(C_74, B_75) | ~r2_hidden(C_74, A_76) | ~r1_tarski(A_76, B_75))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.97/2.38  tff(c_970, plain, (![B_135, B_136, A_137]: (r2_hidden(B_135, B_136) | ~r1_tarski(A_137, B_136) | ~m1_subset_1(B_135, A_137) | v1_xboole_0(A_137))), inference(resolution, [status(thm)], [c_28, c_329])).
% 6.97/2.38  tff(c_978, plain, (![B_135]: (r2_hidden(B_135, '#skF_4') | ~m1_subset_1(B_135, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_126, c_970])).
% 6.97/2.38  tff(c_996, plain, (![B_138]: (r2_hidden(B_138, '#skF_4') | ~m1_subset_1(B_138, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_221, c_978])).
% 6.97/2.38  tff(c_1001, plain, (![B_138]: (m1_subset_1(B_138, '#skF_4') | v1_xboole_0('#skF_4') | ~m1_subset_1(B_138, '#skF_5'))), inference(resolution, [status(thm)], [c_996, c_26])).
% 6.97/2.38  tff(c_1044, plain, (![B_140]: (m1_subset_1(B_140, '#skF_4') | ~m1_subset_1(B_140, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_220, c_1001])).
% 6.97/2.38  tff(c_1056, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_4') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_296, c_1044])).
% 6.97/2.38  tff(c_1070, plain, $false, inference(negUnitSimplification, [status(thm)], [c_221, c_314, c_1056])).
% 6.97/2.38  tff(c_1071, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_313])).
% 6.97/2.38  tff(c_1100, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_1071, c_2])).
% 6.97/2.38  tff(c_290, plain, (![A_12, B_13]: (m1_subset_1('#skF_3'(A_12, B_13), B_13) | v1_xboole_0(B_13) | ~r2_xboole_0(A_12, B_13))), inference(resolution, [status(thm)], [c_20, c_268])).
% 6.97/2.38  tff(c_38, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.97/2.38  tff(c_125, plain, (r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_113])).
% 6.97/2.38  tff(c_5364, plain, (![B_447, B_448, A_449]: (r2_hidden(B_447, B_448) | ~r1_tarski(A_449, B_448) | ~m1_subset_1(B_447, A_449) | v1_xboole_0(A_449))), inference(resolution, [status(thm)], [c_28, c_1120])).
% 6.97/2.38  tff(c_5380, plain, (![B_447]: (r2_hidden(B_447, '#skF_4') | ~m1_subset_1(B_447, '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_125, c_5364])).
% 6.97/2.38  tff(c_5464, plain, (![B_452]: (r2_hidden(B_452, '#skF_4') | ~m1_subset_1(B_452, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_1100, c_5380])).
% 6.97/2.38  tff(c_5469, plain, (![B_452]: (m1_subset_1(B_452, '#skF_4') | v1_xboole_0('#skF_4') | ~m1_subset_1(B_452, '#skF_6'))), inference(resolution, [status(thm)], [c_5464, c_26])).
% 6.97/2.38  tff(c_5555, plain, (![B_455]: (m1_subset_1(B_455, '#skF_4') | ~m1_subset_1(B_455, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_220, c_5469])).
% 6.97/2.38  tff(c_5571, plain, (![A_12]: (m1_subset_1('#skF_3'(A_12, '#skF_6'), '#skF_4') | v1_xboole_0('#skF_6') | ~r2_xboole_0(A_12, '#skF_6'))), inference(resolution, [status(thm)], [c_290, c_5555])).
% 6.97/2.38  tff(c_5839, plain, (![A_469]: (m1_subset_1('#skF_3'(A_469, '#skF_6'), '#skF_4') | ~r2_xboole_0(A_469, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_1100, c_5571])).
% 6.97/2.38  tff(c_5184, plain, (![A_433, B_434, B_435]: (r2_hidden('#skF_3'(A_433, B_434), B_435) | ~r1_tarski(B_434, B_435) | ~r2_xboole_0(A_433, B_434))), inference(resolution, [status(thm)], [c_20, c_1120])).
% 6.97/2.38  tff(c_161, plain, (![B_54]: (~r2_xboole_0('#skF_5', B_54) | ~r2_hidden('#skF_3'('#skF_5', B_54), '#skF_6') | ~m1_subset_1('#skF_3'('#skF_5', B_54), '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_152])).
% 6.97/2.38  tff(c_5230, plain, (![B_434]: (~m1_subset_1('#skF_3'('#skF_5', B_434), '#skF_4') | ~r1_tarski(B_434, '#skF_6') | ~r2_xboole_0('#skF_5', B_434))), inference(resolution, [status(thm)], [c_5184, c_161])).
% 6.97/2.38  tff(c_5843, plain, (~r1_tarski('#skF_6', '#skF_6') | ~r2_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_5839, c_5230])).
% 6.97/2.38  tff(c_5857, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3358, c_259, c_5843])).
% 6.97/2.38  tff(c_5859, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_135])).
% 6.97/2.38  tff(c_30, plain, (![B_19, A_18]: (m1_subset_1(B_19, A_18) | ~v1_xboole_0(B_19) | ~v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.97/2.38  tff(c_5861, plain, (![D_470]: (~r2_hidden(D_470, '#skF_6') | ~m1_subset_1(D_470, '#skF_4'))), inference(splitRight, [status(thm)], [c_135])).
% 6.97/2.38  tff(c_5880, plain, (![B_19]: (~m1_subset_1(B_19, '#skF_4') | ~m1_subset_1(B_19, '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_28, c_5861])).
% 6.97/2.38  tff(c_6015, plain, (![B_488]: (~m1_subset_1(B_488, '#skF_4') | ~m1_subset_1(B_488, '#skF_6'))), inference(splitLeft, [status(thm)], [c_5880])).
% 6.97/2.38  tff(c_6025, plain, (![B_19]: (~m1_subset_1(B_19, '#skF_4') | ~v1_xboole_0(B_19) | ~v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_30, c_6015])).
% 6.97/2.38  tff(c_6026, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_6025])).
% 6.97/2.38  tff(c_5881, plain, (~m1_subset_1('#skF_1'('#skF_6'), '#skF_4') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_4, c_5861])).
% 6.97/2.38  tff(c_5882, plain, (~m1_subset_1('#skF_1'('#skF_6'), '#skF_4')), inference(splitLeft, [status(thm)], [c_5881])).
% 6.97/2.38  tff(c_5907, plain, (![B_474, A_475]: (m1_subset_1(B_474, A_475) | ~r2_hidden(B_474, A_475) | v1_xboole_0(A_475))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.97/2.38  tff(c_5923, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_5907])).
% 6.97/2.38  tff(c_5993, plain, (![C_484, B_485, A_486]: (r2_hidden(C_484, B_485) | ~r2_hidden(C_484, A_486) | ~r1_tarski(A_486, B_485))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.97/2.38  tff(c_7106, plain, (![B_567, B_568, A_569]: (r2_hidden(B_567, B_568) | ~r1_tarski(A_569, B_568) | ~m1_subset_1(B_567, A_569) | v1_xboole_0(A_569))), inference(resolution, [status(thm)], [c_28, c_5993])).
% 6.97/2.38  tff(c_7118, plain, (![B_567]: (r2_hidden(B_567, '#skF_4') | ~m1_subset_1(B_567, '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_125, c_7106])).
% 6.97/2.38  tff(c_7134, plain, (![B_570]: (r2_hidden(B_570, '#skF_4') | ~m1_subset_1(B_570, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_6026, c_7118])).
% 6.97/2.38  tff(c_7143, plain, (![B_570]: (m1_subset_1(B_570, '#skF_4') | v1_xboole_0('#skF_4') | ~m1_subset_1(B_570, '#skF_6'))), inference(resolution, [status(thm)], [c_7134, c_26])).
% 6.97/2.38  tff(c_7158, plain, (![B_571]: (m1_subset_1(B_571, '#skF_4') | ~m1_subset_1(B_571, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_220, c_7143])).
% 6.97/2.38  tff(c_7170, plain, (m1_subset_1('#skF_1'('#skF_6'), '#skF_4') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_5923, c_7158])).
% 6.97/2.38  tff(c_7184, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6026, c_5882, c_7170])).
% 6.97/2.38  tff(c_7186, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_6025])).
% 6.97/2.38  tff(c_150, plain, (![A_49, B_50]: (~v1_xboole_0(A_49) | r1_tarski(A_49, B_50))), inference(resolution, [status(thm)], [c_136, c_2])).
% 6.97/2.38  tff(c_5903, plain, (![B_472, A_473]: (~v1_xboole_0(B_472) | B_472=A_473 | ~v1_xboole_0(A_473))), inference(resolution, [status(thm)], [c_150, c_199])).
% 6.97/2.38  tff(c_5906, plain, (![A_473]: (A_473='#skF_5' | ~v1_xboole_0(A_473))), inference(resolution, [status(thm)], [c_5859, c_5903])).
% 6.97/2.38  tff(c_7189, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_7186, c_5906])).
% 6.97/2.38  tff(c_7195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_7189])).
% 6.97/2.38  tff(c_7196, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_5881])).
% 6.97/2.38  tff(c_7219, plain, (![B_573, A_574]: (~v1_xboole_0(B_573) | B_573=A_574 | ~v1_xboole_0(A_574))), inference(resolution, [status(thm)], [c_150, c_199])).
% 6.97/2.38  tff(c_7226, plain, (![A_575]: (A_575='#skF_6' | ~v1_xboole_0(A_575))), inference(resolution, [status(thm)], [c_7196, c_7219])).
% 6.97/2.38  tff(c_7232, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_5859, c_7226])).
% 6.97/2.38  tff(c_7238, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_7232])).
% 6.97/2.38  tff(c_7239, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_216])).
% 6.97/2.38  tff(c_7261, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7239, c_36])).
% 6.97/2.38  tff(c_7240, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_216])).
% 6.97/2.38  tff(c_217, plain, (~v1_xboole_0('#skF_4') | '#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_125, c_199])).
% 6.97/2.38  tff(c_7284, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7240, c_217])).
% 6.97/2.38  tff(c_7285, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7261, c_7284])).
% 6.97/2.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.97/2.38  
% 6.97/2.38  Inference rules
% 6.97/2.38  ----------------------
% 6.97/2.38  #Ref     : 0
% 6.97/2.38  #Sup     : 1503
% 6.97/2.38  #Fact    : 0
% 6.97/2.38  #Define  : 0
% 6.97/2.38  #Split   : 34
% 6.97/2.38  #Chain   : 0
% 6.97/2.38  #Close   : 0
% 6.97/2.38  
% 6.97/2.38  Ordering : KBO
% 6.97/2.38  
% 6.97/2.38  Simplification rules
% 6.97/2.38  ----------------------
% 6.97/2.38  #Subsume      : 593
% 6.97/2.38  #Demod        : 159
% 6.97/2.38  #Tautology    : 180
% 6.97/2.38  #SimpNegUnit  : 358
% 6.97/2.38  #BackRed      : 18
% 6.97/2.38  
% 6.97/2.38  #Partial instantiations: 0
% 6.97/2.38  #Strategies tried      : 1
% 6.97/2.38  
% 6.97/2.38  Timing (in seconds)
% 6.97/2.38  ----------------------
% 6.97/2.39  Preprocessing        : 0.31
% 6.97/2.39  Parsing              : 0.15
% 6.97/2.39  CNF conversion       : 0.02
% 6.97/2.39  Main loop            : 1.26
% 6.97/2.39  Inferencing          : 0.46
% 6.97/2.39  Reduction            : 0.35
% 6.97/2.39  Demodulation         : 0.19
% 6.97/2.39  BG Simplification    : 0.04
% 6.97/2.39  Subsumption          : 0.31
% 6.97/2.39  Abstraction          : 0.05
% 6.97/2.39  MUC search           : 0.00
% 6.97/2.39  Cooper               : 0.00
% 6.97/2.39  Total                : 1.62
% 6.97/2.39  Index Insertion      : 0.00
% 6.97/2.39  Index Deletion       : 0.00
% 6.97/2.39  Index Matching       : 0.00
% 6.97/2.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
