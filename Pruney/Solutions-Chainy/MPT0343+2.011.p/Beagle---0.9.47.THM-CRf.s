%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:18 EST 2020

% Result     : Theorem 6.10s
% Output     : CNFRefutation 6.10s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 606 expanded)
%              Number of leaves         :   22 ( 196 expanded)
%              Depth                    :   13
%              Number of atoms          :  300 (1609 expanded)
%              Number of equality atoms :   17 (  96 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

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

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_32,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_26,plain,(
    ! [B_16,A_15] :
      ( m1_subset_1(B_16,A_15)
      | ~ v1_xboole_0(B_16)
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( r2_hidden(B_16,A_15)
      | ~ m1_subset_1(B_16,A_15)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

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

tff(c_38,plain,(
    ! [D_25] :
      ( r2_hidden(D_25,'#skF_5')
      | ~ r2_hidden(D_25,'#skF_6')
      | ~ m1_subset_1(D_25,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_154,plain,(
    ! [A_54,B_55] :
      ( ~ r2_hidden('#skF_3'(A_54,B_55),A_54)
      | ~ r2_xboole_0(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2554,plain,(
    ! [B_268] :
      ( ~ r2_xboole_0('#skF_5',B_268)
      | ~ r2_hidden('#skF_3'('#skF_5',B_268),'#skF_6')
      | ~ m1_subset_1('#skF_3'('#skF_5',B_268),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_154])).

tff(c_2569,plain,
    ( ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),'#skF_4')
    | ~ r2_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_2554])).

tff(c_2570,plain,(
    ~ r2_xboole_0('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2569])).

tff(c_2573,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_12,c_2570])).

tff(c_2576,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_2573])).

tff(c_59,plain,(
    ! [D_34] :
      ( r2_hidden(D_34,'#skF_5')
      | ~ r2_hidden(D_34,'#skF_6')
      | ~ m1_subset_1(D_34,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_63,plain,(
    ! [D_34] :
      ( ~ v1_xboole_0('#skF_5')
      | ~ r2_hidden(D_34,'#skF_6')
      | ~ m1_subset_1(D_34,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_59,c_2])).

tff(c_214,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_102,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_2'(A_46,B_47),A_46)
      | r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_22,plain,(
    ! [B_16,A_15] :
      ( m1_subset_1(B_16,A_15)
      | ~ r2_hidden(B_16,A_15)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_109,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1('#skF_2'(A_46,B_47),A_46)
      | v1_xboole_0(A_46)
      | r1_tarski(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_102,c_22])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_111,plain,(
    ! [D_48] :
      ( r2_hidden(D_48,'#skF_6')
      | ~ r2_hidden(D_48,'#skF_5')
      | ~ m1_subset_1(D_48,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_135,plain,
    ( r2_hidden('#skF_1'('#skF_5'),'#skF_6')
    | ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_111])).

tff(c_215,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_219,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_5'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_215])).

tff(c_220,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_219])).

tff(c_187,plain,(
    ! [C_58,B_59,A_60] :
      ( r2_hidden(C_58,B_59)
      | ~ r2_hidden(C_58,A_60)
      | ~ r1_tarski(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_221,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_1'(A_65),B_66)
      | ~ r1_tarski(A_65,B_66)
      | v1_xboole_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_4,c_187])).

tff(c_928,plain,(
    ! [A_137,B_138] :
      ( m1_subset_1('#skF_1'(A_137),B_138)
      | v1_xboole_0(B_138)
      | ~ r1_tarski(A_137,B_138)
      | v1_xboole_0(A_137) ) ),
    inference(resolution,[status(thm)],[c_221,c_22])).

tff(c_935,plain,
    ( v1_xboole_0('#skF_4')
    | ~ r1_tarski('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_928,c_215])).

tff(c_942,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_220,c_935])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_238,plain,(
    ! [C_67,A_68,B_69] :
      ( r2_hidden(C_67,A_68)
      | ~ r2_hidden(C_67,B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_993,plain,(
    ! [A_141,B_142,A_143] :
      ( r2_hidden('#skF_2'(A_141,B_142),A_143)
      | ~ m1_subset_1(A_141,k1_zfmisc_1(A_143))
      | r1_tarski(A_141,B_142) ) ),
    inference(resolution,[status(thm)],[c_10,c_238])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1031,plain,(
    ! [A_144,A_145] :
      ( ~ m1_subset_1(A_144,k1_zfmisc_1(A_145))
      | r1_tarski(A_144,A_145) ) ),
    inference(resolution,[status(thm)],[c_993,c_8])).

tff(c_1057,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_1031])).

tff(c_1067,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_942,c_1057])).

tff(c_1069,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_1345,plain,(
    ! [C_172,A_173,B_174] :
      ( r2_hidden(C_172,A_173)
      | ~ r2_hidden(C_172,B_174)
      | ~ m1_subset_1(B_174,k1_zfmisc_1(A_173)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1450,plain,(
    ! [A_178,A_179] :
      ( r2_hidden('#skF_1'(A_178),A_179)
      | ~ m1_subset_1(A_178,k1_zfmisc_1(A_179))
      | v1_xboole_0(A_178) ) ),
    inference(resolution,[status(thm)],[c_4,c_1345])).

tff(c_1475,plain,(
    ! [A_180,A_181] :
      ( ~ v1_xboole_0(A_180)
      | ~ m1_subset_1(A_181,k1_zfmisc_1(A_180))
      | v1_xboole_0(A_181) ) ),
    inference(resolution,[status(thm)],[c_1450,c_2])).

tff(c_1489,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_1475])).

tff(c_1497,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1069,c_1489])).

tff(c_1499,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_1497])).

tff(c_1501,plain,(
    m1_subset_1('#skF_1'('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_28,plain,(
    ! [B_16,A_15] :
      ( v1_xboole_0(B_16)
      | ~ m1_subset_1(B_16,A_15)
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1505,plain,
    ( v1_xboole_0('#skF_1'('#skF_5'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1501,c_28])).

tff(c_1522,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1505])).

tff(c_1506,plain,(
    ! [C_182,A_183,B_184] :
      ( r2_hidden(C_182,A_183)
      | ~ r2_hidden(C_182,B_184)
      | ~ m1_subset_1(B_184,k1_zfmisc_1(A_183)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3091,plain,(
    ! [B_305,A_306,A_307] :
      ( r2_hidden(B_305,A_306)
      | ~ m1_subset_1(A_307,k1_zfmisc_1(A_306))
      | ~ m1_subset_1(B_305,A_307)
      | v1_xboole_0(A_307) ) ),
    inference(resolution,[status(thm)],[c_24,c_1506])).

tff(c_3119,plain,(
    ! [B_305] :
      ( r2_hidden(B_305,'#skF_4')
      | ~ m1_subset_1(B_305,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_3091])).

tff(c_3161,plain,(
    ! [B_309] :
      ( r2_hidden(B_309,'#skF_4')
      | ~ m1_subset_1(B_309,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_3119])).

tff(c_3176,plain,(
    ! [B_309] :
      ( m1_subset_1(B_309,'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(B_309,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3161,c_22])).

tff(c_3262,plain,(
    ! [B_313] :
      ( m1_subset_1(B_313,'#skF_4')
      | ~ m1_subset_1(B_313,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1522,c_3176])).

tff(c_3289,plain,(
    ! [B_47] :
      ( m1_subset_1('#skF_2'('#skF_5',B_47),'#skF_4')
      | v1_xboole_0('#skF_5')
      | r1_tarski('#skF_5',B_47) ) ),
    inference(resolution,[status(thm)],[c_109,c_3262])).

tff(c_3821,plain,(
    ! [B_332] :
      ( m1_subset_1('#skF_2'('#skF_5',B_332),'#skF_4')
      | r1_tarski('#skF_5',B_332) ) ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_3289])).

tff(c_2777,plain,(
    ! [B_295] :
      ( r2_hidden('#skF_2'('#skF_5',B_295),'#skF_6')
      | ~ m1_subset_1('#skF_2'('#skF_5',B_295),'#skF_4')
      | r1_tarski('#skF_5',B_295) ) ),
    inference(resolution,[status(thm)],[c_10,c_111])).

tff(c_2794,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_5','#skF_6'),'#skF_4')
    | r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_2777,c_8])).

tff(c_2809,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5','#skF_6'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_2576,c_2576,c_2794])).

tff(c_3824,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_3821,c_2809])).

tff(c_3839,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2576,c_3824])).

tff(c_3841,plain,(
    r2_xboole_0('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_2569])).

tff(c_1500,plain,
    ( v1_xboole_0('#skF_5')
    | r2_hidden('#skF_1'('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_1523,plain,(
    r2_hidden('#skF_1'('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_1500])).

tff(c_1537,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1523,c_2])).

tff(c_83,plain,(
    ! [A_40,B_41] :
      ( r2_hidden('#skF_3'(A_40,B_41),B_41)
      | ~ r2_xboole_0(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_90,plain,(
    ! [A_40,B_41] :
      ( m1_subset_1('#skF_3'(A_40,B_41),B_41)
      | v1_xboole_0(B_41)
      | ~ r2_xboole_0(A_40,B_41) ) ),
    inference(resolution,[status(thm)],[c_83,c_22])).

tff(c_34,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4442,plain,(
    ! [A_365,B_366,A_367] :
      ( r2_hidden('#skF_2'(A_365,B_366),A_367)
      | ~ m1_subset_1(A_365,k1_zfmisc_1(A_367))
      | r1_tarski(A_365,B_366) ) ),
    inference(resolution,[status(thm)],[c_10,c_1506])).

tff(c_4486,plain,(
    ! [A_368,A_369] :
      ( ~ m1_subset_1(A_368,k1_zfmisc_1(A_369))
      | r1_tarski(A_368,A_369) ) ),
    inference(resolution,[status(thm)],[c_4442,c_8])).

tff(c_4528,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_4486])).

tff(c_199,plain,(
    ! [B_16,B_59,A_15] :
      ( r2_hidden(B_16,B_59)
      | ~ r1_tarski(A_15,B_59)
      | ~ m1_subset_1(B_16,A_15)
      | v1_xboole_0(A_15) ) ),
    inference(resolution,[status(thm)],[c_24,c_187])).

tff(c_4531,plain,(
    ! [B_16] :
      ( r2_hidden(B_16,'#skF_4')
      | ~ m1_subset_1(B_16,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_4528,c_199])).

tff(c_4654,plain,(
    ! [B_372] :
      ( r2_hidden(B_372,'#skF_4')
      | ~ m1_subset_1(B_372,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1537,c_4531])).

tff(c_4669,plain,(
    ! [B_372] :
      ( m1_subset_1(B_372,'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(B_372,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_4654,c_22])).

tff(c_4788,plain,(
    ! [B_377] :
      ( m1_subset_1(B_377,'#skF_4')
      | ~ m1_subset_1(B_377,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1522,c_4669])).

tff(c_4799,plain,(
    ! [A_40] :
      ( m1_subset_1('#skF_3'(A_40,'#skF_6'),'#skF_4')
      | v1_xboole_0('#skF_6')
      | ~ r2_xboole_0(A_40,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_90,c_4788])).

tff(c_5232,plain,(
    ! [A_399] :
      ( m1_subset_1('#skF_3'(A_399,'#skF_6'),'#skF_4')
      | ~ r2_xboole_0(A_399,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1537,c_4799])).

tff(c_3840,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_2569])).

tff(c_5235,plain,(
    ~ r2_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_5232,c_3840])).

tff(c_5246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3841,c_5235])).

tff(c_5248,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1505])).

tff(c_5247,plain,(
    v1_xboole_0('#skF_1'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1505])).

tff(c_110,plain,(
    ! [A_46,B_47] :
      ( ~ v1_xboole_0(A_46)
      | r1_tarski(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_102,c_2])).

tff(c_170,plain,(
    ! [A_56,B_57] :
      ( r2_xboole_0(A_56,B_57)
      | B_57 = A_56
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_91,plain,(
    ! [B_41,A_40] :
      ( ~ v1_xboole_0(B_41)
      | ~ r2_xboole_0(A_40,B_41) ) ),
    inference(resolution,[status(thm)],[c_83,c_2])).

tff(c_203,plain,(
    ! [B_61,A_62] :
      ( ~ v1_xboole_0(B_61)
      | B_61 = A_62
      | ~ r1_tarski(A_62,B_61) ) ),
    inference(resolution,[status(thm)],[c_170,c_91])).

tff(c_212,plain,(
    ! [B_47,A_46] :
      ( ~ v1_xboole_0(B_47)
      | B_47 = A_46
      | ~ v1_xboole_0(A_46) ) ),
    inference(resolution,[status(thm)],[c_110,c_203])).

tff(c_5281,plain,(
    ! [A_401] :
      ( A_401 = '#skF_4'
      | ~ v1_xboole_0(A_401) ) ),
    inference(resolution,[status(thm)],[c_5248,c_212])).

tff(c_5288,plain,(
    '#skF_1'('#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5247,c_5281])).

tff(c_5312,plain,
    ( v1_xboole_0('#skF_5')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5288,c_1500])).

tff(c_5313,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_5312])).

tff(c_30,plain,(
    ! [C_20,A_17,B_18] :
      ( r2_hidden(C_20,A_17)
      | ~ r2_hidden(C_20,B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_5516,plain,(
    ! [A_411] :
      ( r2_hidden('#skF_4',A_411)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_411)) ) ),
    inference(resolution,[status(thm)],[c_5313,c_30])).

tff(c_5524,plain,(
    r2_hidden('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_5516])).

tff(c_5534,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_5524,c_2])).

tff(c_5542,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5248,c_5534])).

tff(c_5554,plain,(
    ! [D_413] :
      ( ~ r2_hidden(D_413,'#skF_6')
      | ~ m1_subset_1(D_413,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_5572,plain,(
    ! [B_16] :
      ( ~ m1_subset_1(B_16,'#skF_4')
      | ~ m1_subset_1(B_16,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_24,c_5554])).

tff(c_5596,plain,(
    ! [B_417] :
      ( ~ m1_subset_1(B_417,'#skF_4')
      | ~ m1_subset_1(B_417,'#skF_6') ) ),
    inference(splitLeft,[status(thm)],[c_5572])).

tff(c_5606,plain,(
    ! [B_16] :
      ( ~ m1_subset_1(B_16,'#skF_4')
      | ~ v1_xboole_0(B_16)
      | ~ v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_26,c_5596])).

tff(c_5607,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_5606])).

tff(c_5574,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6'),'#skF_4')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_5554])).

tff(c_5575,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5574])).

tff(c_5579,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_6'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_5575])).

tff(c_5593,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5579])).

tff(c_5618,plain,(
    ! [A_420,B_421] :
      ( r2_hidden('#skF_1'(A_420),B_421)
      | ~ r1_tarski(A_420,B_421)
      | v1_xboole_0(A_420) ) ),
    inference(resolution,[status(thm)],[c_4,c_187])).

tff(c_5945,plain,(
    ! [A_462,B_463] :
      ( m1_subset_1('#skF_1'(A_462),B_463)
      | v1_xboole_0(B_463)
      | ~ r1_tarski(A_462,B_463)
      | v1_xboole_0(A_462) ) ),
    inference(resolution,[status(thm)],[c_5618,c_22])).

tff(c_5964,plain,
    ( v1_xboole_0('#skF_4')
    | ~ r1_tarski('#skF_6','#skF_4')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_5945,c_5575])).

tff(c_5982,plain,(
    ~ r1_tarski('#skF_6','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_5607,c_5593,c_5964])).

tff(c_5580,plain,(
    ! [C_414,A_415,B_416] :
      ( r2_hidden(C_414,A_415)
      | ~ r2_hidden(C_414,B_416)
      | ~ m1_subset_1(B_416,k1_zfmisc_1(A_415)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6026,plain,(
    ! [A_466,B_467,A_468] :
      ( r2_hidden('#skF_2'(A_466,B_467),A_468)
      | ~ m1_subset_1(A_466,k1_zfmisc_1(A_468))
      | r1_tarski(A_466,B_467) ) ),
    inference(resolution,[status(thm)],[c_10,c_5580])).

tff(c_6056,plain,(
    ! [A_469,A_470] :
      ( ~ m1_subset_1(A_469,k1_zfmisc_1(A_470))
      | r1_tarski(A_469,A_470) ) ),
    inference(resolution,[status(thm)],[c_6026,c_8])).

tff(c_6079,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_6056])).

tff(c_6091,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5982,c_6079])).

tff(c_6093,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_5606])).

tff(c_5544,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_5547,plain,(
    ! [A_46] :
      ( A_46 = '#skF_5'
      | ~ v1_xboole_0(A_46) ) ),
    inference(resolution,[status(thm)],[c_5544,c_212])).

tff(c_6096,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_6093,c_5547])).

tff(c_6102,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_6096])).

tff(c_6104,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_5579])).

tff(c_6110,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6104,c_5547])).

tff(c_6117,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6110,c_32])).

tff(c_6193,plain,(
    ! [B_477] :
      ( ~ m1_subset_1(B_477,'#skF_4')
      | ~ m1_subset_1(B_477,'#skF_6') ) ),
    inference(splitLeft,[status(thm)],[c_5572])).

tff(c_6203,plain,(
    ! [B_16] :
      ( ~ m1_subset_1(B_16,'#skF_4')
      | ~ v1_xboole_0(B_16)
      | ~ v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_26,c_6193])).

tff(c_6232,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_6203])).

tff(c_6320,plain,(
    ! [A_495,A_496] :
      ( r2_hidden('#skF_1'(A_495),A_496)
      | ~ m1_subset_1(A_495,k1_zfmisc_1(A_496))
      | v1_xboole_0(A_495) ) ),
    inference(resolution,[status(thm)],[c_4,c_5580])).

tff(c_6345,plain,(
    ! [A_497,A_498] :
      ( ~ v1_xboole_0(A_497)
      | ~ m1_subset_1(A_498,k1_zfmisc_1(A_497))
      | v1_xboole_0(A_498) ) ),
    inference(resolution,[status(thm)],[c_6320,c_2])).

tff(c_6363,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_6345])).

tff(c_6372,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6104,c_6363])).

tff(c_6374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6232,c_6372])).

tff(c_6376,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_6203])).

tff(c_6111,plain,(
    ! [A_46] :
      ( A_46 = '#skF_4'
      | ~ v1_xboole_0(A_46) ) ),
    inference(resolution,[status(thm)],[c_6104,c_212])).

tff(c_6379,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6376,c_6111])).

tff(c_6385,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6117,c_6379])).

tff(c_6386,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_5574])).

tff(c_6403,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_6386,c_5547])).

tff(c_6409,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_6403])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:23:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.10/2.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.10/2.16  
% 6.10/2.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.10/2.16  %$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 6.10/2.16  
% 6.10/2.16  %Foreground sorts:
% 6.10/2.16  
% 6.10/2.16  
% 6.10/2.16  %Background operators:
% 6.10/2.16  
% 6.10/2.16  
% 6.10/2.16  %Foreground operators:
% 6.10/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.10/2.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.10/2.16  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.10/2.16  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.10/2.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.10/2.16  tff('#skF_5', type, '#skF_5': $i).
% 6.10/2.16  tff('#skF_6', type, '#skF_6': $i).
% 6.10/2.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.10/2.16  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 6.10/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.10/2.16  tff('#skF_4', type, '#skF_4': $i).
% 6.10/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.10/2.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.10/2.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.10/2.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.10/2.16  
% 6.10/2.18  tff(f_90, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_subset_1)).
% 6.10/2.18  tff(f_68, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 6.10/2.18  tff(f_45, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 6.10/2.18  tff(f_55, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_0)).
% 6.10/2.18  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.10/2.18  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.10/2.18  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 6.10/2.18  tff(c_32, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.10/2.18  tff(c_26, plain, (![B_16, A_15]: (m1_subset_1(B_16, A_15) | ~v1_xboole_0(B_16) | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.10/2.18  tff(c_24, plain, (![B_16, A_15]: (r2_hidden(B_16, A_15) | ~m1_subset_1(B_16, A_15) | v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.10/2.18  tff(c_12, plain, (![A_10, B_11]: (r2_xboole_0(A_10, B_11) | B_11=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.10/2.18  tff(c_20, plain, (![A_12, B_13]: (r2_hidden('#skF_3'(A_12, B_13), B_13) | ~r2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.10/2.18  tff(c_38, plain, (![D_25]: (r2_hidden(D_25, '#skF_5') | ~r2_hidden(D_25, '#skF_6') | ~m1_subset_1(D_25, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.10/2.18  tff(c_154, plain, (![A_54, B_55]: (~r2_hidden('#skF_3'(A_54, B_55), A_54) | ~r2_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.10/2.18  tff(c_2554, plain, (![B_268]: (~r2_xboole_0('#skF_5', B_268) | ~r2_hidden('#skF_3'('#skF_5', B_268), '#skF_6') | ~m1_subset_1('#skF_3'('#skF_5', B_268), '#skF_4'))), inference(resolution, [status(thm)], [c_38, c_154])).
% 6.10/2.18  tff(c_2569, plain, (~m1_subset_1('#skF_3'('#skF_5', '#skF_6'), '#skF_4') | ~r2_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_20, c_2554])).
% 6.10/2.18  tff(c_2570, plain, (~r2_xboole_0('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_2569])).
% 6.10/2.18  tff(c_2573, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_12, c_2570])).
% 6.10/2.18  tff(c_2576, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_32, c_2573])).
% 6.10/2.18  tff(c_59, plain, (![D_34]: (r2_hidden(D_34, '#skF_5') | ~r2_hidden(D_34, '#skF_6') | ~m1_subset_1(D_34, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.10/2.18  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.10/2.18  tff(c_63, plain, (![D_34]: (~v1_xboole_0('#skF_5') | ~r2_hidden(D_34, '#skF_6') | ~m1_subset_1(D_34, '#skF_4'))), inference(resolution, [status(thm)], [c_59, c_2])).
% 6.10/2.18  tff(c_214, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_63])).
% 6.10/2.18  tff(c_102, plain, (![A_46, B_47]: (r2_hidden('#skF_2'(A_46, B_47), A_46) | r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.10/2.18  tff(c_22, plain, (![B_16, A_15]: (m1_subset_1(B_16, A_15) | ~r2_hidden(B_16, A_15) | v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.10/2.18  tff(c_109, plain, (![A_46, B_47]: (m1_subset_1('#skF_2'(A_46, B_47), A_46) | v1_xboole_0(A_46) | r1_tarski(A_46, B_47))), inference(resolution, [status(thm)], [c_102, c_22])).
% 6.10/2.18  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.10/2.18  tff(c_111, plain, (![D_48]: (r2_hidden(D_48, '#skF_6') | ~r2_hidden(D_48, '#skF_5') | ~m1_subset_1(D_48, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.10/2.18  tff(c_135, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_6') | ~m1_subset_1('#skF_1'('#skF_5'), '#skF_4') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_111])).
% 6.10/2.18  tff(c_215, plain, (~m1_subset_1('#skF_1'('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_135])).
% 6.10/2.18  tff(c_219, plain, (~v1_xboole_0('#skF_1'('#skF_5')) | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_26, c_215])).
% 6.10/2.18  tff(c_220, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_219])).
% 6.10/2.18  tff(c_187, plain, (![C_58, B_59, A_60]: (r2_hidden(C_58, B_59) | ~r2_hidden(C_58, A_60) | ~r1_tarski(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.10/2.18  tff(c_221, plain, (![A_65, B_66]: (r2_hidden('#skF_1'(A_65), B_66) | ~r1_tarski(A_65, B_66) | v1_xboole_0(A_65))), inference(resolution, [status(thm)], [c_4, c_187])).
% 6.10/2.18  tff(c_928, plain, (![A_137, B_138]: (m1_subset_1('#skF_1'(A_137), B_138) | v1_xboole_0(B_138) | ~r1_tarski(A_137, B_138) | v1_xboole_0(A_137))), inference(resolution, [status(thm)], [c_221, c_22])).
% 6.10/2.18  tff(c_935, plain, (v1_xboole_0('#skF_4') | ~r1_tarski('#skF_5', '#skF_4') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_928, c_215])).
% 6.10/2.18  tff(c_942, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_214, c_220, c_935])).
% 6.10/2.18  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.10/2.18  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.10/2.18  tff(c_238, plain, (![C_67, A_68, B_69]: (r2_hidden(C_67, A_68) | ~r2_hidden(C_67, B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.10/2.18  tff(c_993, plain, (![A_141, B_142, A_143]: (r2_hidden('#skF_2'(A_141, B_142), A_143) | ~m1_subset_1(A_141, k1_zfmisc_1(A_143)) | r1_tarski(A_141, B_142))), inference(resolution, [status(thm)], [c_10, c_238])).
% 6.10/2.18  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.10/2.18  tff(c_1031, plain, (![A_144, A_145]: (~m1_subset_1(A_144, k1_zfmisc_1(A_145)) | r1_tarski(A_144, A_145))), inference(resolution, [status(thm)], [c_993, c_8])).
% 6.10/2.18  tff(c_1057, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_36, c_1031])).
% 6.10/2.18  tff(c_1067, plain, $false, inference(negUnitSimplification, [status(thm)], [c_942, c_1057])).
% 6.10/2.18  tff(c_1069, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_219])).
% 6.10/2.18  tff(c_1345, plain, (![C_172, A_173, B_174]: (r2_hidden(C_172, A_173) | ~r2_hidden(C_172, B_174) | ~m1_subset_1(B_174, k1_zfmisc_1(A_173)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.10/2.18  tff(c_1450, plain, (![A_178, A_179]: (r2_hidden('#skF_1'(A_178), A_179) | ~m1_subset_1(A_178, k1_zfmisc_1(A_179)) | v1_xboole_0(A_178))), inference(resolution, [status(thm)], [c_4, c_1345])).
% 6.10/2.18  tff(c_1475, plain, (![A_180, A_181]: (~v1_xboole_0(A_180) | ~m1_subset_1(A_181, k1_zfmisc_1(A_180)) | v1_xboole_0(A_181))), inference(resolution, [status(thm)], [c_1450, c_2])).
% 6.10/2.18  tff(c_1489, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_36, c_1475])).
% 6.10/2.18  tff(c_1497, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1069, c_1489])).
% 6.10/2.18  tff(c_1499, plain, $false, inference(negUnitSimplification, [status(thm)], [c_214, c_1497])).
% 6.10/2.18  tff(c_1501, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_135])).
% 6.10/2.18  tff(c_28, plain, (![B_16, A_15]: (v1_xboole_0(B_16) | ~m1_subset_1(B_16, A_15) | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.10/2.18  tff(c_1505, plain, (v1_xboole_0('#skF_1'('#skF_5')) | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1501, c_28])).
% 6.10/2.18  tff(c_1522, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_1505])).
% 6.10/2.18  tff(c_1506, plain, (![C_182, A_183, B_184]: (r2_hidden(C_182, A_183) | ~r2_hidden(C_182, B_184) | ~m1_subset_1(B_184, k1_zfmisc_1(A_183)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.10/2.18  tff(c_3091, plain, (![B_305, A_306, A_307]: (r2_hidden(B_305, A_306) | ~m1_subset_1(A_307, k1_zfmisc_1(A_306)) | ~m1_subset_1(B_305, A_307) | v1_xboole_0(A_307))), inference(resolution, [status(thm)], [c_24, c_1506])).
% 6.10/2.18  tff(c_3119, plain, (![B_305]: (r2_hidden(B_305, '#skF_4') | ~m1_subset_1(B_305, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_36, c_3091])).
% 6.10/2.18  tff(c_3161, plain, (![B_309]: (r2_hidden(B_309, '#skF_4') | ~m1_subset_1(B_309, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_214, c_3119])).
% 6.10/2.18  tff(c_3176, plain, (![B_309]: (m1_subset_1(B_309, '#skF_4') | v1_xboole_0('#skF_4') | ~m1_subset_1(B_309, '#skF_5'))), inference(resolution, [status(thm)], [c_3161, c_22])).
% 6.10/2.18  tff(c_3262, plain, (![B_313]: (m1_subset_1(B_313, '#skF_4') | ~m1_subset_1(B_313, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_1522, c_3176])).
% 6.10/2.18  tff(c_3289, plain, (![B_47]: (m1_subset_1('#skF_2'('#skF_5', B_47), '#skF_4') | v1_xboole_0('#skF_5') | r1_tarski('#skF_5', B_47))), inference(resolution, [status(thm)], [c_109, c_3262])).
% 6.10/2.18  tff(c_3821, plain, (![B_332]: (m1_subset_1('#skF_2'('#skF_5', B_332), '#skF_4') | r1_tarski('#skF_5', B_332))), inference(negUnitSimplification, [status(thm)], [c_214, c_3289])).
% 6.10/2.18  tff(c_2777, plain, (![B_295]: (r2_hidden('#skF_2'('#skF_5', B_295), '#skF_6') | ~m1_subset_1('#skF_2'('#skF_5', B_295), '#skF_4') | r1_tarski('#skF_5', B_295))), inference(resolution, [status(thm)], [c_10, c_111])).
% 6.10/2.18  tff(c_2794, plain, (~m1_subset_1('#skF_2'('#skF_5', '#skF_6'), '#skF_4') | r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_2777, c_8])).
% 6.10/2.18  tff(c_2809, plain, (~m1_subset_1('#skF_2'('#skF_5', '#skF_6'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_2576, c_2576, c_2794])).
% 6.10/2.18  tff(c_3824, plain, (r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_3821, c_2809])).
% 6.10/2.18  tff(c_3839, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2576, c_3824])).
% 6.10/2.18  tff(c_3841, plain, (r2_xboole_0('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_2569])).
% 6.10/2.18  tff(c_1500, plain, (v1_xboole_0('#skF_5') | r2_hidden('#skF_1'('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_135])).
% 6.10/2.18  tff(c_1523, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_214, c_1500])).
% 6.10/2.18  tff(c_1537, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_1523, c_2])).
% 6.10/2.18  tff(c_83, plain, (![A_40, B_41]: (r2_hidden('#skF_3'(A_40, B_41), B_41) | ~r2_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.10/2.18  tff(c_90, plain, (![A_40, B_41]: (m1_subset_1('#skF_3'(A_40, B_41), B_41) | v1_xboole_0(B_41) | ~r2_xboole_0(A_40, B_41))), inference(resolution, [status(thm)], [c_83, c_22])).
% 6.10/2.18  tff(c_34, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.10/2.18  tff(c_4442, plain, (![A_365, B_366, A_367]: (r2_hidden('#skF_2'(A_365, B_366), A_367) | ~m1_subset_1(A_365, k1_zfmisc_1(A_367)) | r1_tarski(A_365, B_366))), inference(resolution, [status(thm)], [c_10, c_1506])).
% 6.10/2.18  tff(c_4486, plain, (![A_368, A_369]: (~m1_subset_1(A_368, k1_zfmisc_1(A_369)) | r1_tarski(A_368, A_369))), inference(resolution, [status(thm)], [c_4442, c_8])).
% 6.10/2.18  tff(c_4528, plain, (r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_4486])).
% 6.10/2.18  tff(c_199, plain, (![B_16, B_59, A_15]: (r2_hidden(B_16, B_59) | ~r1_tarski(A_15, B_59) | ~m1_subset_1(B_16, A_15) | v1_xboole_0(A_15))), inference(resolution, [status(thm)], [c_24, c_187])).
% 6.10/2.18  tff(c_4531, plain, (![B_16]: (r2_hidden(B_16, '#skF_4') | ~m1_subset_1(B_16, '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_4528, c_199])).
% 6.10/2.18  tff(c_4654, plain, (![B_372]: (r2_hidden(B_372, '#skF_4') | ~m1_subset_1(B_372, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_1537, c_4531])).
% 6.10/2.18  tff(c_4669, plain, (![B_372]: (m1_subset_1(B_372, '#skF_4') | v1_xboole_0('#skF_4') | ~m1_subset_1(B_372, '#skF_6'))), inference(resolution, [status(thm)], [c_4654, c_22])).
% 6.10/2.18  tff(c_4788, plain, (![B_377]: (m1_subset_1(B_377, '#skF_4') | ~m1_subset_1(B_377, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_1522, c_4669])).
% 6.10/2.18  tff(c_4799, plain, (![A_40]: (m1_subset_1('#skF_3'(A_40, '#skF_6'), '#skF_4') | v1_xboole_0('#skF_6') | ~r2_xboole_0(A_40, '#skF_6'))), inference(resolution, [status(thm)], [c_90, c_4788])).
% 6.10/2.18  tff(c_5232, plain, (![A_399]: (m1_subset_1('#skF_3'(A_399, '#skF_6'), '#skF_4') | ~r2_xboole_0(A_399, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_1537, c_4799])).
% 6.10/2.18  tff(c_3840, plain, (~m1_subset_1('#skF_3'('#skF_5', '#skF_6'), '#skF_4')), inference(splitRight, [status(thm)], [c_2569])).
% 6.10/2.18  tff(c_5235, plain, (~r2_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_5232, c_3840])).
% 6.10/2.18  tff(c_5246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3841, c_5235])).
% 6.10/2.18  tff(c_5248, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_1505])).
% 6.10/2.18  tff(c_5247, plain, (v1_xboole_0('#skF_1'('#skF_5'))), inference(splitRight, [status(thm)], [c_1505])).
% 6.10/2.18  tff(c_110, plain, (![A_46, B_47]: (~v1_xboole_0(A_46) | r1_tarski(A_46, B_47))), inference(resolution, [status(thm)], [c_102, c_2])).
% 6.10/2.18  tff(c_170, plain, (![A_56, B_57]: (r2_xboole_0(A_56, B_57) | B_57=A_56 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.10/2.18  tff(c_91, plain, (![B_41, A_40]: (~v1_xboole_0(B_41) | ~r2_xboole_0(A_40, B_41))), inference(resolution, [status(thm)], [c_83, c_2])).
% 6.10/2.18  tff(c_203, plain, (![B_61, A_62]: (~v1_xboole_0(B_61) | B_61=A_62 | ~r1_tarski(A_62, B_61))), inference(resolution, [status(thm)], [c_170, c_91])).
% 6.10/2.18  tff(c_212, plain, (![B_47, A_46]: (~v1_xboole_0(B_47) | B_47=A_46 | ~v1_xboole_0(A_46))), inference(resolution, [status(thm)], [c_110, c_203])).
% 6.10/2.18  tff(c_5281, plain, (![A_401]: (A_401='#skF_4' | ~v1_xboole_0(A_401))), inference(resolution, [status(thm)], [c_5248, c_212])).
% 6.10/2.18  tff(c_5288, plain, ('#skF_1'('#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_5247, c_5281])).
% 6.10/2.18  tff(c_5312, plain, (v1_xboole_0('#skF_5') | r2_hidden('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5288, c_1500])).
% 6.10/2.18  tff(c_5313, plain, (r2_hidden('#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_214, c_5312])).
% 6.10/2.18  tff(c_30, plain, (![C_20, A_17, B_18]: (r2_hidden(C_20, A_17) | ~r2_hidden(C_20, B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.10/2.18  tff(c_5516, plain, (![A_411]: (r2_hidden('#skF_4', A_411) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_411)))), inference(resolution, [status(thm)], [c_5313, c_30])).
% 6.10/2.18  tff(c_5524, plain, (r2_hidden('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_5516])).
% 6.10/2.18  tff(c_5534, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_5524, c_2])).
% 6.10/2.18  tff(c_5542, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5248, c_5534])).
% 6.10/2.18  tff(c_5554, plain, (![D_413]: (~r2_hidden(D_413, '#skF_6') | ~m1_subset_1(D_413, '#skF_4'))), inference(splitRight, [status(thm)], [c_63])).
% 6.10/2.18  tff(c_5572, plain, (![B_16]: (~m1_subset_1(B_16, '#skF_4') | ~m1_subset_1(B_16, '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_24, c_5554])).
% 6.10/2.18  tff(c_5596, plain, (![B_417]: (~m1_subset_1(B_417, '#skF_4') | ~m1_subset_1(B_417, '#skF_6'))), inference(splitLeft, [status(thm)], [c_5572])).
% 6.10/2.18  tff(c_5606, plain, (![B_16]: (~m1_subset_1(B_16, '#skF_4') | ~v1_xboole_0(B_16) | ~v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_26, c_5596])).
% 6.10/2.18  tff(c_5607, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_5606])).
% 6.10/2.18  tff(c_5574, plain, (~m1_subset_1('#skF_1'('#skF_6'), '#skF_4') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_4, c_5554])).
% 6.10/2.18  tff(c_5575, plain, (~m1_subset_1('#skF_1'('#skF_6'), '#skF_4')), inference(splitLeft, [status(thm)], [c_5574])).
% 6.10/2.18  tff(c_5579, plain, (~v1_xboole_0('#skF_1'('#skF_6')) | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_26, c_5575])).
% 6.10/2.18  tff(c_5593, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_5579])).
% 6.10/2.18  tff(c_5618, plain, (![A_420, B_421]: (r2_hidden('#skF_1'(A_420), B_421) | ~r1_tarski(A_420, B_421) | v1_xboole_0(A_420))), inference(resolution, [status(thm)], [c_4, c_187])).
% 6.10/2.18  tff(c_5945, plain, (![A_462, B_463]: (m1_subset_1('#skF_1'(A_462), B_463) | v1_xboole_0(B_463) | ~r1_tarski(A_462, B_463) | v1_xboole_0(A_462))), inference(resolution, [status(thm)], [c_5618, c_22])).
% 6.10/2.18  tff(c_5964, plain, (v1_xboole_0('#skF_4') | ~r1_tarski('#skF_6', '#skF_4') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_5945, c_5575])).
% 6.10/2.18  tff(c_5982, plain, (~r1_tarski('#skF_6', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_5607, c_5593, c_5964])).
% 6.10/2.18  tff(c_5580, plain, (![C_414, A_415, B_416]: (r2_hidden(C_414, A_415) | ~r2_hidden(C_414, B_416) | ~m1_subset_1(B_416, k1_zfmisc_1(A_415)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.10/2.18  tff(c_6026, plain, (![A_466, B_467, A_468]: (r2_hidden('#skF_2'(A_466, B_467), A_468) | ~m1_subset_1(A_466, k1_zfmisc_1(A_468)) | r1_tarski(A_466, B_467))), inference(resolution, [status(thm)], [c_10, c_5580])).
% 6.10/2.18  tff(c_6056, plain, (![A_469, A_470]: (~m1_subset_1(A_469, k1_zfmisc_1(A_470)) | r1_tarski(A_469, A_470))), inference(resolution, [status(thm)], [c_6026, c_8])).
% 6.10/2.18  tff(c_6079, plain, (r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_6056])).
% 6.10/2.18  tff(c_6091, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5982, c_6079])).
% 6.10/2.18  tff(c_6093, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_5606])).
% 6.10/2.18  tff(c_5544, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_63])).
% 6.10/2.18  tff(c_5547, plain, (![A_46]: (A_46='#skF_5' | ~v1_xboole_0(A_46))), inference(resolution, [status(thm)], [c_5544, c_212])).
% 6.10/2.18  tff(c_6096, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_6093, c_5547])).
% 6.10/2.18  tff(c_6102, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_6096])).
% 6.10/2.18  tff(c_6104, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_5579])).
% 6.10/2.18  tff(c_6110, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_6104, c_5547])).
% 6.10/2.18  tff(c_6117, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6110, c_32])).
% 6.10/2.18  tff(c_6193, plain, (![B_477]: (~m1_subset_1(B_477, '#skF_4') | ~m1_subset_1(B_477, '#skF_6'))), inference(splitLeft, [status(thm)], [c_5572])).
% 6.10/2.18  tff(c_6203, plain, (![B_16]: (~m1_subset_1(B_16, '#skF_4') | ~v1_xboole_0(B_16) | ~v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_26, c_6193])).
% 6.10/2.18  tff(c_6232, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_6203])).
% 6.10/2.18  tff(c_6320, plain, (![A_495, A_496]: (r2_hidden('#skF_1'(A_495), A_496) | ~m1_subset_1(A_495, k1_zfmisc_1(A_496)) | v1_xboole_0(A_495))), inference(resolution, [status(thm)], [c_4, c_5580])).
% 6.10/2.18  tff(c_6345, plain, (![A_497, A_498]: (~v1_xboole_0(A_497) | ~m1_subset_1(A_498, k1_zfmisc_1(A_497)) | v1_xboole_0(A_498))), inference(resolution, [status(thm)], [c_6320, c_2])).
% 6.10/2.18  tff(c_6363, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_34, c_6345])).
% 6.10/2.18  tff(c_6372, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6104, c_6363])).
% 6.10/2.18  tff(c_6374, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6232, c_6372])).
% 6.10/2.18  tff(c_6376, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_6203])).
% 6.10/2.18  tff(c_6111, plain, (![A_46]: (A_46='#skF_4' | ~v1_xboole_0(A_46))), inference(resolution, [status(thm)], [c_6104, c_212])).
% 6.10/2.18  tff(c_6379, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_6376, c_6111])).
% 6.10/2.18  tff(c_6385, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6117, c_6379])).
% 6.10/2.18  tff(c_6386, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_5574])).
% 6.10/2.18  tff(c_6403, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_6386, c_5547])).
% 6.10/2.18  tff(c_6409, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_6403])).
% 6.10/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.10/2.18  
% 6.10/2.18  Inference rules
% 6.10/2.18  ----------------------
% 6.10/2.18  #Ref     : 0
% 6.10/2.18  #Sup     : 1327
% 6.10/2.18  #Fact    : 0
% 6.10/2.18  #Define  : 0
% 6.10/2.18  #Split   : 29
% 6.10/2.18  #Chain   : 0
% 6.10/2.18  #Close   : 0
% 6.10/2.18  
% 6.10/2.18  Ordering : KBO
% 6.10/2.18  
% 6.10/2.18  Simplification rules
% 6.10/2.18  ----------------------
% 6.10/2.18  #Subsume      : 323
% 6.10/2.18  #Demod        : 267
% 6.10/2.18  #Tautology    : 193
% 6.10/2.18  #SimpNegUnit  : 194
% 6.10/2.18  #BackRed      : 13
% 6.10/2.18  
% 6.10/2.18  #Partial instantiations: 0
% 6.10/2.18  #Strategies tried      : 1
% 6.10/2.18  
% 6.10/2.18  Timing (in seconds)
% 6.10/2.18  ----------------------
% 6.10/2.19  Preprocessing        : 0.29
% 6.10/2.19  Parsing              : 0.15
% 6.10/2.19  CNF conversion       : 0.02
% 6.10/2.19  Main loop            : 1.11
% 6.10/2.19  Inferencing          : 0.39
% 6.10/2.19  Reduction            : 0.30
% 6.10/2.19  Demodulation         : 0.19
% 6.10/2.19  BG Simplification    : 0.04
% 6.10/2.19  Subsumption          : 0.28
% 6.10/2.19  Abstraction          : 0.04
% 6.10/2.19  MUC search           : 0.00
% 6.10/2.19  Cooper               : 0.00
% 6.10/2.19  Total                : 1.45
% 6.10/2.19  Index Insertion      : 0.00
% 6.10/2.19  Index Deletion       : 0.00
% 6.10/2.19  Index Matching       : 0.00
% 6.10/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
