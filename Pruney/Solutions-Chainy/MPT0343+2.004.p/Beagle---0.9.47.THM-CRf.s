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
% DateTime   : Thu Dec  3 09:55:17 EST 2020

% Result     : Theorem 4.76s
% Output     : CNFRefutation 5.09s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 855 expanded)
%              Number of leaves         :   19 ( 267 expanded)
%              Depth                    :   17
%              Number of atoms          :  288 (2306 expanded)
%              Number of equality atoms :   17 ( 125 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_79,negated_conjecture,(
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

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

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

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_28,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_22,plain,(
    ! [B_13,A_12] :
      ( m1_subset_1(B_13,A_12)
      | ~ v1_xboole_0(B_13)
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_118,plain,(
    ! [D_45] :
      ( r2_hidden(D_45,'#skF_5')
      | ~ r2_hidden(D_45,'#skF_4')
      | ~ m1_subset_1(D_45,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,(
    ! [D_45] :
      ( ~ v1_xboole_0('#skF_5')
      | ~ r2_hidden(D_45,'#skF_4')
      | ~ m1_subset_1(D_45,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_118,c_2])).

tff(c_156,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_55,plain,(
    ! [D_29] :
      ( r2_hidden(D_29,'#skF_4')
      | ~ r2_hidden(D_29,'#skF_5')
      | ~ m1_subset_1(D_29,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_60,plain,
    ( r2_hidden('#skF_1'('#skF_5'),'#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_3')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_55])).

tff(c_217,plain,
    ( r2_hidden('#skF_1'('#skF_5'),'#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_60])).

tff(c_218,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_222,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_5'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_218])).

tff(c_223,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_222])).

tff(c_157,plain,(
    ! [C_50,B_51,A_52] :
      ( r2_hidden(C_50,B_51)
      | ~ r2_hidden(C_50,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_183,plain,(
    ! [A_56,B_57] :
      ( r2_hidden('#skF_1'(A_56),B_57)
      | ~ r1_tarski(A_56,B_57)
      | v1_xboole_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_4,c_157])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( m1_subset_1(B_13,A_12)
      | ~ r2_hidden(B_13,A_12)
      | v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_388,plain,(
    ! [A_80,B_81] :
      ( m1_subset_1('#skF_1'(A_80),B_81)
      | v1_xboole_0(B_81)
      | ~ r1_tarski(A_80,B_81)
      | v1_xboole_0(A_80) ) ),
    inference(resolution,[status(thm)],[c_183,c_18])).

tff(c_398,plain,
    ( v1_xboole_0('#skF_3')
    | ~ r1_tarski('#skF_5','#skF_3')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_388,c_218])).

tff(c_408,plain,(
    ~ r1_tarski('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_223,c_398])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_170,plain,(
    ! [C_53,A_54,B_55] :
      ( r2_hidden(C_53,A_54)
      | ~ r2_hidden(C_53,B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_497,plain,(
    ! [A_88,B_89,A_90] :
      ( r2_hidden('#skF_2'(A_88,B_89),A_90)
      | ~ m1_subset_1(A_88,k1_zfmisc_1(A_90))
      | r1_tarski(A_88,B_89) ) ),
    inference(resolution,[status(thm)],[c_10,c_170])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_531,plain,(
    ! [A_91,A_92] :
      ( ~ m1_subset_1(A_91,k1_zfmisc_1(A_92))
      | r1_tarski(A_91,A_92) ) ),
    inference(resolution,[status(thm)],[c_497,c_8])).

tff(c_550,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_531])).

tff(c_561,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_408,c_550])).

tff(c_563,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_564,plain,(
    ! [A_93,A_94] :
      ( r2_hidden('#skF_1'(A_93),A_94)
      | ~ m1_subset_1(A_93,k1_zfmisc_1(A_94))
      | v1_xboole_0(A_93) ) ),
    inference(resolution,[status(thm)],[c_4,c_170])).

tff(c_620,plain,(
    ! [A_97,A_98] :
      ( ~ v1_xboole_0(A_97)
      | ~ m1_subset_1(A_98,k1_zfmisc_1(A_97))
      | v1_xboole_0(A_98) ) ),
    inference(resolution,[status(thm)],[c_564,c_2])).

tff(c_635,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_620])).

tff(c_644,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_563,c_635])).

tff(c_646,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_644])).

tff(c_647,plain,(
    r2_hidden('#skF_1'('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_662,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_647,c_2])).

tff(c_84,plain,(
    ! [A_39,B_40] :
      ( r2_hidden('#skF_2'(A_39,B_40),A_39)
      | r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_101,plain,(
    ! [A_39,B_40] :
      ( m1_subset_1('#skF_2'(A_39,B_40),A_39)
      | v1_xboole_0(A_39)
      | r1_tarski(A_39,B_40) ) ),
    inference(resolution,[status(thm)],[c_84,c_18])).

tff(c_648,plain,(
    m1_subset_1('#skF_1'('#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_24,plain,(
    ! [B_13,A_12] :
      ( v1_xboole_0(B_13)
      | ~ m1_subset_1(B_13,A_12)
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_666,plain,
    ( v1_xboole_0('#skF_1'('#skF_5'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_648,c_24])).

tff(c_667,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_666])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_20,plain,(
    ! [B_13,A_12] :
      ( r2_hidden(B_13,A_12)
      | ~ m1_subset_1(B_13,A_12)
      | v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2096,plain,(
    ! [B_182,A_183,A_184] :
      ( r2_hidden(B_182,A_183)
      | ~ m1_subset_1(A_184,k1_zfmisc_1(A_183))
      | ~ m1_subset_1(B_182,A_184)
      | v1_xboole_0(A_184) ) ),
    inference(resolution,[status(thm)],[c_20,c_170])).

tff(c_2124,plain,(
    ! [B_182] :
      ( r2_hidden(B_182,'#skF_3')
      | ~ m1_subset_1(B_182,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_2096])).

tff(c_2165,plain,(
    ! [B_186] :
      ( r2_hidden(B_186,'#skF_3')
      | ~ m1_subset_1(B_186,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_662,c_2124])).

tff(c_2176,plain,(
    ! [B_186] :
      ( m1_subset_1(B_186,'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(B_186,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2165,c_18])).

tff(c_2185,plain,(
    ! [B_186] :
      ( m1_subset_1(B_186,'#skF_3')
      | ~ m1_subset_1(B_186,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_667,c_2176])).

tff(c_2047,plain,(
    ! [A_181] :
      ( r1_tarski(A_181,'#skF_5')
      | ~ r2_hidden('#skF_2'(A_181,'#skF_5'),'#skF_4')
      | ~ m1_subset_1('#skF_2'(A_181,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_118,c_8])).

tff(c_2072,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_4','#skF_5'),'#skF_3')
    | r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_2047])).

tff(c_2306,plain,(
    ~ m1_subset_1('#skF_2'('#skF_4','#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2072])).

tff(c_2313,plain,(
    ~ m1_subset_1('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_2185,c_2306])).

tff(c_2317,plain,
    ( v1_xboole_0('#skF_4')
    | r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_101,c_2313])).

tff(c_2323,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_662,c_2317])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2343,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_2323,c_12])).

tff(c_2359,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_2343])).

tff(c_2122,plain,(
    ! [B_182] :
      ( r2_hidden(B_182,'#skF_3')
      | ~ m1_subset_1(B_182,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_2096])).

tff(c_2143,plain,(
    ! [B_185] :
      ( r2_hidden(B_185,'#skF_3')
      | ~ m1_subset_1(B_185,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_2122])).

tff(c_2154,plain,(
    ! [B_185] :
      ( m1_subset_1(B_185,'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(B_185,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2143,c_18])).

tff(c_2222,plain,(
    ! [B_188] :
      ( m1_subset_1(B_188,'#skF_3')
      | ~ m1_subset_1(B_188,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_667,c_2154])).

tff(c_2255,plain,(
    ! [B_40] :
      ( m1_subset_1('#skF_2'('#skF_5',B_40),'#skF_3')
      | v1_xboole_0('#skF_5')
      | r1_tarski('#skF_5',B_40) ) ),
    inference(resolution,[status(thm)],[c_101,c_2222])).

tff(c_2578,plain,(
    ! [B_198] :
      ( m1_subset_1('#skF_2'('#skF_5',B_198),'#skF_3')
      | r1_tarski('#skF_5',B_198) ) ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_2255])).

tff(c_34,plain,(
    ! [D_22] :
      ( r2_hidden(D_22,'#skF_4')
      | ~ r2_hidden(D_22,'#skF_5')
      | ~ m1_subset_1(D_22,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2187,plain,(
    ! [B_187] :
      ( r2_hidden('#skF_2'('#skF_5',B_187),'#skF_4')
      | ~ m1_subset_1('#skF_2'('#skF_5',B_187),'#skF_3')
      | r1_tarski('#skF_5',B_187) ) ),
    inference(resolution,[status(thm)],[c_84,c_34])).

tff(c_2217,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_5','#skF_4'),'#skF_3')
    | r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_2187,c_8])).

tff(c_2468,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_2359,c_2217])).

tff(c_2581,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_2578,c_2468])).

tff(c_2592,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2359,c_2581])).

tff(c_2593,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_2072])).

tff(c_2613,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_2593,c_12])).

tff(c_2629,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_2613])).

tff(c_2888,plain,(
    ! [B_209] :
      ( m1_subset_1('#skF_2'('#skF_5',B_209),'#skF_3')
      | r1_tarski('#skF_5',B_209) ) ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_2255])).

tff(c_2767,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_2629,c_2217])).

tff(c_2891,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_2888,c_2767])).

tff(c_2902,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2629,c_2891])).

tff(c_2904,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_666])).

tff(c_2903,plain,(
    v1_xboole_0('#skF_1'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_666])).

tff(c_103,plain,(
    ! [A_39,B_40] :
      ( ~ v1_xboole_0(A_39)
      | r1_tarski(A_39,B_40) ) ),
    inference(resolution,[status(thm)],[c_84,c_2])).

tff(c_104,plain,(
    ! [A_41,B_42] :
      ( ~ v1_xboole_0(A_41)
      | r1_tarski(A_41,B_42) ) ),
    inference(resolution,[status(thm)],[c_84,c_2])).

tff(c_108,plain,(
    ! [B_43,A_44] :
      ( B_43 = A_44
      | ~ r1_tarski(B_43,A_44)
      | ~ v1_xboole_0(A_44) ) ),
    inference(resolution,[status(thm)],[c_104,c_12])).

tff(c_115,plain,(
    ! [B_40,A_39] :
      ( B_40 = A_39
      | ~ v1_xboole_0(B_40)
      | ~ v1_xboole_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_103,c_108])).

tff(c_2923,plain,(
    ! [A_212] :
      ( A_212 = '#skF_3'
      | ~ v1_xboole_0(A_212) ) ),
    inference(resolution,[status(thm)],[c_2904,c_115])).

tff(c_2930,plain,(
    '#skF_1'('#skF_5') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2903,c_2923])).

tff(c_2935,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2930,c_647])).

tff(c_26,plain,(
    ! [C_17,A_14,B_15] :
      ( r2_hidden(C_17,A_14)
      | ~ r2_hidden(C_17,B_15)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3209,plain,(
    ! [A_224] :
      ( r2_hidden('#skF_3',A_224)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_224)) ) ),
    inference(resolution,[status(thm)],[c_2935,c_26])).

tff(c_3217,plain,(
    r2_hidden('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_3209])).

tff(c_3227,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_3217,c_2])).

tff(c_3235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2904,c_3227])).

tff(c_3248,plain,(
    ! [D_226] :
      ( ~ r2_hidden(D_226,'#skF_4')
      | ~ m1_subset_1(D_226,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_3263,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_4'),'#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_3248])).

tff(c_3264,plain,(
    ~ m1_subset_1('#skF_1'('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3263])).

tff(c_3268,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_4'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_3264])).

tff(c_3269,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3268])).

tff(c_66,plain,(
    ! [B_32,A_33] :
      ( m1_subset_1(B_32,A_33)
      | ~ r2_hidden(B_32,A_33)
      | v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_70,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_66])).

tff(c_3261,plain,(
    ! [B_13] :
      ( ~ m1_subset_1(B_13,'#skF_3')
      | ~ m1_subset_1(B_13,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_20,c_3248])).

tff(c_3281,plain,(
    ! [B_230] :
      ( ~ m1_subset_1(B_230,'#skF_3')
      | ~ m1_subset_1(B_230,'#skF_4') ) ),
    inference(splitLeft,[status(thm)],[c_3261])).

tff(c_3285,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_3'),'#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_3281])).

tff(c_3292,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_3269,c_3285])).

tff(c_3298,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_3'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_3292])).

tff(c_3299,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3298])).

tff(c_3270,plain,(
    ! [C_227,B_228,A_229] :
      ( r2_hidden(C_227,B_228)
      | ~ r2_hidden(C_227,A_229)
      | ~ r1_tarski(A_229,B_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3305,plain,(
    ! [A_232,B_233] :
      ( r2_hidden('#skF_1'(A_232),B_233)
      | ~ r1_tarski(A_232,B_233)
      | v1_xboole_0(A_232) ) ),
    inference(resolution,[status(thm)],[c_4,c_3270])).

tff(c_3557,plain,(
    ! [A_262,B_263] :
      ( m1_subset_1('#skF_1'(A_262),B_263)
      | v1_xboole_0(B_263)
      | ~ r1_tarski(A_262,B_263)
      | v1_xboole_0(A_262) ) ),
    inference(resolution,[status(thm)],[c_3305,c_18])).

tff(c_3579,plain,
    ( v1_xboole_0('#skF_3')
    | ~ r1_tarski('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_3557,c_3264])).

tff(c_3600,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_3299,c_3269,c_3579])).

tff(c_3327,plain,(
    ! [C_234,A_235,B_236] :
      ( r2_hidden(C_234,A_235)
      | ~ r2_hidden(C_234,B_236)
      | ~ m1_subset_1(B_236,k1_zfmisc_1(A_235)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3602,plain,(
    ! [A_264,B_265,A_266] :
      ( r2_hidden('#skF_2'(A_264,B_265),A_266)
      | ~ m1_subset_1(A_264,k1_zfmisc_1(A_266))
      | r1_tarski(A_264,B_265) ) ),
    inference(resolution,[status(thm)],[c_10,c_3327])).

tff(c_3636,plain,(
    ! [A_267,A_268] :
      ( ~ m1_subset_1(A_267,k1_zfmisc_1(A_268))
      | r1_tarski(A_267,A_268) ) ),
    inference(resolution,[status(thm)],[c_3602,c_8])).

tff(c_3658,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_3636])).

tff(c_3667,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3600,c_3658])).

tff(c_3669,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_3298])).

tff(c_3237,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_3240,plain,(
    ! [A_39] :
      ( A_39 = '#skF_5'
      | ~ v1_xboole_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_3237,c_115])).

tff(c_3672,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3669,c_3240])).

tff(c_3678,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_3672])).

tff(c_3680,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_3268])).

tff(c_3687,plain,(
    '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3680,c_3240])).

tff(c_3693,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3687,c_28])).

tff(c_3747,plain,(
    ! [B_276] :
      ( ~ m1_subset_1(B_276,'#skF_3')
      | ~ m1_subset_1(B_276,'#skF_4') ) ),
    inference(splitLeft,[status(thm)],[c_3261])).

tff(c_3755,plain,(
    ! [B_13] :
      ( ~ m1_subset_1(B_13,'#skF_4')
      | ~ v1_xboole_0(B_13)
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_3747])).

tff(c_3761,plain,(
    ! [B_277] :
      ( ~ m1_subset_1(B_277,'#skF_4')
      | ~ v1_xboole_0(B_277) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3680,c_3755])).

tff(c_3771,plain,(
    ! [B_13] :
      ( ~ v1_xboole_0(B_13)
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_3761])).

tff(c_3772,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3771])).

tff(c_3773,plain,(
    ! [C_278,A_279,B_280] :
      ( r2_hidden(C_278,A_279)
      | ~ r2_hidden(C_278,B_280)
      | ~ m1_subset_1(B_280,k1_zfmisc_1(A_279)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3861,plain,(
    ! [A_291,A_292] :
      ( r2_hidden('#skF_1'(A_291),A_292)
      | ~ m1_subset_1(A_291,k1_zfmisc_1(A_292))
      | v1_xboole_0(A_291) ) ),
    inference(resolution,[status(thm)],[c_4,c_3773])).

tff(c_3893,plain,(
    ! [A_296,A_297] :
      ( ~ v1_xboole_0(A_296)
      | ~ m1_subset_1(A_297,k1_zfmisc_1(A_296))
      | v1_xboole_0(A_297) ) ),
    inference(resolution,[status(thm)],[c_3861,c_2])).

tff(c_3911,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_3893])).

tff(c_3920,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3680,c_3911])).

tff(c_3922,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3772,c_3920])).

tff(c_3924,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_3771])).

tff(c_3688,plain,(
    ! [A_39] :
      ( A_39 = '#skF_3'
      | ~ v1_xboole_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_3680,c_115])).

tff(c_3927,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3924,c_3688])).

tff(c_3933,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3693,c_3927])).

tff(c_3934,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_3263])).

tff(c_3938,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3934,c_3240])).

tff(c_3944,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_3938])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:08:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.76/1.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.76/1.91  
% 4.76/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.76/1.91  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 4.76/1.91  
% 4.76/1.91  %Foreground sorts:
% 4.76/1.91  
% 4.76/1.91  
% 4.76/1.91  %Background operators:
% 4.76/1.91  
% 4.76/1.91  
% 4.76/1.91  %Foreground operators:
% 4.76/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.76/1.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.76/1.91  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.76/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.76/1.91  tff('#skF_5', type, '#skF_5': $i).
% 4.76/1.91  tff('#skF_3', type, '#skF_3': $i).
% 4.76/1.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.76/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.76/1.91  tff('#skF_4', type, '#skF_4': $i).
% 4.76/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.76/1.91  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.76/1.91  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.76/1.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.76/1.91  
% 5.09/1.93  tff(f_79, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_subset_1)).
% 5.09/1.93  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 5.09/1.93  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.09/1.93  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.09/1.93  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 5.09/1.93  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.09/1.93  tff(c_28, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.09/1.93  tff(c_22, plain, (![B_13, A_12]: (m1_subset_1(B_13, A_12) | ~v1_xboole_0(B_13) | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.09/1.93  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.09/1.93  tff(c_118, plain, (![D_45]: (r2_hidden(D_45, '#skF_5') | ~r2_hidden(D_45, '#skF_4') | ~m1_subset_1(D_45, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.09/1.93  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.09/1.93  tff(c_135, plain, (![D_45]: (~v1_xboole_0('#skF_5') | ~r2_hidden(D_45, '#skF_4') | ~m1_subset_1(D_45, '#skF_3'))), inference(resolution, [status(thm)], [c_118, c_2])).
% 5.09/1.93  tff(c_156, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_135])).
% 5.09/1.93  tff(c_55, plain, (![D_29]: (r2_hidden(D_29, '#skF_4') | ~r2_hidden(D_29, '#skF_5') | ~m1_subset_1(D_29, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.09/1.93  tff(c_60, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_5'), '#skF_3') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_55])).
% 5.09/1.93  tff(c_217, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_156, c_60])).
% 5.09/1.93  tff(c_218, plain, (~m1_subset_1('#skF_1'('#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_217])).
% 5.09/1.93  tff(c_222, plain, (~v1_xboole_0('#skF_1'('#skF_5')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_22, c_218])).
% 5.09/1.93  tff(c_223, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_222])).
% 5.09/1.93  tff(c_157, plain, (![C_50, B_51, A_52]: (r2_hidden(C_50, B_51) | ~r2_hidden(C_50, A_52) | ~r1_tarski(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.09/1.93  tff(c_183, plain, (![A_56, B_57]: (r2_hidden('#skF_1'(A_56), B_57) | ~r1_tarski(A_56, B_57) | v1_xboole_0(A_56))), inference(resolution, [status(thm)], [c_4, c_157])).
% 5.09/1.93  tff(c_18, plain, (![B_13, A_12]: (m1_subset_1(B_13, A_12) | ~r2_hidden(B_13, A_12) | v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.09/1.93  tff(c_388, plain, (![A_80, B_81]: (m1_subset_1('#skF_1'(A_80), B_81) | v1_xboole_0(B_81) | ~r1_tarski(A_80, B_81) | v1_xboole_0(A_80))), inference(resolution, [status(thm)], [c_183, c_18])).
% 5.09/1.93  tff(c_398, plain, (v1_xboole_0('#skF_3') | ~r1_tarski('#skF_5', '#skF_3') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_388, c_218])).
% 5.09/1.93  tff(c_408, plain, (~r1_tarski('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_156, c_223, c_398])).
% 5.09/1.93  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.09/1.93  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.09/1.93  tff(c_170, plain, (![C_53, A_54, B_55]: (r2_hidden(C_53, A_54) | ~r2_hidden(C_53, B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.09/1.93  tff(c_497, plain, (![A_88, B_89, A_90]: (r2_hidden('#skF_2'(A_88, B_89), A_90) | ~m1_subset_1(A_88, k1_zfmisc_1(A_90)) | r1_tarski(A_88, B_89))), inference(resolution, [status(thm)], [c_10, c_170])).
% 5.09/1.93  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.09/1.93  tff(c_531, plain, (![A_91, A_92]: (~m1_subset_1(A_91, k1_zfmisc_1(A_92)) | r1_tarski(A_91, A_92))), inference(resolution, [status(thm)], [c_497, c_8])).
% 5.09/1.93  tff(c_550, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_531])).
% 5.09/1.93  tff(c_561, plain, $false, inference(negUnitSimplification, [status(thm)], [c_408, c_550])).
% 5.09/1.93  tff(c_563, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_222])).
% 5.09/1.93  tff(c_564, plain, (![A_93, A_94]: (r2_hidden('#skF_1'(A_93), A_94) | ~m1_subset_1(A_93, k1_zfmisc_1(A_94)) | v1_xboole_0(A_93))), inference(resolution, [status(thm)], [c_4, c_170])).
% 5.09/1.93  tff(c_620, plain, (![A_97, A_98]: (~v1_xboole_0(A_97) | ~m1_subset_1(A_98, k1_zfmisc_1(A_97)) | v1_xboole_0(A_98))), inference(resolution, [status(thm)], [c_564, c_2])).
% 5.09/1.93  tff(c_635, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_30, c_620])).
% 5.09/1.93  tff(c_644, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_563, c_635])).
% 5.09/1.93  tff(c_646, plain, $false, inference(negUnitSimplification, [status(thm)], [c_156, c_644])).
% 5.09/1.93  tff(c_647, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_217])).
% 5.09/1.93  tff(c_662, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_647, c_2])).
% 5.09/1.93  tff(c_84, plain, (![A_39, B_40]: (r2_hidden('#skF_2'(A_39, B_40), A_39) | r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.09/1.93  tff(c_101, plain, (![A_39, B_40]: (m1_subset_1('#skF_2'(A_39, B_40), A_39) | v1_xboole_0(A_39) | r1_tarski(A_39, B_40))), inference(resolution, [status(thm)], [c_84, c_18])).
% 5.09/1.93  tff(c_648, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_217])).
% 5.09/1.93  tff(c_24, plain, (![B_13, A_12]: (v1_xboole_0(B_13) | ~m1_subset_1(B_13, A_12) | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.09/1.93  tff(c_666, plain, (v1_xboole_0('#skF_1'('#skF_5')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_648, c_24])).
% 5.09/1.93  tff(c_667, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_666])).
% 5.09/1.93  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.09/1.93  tff(c_20, plain, (![B_13, A_12]: (r2_hidden(B_13, A_12) | ~m1_subset_1(B_13, A_12) | v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.09/1.93  tff(c_2096, plain, (![B_182, A_183, A_184]: (r2_hidden(B_182, A_183) | ~m1_subset_1(A_184, k1_zfmisc_1(A_183)) | ~m1_subset_1(B_182, A_184) | v1_xboole_0(A_184))), inference(resolution, [status(thm)], [c_20, c_170])).
% 5.09/1.93  tff(c_2124, plain, (![B_182]: (r2_hidden(B_182, '#skF_3') | ~m1_subset_1(B_182, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_32, c_2096])).
% 5.09/1.93  tff(c_2165, plain, (![B_186]: (r2_hidden(B_186, '#skF_3') | ~m1_subset_1(B_186, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_662, c_2124])).
% 5.09/1.93  tff(c_2176, plain, (![B_186]: (m1_subset_1(B_186, '#skF_3') | v1_xboole_0('#skF_3') | ~m1_subset_1(B_186, '#skF_4'))), inference(resolution, [status(thm)], [c_2165, c_18])).
% 5.09/1.93  tff(c_2185, plain, (![B_186]: (m1_subset_1(B_186, '#skF_3') | ~m1_subset_1(B_186, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_667, c_2176])).
% 5.09/1.93  tff(c_2047, plain, (![A_181]: (r1_tarski(A_181, '#skF_5') | ~r2_hidden('#skF_2'(A_181, '#skF_5'), '#skF_4') | ~m1_subset_1('#skF_2'(A_181, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_118, c_8])).
% 5.09/1.93  tff(c_2072, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_5'), '#skF_3') | r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_10, c_2047])).
% 5.09/1.93  tff(c_2306, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_2072])).
% 5.09/1.93  tff(c_2313, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_2185, c_2306])).
% 5.09/1.93  tff(c_2317, plain, (v1_xboole_0('#skF_4') | r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_101, c_2313])).
% 5.09/1.93  tff(c_2323, plain, (r1_tarski('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_662, c_2317])).
% 5.09/1.93  tff(c_12, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.09/1.93  tff(c_2343, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_2323, c_12])).
% 5.09/1.93  tff(c_2359, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_28, c_2343])).
% 5.09/1.93  tff(c_2122, plain, (![B_182]: (r2_hidden(B_182, '#skF_3') | ~m1_subset_1(B_182, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_30, c_2096])).
% 5.09/1.93  tff(c_2143, plain, (![B_185]: (r2_hidden(B_185, '#skF_3') | ~m1_subset_1(B_185, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_156, c_2122])).
% 5.09/1.93  tff(c_2154, plain, (![B_185]: (m1_subset_1(B_185, '#skF_3') | v1_xboole_0('#skF_3') | ~m1_subset_1(B_185, '#skF_5'))), inference(resolution, [status(thm)], [c_2143, c_18])).
% 5.09/1.93  tff(c_2222, plain, (![B_188]: (m1_subset_1(B_188, '#skF_3') | ~m1_subset_1(B_188, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_667, c_2154])).
% 5.09/1.93  tff(c_2255, plain, (![B_40]: (m1_subset_1('#skF_2'('#skF_5', B_40), '#skF_3') | v1_xboole_0('#skF_5') | r1_tarski('#skF_5', B_40))), inference(resolution, [status(thm)], [c_101, c_2222])).
% 5.09/1.93  tff(c_2578, plain, (![B_198]: (m1_subset_1('#skF_2'('#skF_5', B_198), '#skF_3') | r1_tarski('#skF_5', B_198))), inference(negUnitSimplification, [status(thm)], [c_156, c_2255])).
% 5.09/1.93  tff(c_34, plain, (![D_22]: (r2_hidden(D_22, '#skF_4') | ~r2_hidden(D_22, '#skF_5') | ~m1_subset_1(D_22, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.09/1.93  tff(c_2187, plain, (![B_187]: (r2_hidden('#skF_2'('#skF_5', B_187), '#skF_4') | ~m1_subset_1('#skF_2'('#skF_5', B_187), '#skF_3') | r1_tarski('#skF_5', B_187))), inference(resolution, [status(thm)], [c_84, c_34])).
% 5.09/1.93  tff(c_2217, plain, (~m1_subset_1('#skF_2'('#skF_5', '#skF_4'), '#skF_3') | r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_2187, c_8])).
% 5.09/1.93  tff(c_2468, plain, (~m1_subset_1('#skF_2'('#skF_5', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_2359, c_2217])).
% 5.09/1.93  tff(c_2581, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_2578, c_2468])).
% 5.09/1.93  tff(c_2592, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2359, c_2581])).
% 5.09/1.93  tff(c_2593, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_2072])).
% 5.09/1.93  tff(c_2613, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_2593, c_12])).
% 5.09/1.93  tff(c_2629, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_28, c_2613])).
% 5.09/1.93  tff(c_2888, plain, (![B_209]: (m1_subset_1('#skF_2'('#skF_5', B_209), '#skF_3') | r1_tarski('#skF_5', B_209))), inference(negUnitSimplification, [status(thm)], [c_156, c_2255])).
% 5.09/1.93  tff(c_2767, plain, (~m1_subset_1('#skF_2'('#skF_5', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_2629, c_2217])).
% 5.09/1.93  tff(c_2891, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_2888, c_2767])).
% 5.09/1.93  tff(c_2902, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2629, c_2891])).
% 5.09/1.93  tff(c_2904, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_666])).
% 5.09/1.93  tff(c_2903, plain, (v1_xboole_0('#skF_1'('#skF_5'))), inference(splitRight, [status(thm)], [c_666])).
% 5.09/1.93  tff(c_103, plain, (![A_39, B_40]: (~v1_xboole_0(A_39) | r1_tarski(A_39, B_40))), inference(resolution, [status(thm)], [c_84, c_2])).
% 5.09/1.93  tff(c_104, plain, (![A_41, B_42]: (~v1_xboole_0(A_41) | r1_tarski(A_41, B_42))), inference(resolution, [status(thm)], [c_84, c_2])).
% 5.09/1.93  tff(c_108, plain, (![B_43, A_44]: (B_43=A_44 | ~r1_tarski(B_43, A_44) | ~v1_xboole_0(A_44))), inference(resolution, [status(thm)], [c_104, c_12])).
% 5.09/1.93  tff(c_115, plain, (![B_40, A_39]: (B_40=A_39 | ~v1_xboole_0(B_40) | ~v1_xboole_0(A_39))), inference(resolution, [status(thm)], [c_103, c_108])).
% 5.09/1.93  tff(c_2923, plain, (![A_212]: (A_212='#skF_3' | ~v1_xboole_0(A_212))), inference(resolution, [status(thm)], [c_2904, c_115])).
% 5.09/1.93  tff(c_2930, plain, ('#skF_1'('#skF_5')='#skF_3'), inference(resolution, [status(thm)], [c_2903, c_2923])).
% 5.09/1.93  tff(c_2935, plain, (r2_hidden('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2930, c_647])).
% 5.09/1.93  tff(c_26, plain, (![C_17, A_14, B_15]: (r2_hidden(C_17, A_14) | ~r2_hidden(C_17, B_15) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.09/1.93  tff(c_3209, plain, (![A_224]: (r2_hidden('#skF_3', A_224) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_224)))), inference(resolution, [status(thm)], [c_2935, c_26])).
% 5.09/1.93  tff(c_3217, plain, (r2_hidden('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_3209])).
% 5.09/1.93  tff(c_3227, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_3217, c_2])).
% 5.09/1.93  tff(c_3235, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2904, c_3227])).
% 5.09/1.93  tff(c_3248, plain, (![D_226]: (~r2_hidden(D_226, '#skF_4') | ~m1_subset_1(D_226, '#skF_3'))), inference(splitRight, [status(thm)], [c_135])).
% 5.09/1.93  tff(c_3263, plain, (~m1_subset_1('#skF_1'('#skF_4'), '#skF_3') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_3248])).
% 5.09/1.93  tff(c_3264, plain, (~m1_subset_1('#skF_1'('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_3263])).
% 5.09/1.93  tff(c_3268, plain, (~v1_xboole_0('#skF_1'('#skF_4')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_22, c_3264])).
% 5.09/1.93  tff(c_3269, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_3268])).
% 5.09/1.93  tff(c_66, plain, (![B_32, A_33]: (m1_subset_1(B_32, A_33) | ~r2_hidden(B_32, A_33) | v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.09/1.93  tff(c_70, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_66])).
% 5.09/1.93  tff(c_3261, plain, (![B_13]: (~m1_subset_1(B_13, '#skF_3') | ~m1_subset_1(B_13, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_20, c_3248])).
% 5.09/1.93  tff(c_3281, plain, (![B_230]: (~m1_subset_1(B_230, '#skF_3') | ~m1_subset_1(B_230, '#skF_4'))), inference(splitLeft, [status(thm)], [c_3261])).
% 5.09/1.93  tff(c_3285, plain, (~m1_subset_1('#skF_1'('#skF_3'), '#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_70, c_3281])).
% 5.09/1.93  tff(c_3292, plain, (~m1_subset_1('#skF_1'('#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_3269, c_3285])).
% 5.09/1.93  tff(c_3298, plain, (~v1_xboole_0('#skF_1'('#skF_3')) | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_22, c_3292])).
% 5.09/1.93  tff(c_3299, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_3298])).
% 5.09/1.93  tff(c_3270, plain, (![C_227, B_228, A_229]: (r2_hidden(C_227, B_228) | ~r2_hidden(C_227, A_229) | ~r1_tarski(A_229, B_228))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.09/1.93  tff(c_3305, plain, (![A_232, B_233]: (r2_hidden('#skF_1'(A_232), B_233) | ~r1_tarski(A_232, B_233) | v1_xboole_0(A_232))), inference(resolution, [status(thm)], [c_4, c_3270])).
% 5.09/1.93  tff(c_3557, plain, (![A_262, B_263]: (m1_subset_1('#skF_1'(A_262), B_263) | v1_xboole_0(B_263) | ~r1_tarski(A_262, B_263) | v1_xboole_0(A_262))), inference(resolution, [status(thm)], [c_3305, c_18])).
% 5.09/1.93  tff(c_3579, plain, (v1_xboole_0('#skF_3') | ~r1_tarski('#skF_4', '#skF_3') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_3557, c_3264])).
% 5.09/1.93  tff(c_3600, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_3299, c_3269, c_3579])).
% 5.09/1.93  tff(c_3327, plain, (![C_234, A_235, B_236]: (r2_hidden(C_234, A_235) | ~r2_hidden(C_234, B_236) | ~m1_subset_1(B_236, k1_zfmisc_1(A_235)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.09/1.93  tff(c_3602, plain, (![A_264, B_265, A_266]: (r2_hidden('#skF_2'(A_264, B_265), A_266) | ~m1_subset_1(A_264, k1_zfmisc_1(A_266)) | r1_tarski(A_264, B_265))), inference(resolution, [status(thm)], [c_10, c_3327])).
% 5.09/1.93  tff(c_3636, plain, (![A_267, A_268]: (~m1_subset_1(A_267, k1_zfmisc_1(A_268)) | r1_tarski(A_267, A_268))), inference(resolution, [status(thm)], [c_3602, c_8])).
% 5.09/1.93  tff(c_3658, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_3636])).
% 5.09/1.93  tff(c_3667, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3600, c_3658])).
% 5.09/1.93  tff(c_3669, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_3298])).
% 5.09/1.93  tff(c_3237, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_135])).
% 5.09/1.93  tff(c_3240, plain, (![A_39]: (A_39='#skF_5' | ~v1_xboole_0(A_39))), inference(resolution, [status(thm)], [c_3237, c_115])).
% 5.09/1.93  tff(c_3672, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_3669, c_3240])).
% 5.09/1.93  tff(c_3678, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_3672])).
% 5.09/1.93  tff(c_3680, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_3268])).
% 5.09/1.93  tff(c_3687, plain, ('#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_3680, c_3240])).
% 5.09/1.93  tff(c_3693, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3687, c_28])).
% 5.09/1.93  tff(c_3747, plain, (![B_276]: (~m1_subset_1(B_276, '#skF_3') | ~m1_subset_1(B_276, '#skF_4'))), inference(splitLeft, [status(thm)], [c_3261])).
% 5.09/1.93  tff(c_3755, plain, (![B_13]: (~m1_subset_1(B_13, '#skF_4') | ~v1_xboole_0(B_13) | ~v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_3747])).
% 5.09/1.93  tff(c_3761, plain, (![B_277]: (~m1_subset_1(B_277, '#skF_4') | ~v1_xboole_0(B_277))), inference(demodulation, [status(thm), theory('equality')], [c_3680, c_3755])).
% 5.09/1.93  tff(c_3771, plain, (![B_13]: (~v1_xboole_0(B_13) | ~v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_22, c_3761])).
% 5.09/1.93  tff(c_3772, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_3771])).
% 5.09/1.93  tff(c_3773, plain, (![C_278, A_279, B_280]: (r2_hidden(C_278, A_279) | ~r2_hidden(C_278, B_280) | ~m1_subset_1(B_280, k1_zfmisc_1(A_279)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.09/1.93  tff(c_3861, plain, (![A_291, A_292]: (r2_hidden('#skF_1'(A_291), A_292) | ~m1_subset_1(A_291, k1_zfmisc_1(A_292)) | v1_xboole_0(A_291))), inference(resolution, [status(thm)], [c_4, c_3773])).
% 5.09/1.93  tff(c_3893, plain, (![A_296, A_297]: (~v1_xboole_0(A_296) | ~m1_subset_1(A_297, k1_zfmisc_1(A_296)) | v1_xboole_0(A_297))), inference(resolution, [status(thm)], [c_3861, c_2])).
% 5.09/1.93  tff(c_3911, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_32, c_3893])).
% 5.09/1.93  tff(c_3920, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3680, c_3911])).
% 5.09/1.93  tff(c_3922, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3772, c_3920])).
% 5.09/1.93  tff(c_3924, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_3771])).
% 5.09/1.93  tff(c_3688, plain, (![A_39]: (A_39='#skF_3' | ~v1_xboole_0(A_39))), inference(resolution, [status(thm)], [c_3680, c_115])).
% 5.09/1.93  tff(c_3927, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_3924, c_3688])).
% 5.09/1.93  tff(c_3933, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3693, c_3927])).
% 5.09/1.93  tff(c_3934, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_3263])).
% 5.09/1.93  tff(c_3938, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_3934, c_3240])).
% 5.09/1.93  tff(c_3944, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_3938])).
% 5.09/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.09/1.93  
% 5.09/1.93  Inference rules
% 5.09/1.93  ----------------------
% 5.09/1.93  #Ref     : 0
% 5.09/1.93  #Sup     : 817
% 5.09/1.93  #Fact    : 0
% 5.09/1.93  #Define  : 0
% 5.09/1.93  #Split   : 18
% 5.09/1.93  #Chain   : 0
% 5.09/1.93  #Close   : 0
% 5.09/1.93  
% 5.09/1.93  Ordering : KBO
% 5.09/1.93  
% 5.09/1.93  Simplification rules
% 5.09/1.93  ----------------------
% 5.09/1.93  #Subsume      : 202
% 5.09/1.93  #Demod        : 203
% 5.09/1.93  #Tautology    : 144
% 5.09/1.93  #SimpNegUnit  : 132
% 5.09/1.93  #BackRed      : 8
% 5.09/1.93  
% 5.09/1.93  #Partial instantiations: 0
% 5.09/1.93  #Strategies tried      : 1
% 5.09/1.93  
% 5.09/1.93  Timing (in seconds)
% 5.09/1.93  ----------------------
% 5.09/1.94  Preprocessing        : 0.28
% 5.09/1.94  Parsing              : 0.14
% 5.09/1.94  CNF conversion       : 0.02
% 5.09/1.94  Main loop            : 0.84
% 5.09/1.94  Inferencing          : 0.30
% 5.09/1.94  Reduction            : 0.22
% 5.09/1.94  Demodulation         : 0.14
% 5.09/1.94  BG Simplification    : 0.03
% 5.09/1.94  Subsumption          : 0.20
% 5.09/1.94  Abstraction          : 0.03
% 5.09/1.94  MUC search           : 0.00
% 5.09/1.94  Cooper               : 0.00
% 5.09/1.94  Total                : 1.17
% 5.09/1.94  Index Insertion      : 0.00
% 5.09/1.94  Index Deletion       : 0.00
% 5.09/1.94  Index Matching       : 0.00
% 5.09/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
