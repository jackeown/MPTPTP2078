%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:18 EST 2020

% Result     : Theorem 9.52s
% Output     : CNFRefutation 9.76s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 891 expanded)
%              Number of leaves         :   18 ( 283 expanded)
%              Depth                    :   17
%              Number of atoms          :  337 (2565 expanded)
%              Number of equality atoms :   37 ( 218 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_73,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_24,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_54,plain,(
    ! [D_26] :
      ( r2_hidden(D_26,'#skF_5')
      | ~ r2_hidden(D_26,'#skF_6')
      | ~ m1_subset_1(D_26,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    ! [D_26] :
      ( ~ v1_xboole_0('#skF_5')
      | ~ r2_hidden(D_26,'#skF_6')
      | ~ m1_subset_1(D_26,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_2])).

tff(c_82,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r2_hidden('#skF_3'(A_5,B_6),A_5)
      | B_6 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_30,plain,(
    ! [D_18] :
      ( r2_hidden(D_18,'#skF_5')
      | ~ r2_hidden(D_18,'#skF_6')
      | ~ m1_subset_1(D_18,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1390,plain,(
    ! [A_126,B_127] :
      ( r2_hidden('#skF_2'(A_126,B_127),B_127)
      | ~ r2_hidden('#skF_3'(A_126,B_127),B_127)
      | B_127 = A_126 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2883,plain,(
    ! [A_215] :
      ( r2_hidden('#skF_2'(A_215,'#skF_5'),'#skF_5')
      | A_215 = '#skF_5'
      | ~ r2_hidden('#skF_3'(A_215,'#skF_5'),'#skF_6')
      | ~ m1_subset_1('#skF_3'(A_215,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_1390])).

tff(c_2903,plain,
    ( ~ m1_subset_1('#skF_3'('#skF_6','#skF_5'),'#skF_4')
    | r2_hidden('#skF_2'('#skF_6','#skF_5'),'#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_12,c_2883])).

tff(c_2921,plain,
    ( ~ m1_subset_1('#skF_3'('#skF_6','#skF_5'),'#skF_4')
    | r2_hidden('#skF_2'('#skF_6','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_24,c_2903])).

tff(c_2926,plain,(
    ~ m1_subset_1('#skF_3'('#skF_6','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2921])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_83,plain,(
    ! [D_32] :
      ( r2_hidden(D_32,'#skF_6')
      | ~ r2_hidden(D_32,'#skF_5')
      | ~ m1_subset_1(D_32,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_97,plain,
    ( r2_hidden('#skF_1'('#skF_5'),'#skF_6')
    | ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_83])).

tff(c_108,plain,
    ( r2_hidden('#skF_1'('#skF_5'),'#skF_6')
    | ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_97])).

tff(c_109,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_64,plain,(
    ! [B_29,A_30] :
      ( m1_subset_1(B_29,A_30)
      | ~ r2_hidden(B_29,A_30)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_76,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_64])).

tff(c_18,plain,(
    ! [B_9,A_8] :
      ( m1_subset_1(B_9,A_8)
      | ~ v1_xboole_0(B_9)
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_126,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_5'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_109])).

tff(c_127,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( r2_hidden(B_9,A_8)
      | ~ m1_subset_1(B_9,A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_98,plain,(
    ! [C_33,A_34,B_35] :
      ( r2_hidden(C_33,A_34)
      | ~ r2_hidden(C_33,B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1065,plain,(
    ! [B_106,A_107,A_108] :
      ( r2_hidden(B_106,A_107)
      | ~ m1_subset_1(A_108,k1_zfmisc_1(A_107))
      | ~ m1_subset_1(B_106,A_108)
      | v1_xboole_0(A_108) ) ),
    inference(resolution,[status(thm)],[c_16,c_98])).

tff(c_1084,plain,(
    ! [B_106] :
      ( r2_hidden(B_106,'#skF_4')
      | ~ m1_subset_1(B_106,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_1065])).

tff(c_1147,plain,(
    ! [B_111] :
      ( r2_hidden(B_111,'#skF_4')
      | ~ m1_subset_1(B_111,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1084])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( m1_subset_1(B_9,A_8)
      | ~ r2_hidden(B_9,A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1159,plain,(
    ! [B_111] :
      ( m1_subset_1(B_111,'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(B_111,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1147,c_14])).

tff(c_1209,plain,(
    ! [B_113] :
      ( m1_subset_1(B_113,'#skF_4')
      | ~ m1_subset_1(B_113,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_1159])).

tff(c_1231,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_1209])).

tff(c_1251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_109,c_1231])).

tff(c_1253,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_1346,plain,(
    ! [A_122,A_123] :
      ( r2_hidden('#skF_1'(A_122),A_123)
      | ~ m1_subset_1(A_122,k1_zfmisc_1(A_123))
      | v1_xboole_0(A_122) ) ),
    inference(resolution,[status(thm)],[c_4,c_98])).

tff(c_1363,plain,(
    ! [A_124,A_125] :
      ( ~ v1_xboole_0(A_124)
      | ~ m1_subset_1(A_125,k1_zfmisc_1(A_124))
      | v1_xboole_0(A_125) ) ),
    inference(resolution,[status(thm)],[c_1346,c_2])).

tff(c_1377,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_1363])).

tff(c_1385,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1253,c_1377])).

tff(c_1387,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1385])).

tff(c_1388,plain,(
    r2_hidden('#skF_1'('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_1411,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1388,c_2])).

tff(c_1470,plain,(
    ! [A_131,B_132] :
      ( r2_hidden('#skF_2'(A_131,B_132),B_132)
      | r2_hidden('#skF_3'(A_131,B_132),A_131)
      | B_132 = A_131 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3442,plain,(
    ! [A_244,B_245] :
      ( m1_subset_1('#skF_3'(A_244,B_245),A_244)
      | v1_xboole_0(A_244)
      | r2_hidden('#skF_2'(A_244,B_245),B_245)
      | B_245 = A_244 ) ),
    inference(resolution,[status(thm)],[c_1470,c_14])).

tff(c_32,plain,(
    ! [D_18] :
      ( r2_hidden(D_18,'#skF_6')
      | ~ r2_hidden(D_18,'#skF_5')
      | ~ m1_subset_1(D_18,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_7834,plain,(
    ! [A_397] :
      ( r2_hidden('#skF_2'(A_397,'#skF_5'),'#skF_6')
      | ~ m1_subset_1('#skF_2'(A_397,'#skF_5'),'#skF_4')
      | m1_subset_1('#skF_3'(A_397,'#skF_5'),A_397)
      | v1_xboole_0(A_397)
      | A_397 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_3442,c_32])).

tff(c_2198,plain,(
    ! [A_176,B_177] :
      ( ~ r2_hidden('#skF_2'(A_176,B_177),A_176)
      | r2_hidden('#skF_3'(A_176,B_177),A_176)
      | B_177 = A_176 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2229,plain,(
    ! [A_176,B_177] :
      ( m1_subset_1('#skF_3'(A_176,B_177),A_176)
      | v1_xboole_0(A_176)
      | ~ r2_hidden('#skF_2'(A_176,B_177),A_176)
      | B_177 = A_176 ) ),
    inference(resolution,[status(thm)],[c_2198,c_14])).

tff(c_7841,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_6','#skF_5'),'#skF_4')
    | m1_subset_1('#skF_3'('#skF_6','#skF_5'),'#skF_6')
    | v1_xboole_0('#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_7834,c_2229])).

tff(c_7901,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_6','#skF_5'),'#skF_4')
    | m1_subset_1('#skF_3'('#skF_6','#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_1411,c_24,c_1411,c_7841])).

tff(c_7921,plain,(
    ~ m1_subset_1('#skF_2'('#skF_6','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_7901])).

tff(c_8843,plain,(
    ! [A_431,B_432] :
      ( m1_subset_1('#skF_2'(A_431,B_432),B_432)
      | v1_xboole_0(B_432)
      | m1_subset_1('#skF_3'(A_431,B_432),A_431)
      | v1_xboole_0(A_431)
      | B_432 = A_431 ) ),
    inference(resolution,[status(thm)],[c_3442,c_14])).

tff(c_1389,plain,(
    m1_subset_1('#skF_1'('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_20,plain,(
    ! [B_9,A_8] :
      ( v1_xboole_0(B_9)
      | ~ m1_subset_1(B_9,A_8)
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1415,plain,
    ( v1_xboole_0('#skF_1'('#skF_5'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1389,c_20])).

tff(c_1436,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1415])).

tff(c_26,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2549,plain,(
    ! [B_195,A_196,A_197] :
      ( r2_hidden(B_195,A_196)
      | ~ m1_subset_1(A_197,k1_zfmisc_1(A_196))
      | ~ m1_subset_1(B_195,A_197)
      | v1_xboole_0(A_197) ) ),
    inference(resolution,[status(thm)],[c_16,c_98])).

tff(c_2560,plain,(
    ! [B_195] :
      ( r2_hidden(B_195,'#skF_4')
      | ~ m1_subset_1(B_195,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_26,c_2549])).

tff(c_2572,plain,(
    ! [B_198] :
      ( r2_hidden(B_198,'#skF_4')
      | ~ m1_subset_1(B_198,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1411,c_2560])).

tff(c_2584,plain,(
    ! [B_198] :
      ( m1_subset_1(B_198,'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(B_198,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2572,c_14])).

tff(c_2593,plain,(
    ! [B_198] :
      ( m1_subset_1(B_198,'#skF_4')
      | ~ m1_subset_1(B_198,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1436,c_2584])).

tff(c_8941,plain,(
    ! [B_432] :
      ( m1_subset_1('#skF_3'('#skF_6',B_432),'#skF_4')
      | m1_subset_1('#skF_2'('#skF_6',B_432),B_432)
      | v1_xboole_0(B_432)
      | v1_xboole_0('#skF_6')
      | B_432 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_8843,c_2593])).

tff(c_10530,plain,(
    ! [B_460] :
      ( m1_subset_1('#skF_3'('#skF_6',B_460),'#skF_4')
      | m1_subset_1('#skF_2'('#skF_6',B_460),B_460)
      | v1_xboole_0(B_460)
      | B_460 = '#skF_6' ) ),
    inference(negUnitSimplification,[status(thm)],[c_1411,c_8941])).

tff(c_10537,plain,
    ( m1_subset_1('#skF_2'('#skF_6','#skF_5'),'#skF_5')
    | v1_xboole_0('#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_10530,c_2926])).

tff(c_10595,plain,(
    m1_subset_1('#skF_2'('#skF_6','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_82,c_10537])).

tff(c_2562,plain,(
    ! [B_195] :
      ( r2_hidden(B_195,'#skF_4')
      | ~ m1_subset_1(B_195,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_2549])).

tff(c_2595,plain,(
    ! [B_199] :
      ( r2_hidden(B_199,'#skF_4')
      | ~ m1_subset_1(B_199,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_2562])).

tff(c_2607,plain,(
    ! [B_199] :
      ( m1_subset_1(B_199,'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(B_199,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2595,c_14])).

tff(c_2616,plain,(
    ! [B_199] :
      ( m1_subset_1(B_199,'#skF_4')
      | ~ m1_subset_1(B_199,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1436,c_2607])).

tff(c_10613,plain,(
    m1_subset_1('#skF_2'('#skF_6','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_10595,c_2616])).

tff(c_10623,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7921,c_10613])).

tff(c_10624,plain,(
    m1_subset_1('#skF_3'('#skF_6','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_7901])).

tff(c_10628,plain,(
    m1_subset_1('#skF_3'('#skF_6','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_10624,c_2593])).

tff(c_10635,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2926,c_10628])).

tff(c_10636,plain,(
    r2_hidden('#skF_2'('#skF_6','#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_2921])).

tff(c_10645,plain,
    ( m1_subset_1('#skF_2'('#skF_6','#skF_5'),'#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_10636,c_14])).

tff(c_10653,plain,(
    m1_subset_1('#skF_2'('#skF_6','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_10645])).

tff(c_10706,plain,(
    m1_subset_1('#skF_2'('#skF_6','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_10653,c_2616])).

tff(c_10650,plain,
    ( r2_hidden('#skF_2'('#skF_6','#skF_5'),'#skF_6')
    | ~ m1_subset_1('#skF_2'('#skF_6','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_10636,c_32])).

tff(c_10714,plain,(
    r2_hidden('#skF_2'('#skF_6','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10706,c_10650])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r2_hidden('#skF_3'(A_5,B_6),A_5)
      | B_6 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10637,plain,(
    m1_subset_1('#skF_3'('#skF_6','#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_2921])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),A_5)
      | ~ r2_hidden('#skF_3'(A_5,B_6),B_6)
      | B_6 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10716,plain,
    ( ~ r2_hidden('#skF_3'('#skF_6','#skF_5'),'#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_10714,c_6])).

tff(c_10733,plain,(
    ~ r2_hidden('#skF_3'('#skF_6','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_10716])).

tff(c_10750,plain,
    ( ~ r2_hidden('#skF_3'('#skF_6','#skF_5'),'#skF_6')
    | ~ m1_subset_1('#skF_3'('#skF_6','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_10733])).

tff(c_10756,plain,(
    ~ r2_hidden('#skF_3'('#skF_6','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10637,c_10750])).

tff(c_10794,plain,
    ( ~ r2_hidden('#skF_2'('#skF_6','#skF_5'),'#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_10,c_10756])).

tff(c_10812,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10714,c_10794])).

tff(c_10814,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_10812])).

tff(c_10816,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1415])).

tff(c_22,plain,(
    ! [C_13,A_10,B_11] :
      ( r2_hidden(C_13,A_10)
      | ~ r2_hidden(C_13,B_11)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10897,plain,(
    ! [A_466] :
      ( r2_hidden('#skF_1'('#skF_5'),A_466)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_466)) ) ),
    inference(resolution,[status(thm)],[c_1388,c_22])).

tff(c_10923,plain,(
    ! [A_467] :
      ( ~ v1_xboole_0(A_467)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_467)) ) ),
    inference(resolution,[status(thm)],[c_10897,c_2])).

tff(c_10929,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_10923])).

tff(c_10934,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10816,c_10929])).

tff(c_10936,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_10937,plain,(
    ! [D_468] :
      ( ~ r2_hidden(D_468,'#skF_6')
      | ~ m1_subset_1(D_468,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_10946,plain,(
    ! [B_9] :
      ( ~ m1_subset_1(B_9,'#skF_4')
      | ~ m1_subset_1(B_9,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_16,c_10937])).

tff(c_10969,plain,(
    ! [B_470] :
      ( ~ m1_subset_1(B_470,'#skF_4')
      | ~ m1_subset_1(B_470,'#skF_6') ) ),
    inference(splitLeft,[status(thm)],[c_10946])).

tff(c_10979,plain,(
    ! [B_9] :
      ( ~ m1_subset_1(B_9,'#skF_4')
      | ~ v1_xboole_0(B_9)
      | ~ v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_18,c_10969])).

tff(c_10980,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_10979])).

tff(c_10947,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6'),'#skF_4')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_10937])).

tff(c_10961,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_10947])).

tff(c_10965,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_6'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_10961])).

tff(c_10966,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_10965])).

tff(c_10981,plain,(
    ! [C_471,A_472,B_473] :
      ( r2_hidden(C_471,A_472)
      | ~ r2_hidden(C_471,B_473)
      | ~ m1_subset_1(B_473,k1_zfmisc_1(A_472)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_11387,plain,(
    ! [B_511,A_512,A_513] :
      ( r2_hidden(B_511,A_512)
      | ~ m1_subset_1(A_513,k1_zfmisc_1(A_512))
      | ~ m1_subset_1(B_511,A_513)
      | v1_xboole_0(A_513) ) ),
    inference(resolution,[status(thm)],[c_16,c_10981])).

tff(c_11401,plain,(
    ! [B_511] :
      ( r2_hidden(B_511,'#skF_4')
      | ~ m1_subset_1(B_511,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_26,c_11387])).

tff(c_11413,plain,(
    ! [B_514] :
      ( r2_hidden(B_514,'#skF_4')
      | ~ m1_subset_1(B_514,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_10980,c_11401])).

tff(c_11425,plain,(
    ! [B_514] :
      ( m1_subset_1(B_514,'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(B_514,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_11413,c_14])).

tff(c_11465,plain,(
    ! [B_517] :
      ( m1_subset_1(B_517,'#skF_4')
      | ~ m1_subset_1(B_517,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_10966,c_11425])).

tff(c_11477,plain,
    ( m1_subset_1('#skF_1'('#skF_6'),'#skF_4')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_11465])).

tff(c_11491,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10980,c_10961,c_11477])).

tff(c_11493,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_10979])).

tff(c_11648,plain,(
    ! [A_536,B_537] :
      ( r2_hidden('#skF_2'(A_536,B_537),B_537)
      | r2_hidden('#skF_3'(A_536,B_537),A_536)
      | B_537 = A_536 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_11692,plain,(
    ! [B_538,A_539] :
      ( ~ v1_xboole_0(B_538)
      | r2_hidden('#skF_3'(A_539,B_538),A_539)
      | B_538 = A_539 ) ),
    inference(resolution,[status(thm)],[c_11648,c_2])).

tff(c_11746,plain,(
    ! [A_542,B_543] :
      ( ~ v1_xboole_0(A_542)
      | ~ v1_xboole_0(B_543)
      | B_543 = A_542 ) ),
    inference(resolution,[status(thm)],[c_11692,c_2])).

tff(c_11756,plain,(
    ! [B_544] :
      ( ~ v1_xboole_0(B_544)
      | B_544 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_10936,c_11746])).

tff(c_11762,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_11493,c_11756])).

tff(c_11770,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_11762])).

tff(c_11772,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_10965])).

tff(c_11775,plain,(
    ! [B_545] :
      ( ~ m1_subset_1(B_545,'#skF_4')
      | ~ m1_subset_1(B_545,'#skF_6') ) ),
    inference(splitLeft,[status(thm)],[c_10946])).

tff(c_11785,plain,(
    ! [B_9] :
      ( ~ m1_subset_1(B_9,'#skF_4')
      | ~ v1_xboole_0(B_9)
      | ~ v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_18,c_11775])).

tff(c_11786,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_11785])).

tff(c_11787,plain,(
    ! [C_546,A_547,B_548] :
      ( r2_hidden(C_546,A_547)
      | ~ r2_hidden(C_546,B_548)
      | ~ m1_subset_1(B_548,k1_zfmisc_1(A_547)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_11794,plain,(
    ! [A_549,A_550] :
      ( r2_hidden('#skF_1'(A_549),A_550)
      | ~ m1_subset_1(A_549,k1_zfmisc_1(A_550))
      | v1_xboole_0(A_549) ) ),
    inference(resolution,[status(thm)],[c_4,c_11787])).

tff(c_11816,plain,(
    ! [A_551,A_552] :
      ( ~ v1_xboole_0(A_551)
      | ~ m1_subset_1(A_552,k1_zfmisc_1(A_551))
      | v1_xboole_0(A_552) ) ),
    inference(resolution,[status(thm)],[c_11794,c_2])).

tff(c_11827,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_11816])).

tff(c_11835,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11772,c_11827])).

tff(c_11837,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11786,c_11835])).

tff(c_11840,plain,(
    ! [B_553] :
      ( ~ m1_subset_1(B_553,'#skF_4')
      | ~ v1_xboole_0(B_553) ) ),
    inference(splitRight,[status(thm)],[c_11785])).

tff(c_11848,plain,(
    ! [B_9] :
      ( ~ v1_xboole_0(B_9)
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_11840])).

tff(c_11853,plain,(
    ! [B_9] : ~ v1_xboole_0(B_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11772,c_11848])).

tff(c_11839,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_11785])).

tff(c_11862,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11853,c_11839])).

tff(c_11863,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_10946])).

tff(c_12023,plain,(
    ! [A_573,B_574] :
      ( r2_hidden('#skF_2'(A_573,B_574),B_574)
      | r2_hidden('#skF_3'(A_573,B_574),A_573)
      | B_574 = A_573 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12067,plain,(
    ! [B_575,A_576] :
      ( ~ v1_xboole_0(B_575)
      | r2_hidden('#skF_3'(A_576,B_575),A_576)
      | B_575 = A_576 ) ),
    inference(resolution,[status(thm)],[c_12023,c_2])).

tff(c_12095,plain,(
    ! [A_577,B_578] :
      ( ~ v1_xboole_0(A_577)
      | ~ v1_xboole_0(B_578)
      | B_578 = A_577 ) ),
    inference(resolution,[status(thm)],[c_12067,c_2])).

tff(c_12108,plain,(
    ! [B_579] :
      ( ~ v1_xboole_0(B_579)
      | B_579 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_10936,c_12095])).

tff(c_12114,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_11863,c_12108])).

tff(c_12125,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_12114])).

tff(c_12126,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_10947])).

tff(c_12274,plain,(
    ! [A_595,B_596] :
      ( r2_hidden('#skF_2'(A_595,B_596),B_596)
      | r2_hidden('#skF_3'(A_595,B_596),A_595)
      | B_596 = A_595 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12312,plain,(
    ! [B_597,A_598] :
      ( ~ v1_xboole_0(B_597)
      | r2_hidden('#skF_3'(A_598,B_597),A_598)
      | B_597 = A_598 ) ),
    inference(resolution,[status(thm)],[c_12274,c_2])).

tff(c_12353,plain,(
    ! [A_600,B_601] :
      ( ~ v1_xboole_0(A_600)
      | ~ v1_xboole_0(B_601)
      | B_601 = A_600 ) ),
    inference(resolution,[status(thm)],[c_12312,c_2])).

tff(c_12363,plain,(
    ! [B_602] :
      ( ~ v1_xboole_0(B_602)
      | B_602 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_12126,c_12353])).

tff(c_12372,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_10936,c_12363])).

tff(c_12379,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_12372])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.52/3.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.52/3.18  
% 9.52/3.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.52/3.18  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 9.52/3.18  
% 9.52/3.18  %Foreground sorts:
% 9.52/3.18  
% 9.52/3.18  
% 9.52/3.18  %Background operators:
% 9.52/3.18  
% 9.52/3.18  
% 9.52/3.18  %Foreground operators:
% 9.52/3.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.52/3.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.52/3.18  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.52/3.18  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.52/3.18  tff('#skF_5', type, '#skF_5': $i).
% 9.52/3.18  tff('#skF_6', type, '#skF_6': $i).
% 9.52/3.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.52/3.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.52/3.18  tff('#skF_4', type, '#skF_4': $i).
% 9.52/3.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.52/3.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.52/3.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.52/3.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.52/3.18  
% 9.76/3.21  tff(f_73, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_subset_1)).
% 9.76/3.21  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.76/3.21  tff(f_38, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 9.76/3.21  tff(f_51, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 9.76/3.21  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 9.76/3.21  tff(c_24, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.76/3.21  tff(c_54, plain, (![D_26]: (r2_hidden(D_26, '#skF_5') | ~r2_hidden(D_26, '#skF_6') | ~m1_subset_1(D_26, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.76/3.21  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.76/3.21  tff(c_58, plain, (![D_26]: (~v1_xboole_0('#skF_5') | ~r2_hidden(D_26, '#skF_6') | ~m1_subset_1(D_26, '#skF_4'))), inference(resolution, [status(thm)], [c_54, c_2])).
% 9.76/3.21  tff(c_82, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_58])).
% 9.76/3.21  tff(c_12, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), B_6) | r2_hidden('#skF_3'(A_5, B_6), A_5) | B_6=A_5)), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.76/3.21  tff(c_30, plain, (![D_18]: (r2_hidden(D_18, '#skF_5') | ~r2_hidden(D_18, '#skF_6') | ~m1_subset_1(D_18, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.76/3.21  tff(c_1390, plain, (![A_126, B_127]: (r2_hidden('#skF_2'(A_126, B_127), B_127) | ~r2_hidden('#skF_3'(A_126, B_127), B_127) | B_127=A_126)), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.76/3.21  tff(c_2883, plain, (![A_215]: (r2_hidden('#skF_2'(A_215, '#skF_5'), '#skF_5') | A_215='#skF_5' | ~r2_hidden('#skF_3'(A_215, '#skF_5'), '#skF_6') | ~m1_subset_1('#skF_3'(A_215, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_30, c_1390])).
% 9.76/3.21  tff(c_2903, plain, (~m1_subset_1('#skF_3'('#skF_6', '#skF_5'), '#skF_4') | r2_hidden('#skF_2'('#skF_6', '#skF_5'), '#skF_5') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_12, c_2883])).
% 9.76/3.21  tff(c_2921, plain, (~m1_subset_1('#skF_3'('#skF_6', '#skF_5'), '#skF_4') | r2_hidden('#skF_2'('#skF_6', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_24, c_24, c_2903])).
% 9.76/3.21  tff(c_2926, plain, (~m1_subset_1('#skF_3'('#skF_6', '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_2921])).
% 9.76/3.21  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.76/3.21  tff(c_83, plain, (![D_32]: (r2_hidden(D_32, '#skF_6') | ~r2_hidden(D_32, '#skF_5') | ~m1_subset_1(D_32, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.76/3.21  tff(c_97, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_6') | ~m1_subset_1('#skF_1'('#skF_5'), '#skF_4') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_83])).
% 9.76/3.21  tff(c_108, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_6') | ~m1_subset_1('#skF_1'('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_82, c_97])).
% 9.76/3.21  tff(c_109, plain, (~m1_subset_1('#skF_1'('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_108])).
% 9.76/3.21  tff(c_64, plain, (![B_29, A_30]: (m1_subset_1(B_29, A_30) | ~r2_hidden(B_29, A_30) | v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.76/3.21  tff(c_76, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_64])).
% 9.76/3.21  tff(c_18, plain, (![B_9, A_8]: (m1_subset_1(B_9, A_8) | ~v1_xboole_0(B_9) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.76/3.21  tff(c_126, plain, (~v1_xboole_0('#skF_1'('#skF_5')) | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_18, c_109])).
% 9.76/3.21  tff(c_127, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_126])).
% 9.76/3.21  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.76/3.21  tff(c_16, plain, (![B_9, A_8]: (r2_hidden(B_9, A_8) | ~m1_subset_1(B_9, A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.76/3.21  tff(c_98, plain, (![C_33, A_34, B_35]: (r2_hidden(C_33, A_34) | ~r2_hidden(C_33, B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.76/3.21  tff(c_1065, plain, (![B_106, A_107, A_108]: (r2_hidden(B_106, A_107) | ~m1_subset_1(A_108, k1_zfmisc_1(A_107)) | ~m1_subset_1(B_106, A_108) | v1_xboole_0(A_108))), inference(resolution, [status(thm)], [c_16, c_98])).
% 9.76/3.21  tff(c_1084, plain, (![B_106]: (r2_hidden(B_106, '#skF_4') | ~m1_subset_1(B_106, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_28, c_1065])).
% 9.76/3.21  tff(c_1147, plain, (![B_111]: (r2_hidden(B_111, '#skF_4') | ~m1_subset_1(B_111, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_82, c_1084])).
% 9.76/3.21  tff(c_14, plain, (![B_9, A_8]: (m1_subset_1(B_9, A_8) | ~r2_hidden(B_9, A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.76/3.21  tff(c_1159, plain, (![B_111]: (m1_subset_1(B_111, '#skF_4') | v1_xboole_0('#skF_4') | ~m1_subset_1(B_111, '#skF_5'))), inference(resolution, [status(thm)], [c_1147, c_14])).
% 9.76/3.21  tff(c_1209, plain, (![B_113]: (m1_subset_1(B_113, '#skF_4') | ~m1_subset_1(B_113, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_127, c_1159])).
% 9.76/3.21  tff(c_1231, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_4') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_76, c_1209])).
% 9.76/3.21  tff(c_1251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_109, c_1231])).
% 9.76/3.21  tff(c_1253, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_126])).
% 9.76/3.21  tff(c_1346, plain, (![A_122, A_123]: (r2_hidden('#skF_1'(A_122), A_123) | ~m1_subset_1(A_122, k1_zfmisc_1(A_123)) | v1_xboole_0(A_122))), inference(resolution, [status(thm)], [c_4, c_98])).
% 9.76/3.21  tff(c_1363, plain, (![A_124, A_125]: (~v1_xboole_0(A_124) | ~m1_subset_1(A_125, k1_zfmisc_1(A_124)) | v1_xboole_0(A_125))), inference(resolution, [status(thm)], [c_1346, c_2])).
% 9.76/3.21  tff(c_1377, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_28, c_1363])).
% 9.76/3.21  tff(c_1385, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1253, c_1377])).
% 9.76/3.21  tff(c_1387, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_1385])).
% 9.76/3.21  tff(c_1388, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_108])).
% 9.76/3.21  tff(c_1411, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_1388, c_2])).
% 9.76/3.21  tff(c_1470, plain, (![A_131, B_132]: (r2_hidden('#skF_2'(A_131, B_132), B_132) | r2_hidden('#skF_3'(A_131, B_132), A_131) | B_132=A_131)), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.76/3.21  tff(c_3442, plain, (![A_244, B_245]: (m1_subset_1('#skF_3'(A_244, B_245), A_244) | v1_xboole_0(A_244) | r2_hidden('#skF_2'(A_244, B_245), B_245) | B_245=A_244)), inference(resolution, [status(thm)], [c_1470, c_14])).
% 9.76/3.21  tff(c_32, plain, (![D_18]: (r2_hidden(D_18, '#skF_6') | ~r2_hidden(D_18, '#skF_5') | ~m1_subset_1(D_18, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.76/3.21  tff(c_7834, plain, (![A_397]: (r2_hidden('#skF_2'(A_397, '#skF_5'), '#skF_6') | ~m1_subset_1('#skF_2'(A_397, '#skF_5'), '#skF_4') | m1_subset_1('#skF_3'(A_397, '#skF_5'), A_397) | v1_xboole_0(A_397) | A_397='#skF_5')), inference(resolution, [status(thm)], [c_3442, c_32])).
% 9.76/3.21  tff(c_2198, plain, (![A_176, B_177]: (~r2_hidden('#skF_2'(A_176, B_177), A_176) | r2_hidden('#skF_3'(A_176, B_177), A_176) | B_177=A_176)), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.76/3.21  tff(c_2229, plain, (![A_176, B_177]: (m1_subset_1('#skF_3'(A_176, B_177), A_176) | v1_xboole_0(A_176) | ~r2_hidden('#skF_2'(A_176, B_177), A_176) | B_177=A_176)), inference(resolution, [status(thm)], [c_2198, c_14])).
% 9.76/3.21  tff(c_7841, plain, (~m1_subset_1('#skF_2'('#skF_6', '#skF_5'), '#skF_4') | m1_subset_1('#skF_3'('#skF_6', '#skF_5'), '#skF_6') | v1_xboole_0('#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_7834, c_2229])).
% 9.76/3.21  tff(c_7901, plain, (~m1_subset_1('#skF_2'('#skF_6', '#skF_5'), '#skF_4') | m1_subset_1('#skF_3'('#skF_6', '#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_24, c_1411, c_24, c_1411, c_7841])).
% 9.76/3.21  tff(c_7921, plain, (~m1_subset_1('#skF_2'('#skF_6', '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_7901])).
% 9.76/3.21  tff(c_8843, plain, (![A_431, B_432]: (m1_subset_1('#skF_2'(A_431, B_432), B_432) | v1_xboole_0(B_432) | m1_subset_1('#skF_3'(A_431, B_432), A_431) | v1_xboole_0(A_431) | B_432=A_431)), inference(resolution, [status(thm)], [c_3442, c_14])).
% 9.76/3.21  tff(c_1389, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_108])).
% 9.76/3.21  tff(c_20, plain, (![B_9, A_8]: (v1_xboole_0(B_9) | ~m1_subset_1(B_9, A_8) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.76/3.21  tff(c_1415, plain, (v1_xboole_0('#skF_1'('#skF_5')) | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1389, c_20])).
% 9.76/3.21  tff(c_1436, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_1415])).
% 9.76/3.21  tff(c_26, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.76/3.21  tff(c_2549, plain, (![B_195, A_196, A_197]: (r2_hidden(B_195, A_196) | ~m1_subset_1(A_197, k1_zfmisc_1(A_196)) | ~m1_subset_1(B_195, A_197) | v1_xboole_0(A_197))), inference(resolution, [status(thm)], [c_16, c_98])).
% 9.76/3.21  tff(c_2560, plain, (![B_195]: (r2_hidden(B_195, '#skF_4') | ~m1_subset_1(B_195, '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_26, c_2549])).
% 9.76/3.21  tff(c_2572, plain, (![B_198]: (r2_hidden(B_198, '#skF_4') | ~m1_subset_1(B_198, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_1411, c_2560])).
% 9.76/3.21  tff(c_2584, plain, (![B_198]: (m1_subset_1(B_198, '#skF_4') | v1_xboole_0('#skF_4') | ~m1_subset_1(B_198, '#skF_6'))), inference(resolution, [status(thm)], [c_2572, c_14])).
% 9.76/3.21  tff(c_2593, plain, (![B_198]: (m1_subset_1(B_198, '#skF_4') | ~m1_subset_1(B_198, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_1436, c_2584])).
% 9.76/3.21  tff(c_8941, plain, (![B_432]: (m1_subset_1('#skF_3'('#skF_6', B_432), '#skF_4') | m1_subset_1('#skF_2'('#skF_6', B_432), B_432) | v1_xboole_0(B_432) | v1_xboole_0('#skF_6') | B_432='#skF_6')), inference(resolution, [status(thm)], [c_8843, c_2593])).
% 9.76/3.21  tff(c_10530, plain, (![B_460]: (m1_subset_1('#skF_3'('#skF_6', B_460), '#skF_4') | m1_subset_1('#skF_2'('#skF_6', B_460), B_460) | v1_xboole_0(B_460) | B_460='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_1411, c_8941])).
% 9.76/3.21  tff(c_10537, plain, (m1_subset_1('#skF_2'('#skF_6', '#skF_5'), '#skF_5') | v1_xboole_0('#skF_5') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_10530, c_2926])).
% 9.76/3.21  tff(c_10595, plain, (m1_subset_1('#skF_2'('#skF_6', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_24, c_82, c_10537])).
% 9.76/3.21  tff(c_2562, plain, (![B_195]: (r2_hidden(B_195, '#skF_4') | ~m1_subset_1(B_195, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_28, c_2549])).
% 9.76/3.21  tff(c_2595, plain, (![B_199]: (r2_hidden(B_199, '#skF_4') | ~m1_subset_1(B_199, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_82, c_2562])).
% 9.76/3.21  tff(c_2607, plain, (![B_199]: (m1_subset_1(B_199, '#skF_4') | v1_xboole_0('#skF_4') | ~m1_subset_1(B_199, '#skF_5'))), inference(resolution, [status(thm)], [c_2595, c_14])).
% 9.76/3.21  tff(c_2616, plain, (![B_199]: (m1_subset_1(B_199, '#skF_4') | ~m1_subset_1(B_199, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_1436, c_2607])).
% 9.76/3.21  tff(c_10613, plain, (m1_subset_1('#skF_2'('#skF_6', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_10595, c_2616])).
% 9.76/3.21  tff(c_10623, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7921, c_10613])).
% 9.76/3.21  tff(c_10624, plain, (m1_subset_1('#skF_3'('#skF_6', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_7901])).
% 9.76/3.21  tff(c_10628, plain, (m1_subset_1('#skF_3'('#skF_6', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_10624, c_2593])).
% 9.76/3.21  tff(c_10635, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2926, c_10628])).
% 9.76/3.21  tff(c_10636, plain, (r2_hidden('#skF_2'('#skF_6', '#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_2921])).
% 9.76/3.21  tff(c_10645, plain, (m1_subset_1('#skF_2'('#skF_6', '#skF_5'), '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_10636, c_14])).
% 9.76/3.21  tff(c_10653, plain, (m1_subset_1('#skF_2'('#skF_6', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_82, c_10645])).
% 9.76/3.21  tff(c_10706, plain, (m1_subset_1('#skF_2'('#skF_6', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_10653, c_2616])).
% 9.76/3.21  tff(c_10650, plain, (r2_hidden('#skF_2'('#skF_6', '#skF_5'), '#skF_6') | ~m1_subset_1('#skF_2'('#skF_6', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_10636, c_32])).
% 9.76/3.21  tff(c_10714, plain, (r2_hidden('#skF_2'('#skF_6', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10706, c_10650])).
% 9.76/3.21  tff(c_10, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), A_5) | r2_hidden('#skF_3'(A_5, B_6), A_5) | B_6=A_5)), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.76/3.21  tff(c_10637, plain, (m1_subset_1('#skF_3'('#skF_6', '#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_2921])).
% 9.76/3.21  tff(c_6, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), A_5) | ~r2_hidden('#skF_3'(A_5, B_6), B_6) | B_6=A_5)), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.76/3.21  tff(c_10716, plain, (~r2_hidden('#skF_3'('#skF_6', '#skF_5'), '#skF_5') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_10714, c_6])).
% 9.76/3.21  tff(c_10733, plain, (~r2_hidden('#skF_3'('#skF_6', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_24, c_10716])).
% 9.76/3.21  tff(c_10750, plain, (~r2_hidden('#skF_3'('#skF_6', '#skF_5'), '#skF_6') | ~m1_subset_1('#skF_3'('#skF_6', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_30, c_10733])).
% 9.76/3.21  tff(c_10756, plain, (~r2_hidden('#skF_3'('#skF_6', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10637, c_10750])).
% 9.76/3.21  tff(c_10794, plain, (~r2_hidden('#skF_2'('#skF_6', '#skF_5'), '#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_10, c_10756])).
% 9.76/3.21  tff(c_10812, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_10714, c_10794])).
% 9.76/3.21  tff(c_10814, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_10812])).
% 9.76/3.21  tff(c_10816, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_1415])).
% 9.76/3.21  tff(c_22, plain, (![C_13, A_10, B_11]: (r2_hidden(C_13, A_10) | ~r2_hidden(C_13, B_11) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.76/3.21  tff(c_10897, plain, (![A_466]: (r2_hidden('#skF_1'('#skF_5'), A_466) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_466)))), inference(resolution, [status(thm)], [c_1388, c_22])).
% 9.76/3.21  tff(c_10923, plain, (![A_467]: (~v1_xboole_0(A_467) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_467)))), inference(resolution, [status(thm)], [c_10897, c_2])).
% 9.76/3.21  tff(c_10929, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_26, c_10923])).
% 9.76/3.21  tff(c_10934, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10816, c_10929])).
% 9.76/3.21  tff(c_10936, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_58])).
% 9.76/3.21  tff(c_10937, plain, (![D_468]: (~r2_hidden(D_468, '#skF_6') | ~m1_subset_1(D_468, '#skF_4'))), inference(splitRight, [status(thm)], [c_58])).
% 9.76/3.21  tff(c_10946, plain, (![B_9]: (~m1_subset_1(B_9, '#skF_4') | ~m1_subset_1(B_9, '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_16, c_10937])).
% 9.76/3.21  tff(c_10969, plain, (![B_470]: (~m1_subset_1(B_470, '#skF_4') | ~m1_subset_1(B_470, '#skF_6'))), inference(splitLeft, [status(thm)], [c_10946])).
% 9.76/3.21  tff(c_10979, plain, (![B_9]: (~m1_subset_1(B_9, '#skF_4') | ~v1_xboole_0(B_9) | ~v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_18, c_10969])).
% 9.76/3.21  tff(c_10980, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_10979])).
% 9.76/3.21  tff(c_10947, plain, (~m1_subset_1('#skF_1'('#skF_6'), '#skF_4') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_4, c_10937])).
% 9.76/3.21  tff(c_10961, plain, (~m1_subset_1('#skF_1'('#skF_6'), '#skF_4')), inference(splitLeft, [status(thm)], [c_10947])).
% 9.76/3.21  tff(c_10965, plain, (~v1_xboole_0('#skF_1'('#skF_6')) | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_18, c_10961])).
% 9.76/3.21  tff(c_10966, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_10965])).
% 9.76/3.21  tff(c_10981, plain, (![C_471, A_472, B_473]: (r2_hidden(C_471, A_472) | ~r2_hidden(C_471, B_473) | ~m1_subset_1(B_473, k1_zfmisc_1(A_472)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.76/3.21  tff(c_11387, plain, (![B_511, A_512, A_513]: (r2_hidden(B_511, A_512) | ~m1_subset_1(A_513, k1_zfmisc_1(A_512)) | ~m1_subset_1(B_511, A_513) | v1_xboole_0(A_513))), inference(resolution, [status(thm)], [c_16, c_10981])).
% 9.76/3.21  tff(c_11401, plain, (![B_511]: (r2_hidden(B_511, '#skF_4') | ~m1_subset_1(B_511, '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_26, c_11387])).
% 9.76/3.21  tff(c_11413, plain, (![B_514]: (r2_hidden(B_514, '#skF_4') | ~m1_subset_1(B_514, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_10980, c_11401])).
% 9.76/3.21  tff(c_11425, plain, (![B_514]: (m1_subset_1(B_514, '#skF_4') | v1_xboole_0('#skF_4') | ~m1_subset_1(B_514, '#skF_6'))), inference(resolution, [status(thm)], [c_11413, c_14])).
% 9.76/3.21  tff(c_11465, plain, (![B_517]: (m1_subset_1(B_517, '#skF_4') | ~m1_subset_1(B_517, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_10966, c_11425])).
% 9.76/3.21  tff(c_11477, plain, (m1_subset_1('#skF_1'('#skF_6'), '#skF_4') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_76, c_11465])).
% 9.76/3.21  tff(c_11491, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10980, c_10961, c_11477])).
% 9.76/3.21  tff(c_11493, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_10979])).
% 9.76/3.21  tff(c_11648, plain, (![A_536, B_537]: (r2_hidden('#skF_2'(A_536, B_537), B_537) | r2_hidden('#skF_3'(A_536, B_537), A_536) | B_537=A_536)), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.76/3.21  tff(c_11692, plain, (![B_538, A_539]: (~v1_xboole_0(B_538) | r2_hidden('#skF_3'(A_539, B_538), A_539) | B_538=A_539)), inference(resolution, [status(thm)], [c_11648, c_2])).
% 9.76/3.21  tff(c_11746, plain, (![A_542, B_543]: (~v1_xboole_0(A_542) | ~v1_xboole_0(B_543) | B_543=A_542)), inference(resolution, [status(thm)], [c_11692, c_2])).
% 9.76/3.21  tff(c_11756, plain, (![B_544]: (~v1_xboole_0(B_544) | B_544='#skF_5')), inference(resolution, [status(thm)], [c_10936, c_11746])).
% 9.76/3.21  tff(c_11762, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_11493, c_11756])).
% 9.76/3.21  tff(c_11770, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_11762])).
% 9.76/3.21  tff(c_11772, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_10965])).
% 9.76/3.21  tff(c_11775, plain, (![B_545]: (~m1_subset_1(B_545, '#skF_4') | ~m1_subset_1(B_545, '#skF_6'))), inference(splitLeft, [status(thm)], [c_10946])).
% 9.76/3.21  tff(c_11785, plain, (![B_9]: (~m1_subset_1(B_9, '#skF_4') | ~v1_xboole_0(B_9) | ~v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_18, c_11775])).
% 9.76/3.21  tff(c_11786, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_11785])).
% 9.76/3.21  tff(c_11787, plain, (![C_546, A_547, B_548]: (r2_hidden(C_546, A_547) | ~r2_hidden(C_546, B_548) | ~m1_subset_1(B_548, k1_zfmisc_1(A_547)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.76/3.21  tff(c_11794, plain, (![A_549, A_550]: (r2_hidden('#skF_1'(A_549), A_550) | ~m1_subset_1(A_549, k1_zfmisc_1(A_550)) | v1_xboole_0(A_549))), inference(resolution, [status(thm)], [c_4, c_11787])).
% 9.76/3.21  tff(c_11816, plain, (![A_551, A_552]: (~v1_xboole_0(A_551) | ~m1_subset_1(A_552, k1_zfmisc_1(A_551)) | v1_xboole_0(A_552))), inference(resolution, [status(thm)], [c_11794, c_2])).
% 9.76/3.21  tff(c_11827, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_26, c_11816])).
% 9.76/3.21  tff(c_11835, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11772, c_11827])).
% 9.76/3.21  tff(c_11837, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11786, c_11835])).
% 9.76/3.21  tff(c_11840, plain, (![B_553]: (~m1_subset_1(B_553, '#skF_4') | ~v1_xboole_0(B_553))), inference(splitRight, [status(thm)], [c_11785])).
% 9.76/3.21  tff(c_11848, plain, (![B_9]: (~v1_xboole_0(B_9) | ~v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_11840])).
% 9.76/3.21  tff(c_11853, plain, (![B_9]: (~v1_xboole_0(B_9))), inference(demodulation, [status(thm), theory('equality')], [c_11772, c_11848])).
% 9.76/3.21  tff(c_11839, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_11785])).
% 9.76/3.21  tff(c_11862, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11853, c_11839])).
% 9.76/3.21  tff(c_11863, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_10946])).
% 9.76/3.21  tff(c_12023, plain, (![A_573, B_574]: (r2_hidden('#skF_2'(A_573, B_574), B_574) | r2_hidden('#skF_3'(A_573, B_574), A_573) | B_574=A_573)), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.76/3.21  tff(c_12067, plain, (![B_575, A_576]: (~v1_xboole_0(B_575) | r2_hidden('#skF_3'(A_576, B_575), A_576) | B_575=A_576)), inference(resolution, [status(thm)], [c_12023, c_2])).
% 9.76/3.21  tff(c_12095, plain, (![A_577, B_578]: (~v1_xboole_0(A_577) | ~v1_xboole_0(B_578) | B_578=A_577)), inference(resolution, [status(thm)], [c_12067, c_2])).
% 9.76/3.21  tff(c_12108, plain, (![B_579]: (~v1_xboole_0(B_579) | B_579='#skF_5')), inference(resolution, [status(thm)], [c_10936, c_12095])).
% 9.76/3.21  tff(c_12114, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_11863, c_12108])).
% 9.76/3.21  tff(c_12125, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_12114])).
% 9.76/3.21  tff(c_12126, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_10947])).
% 9.76/3.21  tff(c_12274, plain, (![A_595, B_596]: (r2_hidden('#skF_2'(A_595, B_596), B_596) | r2_hidden('#skF_3'(A_595, B_596), A_595) | B_596=A_595)), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.76/3.21  tff(c_12312, plain, (![B_597, A_598]: (~v1_xboole_0(B_597) | r2_hidden('#skF_3'(A_598, B_597), A_598) | B_597=A_598)), inference(resolution, [status(thm)], [c_12274, c_2])).
% 9.76/3.21  tff(c_12353, plain, (![A_600, B_601]: (~v1_xboole_0(A_600) | ~v1_xboole_0(B_601) | B_601=A_600)), inference(resolution, [status(thm)], [c_12312, c_2])).
% 9.76/3.21  tff(c_12363, plain, (![B_602]: (~v1_xboole_0(B_602) | B_602='#skF_6')), inference(resolution, [status(thm)], [c_12126, c_12353])).
% 9.76/3.21  tff(c_12372, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_10936, c_12363])).
% 9.76/3.21  tff(c_12379, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_12372])).
% 9.76/3.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.76/3.21  
% 9.76/3.21  Inference rules
% 9.76/3.21  ----------------------
% 9.76/3.21  #Ref     : 0
% 9.76/3.21  #Sup     : 2478
% 9.76/3.21  #Fact    : 0
% 9.76/3.21  #Define  : 0
% 9.76/3.21  #Split   : 44
% 9.76/3.21  #Chain   : 0
% 9.76/3.21  #Close   : 0
% 9.76/3.21  
% 9.76/3.21  Ordering : KBO
% 9.76/3.21  
% 9.76/3.21  Simplification rules
% 9.76/3.21  ----------------------
% 9.76/3.21  #Subsume      : 935
% 9.76/3.21  #Demod        : 874
% 9.76/3.21  #Tautology    : 389
% 9.76/3.21  #SimpNegUnit  : 500
% 9.76/3.21  #BackRed      : 286
% 9.76/3.21  
% 9.76/3.21  #Partial instantiations: 0
% 9.76/3.21  #Strategies tried      : 1
% 9.76/3.21  
% 9.76/3.21  Timing (in seconds)
% 9.76/3.21  ----------------------
% 9.76/3.21  Preprocessing        : 0.29
% 9.76/3.21  Parsing              : 0.15
% 9.76/3.21  CNF conversion       : 0.02
% 9.76/3.21  Main loop            : 2.12
% 9.76/3.21  Inferencing          : 0.66
% 9.76/3.21  Reduction            : 0.52
% 9.76/3.21  Demodulation         : 0.30
% 9.76/3.21  BG Simplification    : 0.06
% 9.76/3.21  Subsumption          : 0.72
% 9.76/3.21  Abstraction          : 0.08
% 9.76/3.21  MUC search           : 0.00
% 9.76/3.21  Cooper               : 0.00
% 9.76/3.21  Total                : 2.46
% 9.76/3.21  Index Insertion      : 0.00
% 9.76/3.21  Index Deletion       : 0.00
% 9.76/3.21  Index Matching       : 0.00
% 9.76/3.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
