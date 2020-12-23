%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:51 EST 2020

% Result     : Theorem 14.55s
% Output     : CNFRefutation 14.67s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 159 expanded)
%              Number of leaves         :   19 (  62 expanded)
%              Depth                    :   16
%              Number of atoms          :  195 ( 502 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k7_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(k7_setfam_1(A,B),k7_setfam_1(A,C))
             => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_setfam_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r2_hidden(k3_subset_1(A,C),k7_setfam_1(A,B))
          <=> r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_setfam_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_20,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_84,plain,(
    ! [A_49,B_50,C_51] :
      ( r2_hidden('#skF_1'(A_49,B_50,C_51),B_50)
      | r1_tarski(B_50,C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(A_49))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_5,B_6,C_10] :
      ( ~ r2_hidden('#skF_1'(A_5,B_6,C_10),C_10)
      | r1_tarski(B_6,C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_112,plain,(
    ! [B_52,A_53] :
      ( r1_tarski(B_52,B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_53)) ) ),
    inference(resolution,[status(thm)],[c_84,c_4])).

tff(c_131,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_112])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_28,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | ~ m1_subset_1(A_24,k1_zfmisc_1(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_40,plain,(
    r1_tarski('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_28])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_212,plain,(
    ! [A_81,B_82,C_83,A_84] :
      ( r2_hidden('#skF_1'(A_81,B_82,C_83),A_84)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_84))
      | r1_tarski(B_82,C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(A_81))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_81)) ) ),
    inference(resolution,[status(thm)],[c_84,c_2])).

tff(c_405,plain,(
    ! [A_138,A_137,B_141,C_139,A_140] :
      ( r2_hidden('#skF_1'(A_138,B_141,C_139),A_140)
      | ~ m1_subset_1(A_137,k1_zfmisc_1(A_140))
      | ~ m1_subset_1(B_141,k1_zfmisc_1(A_137))
      | r1_tarski(B_141,C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(A_138))
      | ~ m1_subset_1(B_141,k1_zfmisc_1(A_138)) ) ),
    inference(resolution,[status(thm)],[c_212,c_2])).

tff(c_877,plain,(
    ! [B_237,A_235,A_234,B_233,C_236] :
      ( r2_hidden('#skF_1'(A_235,B_237,C_236),B_233)
      | ~ m1_subset_1(B_237,k1_zfmisc_1(A_234))
      | r1_tarski(B_237,C_236)
      | ~ m1_subset_1(C_236,k1_zfmisc_1(A_235))
      | ~ m1_subset_1(B_237,k1_zfmisc_1(A_235))
      | ~ r1_tarski(A_234,B_233) ) ),
    inference(resolution,[status(thm)],[c_12,c_405])).

tff(c_1307,plain,(
    ! [A_269,B_267,C_271,B_268,A_270] :
      ( r2_hidden('#skF_1'(A_270,A_269,C_271),B_268)
      | r1_tarski(A_269,C_271)
      | ~ m1_subset_1(C_271,k1_zfmisc_1(A_270))
      | ~ m1_subset_1(A_269,k1_zfmisc_1(A_270))
      | ~ r1_tarski(B_267,B_268)
      | ~ r1_tarski(A_269,B_267) ) ),
    inference(resolution,[status(thm)],[c_12,c_877])).

tff(c_1359,plain,(
    ! [A_272,A_273,C_274] :
      ( r2_hidden('#skF_1'(A_272,A_273,C_274),'#skF_3')
      | r1_tarski(A_273,C_274)
      | ~ m1_subset_1(C_274,k1_zfmisc_1(A_272))
      | ~ m1_subset_1(A_273,k1_zfmisc_1(A_272))
      | ~ r1_tarski(A_273,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_131,c_1307])).

tff(c_3728,plain,(
    ! [A_498,A_499,C_500,A_501] :
      ( r2_hidden('#skF_1'(A_498,A_499,C_500),A_501)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_501))
      | r1_tarski(A_499,C_500)
      | ~ m1_subset_1(C_500,k1_zfmisc_1(A_498))
      | ~ m1_subset_1(A_499,k1_zfmisc_1(A_498))
      | ~ r1_tarski(A_499,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1359,c_2])).

tff(c_42,plain,(
    ! [A_29,C_30,B_31] :
      ( m1_subset_1(A_29,C_30)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(C_30))
      | ~ r2_hidden(A_29,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_49,plain,(
    ! [A_29,B_13,A_12] :
      ( m1_subset_1(A_29,B_13)
      | ~ r2_hidden(A_29,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_12,c_42])).

tff(c_8817,plain,(
    ! [B_933,A_937,A_934,C_936,A_935] :
      ( m1_subset_1('#skF_1'(A_934,A_937,C_936),B_933)
      | ~ r1_tarski(A_935,B_933)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_935))
      | r1_tarski(A_937,C_936)
      | ~ m1_subset_1(C_936,k1_zfmisc_1(A_934))
      | ~ m1_subset_1(A_937,k1_zfmisc_1(A_934))
      | ~ r1_tarski(A_937,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3728,c_49])).

tff(c_8896,plain,(
    ! [A_934,A_937,C_936] :
      ( m1_subset_1('#skF_1'(A_934,A_937,C_936),k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3'))
      | r1_tarski(A_937,C_936)
      | ~ m1_subset_1(C_936,k1_zfmisc_1(A_934))
      | ~ m1_subset_1(A_937,k1_zfmisc_1(A_934))
      | ~ r1_tarski(A_937,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_40,c_8817])).

tff(c_8899,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_8896])).

tff(c_8902,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_8899])).

tff(c_8906,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_8902])).

tff(c_8908,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_8896])).

tff(c_6,plain,(
    ! [A_5,B_6,C_10] :
      ( r2_hidden('#skF_1'(A_5,B_6,C_10),B_6)
      | r1_tarski(B_6,C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_51,plain,(
    ! [A_29] :
      ( m1_subset_1(A_29,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_29,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_42])).

tff(c_22,plain,(
    r1_tarski(k7_setfam_1('#skF_2','#skF_3'),k7_setfam_1('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_111,plain,(
    ! [A_49,B_50,C_51,A_1] :
      ( r2_hidden('#skF_1'(A_49,B_50,C_51),A_1)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_1))
      | r1_tarski(B_50,C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(A_49))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_49)) ) ),
    inference(resolution,[status(thm)],[c_84,c_2])).

tff(c_157,plain,(
    ! [A_57,C_58,B_59] :
      ( r2_hidden(k3_subset_1(A_57,C_58),k7_setfam_1(A_57,B_59))
      | ~ r2_hidden(C_58,B_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(A_57))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(k1_zfmisc_1(A_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_280,plain,(
    ! [A_104,C_105,A_106,B_107] :
      ( r2_hidden(k3_subset_1(A_104,C_105),A_106)
      | ~ m1_subset_1(k7_setfam_1(A_104,B_107),k1_zfmisc_1(A_106))
      | ~ r2_hidden(C_105,B_107)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(A_104))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(k1_zfmisc_1(A_104))) ) ),
    inference(resolution,[status(thm)],[c_157,c_2])).

tff(c_324,plain,(
    ! [A_118,C_119,B_120,B_121] :
      ( r2_hidden(k3_subset_1(A_118,C_119),B_120)
      | ~ r2_hidden(C_119,B_121)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(A_118))
      | ~ m1_subset_1(B_121,k1_zfmisc_1(k1_zfmisc_1(A_118)))
      | ~ r1_tarski(k7_setfam_1(A_118,B_121),B_120) ) ),
    inference(resolution,[status(thm)],[c_12,c_280])).

tff(c_2850,plain,(
    ! [A_438,B_436,C_434,B_437,A_439,A_435] :
      ( r2_hidden(k3_subset_1(A_435,'#skF_1'(A_438,B_436,C_434)),B_437)
      | ~ m1_subset_1('#skF_1'(A_438,B_436,C_434),k1_zfmisc_1(A_435))
      | ~ m1_subset_1(A_439,k1_zfmisc_1(k1_zfmisc_1(A_435)))
      | ~ r1_tarski(k7_setfam_1(A_435,A_439),B_437)
      | ~ m1_subset_1(B_436,k1_zfmisc_1(A_439))
      | r1_tarski(B_436,C_434)
      | ~ m1_subset_1(C_434,k1_zfmisc_1(A_438))
      | ~ m1_subset_1(B_436,k1_zfmisc_1(A_438)) ) ),
    inference(resolution,[status(thm)],[c_111,c_324])).

tff(c_11931,plain,(
    ! [A_1236,B_1240,A_1238,C_1241,A_1237,B_1239] :
      ( r2_hidden(k3_subset_1(A_1236,'#skF_1'(A_1238,B_1240,C_1241)),B_1239)
      | ~ m1_subset_1('#skF_1'(A_1238,B_1240,C_1241),k1_zfmisc_1(A_1236))
      | ~ r1_tarski(k7_setfam_1(A_1236,A_1237),B_1239)
      | ~ m1_subset_1(B_1240,k1_zfmisc_1(A_1237))
      | r1_tarski(B_1240,C_1241)
      | ~ m1_subset_1(C_1241,k1_zfmisc_1(A_1238))
      | ~ m1_subset_1(B_1240,k1_zfmisc_1(A_1238))
      | ~ r1_tarski(A_1237,k1_zfmisc_1(A_1236)) ) ),
    inference(resolution,[status(thm)],[c_12,c_2850])).

tff(c_11935,plain,(
    ! [A_1238,B_1240,C_1241] :
      ( r2_hidden(k3_subset_1('#skF_2','#skF_1'(A_1238,B_1240,C_1241)),k7_setfam_1('#skF_2','#skF_4'))
      | ~ m1_subset_1('#skF_1'(A_1238,B_1240,C_1241),k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(B_1240,k1_zfmisc_1('#skF_3'))
      | r1_tarski(B_1240,C_1241)
      | ~ m1_subset_1(C_1241,k1_zfmisc_1(A_1238))
      | ~ m1_subset_1(B_1240,k1_zfmisc_1(A_1238))
      | ~ r1_tarski('#skF_3',k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_22,c_11931])).

tff(c_11976,plain,(
    ! [A_1245,B_1246,C_1247] :
      ( r2_hidden(k3_subset_1('#skF_2','#skF_1'(A_1245,B_1246,C_1247)),k7_setfam_1('#skF_2','#skF_4'))
      | ~ m1_subset_1('#skF_1'(A_1245,B_1246,C_1247),k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(B_1246,k1_zfmisc_1('#skF_3'))
      | r1_tarski(B_1246,C_1247)
      | ~ m1_subset_1(C_1247,k1_zfmisc_1(A_1245))
      | ~ m1_subset_1(B_1246,k1_zfmisc_1(A_1245)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_11935])).

tff(c_16,plain,(
    ! [C_17,B_15,A_14] :
      ( r2_hidden(C_17,B_15)
      | ~ r2_hidden(k3_subset_1(A_14,C_17),k7_setfam_1(A_14,B_15))
      | ~ m1_subset_1(C_17,k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(k1_zfmisc_1(A_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_11989,plain,(
    ! [A_1245,B_1246,C_1247] :
      ( r2_hidden('#skF_1'(A_1245,B_1246,C_1247),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ m1_subset_1('#skF_1'(A_1245,B_1246,C_1247),k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(B_1246,k1_zfmisc_1('#skF_3'))
      | r1_tarski(B_1246,C_1247)
      | ~ m1_subset_1(C_1247,k1_zfmisc_1(A_1245))
      | ~ m1_subset_1(B_1246,k1_zfmisc_1(A_1245)) ) ),
    inference(resolution,[status(thm)],[c_11976,c_16])).

tff(c_12010,plain,(
    ! [A_1248,B_1249,C_1250] :
      ( r2_hidden('#skF_1'(A_1248,B_1249,C_1250),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_1248,B_1249,C_1250),k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(B_1249,k1_zfmisc_1('#skF_3'))
      | r1_tarski(B_1249,C_1250)
      | ~ m1_subset_1(C_1250,k1_zfmisc_1(A_1248))
      | ~ m1_subset_1(B_1249,k1_zfmisc_1(A_1248)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_11989])).

tff(c_12088,plain,(
    ! [A_1251,B_1252,C_1253] :
      ( r2_hidden('#skF_1'(A_1251,B_1252,C_1253),'#skF_4')
      | ~ m1_subset_1(B_1252,k1_zfmisc_1('#skF_3'))
      | r1_tarski(B_1252,C_1253)
      | ~ m1_subset_1(C_1253,k1_zfmisc_1(A_1251))
      | ~ m1_subset_1(B_1252,k1_zfmisc_1(A_1251))
      | ~ r2_hidden('#skF_1'(A_1251,B_1252,C_1253),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_51,c_12010])).

tff(c_12151,plain,(
    ! [A_5,C_10] :
      ( r2_hidden('#skF_1'(A_5,'#skF_3',C_10),'#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3'))
      | r1_tarski('#skF_3',C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_5))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_5)) ) ),
    inference(resolution,[status(thm)],[c_6,c_12088])).

tff(c_12176,plain,(
    ! [A_1254,C_1255] :
      ( r2_hidden('#skF_1'(A_1254,'#skF_3',C_1255),'#skF_4')
      | r1_tarski('#skF_3',C_1255)
      | ~ m1_subset_1(C_1255,k1_zfmisc_1(A_1254))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1254)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8908,c_12151])).

tff(c_12212,plain,(
    ! [A_1254] :
      ( r1_tarski('#skF_3','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1254))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1254)) ) ),
    inference(resolution,[status(thm)],[c_12176,c_4])).

tff(c_12240,plain,(
    ! [A_1256] :
      ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1256))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1256)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_20,c_12212])).

tff(c_12258,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_26,c_12240])).

tff(c_12266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_12258])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:34:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.55/7.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.67/7.71  
% 14.67/7.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.67/7.71  %$ r2_hidden > r1_tarski > m1_subset_1 > k7_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 14.67/7.71  
% 14.67/7.71  %Foreground sorts:
% 14.67/7.71  
% 14.67/7.71  
% 14.67/7.71  %Background operators:
% 14.67/7.71  
% 14.67/7.71  
% 14.67/7.71  %Foreground operators:
% 14.67/7.71  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 14.67/7.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.67/7.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.67/7.71  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 14.67/7.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.67/7.71  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 14.67/7.71  tff('#skF_2', type, '#skF_2': $i).
% 14.67/7.71  tff('#skF_3', type, '#skF_3': $i).
% 14.67/7.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.67/7.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.67/7.71  tff('#skF_4', type, '#skF_4': $i).
% 14.67/7.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.67/7.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.67/7.71  
% 14.67/7.73  tff(f_75, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(k7_setfam_1(A, B), k7_setfam_1(A, C)) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_setfam_1)).
% 14.67/7.73  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 14.67/7.73  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 14.67/7.73  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 14.67/7.73  tff(f_65, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 14.67/7.73  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r2_hidden(k3_subset_1(A, C), k7_setfam_1(A, B)) <=> r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_setfam_1)).
% 14.67/7.73  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.67/7.73  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.67/7.73  tff(c_20, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.67/7.73  tff(c_84, plain, (![A_49, B_50, C_51]: (r2_hidden('#skF_1'(A_49, B_50, C_51), B_50) | r1_tarski(B_50, C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(A_49)) | ~m1_subset_1(B_50, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 14.67/7.73  tff(c_4, plain, (![A_5, B_6, C_10]: (~r2_hidden('#skF_1'(A_5, B_6, C_10), C_10) | r1_tarski(B_6, C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 14.67/7.73  tff(c_112, plain, (![B_52, A_53]: (r1_tarski(B_52, B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(A_53)))), inference(resolution, [status(thm)], [c_84, c_4])).
% 14.67/7.73  tff(c_131, plain, (r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_112])).
% 14.67/7.73  tff(c_12, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 14.67/7.73  tff(c_28, plain, (![A_24, B_25]: (r1_tarski(A_24, B_25) | ~m1_subset_1(A_24, k1_zfmisc_1(B_25)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 14.67/7.73  tff(c_40, plain, (r1_tarski('#skF_3', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_28])).
% 14.67/7.73  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.67/7.73  tff(c_212, plain, (![A_81, B_82, C_83, A_84]: (r2_hidden('#skF_1'(A_81, B_82, C_83), A_84) | ~m1_subset_1(B_82, k1_zfmisc_1(A_84)) | r1_tarski(B_82, C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(A_81)) | ~m1_subset_1(B_82, k1_zfmisc_1(A_81)))), inference(resolution, [status(thm)], [c_84, c_2])).
% 14.67/7.73  tff(c_405, plain, (![A_138, A_137, B_141, C_139, A_140]: (r2_hidden('#skF_1'(A_138, B_141, C_139), A_140) | ~m1_subset_1(A_137, k1_zfmisc_1(A_140)) | ~m1_subset_1(B_141, k1_zfmisc_1(A_137)) | r1_tarski(B_141, C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(A_138)) | ~m1_subset_1(B_141, k1_zfmisc_1(A_138)))), inference(resolution, [status(thm)], [c_212, c_2])).
% 14.67/7.73  tff(c_877, plain, (![B_237, A_235, A_234, B_233, C_236]: (r2_hidden('#skF_1'(A_235, B_237, C_236), B_233) | ~m1_subset_1(B_237, k1_zfmisc_1(A_234)) | r1_tarski(B_237, C_236) | ~m1_subset_1(C_236, k1_zfmisc_1(A_235)) | ~m1_subset_1(B_237, k1_zfmisc_1(A_235)) | ~r1_tarski(A_234, B_233))), inference(resolution, [status(thm)], [c_12, c_405])).
% 14.67/7.73  tff(c_1307, plain, (![A_269, B_267, C_271, B_268, A_270]: (r2_hidden('#skF_1'(A_270, A_269, C_271), B_268) | r1_tarski(A_269, C_271) | ~m1_subset_1(C_271, k1_zfmisc_1(A_270)) | ~m1_subset_1(A_269, k1_zfmisc_1(A_270)) | ~r1_tarski(B_267, B_268) | ~r1_tarski(A_269, B_267))), inference(resolution, [status(thm)], [c_12, c_877])).
% 14.67/7.73  tff(c_1359, plain, (![A_272, A_273, C_274]: (r2_hidden('#skF_1'(A_272, A_273, C_274), '#skF_3') | r1_tarski(A_273, C_274) | ~m1_subset_1(C_274, k1_zfmisc_1(A_272)) | ~m1_subset_1(A_273, k1_zfmisc_1(A_272)) | ~r1_tarski(A_273, '#skF_3'))), inference(resolution, [status(thm)], [c_131, c_1307])).
% 14.67/7.73  tff(c_3728, plain, (![A_498, A_499, C_500, A_501]: (r2_hidden('#skF_1'(A_498, A_499, C_500), A_501) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_501)) | r1_tarski(A_499, C_500) | ~m1_subset_1(C_500, k1_zfmisc_1(A_498)) | ~m1_subset_1(A_499, k1_zfmisc_1(A_498)) | ~r1_tarski(A_499, '#skF_3'))), inference(resolution, [status(thm)], [c_1359, c_2])).
% 14.67/7.73  tff(c_42, plain, (![A_29, C_30, B_31]: (m1_subset_1(A_29, C_30) | ~m1_subset_1(B_31, k1_zfmisc_1(C_30)) | ~r2_hidden(A_29, B_31))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.67/7.73  tff(c_49, plain, (![A_29, B_13, A_12]: (m1_subset_1(A_29, B_13) | ~r2_hidden(A_29, A_12) | ~r1_tarski(A_12, B_13))), inference(resolution, [status(thm)], [c_12, c_42])).
% 14.67/7.73  tff(c_8817, plain, (![B_933, A_937, A_934, C_936, A_935]: (m1_subset_1('#skF_1'(A_934, A_937, C_936), B_933) | ~r1_tarski(A_935, B_933) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_935)) | r1_tarski(A_937, C_936) | ~m1_subset_1(C_936, k1_zfmisc_1(A_934)) | ~m1_subset_1(A_937, k1_zfmisc_1(A_934)) | ~r1_tarski(A_937, '#skF_3'))), inference(resolution, [status(thm)], [c_3728, c_49])).
% 14.67/7.73  tff(c_8896, plain, (![A_934, A_937, C_936]: (m1_subset_1('#skF_1'(A_934, A_937, C_936), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')) | r1_tarski(A_937, C_936) | ~m1_subset_1(C_936, k1_zfmisc_1(A_934)) | ~m1_subset_1(A_937, k1_zfmisc_1(A_934)) | ~r1_tarski(A_937, '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_8817])).
% 14.67/7.73  tff(c_8899, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_8896])).
% 14.67/7.73  tff(c_8902, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_12, c_8899])).
% 14.67/7.73  tff(c_8906, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_8902])).
% 14.67/7.73  tff(c_8908, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_8896])).
% 14.67/7.73  tff(c_6, plain, (![A_5, B_6, C_10]: (r2_hidden('#skF_1'(A_5, B_6, C_10), B_6) | r1_tarski(B_6, C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 14.67/7.73  tff(c_51, plain, (![A_29]: (m1_subset_1(A_29, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_29, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_42])).
% 14.67/7.73  tff(c_22, plain, (r1_tarski(k7_setfam_1('#skF_2', '#skF_3'), k7_setfam_1('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.67/7.73  tff(c_111, plain, (![A_49, B_50, C_51, A_1]: (r2_hidden('#skF_1'(A_49, B_50, C_51), A_1) | ~m1_subset_1(B_50, k1_zfmisc_1(A_1)) | r1_tarski(B_50, C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(A_49)) | ~m1_subset_1(B_50, k1_zfmisc_1(A_49)))), inference(resolution, [status(thm)], [c_84, c_2])).
% 14.67/7.73  tff(c_157, plain, (![A_57, C_58, B_59]: (r2_hidden(k3_subset_1(A_57, C_58), k7_setfam_1(A_57, B_59)) | ~r2_hidden(C_58, B_59) | ~m1_subset_1(C_58, k1_zfmisc_1(A_57)) | ~m1_subset_1(B_59, k1_zfmisc_1(k1_zfmisc_1(A_57))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.67/7.73  tff(c_280, plain, (![A_104, C_105, A_106, B_107]: (r2_hidden(k3_subset_1(A_104, C_105), A_106) | ~m1_subset_1(k7_setfam_1(A_104, B_107), k1_zfmisc_1(A_106)) | ~r2_hidden(C_105, B_107) | ~m1_subset_1(C_105, k1_zfmisc_1(A_104)) | ~m1_subset_1(B_107, k1_zfmisc_1(k1_zfmisc_1(A_104))))), inference(resolution, [status(thm)], [c_157, c_2])).
% 14.67/7.73  tff(c_324, plain, (![A_118, C_119, B_120, B_121]: (r2_hidden(k3_subset_1(A_118, C_119), B_120) | ~r2_hidden(C_119, B_121) | ~m1_subset_1(C_119, k1_zfmisc_1(A_118)) | ~m1_subset_1(B_121, k1_zfmisc_1(k1_zfmisc_1(A_118))) | ~r1_tarski(k7_setfam_1(A_118, B_121), B_120))), inference(resolution, [status(thm)], [c_12, c_280])).
% 14.67/7.73  tff(c_2850, plain, (![A_438, B_436, C_434, B_437, A_439, A_435]: (r2_hidden(k3_subset_1(A_435, '#skF_1'(A_438, B_436, C_434)), B_437) | ~m1_subset_1('#skF_1'(A_438, B_436, C_434), k1_zfmisc_1(A_435)) | ~m1_subset_1(A_439, k1_zfmisc_1(k1_zfmisc_1(A_435))) | ~r1_tarski(k7_setfam_1(A_435, A_439), B_437) | ~m1_subset_1(B_436, k1_zfmisc_1(A_439)) | r1_tarski(B_436, C_434) | ~m1_subset_1(C_434, k1_zfmisc_1(A_438)) | ~m1_subset_1(B_436, k1_zfmisc_1(A_438)))), inference(resolution, [status(thm)], [c_111, c_324])).
% 14.67/7.73  tff(c_11931, plain, (![A_1236, B_1240, A_1238, C_1241, A_1237, B_1239]: (r2_hidden(k3_subset_1(A_1236, '#skF_1'(A_1238, B_1240, C_1241)), B_1239) | ~m1_subset_1('#skF_1'(A_1238, B_1240, C_1241), k1_zfmisc_1(A_1236)) | ~r1_tarski(k7_setfam_1(A_1236, A_1237), B_1239) | ~m1_subset_1(B_1240, k1_zfmisc_1(A_1237)) | r1_tarski(B_1240, C_1241) | ~m1_subset_1(C_1241, k1_zfmisc_1(A_1238)) | ~m1_subset_1(B_1240, k1_zfmisc_1(A_1238)) | ~r1_tarski(A_1237, k1_zfmisc_1(A_1236)))), inference(resolution, [status(thm)], [c_12, c_2850])).
% 14.67/7.73  tff(c_11935, plain, (![A_1238, B_1240, C_1241]: (r2_hidden(k3_subset_1('#skF_2', '#skF_1'(A_1238, B_1240, C_1241)), k7_setfam_1('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_1'(A_1238, B_1240, C_1241), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(B_1240, k1_zfmisc_1('#skF_3')) | r1_tarski(B_1240, C_1241) | ~m1_subset_1(C_1241, k1_zfmisc_1(A_1238)) | ~m1_subset_1(B_1240, k1_zfmisc_1(A_1238)) | ~r1_tarski('#skF_3', k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_22, c_11931])).
% 14.67/7.73  tff(c_11976, plain, (![A_1245, B_1246, C_1247]: (r2_hidden(k3_subset_1('#skF_2', '#skF_1'(A_1245, B_1246, C_1247)), k7_setfam_1('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_1'(A_1245, B_1246, C_1247), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(B_1246, k1_zfmisc_1('#skF_3')) | r1_tarski(B_1246, C_1247) | ~m1_subset_1(C_1247, k1_zfmisc_1(A_1245)) | ~m1_subset_1(B_1246, k1_zfmisc_1(A_1245)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_11935])).
% 14.67/7.73  tff(c_16, plain, (![C_17, B_15, A_14]: (r2_hidden(C_17, B_15) | ~r2_hidden(k3_subset_1(A_14, C_17), k7_setfam_1(A_14, B_15)) | ~m1_subset_1(C_17, k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(k1_zfmisc_1(A_14))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.67/7.73  tff(c_11989, plain, (![A_1245, B_1246, C_1247]: (r2_hidden('#skF_1'(A_1245, B_1246, C_1247), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1('#skF_1'(A_1245, B_1246, C_1247), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(B_1246, k1_zfmisc_1('#skF_3')) | r1_tarski(B_1246, C_1247) | ~m1_subset_1(C_1247, k1_zfmisc_1(A_1245)) | ~m1_subset_1(B_1246, k1_zfmisc_1(A_1245)))), inference(resolution, [status(thm)], [c_11976, c_16])).
% 14.67/7.73  tff(c_12010, plain, (![A_1248, B_1249, C_1250]: (r2_hidden('#skF_1'(A_1248, B_1249, C_1250), '#skF_4') | ~m1_subset_1('#skF_1'(A_1248, B_1249, C_1250), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(B_1249, k1_zfmisc_1('#skF_3')) | r1_tarski(B_1249, C_1250) | ~m1_subset_1(C_1250, k1_zfmisc_1(A_1248)) | ~m1_subset_1(B_1249, k1_zfmisc_1(A_1248)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_11989])).
% 14.67/7.73  tff(c_12088, plain, (![A_1251, B_1252, C_1253]: (r2_hidden('#skF_1'(A_1251, B_1252, C_1253), '#skF_4') | ~m1_subset_1(B_1252, k1_zfmisc_1('#skF_3')) | r1_tarski(B_1252, C_1253) | ~m1_subset_1(C_1253, k1_zfmisc_1(A_1251)) | ~m1_subset_1(B_1252, k1_zfmisc_1(A_1251)) | ~r2_hidden('#skF_1'(A_1251, B_1252, C_1253), '#skF_3'))), inference(resolution, [status(thm)], [c_51, c_12010])).
% 14.67/7.73  tff(c_12151, plain, (![A_5, C_10]: (r2_hidden('#skF_1'(A_5, '#skF_3', C_10), '#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')) | r1_tarski('#skF_3', C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(A_5)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_5)))), inference(resolution, [status(thm)], [c_6, c_12088])).
% 14.67/7.73  tff(c_12176, plain, (![A_1254, C_1255]: (r2_hidden('#skF_1'(A_1254, '#skF_3', C_1255), '#skF_4') | r1_tarski('#skF_3', C_1255) | ~m1_subset_1(C_1255, k1_zfmisc_1(A_1254)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1254)))), inference(demodulation, [status(thm), theory('equality')], [c_8908, c_12151])).
% 14.67/7.73  tff(c_12212, plain, (![A_1254]: (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1254)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1254)))), inference(resolution, [status(thm)], [c_12176, c_4])).
% 14.67/7.73  tff(c_12240, plain, (![A_1256]: (~m1_subset_1('#skF_4', k1_zfmisc_1(A_1256)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1256)))), inference(negUnitSimplification, [status(thm)], [c_20, c_20, c_12212])).
% 14.67/7.73  tff(c_12258, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_26, c_12240])).
% 14.67/7.73  tff(c_12266, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_12258])).
% 14.67/7.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.67/7.73  
% 14.67/7.73  Inference rules
% 14.67/7.73  ----------------------
% 14.67/7.73  #Ref     : 0
% 14.67/7.73  #Sup     : 3183
% 14.67/7.73  #Fact    : 0
% 14.67/7.73  #Define  : 0
% 14.67/7.73  #Split   : 47
% 14.67/7.73  #Chain   : 0
% 14.67/7.73  #Close   : 0
% 14.67/7.73  
% 14.67/7.73  Ordering : KBO
% 14.67/7.73  
% 14.67/7.73  Simplification rules
% 14.67/7.73  ----------------------
% 14.67/7.73  #Subsume      : 1194
% 14.67/7.73  #Demod        : 143
% 14.67/7.73  #Tautology    : 48
% 14.67/7.73  #SimpNegUnit  : 6
% 14.67/7.73  #BackRed      : 0
% 14.67/7.73  
% 14.67/7.73  #Partial instantiations: 0
% 14.67/7.73  #Strategies tried      : 1
% 14.67/7.73  
% 14.67/7.73  Timing (in seconds)
% 14.67/7.73  ----------------------
% 14.67/7.73  Preprocessing        : 0.28
% 14.67/7.73  Parsing              : 0.16
% 14.67/7.73  CNF conversion       : 0.02
% 14.67/7.73  Main loop            : 6.68
% 14.67/7.73  Inferencing          : 0.88
% 14.67/7.73  Reduction            : 0.86
% 14.67/7.73  Demodulation         : 0.49
% 14.67/7.73  BG Simplification    : 0.08
% 14.67/7.73  Subsumption          : 4.56
% 14.67/7.73  Abstraction          : 0.14
% 14.67/7.73  MUC search           : 0.00
% 14.67/7.73  Cooper               : 0.00
% 14.67/7.73  Total                : 6.99
% 14.67/7.73  Index Insertion      : 0.00
% 14.67/7.73  Index Deletion       : 0.00
% 14.67/7.73  Index Matching       : 0.00
% 14.67/7.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
