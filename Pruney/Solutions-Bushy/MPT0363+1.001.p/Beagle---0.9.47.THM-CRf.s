%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0363+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:10 EST 2020

% Result     : Theorem 20.42s
% Output     : CNFRefutation 20.58s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 134 expanded)
%              Number of leaves         :   23 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :  130 ( 318 expanded)
%              Number of equality atoms :   15 (  45 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,C)
            <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_40,plain,
    ( ~ r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_7'))
    | ~ r1_xboole_0('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_47,plain,(
    ~ r1_xboole_0('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_46,plain,
    ( r1_xboole_0('#skF_6','#skF_7')
    | r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_83,plain,(
    r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_46])).

tff(c_32,plain,(
    ! [A_18,B_19] :
      ( r2_hidden('#skF_4'(A_18,B_19),B_19)
      | r1_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_34,plain,(
    ! [A_18,B_19] :
      ( r2_hidden('#skF_4'(A_18,B_19),A_18)
      | r1_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_92,plain,(
    ! [C_42,B_43,A_44] :
      ( r2_hidden(C_42,B_43)
      | ~ r2_hidden(C_42,A_44)
      | ~ r1_tarski(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_315,plain,(
    ! [A_66,B_67,B_68] :
      ( r2_hidden('#skF_4'(A_66,B_67),B_68)
      | ~ r1_tarski(A_66,B_68)
      | r1_xboole_0(A_66,B_67) ) ),
    inference(resolution,[status(thm)],[c_34,c_92])).

tff(c_36,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_112,plain,(
    ! [A_48,B_49] :
      ( k4_xboole_0(A_48,B_49) = k3_subset_1(A_48,B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_119,plain,(
    k4_xboole_0('#skF_5','#skF_7') = k3_subset_1('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_112])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( ~ r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_127,plain,(
    ! [D_13] :
      ( ~ r2_hidden(D_13,'#skF_7')
      | ~ r2_hidden(D_13,k3_subset_1('#skF_5','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_12])).

tff(c_10250,plain,(
    ! [A_467,B_468] :
      ( ~ r2_hidden('#skF_4'(A_467,B_468),'#skF_7')
      | ~ r1_tarski(A_467,k3_subset_1('#skF_5','#skF_7'))
      | r1_xboole_0(A_467,B_468) ) ),
    inference(resolution,[status(thm)],[c_315,c_127])).

tff(c_10294,plain,(
    ! [A_469] :
      ( ~ r1_tarski(A_469,k3_subset_1('#skF_5','#skF_7'))
      | r1_xboole_0(A_469,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_32,c_10250])).

tff(c_10324,plain,(
    r1_xboole_0('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_83,c_10294])).

tff(c_10340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_10324])).

tff(c_10341,plain,(
    ~ r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10479,plain,(
    ! [C_498,A_499,B_500] :
      ( r2_hidden(C_498,A_499)
      | ~ r2_hidden(C_498,B_500)
      | ~ m1_subset_1(B_500,k1_zfmisc_1(A_499)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12172,plain,(
    ! [A_637,B_638,A_639] :
      ( r2_hidden('#skF_1'(A_637,B_638),A_639)
      | ~ m1_subset_1(A_637,k1_zfmisc_1(A_639))
      | r1_tarski(A_637,B_638) ) ),
    inference(resolution,[status(thm)],[c_6,c_10479])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12268,plain,(
    ! [A_640,A_641] :
      ( ~ m1_subset_1(A_640,k1_zfmisc_1(A_641))
      | r1_tarski(A_640,A_641) ) ),
    inference(resolution,[status(thm)],[c_12172,c_4])).

tff(c_12276,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_12268])).

tff(c_10434,plain,(
    ! [A_495,B_496] :
      ( k4_xboole_0(A_495,B_496) = k3_subset_1(A_495,B_496)
      | ~ m1_subset_1(B_496,k1_zfmisc_1(A_495)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10441,plain,(
    k4_xboole_0('#skF_5','#skF_7') = k3_subset_1('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_10434])).

tff(c_10391,plain,(
    ! [C_488,B_489,A_490] :
      ( r2_hidden(C_488,B_489)
      | ~ r2_hidden(C_488,A_490)
      | ~ r1_tarski(A_490,B_489) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10400,plain,(
    ! [A_1,B_2,B_489] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_489)
      | ~ r1_tarski(A_1,B_489)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_10391])).

tff(c_10549,plain,(
    ! [D_505,A_506,B_507] :
      ( r2_hidden(D_505,k4_xboole_0(A_506,B_507))
      | r2_hidden(D_505,B_507)
      | ~ r2_hidden(D_505,A_506) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14143,plain,(
    ! [A_789,A_790,B_791] :
      ( r1_tarski(A_789,k4_xboole_0(A_790,B_791))
      | r2_hidden('#skF_1'(A_789,k4_xboole_0(A_790,B_791)),B_791)
      | ~ r2_hidden('#skF_1'(A_789,k4_xboole_0(A_790,B_791)),A_790) ) ),
    inference(resolution,[status(thm)],[c_10549,c_4])).

tff(c_57626,plain,(
    ! [A_1950,B_1951,B_1952] :
      ( r2_hidden('#skF_1'(A_1950,k4_xboole_0(B_1951,B_1952)),B_1952)
      | ~ r1_tarski(A_1950,B_1951)
      | r1_tarski(A_1950,k4_xboole_0(B_1951,B_1952)) ) ),
    inference(resolution,[status(thm)],[c_10400,c_14143])).

tff(c_26,plain,(
    ! [A_8,B_9,C_10] :
      ( r2_hidden('#skF_2'(A_8,B_9,C_10),A_8)
      | r2_hidden('#skF_3'(A_8,B_9,C_10),C_10)
      | k4_xboole_0(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10902,plain,(
    ! [A_528,B_529,C_530] :
      ( ~ r2_hidden('#skF_2'(A_528,B_529,C_530),C_530)
      | r2_hidden('#skF_3'(A_528,B_529,C_530),C_530)
      | k4_xboole_0(A_528,B_529) = C_530 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10921,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_3'(A_8,B_9,A_8),A_8)
      | k4_xboole_0(A_8,B_9) = A_8 ) ),
    inference(resolution,[status(thm)],[c_26,c_10902])).

tff(c_20,plain,(
    ! [A_8,B_9,C_10] :
      ( r2_hidden('#skF_2'(A_8,B_9,C_10),A_8)
      | r2_hidden('#skF_3'(A_8,B_9,C_10),B_9)
      | ~ r2_hidden('#skF_3'(A_8,B_9,C_10),A_8)
      | k4_xboole_0(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_11394,plain,(
    ! [A_571,B_572,C_573] :
      ( ~ r2_hidden('#skF_2'(A_571,B_572,C_573),C_573)
      | r2_hidden('#skF_3'(A_571,B_572,C_573),B_572)
      | ~ r2_hidden('#skF_3'(A_571,B_572,C_573),A_571)
      | k4_xboole_0(A_571,B_572) = C_573 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_13706,plain,(
    ! [A_777,B_778] :
      ( r2_hidden('#skF_3'(A_777,B_778,A_777),B_778)
      | ~ r2_hidden('#skF_3'(A_777,B_778,A_777),A_777)
      | k4_xboole_0(A_777,B_778) = A_777 ) ),
    inference(resolution,[status(thm)],[c_20,c_11394])).

tff(c_13728,plain,(
    ! [A_779,B_780] :
      ( r2_hidden('#skF_3'(A_779,B_780,A_779),B_780)
      | k4_xboole_0(A_779,B_780) = A_779 ) ),
    inference(resolution,[status(thm)],[c_10921,c_13706])).

tff(c_10342,plain,(
    r1_xboole_0('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_10387,plain,(
    ! [A_485,B_486,C_487] :
      ( ~ r1_xboole_0(A_485,B_486)
      | ~ r2_hidden(C_487,B_486)
      | ~ r2_hidden(C_487,A_485) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10390,plain,(
    ! [C_487] :
      ( ~ r2_hidden(C_487,'#skF_7')
      | ~ r2_hidden(C_487,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_10342,c_10387])).

tff(c_13950,plain,(
    ! [A_785] :
      ( ~ r2_hidden('#skF_3'(A_785,'#skF_7',A_785),'#skF_6')
      | k4_xboole_0(A_785,'#skF_7') = A_785 ) ),
    inference(resolution,[status(thm)],[c_13728,c_10390])).

tff(c_13957,plain,(
    k4_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_10921,c_13950])).

tff(c_10345,plain,(
    ! [A_476,B_477] :
      ( r2_hidden('#skF_1'(A_476,B_477),A_476)
      | r1_tarski(A_476,B_477) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10354,plain,(
    ! [A_8,B_9,B_477] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_8,B_9),B_477),B_9)
      | r1_tarski(k4_xboole_0(A_8,B_9),B_477) ) ),
    inference(resolution,[status(thm)],[c_10345,c_12])).

tff(c_14026,plain,(
    ! [B_477] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_477),'#skF_7')
      | r1_tarski(k4_xboole_0('#skF_6','#skF_7'),B_477) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13957,c_10354])).

tff(c_14087,plain,(
    ! [B_477] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_477),'#skF_7')
      | r1_tarski('#skF_6',B_477) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13957,c_14026])).

tff(c_58088,plain,(
    ! [B_1954] :
      ( ~ r1_tarski('#skF_6',B_1954)
      | r1_tarski('#skF_6',k4_xboole_0(B_1954,'#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_57626,c_14087])).

tff(c_58192,plain,
    ( ~ r1_tarski('#skF_6','#skF_5')
    | r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10441,c_58088])).

tff(c_58242,plain,(
    r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12276,c_58192])).

tff(c_58244,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10341,c_58242])).

%------------------------------------------------------------------------------
