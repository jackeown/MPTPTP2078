%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:51 EST 2020

% Result     : Theorem 6.00s
% Output     : CNFRefutation 6.00s
% Verified   : 
% Statistics : Number of formulae       :   52 (  73 expanded)
%              Number of leaves         :   19 (  34 expanded)
%              Depth                    :   16
%              Number of atoms          :  136 ( 207 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k7_setfam_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(k7_setfam_1(A,B),k7_setfam_1(A,C))
             => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_setfam_1)).

tff(f_50,axiom,(
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

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r2_hidden(k3_subset_1(A,C),k7_setfam_1(A,B))
          <=> r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_setfam_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8,plain,(
    ! [A_7,B_8,C_12] :
      ( r2_hidden('#skF_1'(A_7,B_8,C_12),B_8)
      | r1_tarski(B_8,C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_97,plain,(
    ! [A_38,B_39,C_40] :
      ( ~ r2_hidden('#skF_1'(A_38,B_39,C_40),C_40)
      | r1_tarski(B_39,C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(A_38))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_103,plain,(
    ! [B_41,A_42] :
      ( r1_tarski(B_41,B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42)) ) ),
    inference(resolution,[status(thm)],[c_8,c_97])).

tff(c_116,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_103])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_20,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_10,plain,(
    ! [A_7,B_8,C_12] :
      ( m1_subset_1('#skF_1'(A_7,B_8,C_12),A_7)
      | r1_tarski(B_8,C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_27,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(A_21,B_22)
      | ~ m1_subset_1(A_21,k1_zfmisc_1(B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_35,plain,(
    r1_tarski('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_27])).

tff(c_22,plain,(
    r1_tarski(k7_setfam_1('#skF_2','#skF_3'),k7_setfam_1('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_93,plain,(
    ! [A_35,B_36,C_37] :
      ( r2_hidden('#skF_1'(A_35,B_36,C_37),B_36)
      | r1_tarski(B_36,C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(A_35))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [C_6,A_3,B_4] :
      ( r2_hidden(C_6,A_3)
      | ~ r2_hidden(C_6,B_4)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_96,plain,(
    ! [A_35,B_36,C_37,A_3] :
      ( r2_hidden('#skF_1'(A_35,B_36,C_37),A_3)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_3))
      | r1_tarski(B_36,C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(A_35))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(resolution,[status(thm)],[c_93,c_4])).

tff(c_166,plain,(
    ! [A_48,C_49,B_50] :
      ( r2_hidden(k3_subset_1(A_48,C_49),k7_setfam_1(A_48,B_50))
      | ~ r2_hidden(C_49,B_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(A_48))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(k1_zfmisc_1(A_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_191,plain,(
    ! [A_58,C_59,A_60,B_61] :
      ( r2_hidden(k3_subset_1(A_58,C_59),A_60)
      | ~ m1_subset_1(k7_setfam_1(A_58,B_61),k1_zfmisc_1(A_60))
      | ~ r2_hidden(C_59,B_61)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(A_58))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k1_zfmisc_1(A_58))) ) ),
    inference(resolution,[status(thm)],[c_166,c_4])).

tff(c_196,plain,(
    ! [A_62,C_63,B_64,B_65] :
      ( r2_hidden(k3_subset_1(A_62,C_63),B_64)
      | ~ r2_hidden(C_63,B_65)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(A_62))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(k1_zfmisc_1(A_62)))
      | ~ r1_tarski(k7_setfam_1(A_62,B_65),B_64) ) ),
    inference(resolution,[status(thm)],[c_14,c_191])).

tff(c_1306,plain,(
    ! [C_290,B_293,A_289,A_288,B_291,A_292] :
      ( r2_hidden(k3_subset_1(A_289,'#skF_1'(A_288,B_293,C_290)),B_291)
      | ~ m1_subset_1('#skF_1'(A_288,B_293,C_290),k1_zfmisc_1(A_289))
      | ~ m1_subset_1(A_292,k1_zfmisc_1(k1_zfmisc_1(A_289)))
      | ~ r1_tarski(k7_setfam_1(A_289,A_292),B_291)
      | ~ m1_subset_1(B_293,k1_zfmisc_1(A_292))
      | r1_tarski(B_293,C_290)
      | ~ m1_subset_1(C_290,k1_zfmisc_1(A_288))
      | ~ m1_subset_1(B_293,k1_zfmisc_1(A_288)) ) ),
    inference(resolution,[status(thm)],[c_96,c_196])).

tff(c_2038,plain,(
    ! [A_498,B_501,B_497,A_500,A_499,C_496] :
      ( r2_hidden(k3_subset_1(A_498,'#skF_1'(A_499,B_501,C_496)),B_497)
      | ~ m1_subset_1('#skF_1'(A_499,B_501,C_496),k1_zfmisc_1(A_498))
      | ~ r1_tarski(k7_setfam_1(A_498,A_500),B_497)
      | ~ m1_subset_1(B_501,k1_zfmisc_1(A_500))
      | r1_tarski(B_501,C_496)
      | ~ m1_subset_1(C_496,k1_zfmisc_1(A_499))
      | ~ m1_subset_1(B_501,k1_zfmisc_1(A_499))
      | ~ r1_tarski(A_500,k1_zfmisc_1(A_498)) ) ),
    inference(resolution,[status(thm)],[c_14,c_1306])).

tff(c_2042,plain,(
    ! [A_499,B_501,C_496] :
      ( r2_hidden(k3_subset_1('#skF_2','#skF_1'(A_499,B_501,C_496)),k7_setfam_1('#skF_2','#skF_4'))
      | ~ m1_subset_1('#skF_1'(A_499,B_501,C_496),k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(B_501,k1_zfmisc_1('#skF_3'))
      | r1_tarski(B_501,C_496)
      | ~ m1_subset_1(C_496,k1_zfmisc_1(A_499))
      | ~ m1_subset_1(B_501,k1_zfmisc_1(A_499))
      | ~ r1_tarski('#skF_3',k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_22,c_2038])).

tff(c_2064,plain,(
    ! [A_507,B_508,C_509] :
      ( r2_hidden(k3_subset_1('#skF_2','#skF_1'(A_507,B_508,C_509)),k7_setfam_1('#skF_2','#skF_4'))
      | ~ m1_subset_1('#skF_1'(A_507,B_508,C_509),k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(B_508,k1_zfmisc_1('#skF_3'))
      | r1_tarski(B_508,C_509)
      | ~ m1_subset_1(C_509,k1_zfmisc_1(A_507))
      | ~ m1_subset_1(B_508,k1_zfmisc_1(A_507)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_2042])).

tff(c_18,plain,(
    ! [C_19,B_17,A_16] :
      ( r2_hidden(C_19,B_17)
      | ~ r2_hidden(k3_subset_1(A_16,C_19),k7_setfam_1(A_16,B_17))
      | ~ m1_subset_1(C_19,k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(A_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2069,plain,(
    ! [A_507,B_508,C_509] :
      ( r2_hidden('#skF_1'(A_507,B_508,C_509),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ m1_subset_1('#skF_1'(A_507,B_508,C_509),k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(B_508,k1_zfmisc_1('#skF_3'))
      | r1_tarski(B_508,C_509)
      | ~ m1_subset_1(C_509,k1_zfmisc_1(A_507))
      | ~ m1_subset_1(B_508,k1_zfmisc_1(A_507)) ) ),
    inference(resolution,[status(thm)],[c_2064,c_18])).

tff(c_2077,plain,(
    ! [A_510,B_511,C_512] :
      ( r2_hidden('#skF_1'(A_510,B_511,C_512),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_510,B_511,C_512),k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(B_511,k1_zfmisc_1('#skF_3'))
      | r1_tarski(B_511,C_512)
      | ~ m1_subset_1(C_512,k1_zfmisc_1(A_510))
      | ~ m1_subset_1(B_511,k1_zfmisc_1(A_510)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2069])).

tff(c_2087,plain,(
    ! [B_513,C_514] :
      ( r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'),B_513,C_514),'#skF_4')
      | ~ m1_subset_1(B_513,k1_zfmisc_1('#skF_3'))
      | r1_tarski(B_513,C_514)
      | ~ m1_subset_1(C_514,k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ m1_subset_1(B_513,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_10,c_2077])).

tff(c_6,plain,(
    ! [A_7,B_8,C_12] :
      ( ~ r2_hidden('#skF_1'(A_7,B_8,C_12),C_12)
      | r1_tarski(B_8,C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2093,plain,(
    ! [B_513] :
      ( ~ m1_subset_1(B_513,k1_zfmisc_1('#skF_3'))
      | r1_tarski(B_513,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ m1_subset_1(B_513,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_2087,c_6])).

tff(c_2101,plain,(
    ! [B_515] :
      ( ~ m1_subset_1(B_515,k1_zfmisc_1('#skF_3'))
      | r1_tarski(B_515,'#skF_4')
      | ~ m1_subset_1(B_515,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2093])).

tff(c_2115,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3'))
    | r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_2101])).

tff(c_2122,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_2115])).

tff(c_2139,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_2122])).

tff(c_2143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_2139])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:20:45 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.00/2.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.00/2.16  
% 6.00/2.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.00/2.16  %$ r2_hidden > r1_tarski > m1_subset_1 > k7_setfam_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 6.00/2.16  
% 6.00/2.16  %Foreground sorts:
% 6.00/2.16  
% 6.00/2.16  
% 6.00/2.16  %Background operators:
% 6.00/2.16  
% 6.00/2.16  
% 6.00/2.16  %Foreground operators:
% 6.00/2.16  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.00/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.00/2.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.00/2.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.00/2.16  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 6.00/2.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.00/2.16  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.00/2.16  tff('#skF_2', type, '#skF_2': $i).
% 6.00/2.16  tff('#skF_3', type, '#skF_3': $i).
% 6.00/2.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.00/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.00/2.16  tff('#skF_4', type, '#skF_4': $i).
% 6.00/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.00/2.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.00/2.16  
% 6.00/2.17  tff(f_73, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(k7_setfam_1(A, B), k7_setfam_1(A, C)) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_setfam_1)).
% 6.00/2.17  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 6.00/2.17  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.00/2.17  tff(f_36, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 6.00/2.17  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r2_hidden(k3_subset_1(A, C), k7_setfam_1(A, B)) <=> r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_setfam_1)).
% 6.00/2.17  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.00/2.17  tff(c_8, plain, (![A_7, B_8, C_12]: (r2_hidden('#skF_1'(A_7, B_8, C_12), B_8) | r1_tarski(B_8, C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.00/2.17  tff(c_97, plain, (![A_38, B_39, C_40]: (~r2_hidden('#skF_1'(A_38, B_39, C_40), C_40) | r1_tarski(B_39, C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(A_38)) | ~m1_subset_1(B_39, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.00/2.17  tff(c_103, plain, (![B_41, A_42]: (r1_tarski(B_41, B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)))), inference(resolution, [status(thm)], [c_8, c_97])).
% 6.00/2.17  tff(c_116, plain, (r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_103])).
% 6.00/2.17  tff(c_14, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.00/2.17  tff(c_20, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.00/2.17  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.00/2.17  tff(c_10, plain, (![A_7, B_8, C_12]: (m1_subset_1('#skF_1'(A_7, B_8, C_12), A_7) | r1_tarski(B_8, C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.00/2.17  tff(c_27, plain, (![A_21, B_22]: (r1_tarski(A_21, B_22) | ~m1_subset_1(A_21, k1_zfmisc_1(B_22)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.00/2.17  tff(c_35, plain, (r1_tarski('#skF_3', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_27])).
% 6.00/2.17  tff(c_22, plain, (r1_tarski(k7_setfam_1('#skF_2', '#skF_3'), k7_setfam_1('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.00/2.17  tff(c_93, plain, (![A_35, B_36, C_37]: (r2_hidden('#skF_1'(A_35, B_36, C_37), B_36) | r1_tarski(B_36, C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(A_35)) | ~m1_subset_1(B_36, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.00/2.17  tff(c_4, plain, (![C_6, A_3, B_4]: (r2_hidden(C_6, A_3) | ~r2_hidden(C_6, B_4) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.00/2.17  tff(c_96, plain, (![A_35, B_36, C_37, A_3]: (r2_hidden('#skF_1'(A_35, B_36, C_37), A_3) | ~m1_subset_1(B_36, k1_zfmisc_1(A_3)) | r1_tarski(B_36, C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(A_35)) | ~m1_subset_1(B_36, k1_zfmisc_1(A_35)))), inference(resolution, [status(thm)], [c_93, c_4])).
% 6.00/2.17  tff(c_166, plain, (![A_48, C_49, B_50]: (r2_hidden(k3_subset_1(A_48, C_49), k7_setfam_1(A_48, B_50)) | ~r2_hidden(C_49, B_50) | ~m1_subset_1(C_49, k1_zfmisc_1(A_48)) | ~m1_subset_1(B_50, k1_zfmisc_1(k1_zfmisc_1(A_48))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.00/2.17  tff(c_191, plain, (![A_58, C_59, A_60, B_61]: (r2_hidden(k3_subset_1(A_58, C_59), A_60) | ~m1_subset_1(k7_setfam_1(A_58, B_61), k1_zfmisc_1(A_60)) | ~r2_hidden(C_59, B_61) | ~m1_subset_1(C_59, k1_zfmisc_1(A_58)) | ~m1_subset_1(B_61, k1_zfmisc_1(k1_zfmisc_1(A_58))))), inference(resolution, [status(thm)], [c_166, c_4])).
% 6.00/2.17  tff(c_196, plain, (![A_62, C_63, B_64, B_65]: (r2_hidden(k3_subset_1(A_62, C_63), B_64) | ~r2_hidden(C_63, B_65) | ~m1_subset_1(C_63, k1_zfmisc_1(A_62)) | ~m1_subset_1(B_65, k1_zfmisc_1(k1_zfmisc_1(A_62))) | ~r1_tarski(k7_setfam_1(A_62, B_65), B_64))), inference(resolution, [status(thm)], [c_14, c_191])).
% 6.00/2.17  tff(c_1306, plain, (![C_290, B_293, A_289, A_288, B_291, A_292]: (r2_hidden(k3_subset_1(A_289, '#skF_1'(A_288, B_293, C_290)), B_291) | ~m1_subset_1('#skF_1'(A_288, B_293, C_290), k1_zfmisc_1(A_289)) | ~m1_subset_1(A_292, k1_zfmisc_1(k1_zfmisc_1(A_289))) | ~r1_tarski(k7_setfam_1(A_289, A_292), B_291) | ~m1_subset_1(B_293, k1_zfmisc_1(A_292)) | r1_tarski(B_293, C_290) | ~m1_subset_1(C_290, k1_zfmisc_1(A_288)) | ~m1_subset_1(B_293, k1_zfmisc_1(A_288)))), inference(resolution, [status(thm)], [c_96, c_196])).
% 6.00/2.17  tff(c_2038, plain, (![A_498, B_501, B_497, A_500, A_499, C_496]: (r2_hidden(k3_subset_1(A_498, '#skF_1'(A_499, B_501, C_496)), B_497) | ~m1_subset_1('#skF_1'(A_499, B_501, C_496), k1_zfmisc_1(A_498)) | ~r1_tarski(k7_setfam_1(A_498, A_500), B_497) | ~m1_subset_1(B_501, k1_zfmisc_1(A_500)) | r1_tarski(B_501, C_496) | ~m1_subset_1(C_496, k1_zfmisc_1(A_499)) | ~m1_subset_1(B_501, k1_zfmisc_1(A_499)) | ~r1_tarski(A_500, k1_zfmisc_1(A_498)))), inference(resolution, [status(thm)], [c_14, c_1306])).
% 6.00/2.17  tff(c_2042, plain, (![A_499, B_501, C_496]: (r2_hidden(k3_subset_1('#skF_2', '#skF_1'(A_499, B_501, C_496)), k7_setfam_1('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_1'(A_499, B_501, C_496), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(B_501, k1_zfmisc_1('#skF_3')) | r1_tarski(B_501, C_496) | ~m1_subset_1(C_496, k1_zfmisc_1(A_499)) | ~m1_subset_1(B_501, k1_zfmisc_1(A_499)) | ~r1_tarski('#skF_3', k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_22, c_2038])).
% 6.00/2.17  tff(c_2064, plain, (![A_507, B_508, C_509]: (r2_hidden(k3_subset_1('#skF_2', '#skF_1'(A_507, B_508, C_509)), k7_setfam_1('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_1'(A_507, B_508, C_509), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(B_508, k1_zfmisc_1('#skF_3')) | r1_tarski(B_508, C_509) | ~m1_subset_1(C_509, k1_zfmisc_1(A_507)) | ~m1_subset_1(B_508, k1_zfmisc_1(A_507)))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_2042])).
% 6.00/2.17  tff(c_18, plain, (![C_19, B_17, A_16]: (r2_hidden(C_19, B_17) | ~r2_hidden(k3_subset_1(A_16, C_19), k7_setfam_1(A_16, B_17)) | ~m1_subset_1(C_19, k1_zfmisc_1(A_16)) | ~m1_subset_1(B_17, k1_zfmisc_1(k1_zfmisc_1(A_16))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.00/2.17  tff(c_2069, plain, (![A_507, B_508, C_509]: (r2_hidden('#skF_1'(A_507, B_508, C_509), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1('#skF_1'(A_507, B_508, C_509), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(B_508, k1_zfmisc_1('#skF_3')) | r1_tarski(B_508, C_509) | ~m1_subset_1(C_509, k1_zfmisc_1(A_507)) | ~m1_subset_1(B_508, k1_zfmisc_1(A_507)))), inference(resolution, [status(thm)], [c_2064, c_18])).
% 6.00/2.17  tff(c_2077, plain, (![A_510, B_511, C_512]: (r2_hidden('#skF_1'(A_510, B_511, C_512), '#skF_4') | ~m1_subset_1('#skF_1'(A_510, B_511, C_512), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(B_511, k1_zfmisc_1('#skF_3')) | r1_tarski(B_511, C_512) | ~m1_subset_1(C_512, k1_zfmisc_1(A_510)) | ~m1_subset_1(B_511, k1_zfmisc_1(A_510)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2069])).
% 6.00/2.17  tff(c_2087, plain, (![B_513, C_514]: (r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'), B_513, C_514), '#skF_4') | ~m1_subset_1(B_513, k1_zfmisc_1('#skF_3')) | r1_tarski(B_513, C_514) | ~m1_subset_1(C_514, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1(B_513, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(resolution, [status(thm)], [c_10, c_2077])).
% 6.00/2.17  tff(c_6, plain, (![A_7, B_8, C_12]: (~r2_hidden('#skF_1'(A_7, B_8, C_12), C_12) | r1_tarski(B_8, C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.00/2.17  tff(c_2093, plain, (![B_513]: (~m1_subset_1(B_513, k1_zfmisc_1('#skF_3')) | r1_tarski(B_513, '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1(B_513, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(resolution, [status(thm)], [c_2087, c_6])).
% 6.00/2.17  tff(c_2101, plain, (![B_515]: (~m1_subset_1(B_515, k1_zfmisc_1('#skF_3')) | r1_tarski(B_515, '#skF_4') | ~m1_subset_1(B_515, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2093])).
% 6.00/2.17  tff(c_2115, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')) | r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_26, c_2101])).
% 6.00/2.17  tff(c_2122, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_20, c_2115])).
% 6.00/2.17  tff(c_2139, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_14, c_2122])).
% 6.00/2.17  tff(c_2143, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_116, c_2139])).
% 6.00/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.00/2.17  
% 6.00/2.17  Inference rules
% 6.00/2.17  ----------------------
% 6.00/2.17  #Ref     : 0
% 6.00/2.17  #Sup     : 497
% 6.00/2.17  #Fact    : 0
% 6.00/2.17  #Define  : 0
% 6.00/2.17  #Split   : 9
% 6.00/2.17  #Chain   : 0
% 6.00/2.17  #Close   : 0
% 6.00/2.17  
% 6.00/2.17  Ordering : KBO
% 6.00/2.17  
% 6.00/2.17  Simplification rules
% 6.00/2.17  ----------------------
% 6.00/2.17  #Subsume      : 102
% 6.00/2.17  #Demod        : 136
% 6.00/2.17  #Tautology    : 127
% 6.00/2.17  #SimpNegUnit  : 11
% 6.00/2.17  #BackRed      : 0
% 6.00/2.17  
% 6.00/2.17  #Partial instantiations: 0
% 6.00/2.17  #Strategies tried      : 1
% 6.00/2.17  
% 6.00/2.17  Timing (in seconds)
% 6.00/2.17  ----------------------
% 6.00/2.18  Preprocessing        : 0.30
% 6.00/2.18  Parsing              : 0.16
% 6.00/2.18  CNF conversion       : 0.02
% 6.00/2.18  Main loop            : 1.12
% 6.00/2.18  Inferencing          : 0.36
% 6.00/2.18  Reduction            : 0.25
% 6.00/2.18  Demodulation         : 0.17
% 6.00/2.18  BG Simplification    : 0.03
% 6.00/2.18  Subsumption          : 0.41
% 6.00/2.18  Abstraction          : 0.04
% 6.00/2.18  MUC search           : 0.00
% 6.00/2.18  Cooper               : 0.00
% 6.00/2.18  Total                : 1.45
% 6.00/2.18  Index Insertion      : 0.00
% 6.00/2.18  Index Deletion       : 0.00
% 6.00/2.18  Index Matching       : 0.00
% 6.00/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
