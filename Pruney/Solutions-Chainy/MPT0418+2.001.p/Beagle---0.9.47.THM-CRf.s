%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:50 EST 2020

% Result     : Theorem 17.04s
% Output     : CNFRefutation 17.13s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 196 expanded)
%              Number of leaves         :   27 (  77 expanded)
%              Depth                    :   11
%              Number of atoms          :  123 ( 308 expanded)
%              Number of equality atoms :   31 (  79 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k7_setfam_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r2_hidden(k3_subset_1(A,C),k7_setfam_1(A,B))
            <=> r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_setfam_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_41,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

tff(c_42,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | ~ r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_116,plain,(
    ~ r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_48,plain,
    ( r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2','#skF_3'))
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_173,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_48])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_95,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,B_45)
      | ~ m1_subset_1(A_44,k1_zfmisc_1(B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_111,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_95])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_115,plain,(
    k3_xboole_0('#skF_4','#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_111,c_6])).

tff(c_179,plain,(
    ! [A_50,B_51] : k4_xboole_0(A_50,k4_xboole_0(A_50,B_51)) = k3_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_13,B_14] : k6_subset_1(A_13,B_14) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_11,B_12] : m1_subset_1(k6_subset_1(A_11,B_12),k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_49,plain,(
    ! [A_11,B_12] : m1_subset_1(k4_xboole_0(A_11,B_12),k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12])).

tff(c_109,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(resolution,[status(thm)],[c_49,c_95])).

tff(c_204,plain,(
    ! [A_52,B_53] : r1_tarski(k3_xboole_0(A_52,B_53),A_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_109])).

tff(c_213,plain,(
    r1_tarski('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_204])).

tff(c_228,plain,(
    k3_xboole_0('#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_213,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_273,plain,(
    ! [A_56,B_57] : r1_tarski(k3_xboole_0(A_56,B_57),B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_204])).

tff(c_2816,plain,(
    ! [A_148,B_149] : k3_xboole_0(k3_xboole_0(A_148,B_149),B_149) = k3_xboole_0(A_148,B_149) ),
    inference(resolution,[status(thm)],[c_273,c_6])).

tff(c_3209,plain,(
    ! [A_152,B_153] : k3_xboole_0(k3_xboole_0(A_152,B_153),A_152) = k3_xboole_0(B_153,A_152) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2816])).

tff(c_3357,plain,(
    k3_xboole_0('#skF_2','#skF_4') = k3_xboole_0('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_3209])).

tff(c_3406,plain,(
    k3_xboole_0('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_3357])).

tff(c_229,plain,(
    ! [A_54,B_55] :
      ( k4_xboole_0(A_54,B_55) = k3_subset_1(A_54,B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_250,plain,(
    k4_xboole_0('#skF_2','#skF_4') = k3_subset_1('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_229])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_479,plain,(
    ! [A_68,B_69] :
      ( m1_subset_1(k7_setfam_1(A_68,B_69),k1_zfmisc_1(k1_zfmisc_1(A_68)))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(k1_zfmisc_1(A_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_32,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,B_29)
      | ~ m1_subset_1(A_28,k1_zfmisc_1(B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2439,plain,(
    ! [A_137,B_138] :
      ( r1_tarski(k7_setfam_1(A_137,B_138),k1_zfmisc_1(A_137))
      | ~ m1_subset_1(B_138,k1_zfmisc_1(k1_zfmisc_1(A_137))) ) ),
    inference(resolution,[status(thm)],[c_479,c_32])).

tff(c_2445,plain,(
    ! [A_137,B_138] :
      ( k3_xboole_0(k7_setfam_1(A_137,B_138),k1_zfmisc_1(A_137)) = k7_setfam_1(A_137,B_138)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(k1_zfmisc_1(A_137))) ) ),
    inference(resolution,[status(thm)],[c_2439,c_6])).

tff(c_5748,plain,(
    ! [A_199,B_200] :
      ( k3_xboole_0(k1_zfmisc_1(A_199),k7_setfam_1(A_199,B_200)) = k7_setfam_1(A_199,B_200)
      | ~ m1_subset_1(B_200,k1_zfmisc_1(k1_zfmisc_1(A_199))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2445])).

tff(c_5780,plain,(
    k3_xboole_0(k1_zfmisc_1('#skF_2'),k7_setfam_1('#skF_2','#skF_3')) = k7_setfam_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_5748])).

tff(c_191,plain,(
    ! [A_50,B_51] : m1_subset_1(k3_xboole_0(A_50,B_51),k1_zfmisc_1(A_50)) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_49])).

tff(c_5859,plain,(
    m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_5780,c_191])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_238,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_subset_1(A_11,k4_xboole_0(A_11,B_12)) ),
    inference(resolution,[status(thm)],[c_49,c_229])).

tff(c_248,plain,(
    ! [A_11,B_12] : k3_subset_1(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_238])).

tff(c_832,plain,(
    ! [D_85,A_86,B_87] :
      ( r2_hidden(D_85,k7_setfam_1(A_86,B_87))
      | ~ r2_hidden(k3_subset_1(A_86,D_85),B_87)
      | ~ m1_subset_1(D_85,k1_zfmisc_1(A_86))
      | ~ m1_subset_1(k7_setfam_1(A_86,B_87),k1_zfmisc_1(k1_zfmisc_1(A_86)))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(k1_zfmisc_1(A_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_836,plain,(
    ! [A_11,B_12,B_87] :
      ( r2_hidden(k4_xboole_0(A_11,B_12),k7_setfam_1(A_11,B_87))
      | ~ r2_hidden(k3_xboole_0(A_11,B_12),B_87)
      | ~ m1_subset_1(k4_xboole_0(A_11,B_12),k1_zfmisc_1(A_11))
      | ~ m1_subset_1(k7_setfam_1(A_11,B_87),k1_zfmisc_1(k1_zfmisc_1(A_11)))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(k1_zfmisc_1(A_11))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_832])).

tff(c_10462,plain,(
    ! [A_262,B_263,B_264] :
      ( r2_hidden(k4_xboole_0(A_262,B_263),k7_setfam_1(A_262,B_264))
      | ~ r2_hidden(k3_xboole_0(A_262,B_263),B_264)
      | ~ m1_subset_1(k7_setfam_1(A_262,B_264),k1_zfmisc_1(k1_zfmisc_1(A_262)))
      | ~ m1_subset_1(B_264,k1_zfmisc_1(k1_zfmisc_1(A_262))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_836])).

tff(c_10464,plain,(
    ! [B_263] :
      ( r2_hidden(k4_xboole_0('#skF_2',B_263),k7_setfam_1('#skF_2','#skF_3'))
      | ~ r2_hidden(k3_xboole_0('#skF_2',B_263),'#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_5859,c_10462])).

tff(c_35250,plain,(
    ! [B_531] :
      ( r2_hidden(k4_xboole_0('#skF_2',B_531),k7_setfam_1('#skF_2','#skF_3'))
      | ~ r2_hidden(k3_xboole_0('#skF_2',B_531),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_10464])).

tff(c_35340,plain,
    ( r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2','#skF_3'))
    | ~ r2_hidden(k3_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_35250])).

tff(c_35375,plain,(
    r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_3406,c_35340])).

tff(c_35377,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_35375])).

tff(c_35378,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_35668,plain,(
    ! [A_554,B_555] :
      ( k4_xboole_0(A_554,B_555) = k3_subset_1(A_554,B_555)
      | ~ m1_subset_1(B_555,k1_zfmisc_1(A_554)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_35705,plain,(
    k4_xboole_0('#skF_2','#skF_4') = k3_subset_1('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_35668])).

tff(c_35715,plain,(
    m1_subset_1(k3_subset_1('#skF_2','#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_35705,c_49])).

tff(c_35379,plain,(
    r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_35709,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_2','#skF_4')) = k3_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_35705,c_8])).

tff(c_35718,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_2,c_35709])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = k3_subset_1(A_9,B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_35756,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_2','#skF_4')) = k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_35715,c_10])).

tff(c_35763,plain,(
    k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35718,c_35756])).

tff(c_30,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(k7_setfam_1(A_26,B_27),k1_zfmisc_1(k1_zfmisc_1(A_26)))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(k1_zfmisc_1(A_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_36080,plain,(
    ! [A_568,D_569,B_570] :
      ( r2_hidden(k3_subset_1(A_568,D_569),B_570)
      | ~ r2_hidden(D_569,k7_setfam_1(A_568,B_570))
      | ~ m1_subset_1(D_569,k1_zfmisc_1(A_568))
      | ~ m1_subset_1(k7_setfam_1(A_568,B_570),k1_zfmisc_1(k1_zfmisc_1(A_568)))
      | ~ m1_subset_1(B_570,k1_zfmisc_1(k1_zfmisc_1(A_568))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_39411,plain,(
    ! [A_644,D_645,B_646] :
      ( r2_hidden(k3_subset_1(A_644,D_645),B_646)
      | ~ r2_hidden(D_645,k7_setfam_1(A_644,B_646))
      | ~ m1_subset_1(D_645,k1_zfmisc_1(A_644))
      | ~ m1_subset_1(B_646,k1_zfmisc_1(k1_zfmisc_1(A_644))) ) ),
    inference(resolution,[status(thm)],[c_30,c_36080])).

tff(c_39444,plain,(
    ! [D_647] :
      ( r2_hidden(k3_subset_1('#skF_2',D_647),'#skF_3')
      | ~ r2_hidden(D_647,k7_setfam_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(D_647,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_40,c_39411])).

tff(c_39469,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | ~ r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k3_subset_1('#skF_2','#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_35763,c_39444])).

tff(c_39484,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35715,c_35379,c_39469])).

tff(c_39486,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35378,c_39484])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:06:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.04/8.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.04/8.15  
% 17.04/8.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.04/8.15  %$ r2_hidden > r1_tarski > m1_subset_1 > k7_setfam_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 17.04/8.15  
% 17.04/8.15  %Foreground sorts:
% 17.04/8.15  
% 17.04/8.15  
% 17.04/8.15  %Background operators:
% 17.04/8.15  
% 17.04/8.15  
% 17.04/8.15  %Foreground operators:
% 17.04/8.15  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 17.04/8.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.04/8.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.04/8.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 17.04/8.15  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 17.04/8.15  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 17.04/8.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.04/8.15  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 17.04/8.15  tff('#skF_2', type, '#skF_2': $i).
% 17.04/8.15  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 17.04/8.15  tff('#skF_3', type, '#skF_3': $i).
% 17.04/8.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 17.04/8.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.04/8.15  tff('#skF_4', type, '#skF_4': $i).
% 17.04/8.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.04/8.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 17.04/8.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 17.04/8.15  
% 17.13/8.17  tff(f_81, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r2_hidden(k3_subset_1(A, C), k7_setfam_1(A, B)) <=> r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_setfam_1)).
% 17.13/8.17  tff(f_65, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 17.13/8.17  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 17.13/8.17  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 17.13/8.17  tff(f_43, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 17.13/8.17  tff(f_41, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 17.13/8.17  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 17.13/8.17  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 17.13/8.17  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 17.13/8.17  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 17.13/8.17  tff(c_42, plain, (~r2_hidden('#skF_4', '#skF_3') | ~r2_hidden(k3_subset_1('#skF_2', '#skF_4'), k7_setfam_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 17.13/8.17  tff(c_116, plain, (~r2_hidden(k3_subset_1('#skF_2', '#skF_4'), k7_setfam_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_42])).
% 17.13/8.17  tff(c_48, plain, (r2_hidden(k3_subset_1('#skF_2', '#skF_4'), k7_setfam_1('#skF_2', '#skF_3')) | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 17.13/8.17  tff(c_173, plain, (r2_hidden('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_116, c_48])).
% 17.13/8.17  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 17.13/8.17  tff(c_95, plain, (![A_44, B_45]: (r1_tarski(A_44, B_45) | ~m1_subset_1(A_44, k1_zfmisc_1(B_45)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 17.13/8.17  tff(c_111, plain, (r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_95])).
% 17.13/8.17  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 17.13/8.17  tff(c_115, plain, (k3_xboole_0('#skF_4', '#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_111, c_6])).
% 17.13/8.17  tff(c_179, plain, (![A_50, B_51]: (k4_xboole_0(A_50, k4_xboole_0(A_50, B_51))=k3_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_35])).
% 17.13/8.17  tff(c_14, plain, (![A_13, B_14]: (k6_subset_1(A_13, B_14)=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 17.13/8.17  tff(c_12, plain, (![A_11, B_12]: (m1_subset_1(k6_subset_1(A_11, B_12), k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 17.13/8.17  tff(c_49, plain, (![A_11, B_12]: (m1_subset_1(k4_xboole_0(A_11, B_12), k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_12])).
% 17.13/8.17  tff(c_109, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(resolution, [status(thm)], [c_49, c_95])).
% 17.13/8.17  tff(c_204, plain, (![A_52, B_53]: (r1_tarski(k3_xboole_0(A_52, B_53), A_52))), inference(superposition, [status(thm), theory('equality')], [c_179, c_109])).
% 17.13/8.17  tff(c_213, plain, (r1_tarski('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_115, c_204])).
% 17.13/8.17  tff(c_228, plain, (k3_xboole_0('#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_213, c_6])).
% 17.13/8.17  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 17.13/8.17  tff(c_273, plain, (![A_56, B_57]: (r1_tarski(k3_xboole_0(A_56, B_57), B_57))), inference(superposition, [status(thm), theory('equality')], [c_2, c_204])).
% 17.13/8.17  tff(c_2816, plain, (![A_148, B_149]: (k3_xboole_0(k3_xboole_0(A_148, B_149), B_149)=k3_xboole_0(A_148, B_149))), inference(resolution, [status(thm)], [c_273, c_6])).
% 17.13/8.17  tff(c_3209, plain, (![A_152, B_153]: (k3_xboole_0(k3_xboole_0(A_152, B_153), A_152)=k3_xboole_0(B_153, A_152))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2816])).
% 17.13/8.17  tff(c_3357, plain, (k3_xboole_0('#skF_2', '#skF_4')=k3_xboole_0('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_115, c_3209])).
% 17.13/8.17  tff(c_3406, plain, (k3_xboole_0('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_228, c_3357])).
% 17.13/8.17  tff(c_229, plain, (![A_54, B_55]: (k4_xboole_0(A_54, B_55)=k3_subset_1(A_54, B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 17.13/8.17  tff(c_250, plain, (k4_xboole_0('#skF_2', '#skF_4')=k3_subset_1('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_229])).
% 17.13/8.17  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 17.13/8.17  tff(c_479, plain, (![A_68, B_69]: (m1_subset_1(k7_setfam_1(A_68, B_69), k1_zfmisc_1(k1_zfmisc_1(A_68))) | ~m1_subset_1(B_69, k1_zfmisc_1(k1_zfmisc_1(A_68))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 17.13/8.17  tff(c_32, plain, (![A_28, B_29]: (r1_tarski(A_28, B_29) | ~m1_subset_1(A_28, k1_zfmisc_1(B_29)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 17.13/8.17  tff(c_2439, plain, (![A_137, B_138]: (r1_tarski(k7_setfam_1(A_137, B_138), k1_zfmisc_1(A_137)) | ~m1_subset_1(B_138, k1_zfmisc_1(k1_zfmisc_1(A_137))))), inference(resolution, [status(thm)], [c_479, c_32])).
% 17.13/8.17  tff(c_2445, plain, (![A_137, B_138]: (k3_xboole_0(k7_setfam_1(A_137, B_138), k1_zfmisc_1(A_137))=k7_setfam_1(A_137, B_138) | ~m1_subset_1(B_138, k1_zfmisc_1(k1_zfmisc_1(A_137))))), inference(resolution, [status(thm)], [c_2439, c_6])).
% 17.13/8.17  tff(c_5748, plain, (![A_199, B_200]: (k3_xboole_0(k1_zfmisc_1(A_199), k7_setfam_1(A_199, B_200))=k7_setfam_1(A_199, B_200) | ~m1_subset_1(B_200, k1_zfmisc_1(k1_zfmisc_1(A_199))))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2445])).
% 17.13/8.17  tff(c_5780, plain, (k3_xboole_0(k1_zfmisc_1('#skF_2'), k7_setfam_1('#skF_2', '#skF_3'))=k7_setfam_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_5748])).
% 17.13/8.17  tff(c_191, plain, (![A_50, B_51]: (m1_subset_1(k3_xboole_0(A_50, B_51), k1_zfmisc_1(A_50)))), inference(superposition, [status(thm), theory('equality')], [c_179, c_49])).
% 17.13/8.17  tff(c_5859, plain, (m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_5780, c_191])).
% 17.13/8.17  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 17.13/8.17  tff(c_238, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_subset_1(A_11, k4_xboole_0(A_11, B_12)))), inference(resolution, [status(thm)], [c_49, c_229])).
% 17.13/8.17  tff(c_248, plain, (![A_11, B_12]: (k3_subset_1(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_238])).
% 17.13/8.17  tff(c_832, plain, (![D_85, A_86, B_87]: (r2_hidden(D_85, k7_setfam_1(A_86, B_87)) | ~r2_hidden(k3_subset_1(A_86, D_85), B_87) | ~m1_subset_1(D_85, k1_zfmisc_1(A_86)) | ~m1_subset_1(k7_setfam_1(A_86, B_87), k1_zfmisc_1(k1_zfmisc_1(A_86))) | ~m1_subset_1(B_87, k1_zfmisc_1(k1_zfmisc_1(A_86))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 17.13/8.17  tff(c_836, plain, (![A_11, B_12, B_87]: (r2_hidden(k4_xboole_0(A_11, B_12), k7_setfam_1(A_11, B_87)) | ~r2_hidden(k3_xboole_0(A_11, B_12), B_87) | ~m1_subset_1(k4_xboole_0(A_11, B_12), k1_zfmisc_1(A_11)) | ~m1_subset_1(k7_setfam_1(A_11, B_87), k1_zfmisc_1(k1_zfmisc_1(A_11))) | ~m1_subset_1(B_87, k1_zfmisc_1(k1_zfmisc_1(A_11))))), inference(superposition, [status(thm), theory('equality')], [c_248, c_832])).
% 17.13/8.17  tff(c_10462, plain, (![A_262, B_263, B_264]: (r2_hidden(k4_xboole_0(A_262, B_263), k7_setfam_1(A_262, B_264)) | ~r2_hidden(k3_xboole_0(A_262, B_263), B_264) | ~m1_subset_1(k7_setfam_1(A_262, B_264), k1_zfmisc_1(k1_zfmisc_1(A_262))) | ~m1_subset_1(B_264, k1_zfmisc_1(k1_zfmisc_1(A_262))))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_836])).
% 17.13/8.17  tff(c_10464, plain, (![B_263]: (r2_hidden(k4_xboole_0('#skF_2', B_263), k7_setfam_1('#skF_2', '#skF_3')) | ~r2_hidden(k3_xboole_0('#skF_2', B_263), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(resolution, [status(thm)], [c_5859, c_10462])).
% 17.13/8.17  tff(c_35250, plain, (![B_531]: (r2_hidden(k4_xboole_0('#skF_2', B_531), k7_setfam_1('#skF_2', '#skF_3')) | ~r2_hidden(k3_xboole_0('#skF_2', B_531), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_10464])).
% 17.13/8.17  tff(c_35340, plain, (r2_hidden(k3_subset_1('#skF_2', '#skF_4'), k7_setfam_1('#skF_2', '#skF_3')) | ~r2_hidden(k3_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_250, c_35250])).
% 17.13/8.17  tff(c_35375, plain, (r2_hidden(k3_subset_1('#skF_2', '#skF_4'), k7_setfam_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_3406, c_35340])).
% 17.13/8.17  tff(c_35377, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116, c_35375])).
% 17.13/8.17  tff(c_35378, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 17.13/8.17  tff(c_35668, plain, (![A_554, B_555]: (k4_xboole_0(A_554, B_555)=k3_subset_1(A_554, B_555) | ~m1_subset_1(B_555, k1_zfmisc_1(A_554)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 17.13/8.17  tff(c_35705, plain, (k4_xboole_0('#skF_2', '#skF_4')=k3_subset_1('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_35668])).
% 17.13/8.17  tff(c_35715, plain, (m1_subset_1(k3_subset_1('#skF_2', '#skF_4'), k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_35705, c_49])).
% 17.13/8.17  tff(c_35379, plain, (r2_hidden(k3_subset_1('#skF_2', '#skF_4'), k7_setfam_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_42])).
% 17.13/8.17  tff(c_35709, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_2', '#skF_4'))=k3_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_35705, c_8])).
% 17.13/8.17  tff(c_35718, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_115, c_2, c_35709])).
% 17.13/8.17  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=k3_subset_1(A_9, B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 17.13/8.17  tff(c_35756, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_2', '#skF_4'))=k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_35715, c_10])).
% 17.13/8.17  tff(c_35763, plain, (k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_35718, c_35756])).
% 17.13/8.17  tff(c_30, plain, (![A_26, B_27]: (m1_subset_1(k7_setfam_1(A_26, B_27), k1_zfmisc_1(k1_zfmisc_1(A_26))) | ~m1_subset_1(B_27, k1_zfmisc_1(k1_zfmisc_1(A_26))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 17.13/8.17  tff(c_36080, plain, (![A_568, D_569, B_570]: (r2_hidden(k3_subset_1(A_568, D_569), B_570) | ~r2_hidden(D_569, k7_setfam_1(A_568, B_570)) | ~m1_subset_1(D_569, k1_zfmisc_1(A_568)) | ~m1_subset_1(k7_setfam_1(A_568, B_570), k1_zfmisc_1(k1_zfmisc_1(A_568))) | ~m1_subset_1(B_570, k1_zfmisc_1(k1_zfmisc_1(A_568))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 17.13/8.17  tff(c_39411, plain, (![A_644, D_645, B_646]: (r2_hidden(k3_subset_1(A_644, D_645), B_646) | ~r2_hidden(D_645, k7_setfam_1(A_644, B_646)) | ~m1_subset_1(D_645, k1_zfmisc_1(A_644)) | ~m1_subset_1(B_646, k1_zfmisc_1(k1_zfmisc_1(A_644))))), inference(resolution, [status(thm)], [c_30, c_36080])).
% 17.13/8.17  tff(c_39444, plain, (![D_647]: (r2_hidden(k3_subset_1('#skF_2', D_647), '#skF_3') | ~r2_hidden(D_647, k7_setfam_1('#skF_2', '#skF_3')) | ~m1_subset_1(D_647, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_40, c_39411])).
% 17.13/8.17  tff(c_39469, plain, (r2_hidden('#skF_4', '#skF_3') | ~r2_hidden(k3_subset_1('#skF_2', '#skF_4'), k7_setfam_1('#skF_2', '#skF_3')) | ~m1_subset_1(k3_subset_1('#skF_2', '#skF_4'), k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_35763, c_39444])).
% 17.13/8.17  tff(c_39484, plain, (r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_35715, c_35379, c_39469])).
% 17.13/8.17  tff(c_39486, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35378, c_39484])).
% 17.13/8.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.13/8.17  
% 17.13/8.17  Inference rules
% 17.13/8.17  ----------------------
% 17.13/8.17  #Ref     : 0
% 17.13/8.17  #Sup     : 9727
% 17.13/8.17  #Fact    : 2
% 17.13/8.17  #Define  : 0
% 17.13/8.17  #Split   : 14
% 17.13/8.17  #Chain   : 0
% 17.13/8.17  #Close   : 0
% 17.13/8.17  
% 17.13/8.17  Ordering : KBO
% 17.13/8.17  
% 17.13/8.17  Simplification rules
% 17.13/8.17  ----------------------
% 17.13/8.17  #Subsume      : 762
% 17.13/8.17  #Demod        : 12372
% 17.13/8.17  #Tautology    : 4614
% 17.13/8.17  #SimpNegUnit  : 79
% 17.13/8.17  #BackRed      : 55
% 17.13/8.17  
% 17.13/8.17  #Partial instantiations: 0
% 17.13/8.17  #Strategies tried      : 1
% 17.13/8.17  
% 17.13/8.17  Timing (in seconds)
% 17.13/8.17  ----------------------
% 17.13/8.17  Preprocessing        : 0.32
% 17.13/8.17  Parsing              : 0.17
% 17.13/8.17  CNF conversion       : 0.02
% 17.13/8.17  Main loop            : 7.07
% 17.13/8.17  Inferencing          : 1.22
% 17.13/8.17  Reduction            : 3.87
% 17.13/8.17  Demodulation         : 3.40
% 17.13/8.17  BG Simplification    : 0.15
% 17.13/8.17  Subsumption          : 1.42
% 17.13/8.17  Abstraction          : 0.26
% 17.13/8.17  MUC search           : 0.00
% 17.13/8.17  Cooper               : 0.00
% 17.13/8.17  Total                : 7.43
% 17.13/8.17  Index Insertion      : 0.00
% 17.13/8.17  Index Deletion       : 0.00
% 17.13/8.17  Index Matching       : 0.00
% 17.13/8.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
