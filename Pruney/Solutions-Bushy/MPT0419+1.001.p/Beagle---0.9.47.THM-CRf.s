%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0419+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:16 EST 2020

% Result     : Theorem 4.45s
% Output     : CNFRefutation 4.60s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 170 expanded)
%              Number of leaves         :   20 (  67 expanded)
%              Depth                    :   18
%              Number of atoms          :  126 ( 376 expanded)
%              Number of equality atoms :    5 (  35 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k7_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(k7_setfam_1(A,B),k7_setfam_1(A,C))
             => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).

tff(c_28,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_47,plain,(
    ! [A_33,C_34,B_35] :
      ( m1_subset_1(A_33,C_34)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(C_34))
      | ~ r2_hidden(A_33,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_53,plain,(
    ! [A_33] :
      ( m1_subset_1(A_33,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_33,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_47])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k7_setfam_1(A_17,B_18),k1_zfmisc_1(k1_zfmisc_1(A_17)))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k1_zfmisc_1(A_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_70,plain,(
    ! [A_42,B_43] :
      ( k7_setfam_1(A_42,k7_setfam_1(A_42,B_43)) = B_43
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k1_zfmisc_1(A_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_75,plain,(
    k7_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_32,c_70])).

tff(c_81,plain,(
    ! [A_44,B_45] :
      ( m1_subset_1(k7_setfam_1(A_44,B_45),k1_zfmisc_1(k1_zfmisc_1(A_44)))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(k1_zfmisc_1(A_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [A_21,C_23,B_22] :
      ( m1_subset_1(A_21,C_23)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(C_23))
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_117,plain,(
    ! [A_53,A_54,B_55] :
      ( m1_subset_1(A_53,k1_zfmisc_1(A_54))
      | ~ r2_hidden(A_53,k7_setfam_1(A_54,B_55))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k1_zfmisc_1(A_54))) ) ),
    inference(resolution,[status(thm)],[c_81,c_26])).

tff(c_243,plain,(
    ! [A_92,B_93,B_94] :
      ( m1_subset_1('#skF_1'(k7_setfam_1(A_92,B_93),B_94),k1_zfmisc_1(A_92))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k1_zfmisc_1(A_92)))
      | r1_tarski(k7_setfam_1(A_92,B_93),B_94) ) ),
    inference(resolution,[status(thm)],[c_6,c_117])).

tff(c_257,plain,(
    ! [B_94] :
      ( m1_subset_1('#skF_1'('#skF_5',B_94),k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1(k7_setfam_1('#skF_3','#skF_5'),k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
      | r1_tarski(k7_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_5')),B_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_243])).

tff(c_262,plain,(
    ! [B_94] :
      ( m1_subset_1('#skF_1'('#skF_5',B_94),k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1(k7_setfam_1('#skF_3','#skF_5'),k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
      | r1_tarski('#skF_5',B_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_257])).

tff(c_382,plain,(
    ~ m1_subset_1(k7_setfam_1('#skF_3','#skF_5'),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_262])).

tff(c_385,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_22,c_382])).

tff(c_389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_385])).

tff(c_391,plain,(
    m1_subset_1(k7_setfam_1('#skF_3','#skF_5'),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_36,plain,(
    ! [A_27,B_28] :
      ( ~ r2_hidden('#skF_1'(A_27,B_28),B_28)
      | r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_41,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_36])).

tff(c_30,plain,(
    r1_tarski(k7_setfam_1('#skF_3','#skF_4'),k7_setfam_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_76,plain,(
    k7_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_70])).

tff(c_254,plain,(
    ! [B_94] :
      ( m1_subset_1('#skF_1'('#skF_4',B_94),k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1(k7_setfam_1('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
      | r1_tarski(k7_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')),B_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_243])).

tff(c_261,plain,(
    ! [B_94] :
      ( m1_subset_1('#skF_1'('#skF_4',B_94),k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1(k7_setfam_1('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
      | r1_tarski('#skF_4',B_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_254])).

tff(c_263,plain,(
    ~ m1_subset_1(k7_setfam_1('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_261])).

tff(c_298,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_22,c_263])).

tff(c_302,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_298])).

tff(c_304,plain,(
    m1_subset_1(k7_setfam_1('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_261])).

tff(c_220,plain,(
    ! [A_86,D_87,B_88] :
      ( r2_hidden(k3_subset_1(A_86,D_87),B_88)
      | ~ r2_hidden(D_87,k7_setfam_1(A_86,B_88))
      | ~ m1_subset_1(D_87,k1_zfmisc_1(A_86))
      | ~ m1_subset_1(k7_setfam_1(A_86,B_88),k1_zfmisc_1(k1_zfmisc_1(A_86)))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(k1_zfmisc_1(A_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_769,plain,(
    ! [A_135,D_136,B_137] :
      ( r2_hidden(k3_subset_1(A_135,D_136),B_137)
      | ~ r2_hidden(D_136,k7_setfam_1(A_135,B_137))
      | ~ m1_subset_1(D_136,k1_zfmisc_1(A_135))
      | ~ m1_subset_1(B_137,k1_zfmisc_1(k1_zfmisc_1(A_135))) ) ),
    inference(resolution,[status(thm)],[c_22,c_220])).

tff(c_773,plain,(
    ! [D_136] :
      ( r2_hidden(k3_subset_1('#skF_3',D_136),k7_setfam_1('#skF_3','#skF_4'))
      | ~ r2_hidden(D_136,k7_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')))
      | ~ m1_subset_1(D_136,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_304,c_769])).

tff(c_839,plain,(
    ! [D_143] :
      ( r2_hidden(k3_subset_1('#skF_3',D_143),k7_setfam_1('#skF_3','#skF_4'))
      | ~ r2_hidden(D_143,'#skF_4')
      | ~ m1_subset_1(D_143,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_773])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_960,plain,(
    ! [D_153,B_154] :
      ( r2_hidden(k3_subset_1('#skF_3',D_153),B_154)
      | ~ r1_tarski(k7_setfam_1('#skF_3','#skF_4'),B_154)
      | ~ r2_hidden(D_153,'#skF_4')
      | ~ m1_subset_1(D_153,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_839,c_2])).

tff(c_1876,plain,(
    ! [D_210,B_211,B_212] :
      ( r2_hidden(k3_subset_1('#skF_3',D_210),B_211)
      | ~ r1_tarski(B_212,B_211)
      | ~ r1_tarski(k7_setfam_1('#skF_3','#skF_4'),B_212)
      | ~ r2_hidden(D_210,'#skF_4')
      | ~ m1_subset_1(D_210,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_960,c_2])).

tff(c_1882,plain,(
    ! [D_210] :
      ( r2_hidden(k3_subset_1('#skF_3',D_210),k7_setfam_1('#skF_3','#skF_5'))
      | ~ r1_tarski(k7_setfam_1('#skF_3','#skF_4'),k7_setfam_1('#skF_3','#skF_4'))
      | ~ r2_hidden(D_210,'#skF_4')
      | ~ m1_subset_1(D_210,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_30,c_1876])).

tff(c_1888,plain,(
    ! [D_213] :
      ( r2_hidden(k3_subset_1('#skF_3',D_213),k7_setfam_1('#skF_3','#skF_5'))
      | ~ r2_hidden(D_213,'#skF_4')
      | ~ m1_subset_1(D_213,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_1882])).

tff(c_18,plain,(
    ! [D_16,A_6,B_7] :
      ( r2_hidden(D_16,k7_setfam_1(A_6,B_7))
      | ~ r2_hidden(k3_subset_1(A_6,D_16),B_7)
      | ~ m1_subset_1(D_16,k1_zfmisc_1(A_6))
      | ~ m1_subset_1(k7_setfam_1(A_6,B_7),k1_zfmisc_1(k1_zfmisc_1(A_6)))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(A_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1896,plain,(
    ! [D_213] :
      ( r2_hidden(D_213,k7_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_5')))
      | ~ m1_subset_1(k7_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_5')),k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
      | ~ m1_subset_1(k7_setfam_1('#skF_3','#skF_5'),k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
      | ~ r2_hidden(D_213,'#skF_4')
      | ~ m1_subset_1(D_213,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1888,c_18])).

tff(c_2018,plain,(
    ! [D_216] :
      ( r2_hidden(D_216,'#skF_5')
      | ~ r2_hidden(D_216,'#skF_4')
      | ~ m1_subset_1(D_216,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_32,c_75,c_75,c_1896])).

tff(c_2077,plain,(
    ! [A_217] :
      ( r2_hidden(A_217,'#skF_5')
      | ~ r2_hidden(A_217,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_53,c_2018])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2119,plain,(
    ! [A_218] :
      ( r1_tarski(A_218,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_218,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2077,c_4])).

tff(c_2131,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_2119])).

tff(c_2137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_28,c_2131])).

%------------------------------------------------------------------------------
