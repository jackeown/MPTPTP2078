%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:47 EST 2020

% Result     : Theorem 5.69s
% Output     : CNFRefutation 5.82s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 443 expanded)
%              Number of leaves         :   23 ( 158 expanded)
%              Depth                    :   14
%              Number of atoms          :  139 ( 959 expanded)
%              Number of equality atoms :   38 ( 352 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > m1_subset_1 > k7_setfam_1 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ~ ( B != k1_xboole_0
            & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_65,axiom,(
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

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_32,plain,(
    k7_setfam_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_120,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1(k7_setfam_1(A_47,B_48),k1_zfmisc_1(k1_zfmisc_1(A_47)))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(k1_zfmisc_1(A_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_127,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_120])).

tff(c_131,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_127])).

tff(c_268,plain,(
    ! [A_61,B_62,C_63] :
      ( m1_subset_1('#skF_2'(A_61,B_62,C_63),k1_zfmisc_1(A_61))
      | k7_setfam_1(A_61,B_62) = C_63
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k1_zfmisc_1(A_61)))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k1_zfmisc_1(A_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k3_subset_1(A_10,k3_subset_1(A_10,B_11)) = B_11
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_500,plain,(
    ! [A_92,B_93,C_94] :
      ( k3_subset_1(A_92,k3_subset_1(A_92,'#skF_2'(A_92,B_93,C_94))) = '#skF_2'(A_92,B_93,C_94)
      | k7_setfam_1(A_92,B_93) = C_94
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k1_zfmisc_1(A_92)))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k1_zfmisc_1(A_92))) ) ),
    inference(resolution,[status(thm)],[c_268,c_12])).

tff(c_521,plain,(
    ! [B_95] :
      ( k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_2'('#skF_3',B_95,k1_xboole_0))) = '#skF_2'('#skF_3',B_95,k1_xboole_0)
      | k7_setfam_1('#skF_3',B_95) = k1_xboole_0
      | ~ m1_subset_1(B_95,k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_131,c_500])).

tff(c_545,plain,
    ( k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_2'('#skF_3',k1_xboole_0,k1_xboole_0))) = '#skF_2'('#skF_3',k1_xboole_0,k1_xboole_0)
    | k7_setfam_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_131,c_521])).

tff(c_550,plain,(
    k7_setfam_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_545])).

tff(c_14,plain,(
    ! [A_12,B_13,C_19] :
      ( m1_subset_1('#skF_2'(A_12,B_13,C_19),k1_zfmisc_1(A_12))
      | k7_setfam_1(A_12,B_13) = C_19
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k1_zfmisc_1(A_12)))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k1_zfmisc_1(A_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k3_subset_1(A_8,B_9),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_697,plain,(
    ! [B_101] :
      ( k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_2'('#skF_3',B_101,'#skF_4'))) = '#skF_2'('#skF_3',B_101,'#skF_4')
      | k7_setfam_1('#skF_3',B_101) = '#skF_4'
      | ~ m1_subset_1(B_101,k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_36,c_500])).

tff(c_707,plain,
    ( k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_2'('#skF_3',k1_xboole_0,'#skF_4'))) = '#skF_2'('#skF_3',k1_xboole_0,'#skF_4')
    | k7_setfam_1('#skF_3',k1_xboole_0) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_131,c_697])).

tff(c_722,plain,
    ( k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_2'('#skF_3',k1_xboole_0,'#skF_4'))) = '#skF_2'('#skF_3',k1_xboole_0,'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_550,c_707])).

tff(c_723,plain,(
    k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_2'('#skF_3',k1_xboole_0,'#skF_4'))) = '#skF_2'('#skF_3',k1_xboole_0,'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_722])).

tff(c_807,plain,
    ( m1_subset_1('#skF_2'('#skF_3',k1_xboole_0,'#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1(k3_subset_1('#skF_3','#skF_2'('#skF_3',k1_xboole_0,'#skF_4')),k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_723,c_10])).

tff(c_858,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_3','#skF_2'('#skF_3',k1_xboole_0,'#skF_4')),k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_807])).

tff(c_872,plain,(
    ~ m1_subset_1('#skF_2'('#skF_3',k1_xboole_0,'#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_10,c_858])).

tff(c_876,plain,
    ( k7_setfam_1('#skF_3',k1_xboole_0) = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_14,c_872])).

tff(c_882,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_36,c_550,c_876])).

tff(c_884,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_882])).

tff(c_886,plain,(
    m1_subset_1(k3_subset_1('#skF_3','#skF_2'('#skF_3',k1_xboole_0,'#skF_4')),k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_807])).

tff(c_551,plain,(
    ! [A_96,B_97,C_98] :
      ( r2_hidden('#skF_2'(A_96,B_97,C_98),C_98)
      | r2_hidden(k3_subset_1(A_96,'#skF_2'(A_96,B_97,C_98)),B_97)
      | k7_setfam_1(A_96,B_97) = C_98
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k1_zfmisc_1(A_96)))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(k1_zfmisc_1(A_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_49,plain,(
    ! [A_30,B_31,C_32] :
      ( ~ r1_xboole_0(A_30,B_31)
      | ~ r2_hidden(C_32,k3_xboole_0(A_30,B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_52,plain,(
    ! [A_6,C_32] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_32,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_49])).

tff(c_54,plain,(
    ! [C_32] : ~ r2_hidden(C_32,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_52])).

tff(c_665,plain,(
    ! [A_99,C_100] :
      ( r2_hidden('#skF_2'(A_99,k1_xboole_0,C_100),C_100)
      | k7_setfam_1(A_99,k1_xboole_0) = C_100
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k1_zfmisc_1(A_99)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_99))) ) ),
    inference(resolution,[status(thm)],[c_551,c_54])).

tff(c_679,plain,
    ( r2_hidden('#skF_2'('#skF_3',k1_xboole_0,'#skF_4'),'#skF_4')
    | k7_setfam_1('#skF_3',k1_xboole_0) = '#skF_4'
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_36,c_665])).

tff(c_692,plain,
    ( r2_hidden('#skF_2'('#skF_3',k1_xboole_0,'#skF_4'),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_550,c_679])).

tff(c_693,plain,(
    r2_hidden('#skF_2'('#skF_3',k1_xboole_0,'#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_692])).

tff(c_69,plain,(
    ! [A_42,B_43] :
      ( k3_subset_1(A_42,k3_subset_1(A_42,B_43)) = B_43
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_76,plain,(
    ! [A_8,B_9] :
      ( k3_subset_1(A_8,k3_subset_1(A_8,k3_subset_1(A_8,B_9))) = k3_subset_1(A_8,B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(resolution,[status(thm)],[c_10,c_69])).

tff(c_276,plain,(
    ! [D_68,A_69,B_70] :
      ( r2_hidden(D_68,k7_setfam_1(A_69,B_70))
      | ~ r2_hidden(k3_subset_1(A_69,D_68),B_70)
      | ~ m1_subset_1(D_68,k1_zfmisc_1(A_69))
      | ~ m1_subset_1(k7_setfam_1(A_69,B_70),k1_zfmisc_1(k1_zfmisc_1(A_69)))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(k1_zfmisc_1(A_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2674,plain,(
    ! [A_197,B_198,B_199] :
      ( r2_hidden(k3_subset_1(A_197,k3_subset_1(A_197,B_198)),k7_setfam_1(A_197,B_199))
      | ~ r2_hidden(k3_subset_1(A_197,B_198),B_199)
      | ~ m1_subset_1(k3_subset_1(A_197,k3_subset_1(A_197,B_198)),k1_zfmisc_1(A_197))
      | ~ m1_subset_1(k7_setfam_1(A_197,B_199),k1_zfmisc_1(k1_zfmisc_1(A_197)))
      | ~ m1_subset_1(B_199,k1_zfmisc_1(k1_zfmisc_1(A_197)))
      | ~ m1_subset_1(B_198,k1_zfmisc_1(A_197)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_276])).

tff(c_2762,plain,(
    ! [B_198] :
      ( r2_hidden(k3_subset_1('#skF_3',k3_subset_1('#skF_3',B_198)),k1_xboole_0)
      | ~ r2_hidden(k3_subset_1('#skF_3',B_198),'#skF_4')
      | ~ m1_subset_1(k3_subset_1('#skF_3',k3_subset_1('#skF_3',B_198)),k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1(k7_setfam_1('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
      | ~ m1_subset_1(B_198,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2674])).

tff(c_2783,plain,(
    ! [B_198] :
      ( r2_hidden(k3_subset_1('#skF_3',k3_subset_1('#skF_3',B_198)),k1_xboole_0)
      | ~ r2_hidden(k3_subset_1('#skF_3',B_198),'#skF_4')
      | ~ m1_subset_1(k3_subset_1('#skF_3',k3_subset_1('#skF_3',B_198)),k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1(B_198,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_131,c_32,c_2762])).

tff(c_2785,plain,(
    ! [B_200] :
      ( ~ r2_hidden(k3_subset_1('#skF_3',B_200),'#skF_4')
      | ~ m1_subset_1(k3_subset_1('#skF_3',k3_subset_1('#skF_3',B_200)),k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1(B_200,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2783])).

tff(c_2828,plain,
    ( ~ r2_hidden(k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_2'('#skF_3',k1_xboole_0,'#skF_4'))),'#skF_4')
    | ~ m1_subset_1(k3_subset_1('#skF_3','#skF_2'('#skF_3',k1_xboole_0,'#skF_4')),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1(k3_subset_1('#skF_3','#skF_2'('#skF_3',k1_xboole_0,'#skF_4')),k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_723,c_2785])).

tff(c_2860,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_886,c_886,c_693,c_723,c_2828])).

tff(c_2862,plain,(
    k7_setfam_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_545])).

tff(c_3335,plain,(
    ! [A_221,B_222,C_223] :
      ( r2_hidden('#skF_2'(A_221,B_222,C_223),C_223)
      | r2_hidden(k3_subset_1(A_221,'#skF_2'(A_221,B_222,C_223)),B_222)
      | k7_setfam_1(A_221,B_222) = C_223
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k1_zfmisc_1(A_221)))
      | ~ m1_subset_1(B_222,k1_zfmisc_1(k1_zfmisc_1(A_221))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3751,plain,(
    ! [A_241,C_242] :
      ( r2_hidden('#skF_2'(A_241,k1_xboole_0,C_242),C_242)
      | k7_setfam_1(A_241,k1_xboole_0) = C_242
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k1_zfmisc_1(A_241)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_241))) ) ),
    inference(resolution,[status(thm)],[c_3335,c_54])).

tff(c_3758,plain,
    ( r2_hidden('#skF_2'('#skF_3',k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k7_setfam_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_131,c_3751])).

tff(c_3772,plain,
    ( r2_hidden('#skF_2'('#skF_3',k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k7_setfam_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_3758])).

tff(c_3774,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2862,c_54,c_3772])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:33:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.69/2.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.69/2.10  
% 5.69/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.69/2.10  %$ r2_hidden > r1_xboole_0 > m1_subset_1 > k7_setfam_1 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 5.69/2.10  
% 5.69/2.10  %Foreground sorts:
% 5.69/2.10  
% 5.69/2.10  
% 5.69/2.10  %Background operators:
% 5.69/2.10  
% 5.69/2.10  
% 5.69/2.10  %Foreground operators:
% 5.69/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.69/2.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.69/2.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.69/2.10  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 5.69/2.10  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.69/2.10  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.69/2.10  tff('#skF_3', type, '#skF_3': $i).
% 5.69/2.10  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.69/2.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.69/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.69/2.10  tff('#skF_4', type, '#skF_4': $i).
% 5.69/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.69/2.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.69/2.10  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.69/2.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.69/2.10  
% 5.82/2.12  tff(f_84, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_setfam_1)).
% 5.82/2.12  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 5.82/2.12  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_setfam_1)).
% 5.82/2.12  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 5.82/2.12  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 5.82/2.12  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.82/2.12  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 5.82/2.12  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.82/2.12  tff(c_34, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.82/2.12  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.82/2.12  tff(c_32, plain, (k7_setfam_1('#skF_3', '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.82/2.12  tff(c_120, plain, (![A_47, B_48]: (m1_subset_1(k7_setfam_1(A_47, B_48), k1_zfmisc_1(k1_zfmisc_1(A_47))) | ~m1_subset_1(B_48, k1_zfmisc_1(k1_zfmisc_1(A_47))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.82/2.12  tff(c_127, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_32, c_120])).
% 5.82/2.12  tff(c_131, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_127])).
% 5.82/2.12  tff(c_268, plain, (![A_61, B_62, C_63]: (m1_subset_1('#skF_2'(A_61, B_62, C_63), k1_zfmisc_1(A_61)) | k7_setfam_1(A_61, B_62)=C_63 | ~m1_subset_1(C_63, k1_zfmisc_1(k1_zfmisc_1(A_61))) | ~m1_subset_1(B_62, k1_zfmisc_1(k1_zfmisc_1(A_61))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.82/2.12  tff(c_12, plain, (![A_10, B_11]: (k3_subset_1(A_10, k3_subset_1(A_10, B_11))=B_11 | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.82/2.12  tff(c_500, plain, (![A_92, B_93, C_94]: (k3_subset_1(A_92, k3_subset_1(A_92, '#skF_2'(A_92, B_93, C_94)))='#skF_2'(A_92, B_93, C_94) | k7_setfam_1(A_92, B_93)=C_94 | ~m1_subset_1(C_94, k1_zfmisc_1(k1_zfmisc_1(A_92))) | ~m1_subset_1(B_93, k1_zfmisc_1(k1_zfmisc_1(A_92))))), inference(resolution, [status(thm)], [c_268, c_12])).
% 5.82/2.12  tff(c_521, plain, (![B_95]: (k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_2'('#skF_3', B_95, k1_xboole_0)))='#skF_2'('#skF_3', B_95, k1_xboole_0) | k7_setfam_1('#skF_3', B_95)=k1_xboole_0 | ~m1_subset_1(B_95, k1_zfmisc_1(k1_zfmisc_1('#skF_3'))))), inference(resolution, [status(thm)], [c_131, c_500])).
% 5.82/2.12  tff(c_545, plain, (k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_2'('#skF_3', k1_xboole_0, k1_xboole_0)))='#skF_2'('#skF_3', k1_xboole_0, k1_xboole_0) | k7_setfam_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_131, c_521])).
% 5.82/2.12  tff(c_550, plain, (k7_setfam_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(splitLeft, [status(thm)], [c_545])).
% 5.82/2.12  tff(c_14, plain, (![A_12, B_13, C_19]: (m1_subset_1('#skF_2'(A_12, B_13, C_19), k1_zfmisc_1(A_12)) | k7_setfam_1(A_12, B_13)=C_19 | ~m1_subset_1(C_19, k1_zfmisc_1(k1_zfmisc_1(A_12))) | ~m1_subset_1(B_13, k1_zfmisc_1(k1_zfmisc_1(A_12))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.82/2.12  tff(c_10, plain, (![A_8, B_9]: (m1_subset_1(k3_subset_1(A_8, B_9), k1_zfmisc_1(A_8)) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.82/2.12  tff(c_697, plain, (![B_101]: (k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_2'('#skF_3', B_101, '#skF_4')))='#skF_2'('#skF_3', B_101, '#skF_4') | k7_setfam_1('#skF_3', B_101)='#skF_4' | ~m1_subset_1(B_101, k1_zfmisc_1(k1_zfmisc_1('#skF_3'))))), inference(resolution, [status(thm)], [c_36, c_500])).
% 5.82/2.12  tff(c_707, plain, (k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_2'('#skF_3', k1_xboole_0, '#skF_4')))='#skF_2'('#skF_3', k1_xboole_0, '#skF_4') | k7_setfam_1('#skF_3', k1_xboole_0)='#skF_4'), inference(resolution, [status(thm)], [c_131, c_697])).
% 5.82/2.12  tff(c_722, plain, (k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_2'('#skF_3', k1_xboole_0, '#skF_4')))='#skF_2'('#skF_3', k1_xboole_0, '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_550, c_707])).
% 5.82/2.12  tff(c_723, plain, (k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_2'('#skF_3', k1_xboole_0, '#skF_4')))='#skF_2'('#skF_3', k1_xboole_0, '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_34, c_722])).
% 5.82/2.12  tff(c_807, plain, (m1_subset_1('#skF_2'('#skF_3', k1_xboole_0, '#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k3_subset_1('#skF_3', '#skF_2'('#skF_3', k1_xboole_0, '#skF_4')), k1_zfmisc_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_723, c_10])).
% 5.82/2.12  tff(c_858, plain, (~m1_subset_1(k3_subset_1('#skF_3', '#skF_2'('#skF_3', k1_xboole_0, '#skF_4')), k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_807])).
% 5.82/2.12  tff(c_872, plain, (~m1_subset_1('#skF_2'('#skF_3', k1_xboole_0, '#skF_4'), k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_10, c_858])).
% 5.82/2.12  tff(c_876, plain, (k7_setfam_1('#skF_3', k1_xboole_0)='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_14, c_872])).
% 5.82/2.12  tff(c_882, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_131, c_36, c_550, c_876])).
% 5.82/2.12  tff(c_884, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_882])).
% 5.82/2.12  tff(c_886, plain, (m1_subset_1(k3_subset_1('#skF_3', '#skF_2'('#skF_3', k1_xboole_0, '#skF_4')), k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_807])).
% 5.82/2.12  tff(c_551, plain, (![A_96, B_97, C_98]: (r2_hidden('#skF_2'(A_96, B_97, C_98), C_98) | r2_hidden(k3_subset_1(A_96, '#skF_2'(A_96, B_97, C_98)), B_97) | k7_setfam_1(A_96, B_97)=C_98 | ~m1_subset_1(C_98, k1_zfmisc_1(k1_zfmisc_1(A_96))) | ~m1_subset_1(B_97, k1_zfmisc_1(k1_zfmisc_1(A_96))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.82/2.12  tff(c_8, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.82/2.12  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.82/2.12  tff(c_49, plain, (![A_30, B_31, C_32]: (~r1_xboole_0(A_30, B_31) | ~r2_hidden(C_32, k3_xboole_0(A_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.82/2.12  tff(c_52, plain, (![A_6, C_32]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_32, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_49])).
% 5.82/2.12  tff(c_54, plain, (![C_32]: (~r2_hidden(C_32, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_52])).
% 5.82/2.12  tff(c_665, plain, (![A_99, C_100]: (r2_hidden('#skF_2'(A_99, k1_xboole_0, C_100), C_100) | k7_setfam_1(A_99, k1_xboole_0)=C_100 | ~m1_subset_1(C_100, k1_zfmisc_1(k1_zfmisc_1(A_99))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_99))))), inference(resolution, [status(thm)], [c_551, c_54])).
% 5.82/2.12  tff(c_679, plain, (r2_hidden('#skF_2'('#skF_3', k1_xboole_0, '#skF_4'), '#skF_4') | k7_setfam_1('#skF_3', k1_xboole_0)='#skF_4' | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_36, c_665])).
% 5.82/2.12  tff(c_692, plain, (r2_hidden('#skF_2'('#skF_3', k1_xboole_0, '#skF_4'), '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_131, c_550, c_679])).
% 5.82/2.12  tff(c_693, plain, (r2_hidden('#skF_2'('#skF_3', k1_xboole_0, '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_34, c_692])).
% 5.82/2.12  tff(c_69, plain, (![A_42, B_43]: (k3_subset_1(A_42, k3_subset_1(A_42, B_43))=B_43 | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.82/2.12  tff(c_76, plain, (![A_8, B_9]: (k3_subset_1(A_8, k3_subset_1(A_8, k3_subset_1(A_8, B_9)))=k3_subset_1(A_8, B_9) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(resolution, [status(thm)], [c_10, c_69])).
% 5.82/2.12  tff(c_276, plain, (![D_68, A_69, B_70]: (r2_hidden(D_68, k7_setfam_1(A_69, B_70)) | ~r2_hidden(k3_subset_1(A_69, D_68), B_70) | ~m1_subset_1(D_68, k1_zfmisc_1(A_69)) | ~m1_subset_1(k7_setfam_1(A_69, B_70), k1_zfmisc_1(k1_zfmisc_1(A_69))) | ~m1_subset_1(B_70, k1_zfmisc_1(k1_zfmisc_1(A_69))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.82/2.12  tff(c_2674, plain, (![A_197, B_198, B_199]: (r2_hidden(k3_subset_1(A_197, k3_subset_1(A_197, B_198)), k7_setfam_1(A_197, B_199)) | ~r2_hidden(k3_subset_1(A_197, B_198), B_199) | ~m1_subset_1(k3_subset_1(A_197, k3_subset_1(A_197, B_198)), k1_zfmisc_1(A_197)) | ~m1_subset_1(k7_setfam_1(A_197, B_199), k1_zfmisc_1(k1_zfmisc_1(A_197))) | ~m1_subset_1(B_199, k1_zfmisc_1(k1_zfmisc_1(A_197))) | ~m1_subset_1(B_198, k1_zfmisc_1(A_197)))), inference(superposition, [status(thm), theory('equality')], [c_76, c_276])).
% 5.82/2.12  tff(c_2762, plain, (![B_198]: (r2_hidden(k3_subset_1('#skF_3', k3_subset_1('#skF_3', B_198)), k1_xboole_0) | ~r2_hidden(k3_subset_1('#skF_3', B_198), '#skF_4') | ~m1_subset_1(k3_subset_1('#skF_3', k3_subset_1('#skF_3', B_198)), k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k7_setfam_1('#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) | ~m1_subset_1(B_198, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_32, c_2674])).
% 5.82/2.12  tff(c_2783, plain, (![B_198]: (r2_hidden(k3_subset_1('#skF_3', k3_subset_1('#skF_3', B_198)), k1_xboole_0) | ~r2_hidden(k3_subset_1('#skF_3', B_198), '#skF_4') | ~m1_subset_1(k3_subset_1('#skF_3', k3_subset_1('#skF_3', B_198)), k1_zfmisc_1('#skF_3')) | ~m1_subset_1(B_198, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_131, c_32, c_2762])).
% 5.82/2.12  tff(c_2785, plain, (![B_200]: (~r2_hidden(k3_subset_1('#skF_3', B_200), '#skF_4') | ~m1_subset_1(k3_subset_1('#skF_3', k3_subset_1('#skF_3', B_200)), k1_zfmisc_1('#skF_3')) | ~m1_subset_1(B_200, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_54, c_2783])).
% 5.82/2.12  tff(c_2828, plain, (~r2_hidden(k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_2'('#skF_3', k1_xboole_0, '#skF_4'))), '#skF_4') | ~m1_subset_1(k3_subset_1('#skF_3', '#skF_2'('#skF_3', k1_xboole_0, '#skF_4')), k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k3_subset_1('#skF_3', '#skF_2'('#skF_3', k1_xboole_0, '#skF_4')), k1_zfmisc_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_723, c_2785])).
% 5.82/2.12  tff(c_2860, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_886, c_886, c_693, c_723, c_2828])).
% 5.82/2.12  tff(c_2862, plain, (k7_setfam_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_545])).
% 5.82/2.12  tff(c_3335, plain, (![A_221, B_222, C_223]: (r2_hidden('#skF_2'(A_221, B_222, C_223), C_223) | r2_hidden(k3_subset_1(A_221, '#skF_2'(A_221, B_222, C_223)), B_222) | k7_setfam_1(A_221, B_222)=C_223 | ~m1_subset_1(C_223, k1_zfmisc_1(k1_zfmisc_1(A_221))) | ~m1_subset_1(B_222, k1_zfmisc_1(k1_zfmisc_1(A_221))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.82/2.12  tff(c_3751, plain, (![A_241, C_242]: (r2_hidden('#skF_2'(A_241, k1_xboole_0, C_242), C_242) | k7_setfam_1(A_241, k1_xboole_0)=C_242 | ~m1_subset_1(C_242, k1_zfmisc_1(k1_zfmisc_1(A_241))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_241))))), inference(resolution, [status(thm)], [c_3335, c_54])).
% 5.82/2.12  tff(c_3758, plain, (r2_hidden('#skF_2'('#skF_3', k1_xboole_0, k1_xboole_0), k1_xboole_0) | k7_setfam_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_131, c_3751])).
% 5.82/2.12  tff(c_3772, plain, (r2_hidden('#skF_2'('#skF_3', k1_xboole_0, k1_xboole_0), k1_xboole_0) | k7_setfam_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_131, c_3758])).
% 5.82/2.12  tff(c_3774, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2862, c_54, c_3772])).
% 5.82/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.82/2.12  
% 5.82/2.12  Inference rules
% 5.82/2.12  ----------------------
% 5.82/2.12  #Ref     : 0
% 5.82/2.12  #Sup     : 841
% 5.82/2.12  #Fact    : 2
% 5.82/2.12  #Define  : 0
% 5.82/2.12  #Split   : 20
% 5.82/2.12  #Chain   : 0
% 5.82/2.12  #Close   : 0
% 5.82/2.12  
% 5.82/2.12  Ordering : KBO
% 5.82/2.12  
% 5.82/2.12  Simplification rules
% 5.82/2.12  ----------------------
% 5.82/2.12  #Subsume      : 130
% 5.82/2.12  #Demod        : 503
% 5.82/2.12  #Tautology    : 232
% 5.82/2.12  #SimpNegUnit  : 72
% 5.82/2.12  #BackRed      : 14
% 5.82/2.12  
% 5.82/2.12  #Partial instantiations: 0
% 5.82/2.12  #Strategies tried      : 1
% 5.82/2.12  
% 5.82/2.12  Timing (in seconds)
% 5.82/2.12  ----------------------
% 5.82/2.12  Preprocessing        : 0.29
% 5.82/2.12  Parsing              : 0.15
% 5.82/2.12  CNF conversion       : 0.02
% 5.82/2.12  Main loop            : 1.04
% 5.82/2.12  Inferencing          : 0.35
% 5.82/2.12  Reduction            : 0.32
% 5.82/2.12  Demodulation         : 0.21
% 5.82/2.12  BG Simplification    : 0.04
% 5.82/2.12  Subsumption          : 0.26
% 5.82/2.12  Abstraction          : 0.06
% 5.82/2.12  MUC search           : 0.00
% 5.82/2.12  Cooper               : 0.00
% 5.82/2.12  Total                : 1.37
% 5.82/2.12  Index Insertion      : 0.00
% 5.82/2.12  Index Deletion       : 0.00
% 5.82/2.12  Index Matching       : 0.00
% 5.82/2.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
