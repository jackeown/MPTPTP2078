%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:40 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 164 expanded)
%              Number of leaves         :   27 (  64 expanded)
%              Depth                    :   15
%              Number of atoms          :  110 ( 314 expanded)
%              Number of equality atoms :   26 (  89 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( B != k1_xboole_0
         => k5_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k6_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tops_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( B != k1_xboole_0
       => k6_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k5_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tops_2)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r2_hidden(k3_subset_1(A,C),k7_setfam_1(A,B))
          <=> r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_setfam_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(c_34,plain,(
    k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) != k3_subset_1('#skF_2',k6_setfam_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_97,plain,(
    ! [A_46,C_47,B_48] :
      ( m1_subset_1(A_46,C_47)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(C_47))
      | ~ r2_hidden(A_46,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_100,plain,(
    ! [A_46] :
      ( m1_subset_1(A_46,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_46,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_97])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_101,plain,(
    ! [A_49,B_50] :
      ( k7_setfam_1(A_49,k7_setfam_1(A_49,B_50)) = B_50
      | ~ m1_subset_1(B_50,k1_zfmisc_1(k1_zfmisc_1(A_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_104,plain,(
    k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_101])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k7_setfam_1(A_13,B_14),k1_zfmisc_1(k1_zfmisc_1(A_13)))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(k1_zfmisc_1(A_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_187,plain,(
    ! [A_67,B_68] :
      ( m1_subset_1(k7_setfam_1(A_67,B_68),k1_zfmisc_1(k1_zfmisc_1(A_67)))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(k1_zfmisc_1(A_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_28,plain,(
    ! [A_21,C_23,B_22] :
      ( m1_subset_1(A_21,C_23)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(C_23))
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_210,plain,(
    ! [A_72,A_73,B_74] :
      ( m1_subset_1(A_72,k1_zfmisc_1(A_73))
      | ~ r2_hidden(A_72,k7_setfam_1(A_73,B_74))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(k1_zfmisc_1(A_73))) ) ),
    inference(resolution,[status(thm)],[c_187,c_28])).

tff(c_365,plain,(
    ! [A_104,B_105,B_106] :
      ( m1_subset_1('#skF_1'(k7_setfam_1(A_104,B_105),B_106),k1_zfmisc_1(A_104))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(k1_zfmisc_1(A_104)))
      | r1_tarski(k7_setfam_1(A_104,B_105),B_106) ) ),
    inference(resolution,[status(thm)],[c_6,c_210])).

tff(c_387,plain,(
    ! [B_106] :
      ( m1_subset_1('#skF_1'('#skF_3',B_106),k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | r1_tarski(k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')),B_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_365])).

tff(c_395,plain,(
    ! [B_106] :
      ( m1_subset_1('#skF_1'('#skF_3',B_106),k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | r1_tarski('#skF_3',B_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_387])).

tff(c_396,plain,(
    ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_395])).

tff(c_399,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_20,c_396])).

tff(c_403,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_399])).

tff(c_405,plain,(
    m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_395])).

tff(c_32,plain,(
    ! [A_26,B_27] :
      ( k6_setfam_1(A_26,k7_setfam_1(A_26,B_27)) = k3_subset_1(A_26,k5_setfam_1(A_26,B_27))
      | k1_xboole_0 = B_27
      | ~ m1_subset_1(B_27,k1_zfmisc_1(k1_zfmisc_1(A_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_407,plain,
    ( k6_setfam_1('#skF_2',k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3'))) = k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')))
    | k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_405,c_32])).

tff(c_419,plain,
    ( k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3'))) = k6_setfam_1('#skF_2','#skF_3')
    | k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_407])).

tff(c_626,plain,(
    k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_419])).

tff(c_535,plain,(
    ! [A_117,C_118,B_119] :
      ( r2_hidden(k3_subset_1(A_117,C_118),k7_setfam_1(A_117,B_119))
      | ~ r2_hidden(C_118,B_119)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(A_117))
      | ~ m1_subset_1(B_119,k1_zfmisc_1(k1_zfmisc_1(A_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    ! [B_25,A_24] :
      ( ~ r1_tarski(B_25,A_24)
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_725,plain,(
    ! [A_123,B_124,C_125] :
      ( ~ r1_tarski(k7_setfam_1(A_123,B_124),k3_subset_1(A_123,C_125))
      | ~ r2_hidden(C_125,B_124)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(A_123))
      | ~ m1_subset_1(B_124,k1_zfmisc_1(k1_zfmisc_1(A_123))) ) ),
    inference(resolution,[status(thm)],[c_535,c_30])).

tff(c_731,plain,(
    ! [C_125] :
      ( ~ r1_tarski(k1_xboole_0,k3_subset_1('#skF_2',C_125))
      | ~ r2_hidden(C_125,'#skF_3')
      | ~ m1_subset_1(C_125,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_626,c_725])).

tff(c_751,plain,(
    ! [C_126] :
      ( ~ r2_hidden(C_126,'#skF_3')
      | ~ m1_subset_1(C_126,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_14,c_731])).

tff(c_779,plain,(
    ! [A_127] : ~ r2_hidden(A_127,'#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_751])).

tff(c_795,plain,(
    ! [B_128] : r1_tarski('#skF_3',B_128) ),
    inference(resolution,[status(thm)],[c_6,c_779])).

tff(c_48,plain,(
    ! [B_34,A_35] :
      ( B_34 = A_35
      | ~ r1_tarski(B_34,A_35)
      | ~ r1_tarski(A_35,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_57,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_48])).

tff(c_815,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_795,c_57])).

tff(c_829,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_815])).

tff(c_830,plain,(
    k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3'))) = k6_setfam_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_419])).

tff(c_137,plain,(
    ! [A_55,B_56] :
      ( m1_subset_1(k5_setfam_1(A_55,B_56),k1_zfmisc_1(A_55))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k1_zfmisc_1(A_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( k3_subset_1(A_9,k3_subset_1(A_9,B_10)) = B_10
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_147,plain,(
    ! [A_55,B_56] :
      ( k3_subset_1(A_55,k3_subset_1(A_55,k5_setfam_1(A_55,B_56))) = k5_setfam_1(A_55,B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k1_zfmisc_1(A_55))) ) ),
    inference(resolution,[status(thm)],[c_137,c_16])).

tff(c_422,plain,(
    k3_subset_1('#skF_2',k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')))) = k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_405,c_147])).

tff(c_900,plain,(
    k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = k3_subset_1('#skF_2',k6_setfam_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_422])).

tff(c_901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_900])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:52:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.46/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.64  
% 3.46/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.64  %$ r2_hidden > r1_tarski > m1_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.46/1.64  
% 3.46/1.64  %Foreground sorts:
% 3.46/1.64  
% 3.46/1.64  
% 3.46/1.64  %Background operators:
% 3.46/1.64  
% 3.46/1.64  
% 3.46/1.64  %Foreground operators:
% 3.46/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.46/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.46/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.46/1.64  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 3.46/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.46/1.64  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.46/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.46/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.46/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.46/1.64  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 3.46/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.46/1.64  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 3.46/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.46/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.46/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.46/1.64  
% 3.46/1.66  tff(f_91, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k5_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k6_setfam_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_tops_2)).
% 3.46/1.66  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.46/1.66  tff(f_71, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.46/1.66  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.46/1.66  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 3.46/1.66  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 3.46/1.66  tff(f_83, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k6_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k5_setfam_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tops_2)).
% 3.46/1.66  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r2_hidden(k3_subset_1(A, C), k7_setfam_1(A, B)) <=> r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_setfam_1)).
% 3.46/1.66  tff(f_76, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.46/1.66  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.46/1.66  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 3.46/1.66  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.46/1.66  tff(c_34, plain, (k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))!=k3_subset_1('#skF_2', k6_setfam_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.46/1.66  tff(c_36, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.46/1.66  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.46/1.66  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.46/1.66  tff(c_97, plain, (![A_46, C_47, B_48]: (m1_subset_1(A_46, C_47) | ~m1_subset_1(B_48, k1_zfmisc_1(C_47)) | ~r2_hidden(A_46, B_48))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.46/1.66  tff(c_100, plain, (![A_46]: (m1_subset_1(A_46, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_46, '#skF_3'))), inference(resolution, [status(thm)], [c_38, c_97])).
% 3.46/1.66  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.46/1.66  tff(c_101, plain, (![A_49, B_50]: (k7_setfam_1(A_49, k7_setfam_1(A_49, B_50))=B_50 | ~m1_subset_1(B_50, k1_zfmisc_1(k1_zfmisc_1(A_49))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.46/1.66  tff(c_104, plain, (k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_38, c_101])).
% 3.46/1.66  tff(c_20, plain, (![A_13, B_14]: (m1_subset_1(k7_setfam_1(A_13, B_14), k1_zfmisc_1(k1_zfmisc_1(A_13))) | ~m1_subset_1(B_14, k1_zfmisc_1(k1_zfmisc_1(A_13))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.46/1.66  tff(c_187, plain, (![A_67, B_68]: (m1_subset_1(k7_setfam_1(A_67, B_68), k1_zfmisc_1(k1_zfmisc_1(A_67))) | ~m1_subset_1(B_68, k1_zfmisc_1(k1_zfmisc_1(A_67))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.46/1.66  tff(c_28, plain, (![A_21, C_23, B_22]: (m1_subset_1(A_21, C_23) | ~m1_subset_1(B_22, k1_zfmisc_1(C_23)) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.46/1.66  tff(c_210, plain, (![A_72, A_73, B_74]: (m1_subset_1(A_72, k1_zfmisc_1(A_73)) | ~r2_hidden(A_72, k7_setfam_1(A_73, B_74)) | ~m1_subset_1(B_74, k1_zfmisc_1(k1_zfmisc_1(A_73))))), inference(resolution, [status(thm)], [c_187, c_28])).
% 3.46/1.66  tff(c_365, plain, (![A_104, B_105, B_106]: (m1_subset_1('#skF_1'(k7_setfam_1(A_104, B_105), B_106), k1_zfmisc_1(A_104)) | ~m1_subset_1(B_105, k1_zfmisc_1(k1_zfmisc_1(A_104))) | r1_tarski(k7_setfam_1(A_104, B_105), B_106))), inference(resolution, [status(thm)], [c_6, c_210])).
% 3.46/1.66  tff(c_387, plain, (![B_106]: (m1_subset_1('#skF_1'('#skF_3', B_106), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | r1_tarski(k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3')), B_106))), inference(superposition, [status(thm), theory('equality')], [c_104, c_365])).
% 3.46/1.66  tff(c_395, plain, (![B_106]: (m1_subset_1('#skF_1'('#skF_3', B_106), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | r1_tarski('#skF_3', B_106))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_387])).
% 3.46/1.66  tff(c_396, plain, (~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_395])).
% 3.46/1.66  tff(c_399, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_20, c_396])).
% 3.46/1.66  tff(c_403, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_399])).
% 3.46/1.66  tff(c_405, plain, (m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(splitRight, [status(thm)], [c_395])).
% 3.46/1.66  tff(c_32, plain, (![A_26, B_27]: (k6_setfam_1(A_26, k7_setfam_1(A_26, B_27))=k3_subset_1(A_26, k5_setfam_1(A_26, B_27)) | k1_xboole_0=B_27 | ~m1_subset_1(B_27, k1_zfmisc_1(k1_zfmisc_1(A_26))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.46/1.66  tff(c_407, plain, (k6_setfam_1('#skF_2', k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3')))=k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))) | k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_405, c_32])).
% 3.46/1.66  tff(c_419, plain, (k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3')))=k6_setfam_1('#skF_2', '#skF_3') | k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_104, c_407])).
% 3.46/1.66  tff(c_626, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_419])).
% 3.46/1.66  tff(c_535, plain, (![A_117, C_118, B_119]: (r2_hidden(k3_subset_1(A_117, C_118), k7_setfam_1(A_117, B_119)) | ~r2_hidden(C_118, B_119) | ~m1_subset_1(C_118, k1_zfmisc_1(A_117)) | ~m1_subset_1(B_119, k1_zfmisc_1(k1_zfmisc_1(A_117))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.46/1.66  tff(c_30, plain, (![B_25, A_24]: (~r1_tarski(B_25, A_24) | ~r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.46/1.66  tff(c_725, plain, (![A_123, B_124, C_125]: (~r1_tarski(k7_setfam_1(A_123, B_124), k3_subset_1(A_123, C_125)) | ~r2_hidden(C_125, B_124) | ~m1_subset_1(C_125, k1_zfmisc_1(A_123)) | ~m1_subset_1(B_124, k1_zfmisc_1(k1_zfmisc_1(A_123))))), inference(resolution, [status(thm)], [c_535, c_30])).
% 3.46/1.66  tff(c_731, plain, (![C_125]: (~r1_tarski(k1_xboole_0, k3_subset_1('#skF_2', C_125)) | ~r2_hidden(C_125, '#skF_3') | ~m1_subset_1(C_125, k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_626, c_725])).
% 3.46/1.66  tff(c_751, plain, (![C_126]: (~r2_hidden(C_126, '#skF_3') | ~m1_subset_1(C_126, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_14, c_731])).
% 3.46/1.66  tff(c_779, plain, (![A_127]: (~r2_hidden(A_127, '#skF_3'))), inference(resolution, [status(thm)], [c_100, c_751])).
% 3.46/1.66  tff(c_795, plain, (![B_128]: (r1_tarski('#skF_3', B_128))), inference(resolution, [status(thm)], [c_6, c_779])).
% 3.46/1.66  tff(c_48, plain, (![B_34, A_35]: (B_34=A_35 | ~r1_tarski(B_34, A_35) | ~r1_tarski(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.46/1.66  tff(c_57, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_48])).
% 3.46/1.66  tff(c_815, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_795, c_57])).
% 3.46/1.66  tff(c_829, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_815])).
% 3.46/1.66  tff(c_830, plain, (k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3')))=k6_setfam_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_419])).
% 3.46/1.66  tff(c_137, plain, (![A_55, B_56]: (m1_subset_1(k5_setfam_1(A_55, B_56), k1_zfmisc_1(A_55)) | ~m1_subset_1(B_56, k1_zfmisc_1(k1_zfmisc_1(A_55))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.46/1.66  tff(c_16, plain, (![A_9, B_10]: (k3_subset_1(A_9, k3_subset_1(A_9, B_10))=B_10 | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.46/1.66  tff(c_147, plain, (![A_55, B_56]: (k3_subset_1(A_55, k3_subset_1(A_55, k5_setfam_1(A_55, B_56)))=k5_setfam_1(A_55, B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(k1_zfmisc_1(A_55))))), inference(resolution, [status(thm)], [c_137, c_16])).
% 3.46/1.66  tff(c_422, plain, (k3_subset_1('#skF_2', k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))))=k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_405, c_147])).
% 3.46/1.66  tff(c_900, plain, (k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))=k3_subset_1('#skF_2', k6_setfam_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_830, c_422])).
% 3.46/1.66  tff(c_901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_900])).
% 3.46/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.66  
% 3.46/1.66  Inference rules
% 3.46/1.66  ----------------------
% 3.46/1.66  #Ref     : 0
% 3.46/1.66  #Sup     : 211
% 3.46/1.66  #Fact    : 0
% 3.46/1.66  #Define  : 0
% 3.46/1.66  #Split   : 4
% 3.46/1.66  #Chain   : 0
% 3.46/1.66  #Close   : 0
% 3.46/1.66  
% 3.46/1.66  Ordering : KBO
% 3.46/1.66  
% 3.46/1.66  Simplification rules
% 3.46/1.66  ----------------------
% 3.46/1.66  #Subsume      : 24
% 3.46/1.66  #Demod        : 67
% 3.46/1.66  #Tautology    : 67
% 3.46/1.66  #SimpNegUnit  : 4
% 3.46/1.66  #BackRed      : 9
% 3.46/1.66  
% 3.46/1.66  #Partial instantiations: 0
% 3.46/1.66  #Strategies tried      : 1
% 3.46/1.66  
% 3.46/1.66  Timing (in seconds)
% 3.46/1.66  ----------------------
% 3.46/1.66  Preprocessing        : 0.33
% 3.46/1.66  Parsing              : 0.18
% 3.46/1.66  CNF conversion       : 0.02
% 3.46/1.66  Main loop            : 0.47
% 3.46/1.66  Inferencing          : 0.16
% 3.46/1.66  Reduction            : 0.14
% 3.46/1.66  Demodulation         : 0.10
% 3.46/1.66  BG Simplification    : 0.02
% 3.46/1.66  Subsumption          : 0.11
% 3.46/1.66  Abstraction          : 0.02
% 3.46/1.66  MUC search           : 0.00
% 3.46/1.66  Cooper               : 0.00
% 3.46/1.66  Total                : 0.84
% 3.46/1.67  Index Insertion      : 0.00
% 3.46/1.67  Index Deletion       : 0.00
% 3.46/1.67  Index Matching       : 0.00
% 3.46/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
