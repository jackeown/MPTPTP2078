%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:43 EST 2020

% Result     : Theorem 4.04s
% Output     : CNFRefutation 4.04s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 336 expanded)
%              Number of leaves         :   23 ( 118 expanded)
%              Depth                    :   11
%              Number of atoms          :  149 ( 669 expanded)
%              Number of equality atoms :   43 ( 192 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( B != k1_xboole_0
         => k5_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k6_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tops_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( r1_tarski(k7_setfam_1(A,B),C)
          <=> r1_tarski(B,k7_setfam_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_setfam_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( B != k1_xboole_0
       => k6_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k5_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tops_2)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_24,plain,(
    k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) != k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_156,plain,(
    ! [A_38,B_39] :
      ( m1_subset_1(k7_setfam_1(A_38,B_39),k1_zfmisc_1(k1_zfmisc_1(A_38)))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k1_zfmisc_1(A_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_172,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(k7_setfam_1(A_38,B_39),k1_zfmisc_1(A_38))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k1_zfmisc_1(A_38))) ) ),
    inference(resolution,[status(thm)],[c_156,c_14])).

tff(c_117,plain,(
    ! [A_35,B_36] :
      ( k7_setfam_1(A_35,k7_setfam_1(A_35,B_36)) = B_36
      | ~ m1_subset_1(B_36,k1_zfmisc_1(k1_zfmisc_1(A_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_128,plain,(
    k7_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_28,c_117])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_368,plain,(
    ! [A_51,B_52,C_53] :
      ( r1_tarski(k7_setfam_1(A_51,B_52),C_53)
      | ~ r1_tarski(B_52,k7_setfam_1(A_51,C_53))
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k1_zfmisc_1(A_51)))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k1_zfmisc_1(A_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_445,plain,(
    ! [B_58] :
      ( r1_tarski(k7_setfam_1('#skF_1',B_58),'#skF_2')
      | ~ r1_tarski(B_58,k7_setfam_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_28,c_368])).

tff(c_1691,plain,(
    ! [A_100] :
      ( r1_tarski(k7_setfam_1('#skF_1',A_100),'#skF_2')
      | ~ r1_tarski(A_100,k7_setfam_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_100,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_16,c_445])).

tff(c_1700,plain,
    ( r1_tarski('#skF_2','#skF_2')
    | ~ r1_tarski(k7_setfam_1('#skF_1','#skF_2'),k7_setfam_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k7_setfam_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_1691])).

tff(c_1965,plain,(
    ~ r1_tarski(k7_setfam_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1700])).

tff(c_1968,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_172,c_1965])).

tff(c_1972,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1968])).

tff(c_1974,plain,(
    r1_tarski(k7_setfam_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1700])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_227,plain,(
    ! [A_40,B_41] :
      ( k6_setfam_1(A_40,k7_setfam_1(A_40,B_41)) = k3_subset_1(A_40,k5_setfam_1(A_40,B_41))
      | k1_xboole_0 = B_41
      | ~ m1_subset_1(B_41,k1_zfmisc_1(k1_zfmisc_1(A_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2091,plain,(
    ! [A_115,A_116] :
      ( k6_setfam_1(A_115,k7_setfam_1(A_115,A_116)) = k3_subset_1(A_115,k5_setfam_1(A_115,A_116))
      | k1_xboole_0 = A_116
      | ~ r1_tarski(A_116,k1_zfmisc_1(A_115)) ) ),
    inference(resolution,[status(thm)],[c_16,c_227])).

tff(c_2093,plain,
    ( k6_setfam_1('#skF_1',k7_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k3_subset_1('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')))
    | k7_setfam_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1974,c_2091])).

tff(c_2111,plain,
    ( k3_subset_1('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k6_setfam_1('#skF_1','#skF_2')
    | k7_setfam_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_2093])).

tff(c_2532,plain,(
    k7_setfam_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2111])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(k7_setfam_1(A_7,B_8),k1_zfmisc_1(k1_zfmisc_1(A_7)))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(k1_zfmisc_1(A_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_281,plain,(
    ! [B_42,A_43,C_44] :
      ( r1_tarski(B_42,k7_setfam_1(A_43,C_44))
      | ~ r1_tarski(k7_setfam_1(A_43,B_42),C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k1_zfmisc_1(A_43)))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(k1_zfmisc_1(A_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_285,plain,(
    ! [C_44] :
      ( r1_tarski(k7_setfam_1('#skF_1','#skF_2'),k7_setfam_1('#skF_1',C_44))
      | ~ r1_tarski('#skF_2',C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k1_zfmisc_1('#skF_1')))
      | ~ m1_subset_1(k7_setfam_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_281])).

tff(c_1185,plain,(
    ~ m1_subset_1(k7_setfam_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_285])).

tff(c_1188,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_10,c_1185])).

tff(c_1195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1188])).

tff(c_1197,plain,(
    m1_subset_1(k7_setfam_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_285])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( k6_setfam_1(A_17,k7_setfam_1(A_17,B_18)) = k3_subset_1(A_17,k5_setfam_1(A_17,B_18))
      | k1_xboole_0 = B_18
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k1_zfmisc_1(A_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1208,plain,
    ( k6_setfam_1('#skF_1',k7_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k3_subset_1('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')))
    | k7_setfam_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1197,c_22])).

tff(c_1227,plain,
    ( k3_subset_1('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k6_setfam_1('#skF_1','#skF_2')
    | k7_setfam_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_1208])).

tff(c_1401,plain,(
    k7_setfam_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1227])).

tff(c_464,plain,
    ( r1_tarski(k7_setfam_1('#skF_1','#skF_2'),'#skF_2')
    | ~ r1_tarski('#skF_2',k7_setfam_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_445])).

tff(c_465,plain,(
    ~ r1_tarski('#skF_2',k7_setfam_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_464])).

tff(c_1411,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1401,c_465])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1414,plain,(
    k7_setfam_1('#skF_1',k1_xboole_0) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1401,c_128])).

tff(c_288,plain,(
    ! [A_45,A_46] :
      ( k7_setfam_1(A_45,k7_setfam_1(A_45,A_46)) = A_46
      | ~ r1_tarski(A_46,k1_zfmisc_1(A_45)) ) ),
    inference(resolution,[status(thm)],[c_16,c_117])).

tff(c_300,plain,(
    ! [A_45] : k7_setfam_1(A_45,k7_setfam_1(A_45,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_288])).

tff(c_995,plain,(
    ! [B_83] :
      ( r1_tarski(k7_setfam_1('#skF_1',k7_setfam_1('#skF_1',B_83)),'#skF_2')
      | ~ r1_tarski(k7_setfam_1('#skF_1',B_83),k7_setfam_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_10,c_445])).

tff(c_1009,plain,
    ( r1_tarski(k7_setfam_1('#skF_1',k1_xboole_0),'#skF_2')
    | ~ r1_tarski(k7_setfam_1('#skF_1',k7_setfam_1('#skF_1',k1_xboole_0)),k7_setfam_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k7_setfam_1('#skF_1',k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_995])).

tff(c_1024,plain,
    ( r1_tarski(k7_setfam_1('#skF_1',k1_xboole_0),'#skF_2')
    | ~ m1_subset_1(k7_setfam_1('#skF_1',k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_300,c_1009])).

tff(c_1029,plain,(
    ~ m1_subset_1(k7_setfam_1('#skF_1',k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1024])).

tff(c_1036,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_10,c_1029])).

tff(c_1040,plain,(
    ~ r1_tarski(k1_xboole_0,k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_16,c_1036])).

tff(c_1044,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1040])).

tff(c_1046,plain,(
    m1_subset_1(k7_setfam_1('#skF_1',k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1024])).

tff(c_302,plain,(
    ! [A_47] : k7_setfam_1(A_47,k7_setfam_1(A_47,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_288])).

tff(c_309,plain,(
    ! [A_47] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_47)))
      | ~ m1_subset_1(k7_setfam_1(A_47,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A_47))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_10])).

tff(c_1084,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1046,c_309])).

tff(c_1522,plain,(
    ! [A_89,B_90,A_91] :
      ( r1_tarski(k7_setfam_1(A_89,B_90),A_91)
      | ~ r1_tarski(B_90,k7_setfam_1(A_89,A_91))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(k1_zfmisc_1(A_89)))
      | ~ r1_tarski(A_91,k1_zfmisc_1(A_89)) ) ),
    inference(resolution,[status(thm)],[c_16,c_368])).

tff(c_1524,plain,(
    ! [A_91] :
      ( r1_tarski(k7_setfam_1('#skF_1',k1_xboole_0),A_91)
      | ~ r1_tarski(k1_xboole_0,k7_setfam_1('#skF_1',A_91))
      | ~ r1_tarski(A_91,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_1084,c_1522])).

tff(c_1548,plain,(
    ! [A_92] :
      ( r1_tarski('#skF_2',A_92)
      | ~ r1_tarski(A_92,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1414,c_1524])).

tff(c_1571,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_1548])).

tff(c_1581,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1411,c_1571])).

tff(c_1582,plain,(
    k3_subset_1('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k6_setfam_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1227])).

tff(c_91,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(k5_setfam_1(A_29,B_30),k1_zfmisc_1(A_29))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(k1_zfmisc_1(A_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k3_subset_1(A_3,k3_subset_1(A_3,B_4)) = B_4
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_97,plain,(
    ! [A_29,B_30] :
      ( k3_subset_1(A_29,k3_subset_1(A_29,k5_setfam_1(A_29,B_30))) = k5_setfam_1(A_29,B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(k1_zfmisc_1(A_29))) ) ),
    inference(resolution,[status(thm)],[c_91,c_6])).

tff(c_1218,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')))) = k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1197,c_97])).

tff(c_1584,plain,(
    k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1582,c_1218])).

tff(c_1586,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_1584])).

tff(c_1588,plain,(
    r1_tarski('#skF_2',k7_setfam_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_464])).

tff(c_2539,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2532,c_1588])).

tff(c_4,plain,(
    ! [A_2] :
      ( k1_xboole_0 = A_2
      | ~ r1_tarski(A_2,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2583,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2539,c_4])).

tff(c_2587,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_2583])).

tff(c_2588,plain,(
    k3_subset_1('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k6_setfam_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_2111])).

tff(c_1850,plain,(
    ! [A_107,B_108] :
      ( k3_subset_1(A_107,k3_subset_1(A_107,k5_setfam_1(A_107,B_108))) = k5_setfam_1(A_107,B_108)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(k1_zfmisc_1(A_107))) ) ),
    inference(resolution,[status(thm)],[c_91,c_6])).

tff(c_1867,plain,(
    ! [A_107,A_11] :
      ( k3_subset_1(A_107,k3_subset_1(A_107,k5_setfam_1(A_107,A_11))) = k5_setfam_1(A_107,A_11)
      | ~ r1_tarski(A_11,k1_zfmisc_1(A_107)) ) ),
    inference(resolution,[status(thm)],[c_16,c_1850])).

tff(c_2593,plain,
    ( k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k7_setfam_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2588,c_1867])).

tff(c_2600,plain,(
    k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1974,c_2593])).

tff(c_2602,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_2600])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:08:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.04/1.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.04/1.71  
% 4.04/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.04/1.72  %$ r1_tarski > m1_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.04/1.72  
% 4.04/1.72  %Foreground sorts:
% 4.04/1.72  
% 4.04/1.72  
% 4.04/1.72  %Background operators:
% 4.04/1.72  
% 4.04/1.72  
% 4.04/1.72  %Foreground operators:
% 4.04/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.04/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.04/1.72  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 4.04/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.04/1.72  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.04/1.72  tff('#skF_2', type, '#skF_2': $i).
% 4.04/1.72  tff('#skF_1', type, '#skF_1': $i).
% 4.04/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.04/1.72  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 4.04/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.04/1.72  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 4.04/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.04/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.04/1.72  
% 4.04/1.74  tff(f_75, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k5_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k6_setfam_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_tops_2)).
% 4.04/1.74  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 4.04/1.74  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.04/1.74  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 4.04/1.74  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(k7_setfam_1(A, B), C) <=> r1_tarski(B, k7_setfam_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_setfam_1)).
% 4.04/1.74  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k6_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k5_setfam_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tops_2)).
% 4.04/1.74  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.04/1.74  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 4.04/1.74  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.04/1.74  tff(f_31, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 4.04/1.74  tff(c_24, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))!=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.04/1.74  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.04/1.74  tff(c_156, plain, (![A_38, B_39]: (m1_subset_1(k7_setfam_1(A_38, B_39), k1_zfmisc_1(k1_zfmisc_1(A_38))) | ~m1_subset_1(B_39, k1_zfmisc_1(k1_zfmisc_1(A_38))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.04/1.74  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.04/1.74  tff(c_172, plain, (![A_38, B_39]: (r1_tarski(k7_setfam_1(A_38, B_39), k1_zfmisc_1(A_38)) | ~m1_subset_1(B_39, k1_zfmisc_1(k1_zfmisc_1(A_38))))), inference(resolution, [status(thm)], [c_156, c_14])).
% 4.04/1.74  tff(c_117, plain, (![A_35, B_36]: (k7_setfam_1(A_35, k7_setfam_1(A_35, B_36))=B_36 | ~m1_subset_1(B_36, k1_zfmisc_1(k1_zfmisc_1(A_35))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.04/1.74  tff(c_128, plain, (k7_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_28, c_117])).
% 4.04/1.74  tff(c_16, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.04/1.74  tff(c_368, plain, (![A_51, B_52, C_53]: (r1_tarski(k7_setfam_1(A_51, B_52), C_53) | ~r1_tarski(B_52, k7_setfam_1(A_51, C_53)) | ~m1_subset_1(C_53, k1_zfmisc_1(k1_zfmisc_1(A_51))) | ~m1_subset_1(B_52, k1_zfmisc_1(k1_zfmisc_1(A_51))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.04/1.74  tff(c_445, plain, (![B_58]: (r1_tarski(k7_setfam_1('#skF_1', B_58), '#skF_2') | ~r1_tarski(B_58, k7_setfam_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_58, k1_zfmisc_1(k1_zfmisc_1('#skF_1'))))), inference(resolution, [status(thm)], [c_28, c_368])).
% 4.04/1.74  tff(c_1691, plain, (![A_100]: (r1_tarski(k7_setfam_1('#skF_1', A_100), '#skF_2') | ~r1_tarski(A_100, k7_setfam_1('#skF_1', '#skF_2')) | ~r1_tarski(A_100, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_16, c_445])).
% 4.04/1.74  tff(c_1700, plain, (r1_tarski('#skF_2', '#skF_2') | ~r1_tarski(k7_setfam_1('#skF_1', '#skF_2'), k7_setfam_1('#skF_1', '#skF_2')) | ~r1_tarski(k7_setfam_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_128, c_1691])).
% 4.04/1.74  tff(c_1965, plain, (~r1_tarski(k7_setfam_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_1700])).
% 4.04/1.74  tff(c_1968, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_172, c_1965])).
% 4.04/1.74  tff(c_1972, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_1968])).
% 4.04/1.74  tff(c_1974, plain, (r1_tarski(k7_setfam_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_1700])).
% 4.04/1.74  tff(c_26, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.04/1.74  tff(c_227, plain, (![A_40, B_41]: (k6_setfam_1(A_40, k7_setfam_1(A_40, B_41))=k3_subset_1(A_40, k5_setfam_1(A_40, B_41)) | k1_xboole_0=B_41 | ~m1_subset_1(B_41, k1_zfmisc_1(k1_zfmisc_1(A_40))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.04/1.74  tff(c_2091, plain, (![A_115, A_116]: (k6_setfam_1(A_115, k7_setfam_1(A_115, A_116))=k3_subset_1(A_115, k5_setfam_1(A_115, A_116)) | k1_xboole_0=A_116 | ~r1_tarski(A_116, k1_zfmisc_1(A_115)))), inference(resolution, [status(thm)], [c_16, c_227])).
% 4.04/1.74  tff(c_2093, plain, (k6_setfam_1('#skF_1', k7_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k3_subset_1('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))) | k7_setfam_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_1974, c_2091])).
% 4.04/1.74  tff(c_2111, plain, (k3_subset_1('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k6_setfam_1('#skF_1', '#skF_2') | k7_setfam_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_128, c_2093])).
% 4.04/1.74  tff(c_2532, plain, (k7_setfam_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2111])).
% 4.04/1.74  tff(c_10, plain, (![A_7, B_8]: (m1_subset_1(k7_setfam_1(A_7, B_8), k1_zfmisc_1(k1_zfmisc_1(A_7))) | ~m1_subset_1(B_8, k1_zfmisc_1(k1_zfmisc_1(A_7))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.04/1.74  tff(c_281, plain, (![B_42, A_43, C_44]: (r1_tarski(B_42, k7_setfam_1(A_43, C_44)) | ~r1_tarski(k7_setfam_1(A_43, B_42), C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k1_zfmisc_1(A_43))) | ~m1_subset_1(B_42, k1_zfmisc_1(k1_zfmisc_1(A_43))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.04/1.74  tff(c_285, plain, (![C_44]: (r1_tarski(k7_setfam_1('#skF_1', '#skF_2'), k7_setfam_1('#skF_1', C_44)) | ~r1_tarski('#skF_2', C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) | ~m1_subset_1(k7_setfam_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_128, c_281])).
% 4.04/1.74  tff(c_1185, plain, (~m1_subset_1(k7_setfam_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(splitLeft, [status(thm)], [c_285])).
% 4.04/1.74  tff(c_1188, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_10, c_1185])).
% 4.04/1.74  tff(c_1195, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_1188])).
% 4.04/1.74  tff(c_1197, plain, (m1_subset_1(k7_setfam_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(splitRight, [status(thm)], [c_285])).
% 4.04/1.74  tff(c_22, plain, (![A_17, B_18]: (k6_setfam_1(A_17, k7_setfam_1(A_17, B_18))=k3_subset_1(A_17, k5_setfam_1(A_17, B_18)) | k1_xboole_0=B_18 | ~m1_subset_1(B_18, k1_zfmisc_1(k1_zfmisc_1(A_17))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.04/1.74  tff(c_1208, plain, (k6_setfam_1('#skF_1', k7_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k3_subset_1('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))) | k7_setfam_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_1197, c_22])).
% 4.04/1.74  tff(c_1227, plain, (k3_subset_1('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k6_setfam_1('#skF_1', '#skF_2') | k7_setfam_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_128, c_1208])).
% 4.04/1.74  tff(c_1401, plain, (k7_setfam_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1227])).
% 4.04/1.74  tff(c_464, plain, (r1_tarski(k7_setfam_1('#skF_1', '#skF_2'), '#skF_2') | ~r1_tarski('#skF_2', k7_setfam_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_445])).
% 4.04/1.74  tff(c_465, plain, (~r1_tarski('#skF_2', k7_setfam_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_464])).
% 4.04/1.74  tff(c_1411, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1401, c_465])).
% 4.04/1.74  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.04/1.74  tff(c_1414, plain, (k7_setfam_1('#skF_1', k1_xboole_0)='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1401, c_128])).
% 4.04/1.74  tff(c_288, plain, (![A_45, A_46]: (k7_setfam_1(A_45, k7_setfam_1(A_45, A_46))=A_46 | ~r1_tarski(A_46, k1_zfmisc_1(A_45)))), inference(resolution, [status(thm)], [c_16, c_117])).
% 4.04/1.74  tff(c_300, plain, (![A_45]: (k7_setfam_1(A_45, k7_setfam_1(A_45, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_288])).
% 4.04/1.74  tff(c_995, plain, (![B_83]: (r1_tarski(k7_setfam_1('#skF_1', k7_setfam_1('#skF_1', B_83)), '#skF_2') | ~r1_tarski(k7_setfam_1('#skF_1', B_83), k7_setfam_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_83, k1_zfmisc_1(k1_zfmisc_1('#skF_1'))))), inference(resolution, [status(thm)], [c_10, c_445])).
% 4.04/1.74  tff(c_1009, plain, (r1_tarski(k7_setfam_1('#skF_1', k1_xboole_0), '#skF_2') | ~r1_tarski(k7_setfam_1('#skF_1', k7_setfam_1('#skF_1', k1_xboole_0)), k7_setfam_1('#skF_1', '#skF_2')) | ~m1_subset_1(k7_setfam_1('#skF_1', k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_300, c_995])).
% 4.04/1.74  tff(c_1024, plain, (r1_tarski(k7_setfam_1('#skF_1', k1_xboole_0), '#skF_2') | ~m1_subset_1(k7_setfam_1('#skF_1', k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_300, c_1009])).
% 4.04/1.74  tff(c_1029, plain, (~m1_subset_1(k7_setfam_1('#skF_1', k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(splitLeft, [status(thm)], [c_1024])).
% 4.04/1.74  tff(c_1036, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_10, c_1029])).
% 4.04/1.74  tff(c_1040, plain, (~r1_tarski(k1_xboole_0, k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_16, c_1036])).
% 4.04/1.74  tff(c_1044, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_1040])).
% 4.04/1.74  tff(c_1046, plain, (m1_subset_1(k7_setfam_1('#skF_1', k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(splitRight, [status(thm)], [c_1024])).
% 4.04/1.74  tff(c_302, plain, (![A_47]: (k7_setfam_1(A_47, k7_setfam_1(A_47, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_288])).
% 4.04/1.74  tff(c_309, plain, (![A_47]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_47))) | ~m1_subset_1(k7_setfam_1(A_47, k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A_47))))), inference(superposition, [status(thm), theory('equality')], [c_302, c_10])).
% 4.04/1.74  tff(c_1084, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_1046, c_309])).
% 4.04/1.74  tff(c_1522, plain, (![A_89, B_90, A_91]: (r1_tarski(k7_setfam_1(A_89, B_90), A_91) | ~r1_tarski(B_90, k7_setfam_1(A_89, A_91)) | ~m1_subset_1(B_90, k1_zfmisc_1(k1_zfmisc_1(A_89))) | ~r1_tarski(A_91, k1_zfmisc_1(A_89)))), inference(resolution, [status(thm)], [c_16, c_368])).
% 4.04/1.74  tff(c_1524, plain, (![A_91]: (r1_tarski(k7_setfam_1('#skF_1', k1_xboole_0), A_91) | ~r1_tarski(k1_xboole_0, k7_setfam_1('#skF_1', A_91)) | ~r1_tarski(A_91, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_1084, c_1522])).
% 4.04/1.74  tff(c_1548, plain, (![A_92]: (r1_tarski('#skF_2', A_92) | ~r1_tarski(A_92, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1414, c_1524])).
% 4.04/1.74  tff(c_1571, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_1548])).
% 4.04/1.74  tff(c_1581, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1411, c_1571])).
% 4.04/1.74  tff(c_1582, plain, (k3_subset_1('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k6_setfam_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_1227])).
% 4.04/1.74  tff(c_91, plain, (![A_29, B_30]: (m1_subset_1(k5_setfam_1(A_29, B_30), k1_zfmisc_1(A_29)) | ~m1_subset_1(B_30, k1_zfmisc_1(k1_zfmisc_1(A_29))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.04/1.74  tff(c_6, plain, (![A_3, B_4]: (k3_subset_1(A_3, k3_subset_1(A_3, B_4))=B_4 | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.04/1.74  tff(c_97, plain, (![A_29, B_30]: (k3_subset_1(A_29, k3_subset_1(A_29, k5_setfam_1(A_29, B_30)))=k5_setfam_1(A_29, B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(k1_zfmisc_1(A_29))))), inference(resolution, [status(thm)], [c_91, c_6])).
% 4.04/1.74  tff(c_1218, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))))=k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_1197, c_97])).
% 4.04/1.74  tff(c_1584, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1582, c_1218])).
% 4.04/1.74  tff(c_1586, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_1584])).
% 4.04/1.74  tff(c_1588, plain, (r1_tarski('#skF_2', k7_setfam_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_464])).
% 4.04/1.74  tff(c_2539, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2532, c_1588])).
% 4.04/1.74  tff(c_4, plain, (![A_2]: (k1_xboole_0=A_2 | ~r1_tarski(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.04/1.74  tff(c_2583, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_2539, c_4])).
% 4.04/1.74  tff(c_2587, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_2583])).
% 4.04/1.74  tff(c_2588, plain, (k3_subset_1('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k6_setfam_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_2111])).
% 4.04/1.74  tff(c_1850, plain, (![A_107, B_108]: (k3_subset_1(A_107, k3_subset_1(A_107, k5_setfam_1(A_107, B_108)))=k5_setfam_1(A_107, B_108) | ~m1_subset_1(B_108, k1_zfmisc_1(k1_zfmisc_1(A_107))))), inference(resolution, [status(thm)], [c_91, c_6])).
% 4.04/1.74  tff(c_1867, plain, (![A_107, A_11]: (k3_subset_1(A_107, k3_subset_1(A_107, k5_setfam_1(A_107, A_11)))=k5_setfam_1(A_107, A_11) | ~r1_tarski(A_11, k1_zfmisc_1(A_107)))), inference(resolution, [status(thm)], [c_16, c_1850])).
% 4.04/1.74  tff(c_2593, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2')) | ~r1_tarski(k7_setfam_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2588, c_1867])).
% 4.04/1.74  tff(c_2600, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1974, c_2593])).
% 4.04/1.74  tff(c_2602, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_2600])).
% 4.04/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.04/1.74  
% 4.04/1.74  Inference rules
% 4.04/1.74  ----------------------
% 4.04/1.74  #Ref     : 0
% 4.04/1.74  #Sup     : 564
% 4.04/1.74  #Fact    : 0
% 4.04/1.74  #Define  : 0
% 4.04/1.74  #Split   : 19
% 4.04/1.74  #Chain   : 0
% 4.04/1.74  #Close   : 0
% 4.04/1.74  
% 4.04/1.74  Ordering : KBO
% 4.04/1.74  
% 4.04/1.74  Simplification rules
% 4.04/1.74  ----------------------
% 4.04/1.74  #Subsume      : 23
% 4.04/1.74  #Demod        : 431
% 4.04/1.74  #Tautology    : 343
% 4.04/1.74  #SimpNegUnit  : 11
% 4.04/1.74  #BackRed      : 56
% 4.04/1.74  
% 4.04/1.74  #Partial instantiations: 0
% 4.04/1.74  #Strategies tried      : 1
% 4.04/1.74  
% 4.04/1.74  Timing (in seconds)
% 4.04/1.75  ----------------------
% 4.04/1.75  Preprocessing        : 0.29
% 4.04/1.75  Parsing              : 0.16
% 4.04/1.75  CNF conversion       : 0.02
% 4.04/1.75  Main loop            : 0.66
% 4.04/1.75  Inferencing          : 0.22
% 4.04/1.75  Reduction            : 0.21
% 4.04/1.75  Demodulation         : 0.15
% 4.04/1.75  BG Simplification    : 0.03
% 4.04/1.75  Subsumption          : 0.14
% 4.04/1.75  Abstraction          : 0.03
% 4.04/1.75  MUC search           : 0.00
% 4.04/1.75  Cooper               : 0.00
% 4.04/1.75  Total                : 1.00
% 4.04/1.75  Index Insertion      : 0.00
% 4.04/1.75  Index Deletion       : 0.00
% 4.04/1.75  Index Matching       : 0.00
% 4.04/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
