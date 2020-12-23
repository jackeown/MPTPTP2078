%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:41 EST 2020

% Result     : Theorem 4.26s
% Output     : CNFRefutation 4.41s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 470 expanded)
%              Number of leaves         :   23 ( 165 expanded)
%              Depth                    :   15
%              Number of atoms          :  161 ( 908 expanded)
%              Number of equality atoms :   40 ( 210 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( B != k1_xboole_0
         => k5_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k6_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tops_2)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( r1_tarski(k7_setfam_1(A,B),C)
          <=> r1_tarski(B,k7_setfam_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_setfam_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( B != k1_xboole_0
       => k6_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k5_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tops_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_232,plain,(
    ! [A_42,B_43] :
      ( k7_setfam_1(A_42,k7_setfam_1(A_42,B_43)) = B_43
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k1_zfmisc_1(A_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_246,plain,(
    k7_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_232])).

tff(c_28,plain,(
    k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) != k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k7_setfam_1(A_8,B_9),k1_zfmisc_1(k1_zfmisc_1(A_8)))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(k1_zfmisc_1(A_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_587,plain,(
    ! [B_66,A_67,C_68] :
      ( r1_tarski(B_66,k7_setfam_1(A_67,C_68))
      | ~ r1_tarski(k7_setfam_1(A_67,B_66),C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k1_zfmisc_1(A_67)))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(k1_zfmisc_1(A_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_595,plain,(
    ! [C_68] :
      ( r1_tarski(k7_setfam_1('#skF_1','#skF_2'),k7_setfam_1('#skF_1',C_68))
      | ~ r1_tarski('#skF_2',C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k1_zfmisc_1('#skF_1')))
      | ~ m1_subset_1(k7_setfam_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_587])).

tff(c_1218,plain,(
    ~ m1_subset_1(k7_setfam_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_595])).

tff(c_1221,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_14,c_1218])).

tff(c_1228,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1221])).

tff(c_1230,plain,(
    m1_subset_1(k7_setfam_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_595])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1265,plain,(
    r1_tarski(k7_setfam_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1230,c_18])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_358,plain,(
    ! [A_50,B_51] :
      ( k6_setfam_1(A_50,k7_setfam_1(A_50,B_51)) = k3_subset_1(A_50,k5_setfam_1(A_50,B_51))
      | k1_xboole_0 = B_51
      | ~ m1_subset_1(B_51,k1_zfmisc_1(k1_zfmisc_1(A_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2093,plain,(
    ! [A_111,B_112] :
      ( k6_setfam_1(A_111,k7_setfam_1(A_111,k7_setfam_1(A_111,B_112))) = k3_subset_1(A_111,k5_setfam_1(A_111,k7_setfam_1(A_111,B_112)))
      | k7_setfam_1(A_111,B_112) = k1_xboole_0
      | ~ m1_subset_1(B_112,k1_zfmisc_1(k1_zfmisc_1(A_111))) ) ),
    inference(resolution,[status(thm)],[c_14,c_358])).

tff(c_2111,plain,
    ( k6_setfam_1('#skF_1',k7_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k3_subset_1('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')))
    | k7_setfam_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_2093])).

tff(c_2125,plain,
    ( k3_subset_1('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k6_setfam_1('#skF_1','#skF_2')
    | k7_setfam_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_2111])).

tff(c_2201,plain,(
    k7_setfam_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2125])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_295,plain,(
    ! [A_44,A_45] :
      ( k7_setfam_1(A_44,k7_setfam_1(A_44,A_45)) = A_45
      | ~ r1_tarski(A_45,k1_zfmisc_1(A_44)) ) ),
    inference(resolution,[status(thm)],[c_20,c_232])).

tff(c_311,plain,(
    ! [A_44] : k7_setfam_1(A_44,k7_setfam_1(A_44,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_295])).

tff(c_462,plain,(
    ! [A_56,B_57,C_58] :
      ( r1_tarski(k7_setfam_1(A_56,B_57),C_58)
      | ~ r1_tarski(B_57,k7_setfam_1(A_56,C_58))
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k1_zfmisc_1(A_56)))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k1_zfmisc_1(A_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_544,plain,(
    ! [B_62] :
      ( r1_tarski(k7_setfam_1('#skF_1',B_62),'#skF_2')
      | ~ r1_tarski(B_62,k7_setfam_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_32,c_462])).

tff(c_929,plain,(
    ! [B_82] :
      ( r1_tarski(k7_setfam_1('#skF_1',k7_setfam_1('#skF_1',B_82)),'#skF_2')
      | ~ r1_tarski(k7_setfam_1('#skF_1',B_82),k7_setfam_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_14,c_544])).

tff(c_945,plain,
    ( r1_tarski(k7_setfam_1('#skF_1',k1_xboole_0),'#skF_2')
    | ~ r1_tarski(k7_setfam_1('#skF_1',k7_setfam_1('#skF_1',k1_xboole_0)),k7_setfam_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k7_setfam_1('#skF_1',k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_929])).

tff(c_963,plain,
    ( r1_tarski(k7_setfam_1('#skF_1',k1_xboole_0),'#skF_2')
    | ~ m1_subset_1(k7_setfam_1('#skF_1',k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_311,c_945])).

tff(c_968,plain,(
    ~ m1_subset_1(k7_setfam_1('#skF_1',k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_963])).

tff(c_975,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_14,c_968])).

tff(c_979,plain,(
    ~ r1_tarski(k1_xboole_0,k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_20,c_975])).

tff(c_983,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_979])).

tff(c_985,plain,(
    m1_subset_1(k7_setfam_1('#skF_1',k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_963])).

tff(c_335,plain,(
    ! [A_48] : k7_setfam_1(A_48,k7_setfam_1(A_48,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_295])).

tff(c_340,plain,(
    ! [A_48] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_48)))
      | ~ m1_subset_1(k7_setfam_1(A_48,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A_48))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_14])).

tff(c_1022,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_985,c_340])).

tff(c_1827,plain,(
    ! [A_105,B_106,A_107] :
      ( r1_tarski(k7_setfam_1(A_105,B_106),A_107)
      | ~ r1_tarski(B_106,k7_setfam_1(A_105,A_107))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(k1_zfmisc_1(A_105)))
      | ~ r1_tarski(A_107,k1_zfmisc_1(A_105)) ) ),
    inference(resolution,[status(thm)],[c_20,c_462])).

tff(c_1833,plain,(
    ! [A_107] :
      ( r1_tarski(k7_setfam_1('#skF_1',k1_xboole_0),A_107)
      | ~ r1_tarski(k1_xboole_0,k7_setfam_1('#skF_1',A_107))
      | ~ r1_tarski(A_107,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_1022,c_1827])).

tff(c_1863,plain,(
    ! [A_108] :
      ( r1_tarski(k7_setfam_1('#skF_1',k1_xboole_0),A_108)
      | ~ r1_tarski(A_108,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1833])).

tff(c_1900,plain,(
    r1_tarski(k7_setfam_1('#skF_1',k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_1863])).

tff(c_46,plain,(
    ! [B_26,A_27] :
      ( B_26 = A_27
      | ~ r1_tarski(B_26,A_27)
      | ~ r1_tarski(A_27,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_46])).

tff(c_1911,plain,(
    k7_setfam_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1900,c_58])).

tff(c_1031,plain,(
    r1_tarski(k7_setfam_1('#skF_1',k1_xboole_0),k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_985,c_18])).

tff(c_653,plain,(
    ! [A_70] :
      ( r1_tarski(k7_setfam_1('#skF_1',A_70),'#skF_2')
      | ~ r1_tarski(A_70,k7_setfam_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_70,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_20,c_544])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1490,plain,(
    ! [A_93] :
      ( k7_setfam_1('#skF_1',A_93) = '#skF_2'
      | ~ r1_tarski('#skF_2',k7_setfam_1('#skF_1',A_93))
      | ~ r1_tarski(A_93,k7_setfam_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_93,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_653,c_2])).

tff(c_1498,plain,
    ( k7_setfam_1('#skF_1',k7_setfam_1('#skF_1',k1_xboole_0)) = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_xboole_0)
    | ~ r1_tarski(k7_setfam_1('#skF_1',k1_xboole_0),k7_setfam_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k7_setfam_1('#skF_1',k1_xboole_0),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_1490])).

tff(c_1507,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_xboole_0)
    | ~ r1_tarski(k7_setfam_1('#skF_1',k1_xboole_0),k7_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1031,c_311,c_1498])).

tff(c_1508,plain,
    ( ~ r1_tarski('#skF_2',k1_xboole_0)
    | ~ r1_tarski(k7_setfam_1('#skF_1',k1_xboole_0),k7_setfam_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1507])).

tff(c_1511,plain,(
    ~ r1_tarski(k7_setfam_1('#skF_1',k1_xboole_0),k7_setfam_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1508])).

tff(c_1520,plain,(
    ! [A_94,B_95,A_96] :
      ( r1_tarski(k7_setfam_1(A_94,B_95),A_96)
      | ~ r1_tarski(B_95,k7_setfam_1(A_94,A_96))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(k1_zfmisc_1(A_94)))
      | ~ r1_tarski(A_96,k1_zfmisc_1(A_94)) ) ),
    inference(resolution,[status(thm)],[c_20,c_462])).

tff(c_1526,plain,(
    ! [A_96] :
      ( r1_tarski(k7_setfam_1('#skF_1',k1_xboole_0),A_96)
      | ~ r1_tarski(k1_xboole_0,k7_setfam_1('#skF_1',A_96))
      | ~ r1_tarski(A_96,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_1022,c_1520])).

tff(c_1556,plain,(
    ! [A_97] :
      ( r1_tarski(k7_setfam_1('#skF_1',k1_xboole_0),A_97)
      | ~ r1_tarski(A_97,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1526])).

tff(c_1558,plain,(
    r1_tarski(k7_setfam_1('#skF_1',k1_xboole_0),k7_setfam_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1265,c_1556])).

tff(c_1584,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1511,c_1558])).

tff(c_1586,plain,(
    r1_tarski(k7_setfam_1('#skF_1',k1_xboole_0),k7_setfam_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1508])).

tff(c_1594,plain,
    ( k7_setfam_1('#skF_1',k1_xboole_0) = k7_setfam_1('#skF_1','#skF_2')
    | ~ r1_tarski(k7_setfam_1('#skF_1','#skF_2'),k7_setfam_1('#skF_1',k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_1586,c_2])).

tff(c_1704,plain,(
    ~ r1_tarski(k7_setfam_1('#skF_1','#skF_2'),k7_setfam_1('#skF_1',k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_1594])).

tff(c_1918,plain,(
    ~ r1_tarski(k7_setfam_1('#skF_1','#skF_2'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1911,c_1704])).

tff(c_2202,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2201,c_1918])).

tff(c_2222,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2202])).

tff(c_2223,plain,(
    k3_subset_1('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k6_setfam_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_2125])).

tff(c_117,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(k5_setfam_1(A_33,B_34),k1_zfmisc_1(A_33))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(k1_zfmisc_1(A_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( k3_subset_1(A_4,k3_subset_1(A_4,B_5)) = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_810,plain,(
    ! [A_77,B_78] :
      ( k3_subset_1(A_77,k3_subset_1(A_77,k5_setfam_1(A_77,B_78))) = k5_setfam_1(A_77,B_78)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(k1_zfmisc_1(A_77))) ) ),
    inference(resolution,[status(thm)],[c_117,c_10])).

tff(c_827,plain,(
    ! [A_77,A_12] :
      ( k3_subset_1(A_77,k3_subset_1(A_77,k5_setfam_1(A_77,A_12))) = k5_setfam_1(A_77,A_12)
      | ~ r1_tarski(A_12,k1_zfmisc_1(A_77)) ) ),
    inference(resolution,[status(thm)],[c_20,c_810])).

tff(c_2228,plain,
    ( k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k7_setfam_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2223,c_827])).

tff(c_2235,plain,(
    k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1265,c_2228])).

tff(c_2237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_2235])).

tff(c_2238,plain,(
    k7_setfam_1('#skF_1',k1_xboole_0) = k7_setfam_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1594])).

tff(c_2293,plain,(
    k7_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2238,c_311])).

tff(c_2325,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_2293])).

tff(c_2327,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_2325])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:24:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.26/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.26/1.80  
% 4.26/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.26/1.80  %$ r1_tarski > m1_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.26/1.80  
% 4.26/1.80  %Foreground sorts:
% 4.26/1.80  
% 4.26/1.80  
% 4.26/1.80  %Background operators:
% 4.26/1.80  
% 4.26/1.80  
% 4.26/1.80  %Foreground operators:
% 4.26/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.26/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.26/1.80  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 4.26/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.26/1.80  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.26/1.80  tff('#skF_2', type, '#skF_2': $i).
% 4.26/1.80  tff('#skF_1', type, '#skF_1': $i).
% 4.26/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.26/1.80  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 4.26/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.26/1.80  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 4.26/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.26/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.26/1.80  
% 4.41/1.83  tff(f_77, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k5_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k6_setfam_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_tops_2)).
% 4.41/1.83  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 4.41/1.83  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 4.41/1.83  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(k7_setfam_1(A, B), C) <=> r1_tarski(B, k7_setfam_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_setfam_1)).
% 4.41/1.83  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.41/1.83  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.41/1.83  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k6_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k5_setfam_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tops_2)).
% 4.41/1.83  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.41/1.83  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 4.41/1.83  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.41/1.83  tff(c_30, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.41/1.83  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.41/1.83  tff(c_232, plain, (![A_42, B_43]: (k7_setfam_1(A_42, k7_setfam_1(A_42, B_43))=B_43 | ~m1_subset_1(B_43, k1_zfmisc_1(k1_zfmisc_1(A_42))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.41/1.83  tff(c_246, plain, (k7_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_32, c_232])).
% 4.41/1.83  tff(c_28, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))!=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.41/1.83  tff(c_14, plain, (![A_8, B_9]: (m1_subset_1(k7_setfam_1(A_8, B_9), k1_zfmisc_1(k1_zfmisc_1(A_8))) | ~m1_subset_1(B_9, k1_zfmisc_1(k1_zfmisc_1(A_8))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.41/1.83  tff(c_587, plain, (![B_66, A_67, C_68]: (r1_tarski(B_66, k7_setfam_1(A_67, C_68)) | ~r1_tarski(k7_setfam_1(A_67, B_66), C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k1_zfmisc_1(A_67))) | ~m1_subset_1(B_66, k1_zfmisc_1(k1_zfmisc_1(A_67))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.41/1.83  tff(c_595, plain, (![C_68]: (r1_tarski(k7_setfam_1('#skF_1', '#skF_2'), k7_setfam_1('#skF_1', C_68)) | ~r1_tarski('#skF_2', C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) | ~m1_subset_1(k7_setfam_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_246, c_587])).
% 4.41/1.83  tff(c_1218, plain, (~m1_subset_1(k7_setfam_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(splitLeft, [status(thm)], [c_595])).
% 4.41/1.83  tff(c_1221, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_1218])).
% 4.41/1.83  tff(c_1228, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_1221])).
% 4.41/1.83  tff(c_1230, plain, (m1_subset_1(k7_setfam_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(splitRight, [status(thm)], [c_595])).
% 4.41/1.83  tff(c_18, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.41/1.83  tff(c_1265, plain, (r1_tarski(k7_setfam_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_1230, c_18])).
% 4.41/1.83  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.41/1.83  tff(c_358, plain, (![A_50, B_51]: (k6_setfam_1(A_50, k7_setfam_1(A_50, B_51))=k3_subset_1(A_50, k5_setfam_1(A_50, B_51)) | k1_xboole_0=B_51 | ~m1_subset_1(B_51, k1_zfmisc_1(k1_zfmisc_1(A_50))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.41/1.83  tff(c_2093, plain, (![A_111, B_112]: (k6_setfam_1(A_111, k7_setfam_1(A_111, k7_setfam_1(A_111, B_112)))=k3_subset_1(A_111, k5_setfam_1(A_111, k7_setfam_1(A_111, B_112))) | k7_setfam_1(A_111, B_112)=k1_xboole_0 | ~m1_subset_1(B_112, k1_zfmisc_1(k1_zfmisc_1(A_111))))), inference(resolution, [status(thm)], [c_14, c_358])).
% 4.41/1.83  tff(c_2111, plain, (k6_setfam_1('#skF_1', k7_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k3_subset_1('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))) | k7_setfam_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_2093])).
% 4.41/1.83  tff(c_2125, plain, (k3_subset_1('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k6_setfam_1('#skF_1', '#skF_2') | k7_setfam_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_246, c_2111])).
% 4.41/1.83  tff(c_2201, plain, (k7_setfam_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2125])).
% 4.41/1.83  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.41/1.83  tff(c_20, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.41/1.83  tff(c_295, plain, (![A_44, A_45]: (k7_setfam_1(A_44, k7_setfam_1(A_44, A_45))=A_45 | ~r1_tarski(A_45, k1_zfmisc_1(A_44)))), inference(resolution, [status(thm)], [c_20, c_232])).
% 4.41/1.83  tff(c_311, plain, (![A_44]: (k7_setfam_1(A_44, k7_setfam_1(A_44, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_295])).
% 4.41/1.83  tff(c_462, plain, (![A_56, B_57, C_58]: (r1_tarski(k7_setfam_1(A_56, B_57), C_58) | ~r1_tarski(B_57, k7_setfam_1(A_56, C_58)) | ~m1_subset_1(C_58, k1_zfmisc_1(k1_zfmisc_1(A_56))) | ~m1_subset_1(B_57, k1_zfmisc_1(k1_zfmisc_1(A_56))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.41/1.83  tff(c_544, plain, (![B_62]: (r1_tarski(k7_setfam_1('#skF_1', B_62), '#skF_2') | ~r1_tarski(B_62, k7_setfam_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_62, k1_zfmisc_1(k1_zfmisc_1('#skF_1'))))), inference(resolution, [status(thm)], [c_32, c_462])).
% 4.41/1.83  tff(c_929, plain, (![B_82]: (r1_tarski(k7_setfam_1('#skF_1', k7_setfam_1('#skF_1', B_82)), '#skF_2') | ~r1_tarski(k7_setfam_1('#skF_1', B_82), k7_setfam_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_82, k1_zfmisc_1(k1_zfmisc_1('#skF_1'))))), inference(resolution, [status(thm)], [c_14, c_544])).
% 4.41/1.83  tff(c_945, plain, (r1_tarski(k7_setfam_1('#skF_1', k1_xboole_0), '#skF_2') | ~r1_tarski(k7_setfam_1('#skF_1', k7_setfam_1('#skF_1', k1_xboole_0)), k7_setfam_1('#skF_1', '#skF_2')) | ~m1_subset_1(k7_setfam_1('#skF_1', k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_311, c_929])).
% 4.41/1.83  tff(c_963, plain, (r1_tarski(k7_setfam_1('#skF_1', k1_xboole_0), '#skF_2') | ~m1_subset_1(k7_setfam_1('#skF_1', k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_311, c_945])).
% 4.41/1.83  tff(c_968, plain, (~m1_subset_1(k7_setfam_1('#skF_1', k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(splitLeft, [status(thm)], [c_963])).
% 4.41/1.83  tff(c_975, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_968])).
% 4.41/1.83  tff(c_979, plain, (~r1_tarski(k1_xboole_0, k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_975])).
% 4.41/1.83  tff(c_983, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_979])).
% 4.41/1.83  tff(c_985, plain, (m1_subset_1(k7_setfam_1('#skF_1', k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(splitRight, [status(thm)], [c_963])).
% 4.41/1.83  tff(c_335, plain, (![A_48]: (k7_setfam_1(A_48, k7_setfam_1(A_48, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_295])).
% 4.41/1.83  tff(c_340, plain, (![A_48]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_48))) | ~m1_subset_1(k7_setfam_1(A_48, k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A_48))))), inference(superposition, [status(thm), theory('equality')], [c_335, c_14])).
% 4.41/1.83  tff(c_1022, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_985, c_340])).
% 4.41/1.83  tff(c_1827, plain, (![A_105, B_106, A_107]: (r1_tarski(k7_setfam_1(A_105, B_106), A_107) | ~r1_tarski(B_106, k7_setfam_1(A_105, A_107)) | ~m1_subset_1(B_106, k1_zfmisc_1(k1_zfmisc_1(A_105))) | ~r1_tarski(A_107, k1_zfmisc_1(A_105)))), inference(resolution, [status(thm)], [c_20, c_462])).
% 4.41/1.83  tff(c_1833, plain, (![A_107]: (r1_tarski(k7_setfam_1('#skF_1', k1_xboole_0), A_107) | ~r1_tarski(k1_xboole_0, k7_setfam_1('#skF_1', A_107)) | ~r1_tarski(A_107, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_1022, c_1827])).
% 4.41/1.83  tff(c_1863, plain, (![A_108]: (r1_tarski(k7_setfam_1('#skF_1', k1_xboole_0), A_108) | ~r1_tarski(A_108, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1833])).
% 4.41/1.83  tff(c_1900, plain, (r1_tarski(k7_setfam_1('#skF_1', k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_1863])).
% 4.41/1.83  tff(c_46, plain, (![B_26, A_27]: (B_26=A_27 | ~r1_tarski(B_26, A_27) | ~r1_tarski(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.41/1.83  tff(c_58, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_46])).
% 4.41/1.83  tff(c_1911, plain, (k7_setfam_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1900, c_58])).
% 4.41/1.83  tff(c_1031, plain, (r1_tarski(k7_setfam_1('#skF_1', k1_xboole_0), k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_985, c_18])).
% 4.41/1.83  tff(c_653, plain, (![A_70]: (r1_tarski(k7_setfam_1('#skF_1', A_70), '#skF_2') | ~r1_tarski(A_70, k7_setfam_1('#skF_1', '#skF_2')) | ~r1_tarski(A_70, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_20, c_544])).
% 4.41/1.83  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.41/1.83  tff(c_1490, plain, (![A_93]: (k7_setfam_1('#skF_1', A_93)='#skF_2' | ~r1_tarski('#skF_2', k7_setfam_1('#skF_1', A_93)) | ~r1_tarski(A_93, k7_setfam_1('#skF_1', '#skF_2')) | ~r1_tarski(A_93, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_653, c_2])).
% 4.41/1.83  tff(c_1498, plain, (k7_setfam_1('#skF_1', k7_setfam_1('#skF_1', k1_xboole_0))='#skF_2' | ~r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski(k7_setfam_1('#skF_1', k1_xboole_0), k7_setfam_1('#skF_1', '#skF_2')) | ~r1_tarski(k7_setfam_1('#skF_1', k1_xboole_0), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_311, c_1490])).
% 4.41/1.83  tff(c_1507, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski(k7_setfam_1('#skF_1', k1_xboole_0), k7_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1031, c_311, c_1498])).
% 4.41/1.83  tff(c_1508, plain, (~r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski(k7_setfam_1('#skF_1', k1_xboole_0), k7_setfam_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_30, c_1507])).
% 4.41/1.83  tff(c_1511, plain, (~r1_tarski(k7_setfam_1('#skF_1', k1_xboole_0), k7_setfam_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_1508])).
% 4.41/1.83  tff(c_1520, plain, (![A_94, B_95, A_96]: (r1_tarski(k7_setfam_1(A_94, B_95), A_96) | ~r1_tarski(B_95, k7_setfam_1(A_94, A_96)) | ~m1_subset_1(B_95, k1_zfmisc_1(k1_zfmisc_1(A_94))) | ~r1_tarski(A_96, k1_zfmisc_1(A_94)))), inference(resolution, [status(thm)], [c_20, c_462])).
% 4.41/1.83  tff(c_1526, plain, (![A_96]: (r1_tarski(k7_setfam_1('#skF_1', k1_xboole_0), A_96) | ~r1_tarski(k1_xboole_0, k7_setfam_1('#skF_1', A_96)) | ~r1_tarski(A_96, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_1022, c_1520])).
% 4.41/1.83  tff(c_1556, plain, (![A_97]: (r1_tarski(k7_setfam_1('#skF_1', k1_xboole_0), A_97) | ~r1_tarski(A_97, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1526])).
% 4.41/1.83  tff(c_1558, plain, (r1_tarski(k7_setfam_1('#skF_1', k1_xboole_0), k7_setfam_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_1265, c_1556])).
% 4.41/1.83  tff(c_1584, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1511, c_1558])).
% 4.41/1.83  tff(c_1586, plain, (r1_tarski(k7_setfam_1('#skF_1', k1_xboole_0), k7_setfam_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_1508])).
% 4.41/1.83  tff(c_1594, plain, (k7_setfam_1('#skF_1', k1_xboole_0)=k7_setfam_1('#skF_1', '#skF_2') | ~r1_tarski(k7_setfam_1('#skF_1', '#skF_2'), k7_setfam_1('#skF_1', k1_xboole_0))), inference(resolution, [status(thm)], [c_1586, c_2])).
% 4.41/1.83  tff(c_1704, plain, (~r1_tarski(k7_setfam_1('#skF_1', '#skF_2'), k7_setfam_1('#skF_1', k1_xboole_0))), inference(splitLeft, [status(thm)], [c_1594])).
% 4.41/1.83  tff(c_1918, plain, (~r1_tarski(k7_setfam_1('#skF_1', '#skF_2'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1911, c_1704])).
% 4.41/1.83  tff(c_2202, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2201, c_1918])).
% 4.41/1.83  tff(c_2222, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2202])).
% 4.41/1.83  tff(c_2223, plain, (k3_subset_1('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k6_setfam_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_2125])).
% 4.41/1.83  tff(c_117, plain, (![A_33, B_34]: (m1_subset_1(k5_setfam_1(A_33, B_34), k1_zfmisc_1(A_33)) | ~m1_subset_1(B_34, k1_zfmisc_1(k1_zfmisc_1(A_33))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.41/1.83  tff(c_10, plain, (![A_4, B_5]: (k3_subset_1(A_4, k3_subset_1(A_4, B_5))=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.41/1.83  tff(c_810, plain, (![A_77, B_78]: (k3_subset_1(A_77, k3_subset_1(A_77, k5_setfam_1(A_77, B_78)))=k5_setfam_1(A_77, B_78) | ~m1_subset_1(B_78, k1_zfmisc_1(k1_zfmisc_1(A_77))))), inference(resolution, [status(thm)], [c_117, c_10])).
% 4.41/1.83  tff(c_827, plain, (![A_77, A_12]: (k3_subset_1(A_77, k3_subset_1(A_77, k5_setfam_1(A_77, A_12)))=k5_setfam_1(A_77, A_12) | ~r1_tarski(A_12, k1_zfmisc_1(A_77)))), inference(resolution, [status(thm)], [c_20, c_810])).
% 4.41/1.83  tff(c_2228, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2')) | ~r1_tarski(k7_setfam_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2223, c_827])).
% 4.41/1.83  tff(c_2235, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1265, c_2228])).
% 4.41/1.83  tff(c_2237, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_2235])).
% 4.41/1.83  tff(c_2238, plain, (k7_setfam_1('#skF_1', k1_xboole_0)=k7_setfam_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_1594])).
% 4.41/1.83  tff(c_2293, plain, (k7_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2238, c_311])).
% 4.41/1.83  tff(c_2325, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_246, c_2293])).
% 4.41/1.83  tff(c_2327, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_2325])).
% 4.41/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.41/1.83  
% 4.41/1.83  Inference rules
% 4.41/1.83  ----------------------
% 4.41/1.83  #Ref     : 0
% 4.41/1.83  #Sup     : 521
% 4.41/1.83  #Fact    : 0
% 4.41/1.83  #Define  : 0
% 4.41/1.83  #Split   : 20
% 4.41/1.83  #Chain   : 0
% 4.41/1.83  #Close   : 0
% 4.41/1.83  
% 4.41/1.83  Ordering : KBO
% 4.41/1.83  
% 4.41/1.83  Simplification rules
% 4.41/1.83  ----------------------
% 4.41/1.83  #Subsume      : 32
% 4.41/1.83  #Demod        : 432
% 4.41/1.83  #Tautology    : 290
% 4.41/1.83  #SimpNegUnit  : 10
% 4.41/1.83  #BackRed      : 41
% 4.41/1.83  
% 4.41/1.83  #Partial instantiations: 0
% 4.41/1.83  #Strategies tried      : 1
% 4.41/1.83  
% 4.41/1.83  Timing (in seconds)
% 4.41/1.83  ----------------------
% 4.41/1.84  Preprocessing        : 0.33
% 4.41/1.84  Parsing              : 0.18
% 4.41/1.84  CNF conversion       : 0.02
% 4.41/1.84  Main loop            : 0.66
% 4.41/1.84  Inferencing          : 0.22
% 4.41/1.84  Reduction            : 0.23
% 4.41/1.84  Demodulation         : 0.16
% 4.41/1.84  BG Simplification    : 0.03
% 4.41/1.84  Subsumption          : 0.14
% 4.41/1.84  Abstraction          : 0.03
% 4.53/1.84  MUC search           : 0.00
% 4.53/1.84  Cooper               : 0.00
% 4.53/1.84  Total                : 1.05
% 4.53/1.84  Index Insertion      : 0.00
% 4.53/1.84  Index Deletion       : 0.00
% 4.53/1.84  Index Matching       : 0.00
% 4.53/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
