%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1103+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:24 EST 2020

% Result     : Theorem 1.55s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 124 expanded)
%              Number of leaves         :   20 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :   65 ( 253 expanded)
%              Number of equality atoms :   34 ( 153 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_struct_0 > k7_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_42,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_64,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ~ ( B != k2_struct_0(A)
                  & k7_subset_1(u1_struct_0(A),k2_struct_0(A),B) = k1_xboole_0 )
              & ~ ( k7_subset_1(u1_struct_0(A),k2_struct_0(A),B) != k1_xboole_0
                  & B = k2_struct_0(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_pre_topc)).

tff(f_34,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | k4_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_68,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = k1_xboole_0
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_76,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_68])).

tff(c_22,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_33,plain,(
    ! [A_13] :
      ( u1_struct_0(A_13) = k2_struct_0(A_13)
      | ~ l1_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_37,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_33])).

tff(c_24,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') = k1_xboole_0
    | k2_struct_0('#skF_1') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_49,plain,
    ( k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') = k1_xboole_0
    | k2_struct_0('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_24])).

tff(c_50,plain,(
    k2_struct_0('#skF_1') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_49])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_20])).

tff(c_52,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_38])).

tff(c_113,plain,(
    ! [A_27,B_28,C_29] :
      ( k7_subset_1(A_27,B_28,C_29) = k4_xboole_0(B_28,C_29)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_119,plain,(
    ! [C_29] : k7_subset_1('#skF_2','#skF_2',C_29) = k4_xboole_0('#skF_2',C_29) ),
    inference(resolution,[status(thm)],[c_52,c_113])).

tff(c_53,plain,(
    u1_struct_0('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_37])).

tff(c_30,plain,
    ( k2_struct_0('#skF_1') != '#skF_2'
    | k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_112,plain,(
    k7_subset_1('#skF_2','#skF_2','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_50,c_50,c_30])).

tff(c_120,plain,(
    k4_xboole_0('#skF_2','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_112])).

tff(c_123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_120])).

tff(c_125,plain,(
    k2_struct_0('#skF_1') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_44,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_48,plain,(
    r1_tarski('#skF_2',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_38,c_44])).

tff(c_151,plain,(
    ! [B_35,A_36] :
      ( B_35 = A_36
      | ~ r1_tarski(B_35,A_36)
      | ~ r1_tarski(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_153,plain,
    ( k2_struct_0('#skF_1') = '#skF_2'
    | ~ r1_tarski(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_151])).

tff(c_160,plain,(
    ~ r1_tarski(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_153])).

tff(c_169,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_160])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_207,plain,(
    ! [A_41,B_42,C_43] :
      ( k7_subset_1(A_41,B_42,C_43) = k4_xboole_0(B_42,C_43)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_223,plain,(
    ! [B_45,A_46,C_47] :
      ( k7_subset_1(B_45,A_46,C_47) = k4_xboole_0(A_46,C_47)
      | ~ r1_tarski(A_46,B_45) ) ),
    inference(resolution,[status(thm)],[c_18,c_207])).

tff(c_234,plain,(
    ! [B_48,C_49] : k7_subset_1(B_48,B_48,C_49) = k4_xboole_0(B_48,C_49) ),
    inference(resolution,[status(thm)],[c_6,c_223])).

tff(c_124,plain,(
    k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_240,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_124])).

tff(c_249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_240])).

%------------------------------------------------------------------------------
