%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:43 EST 2020

% Result     : Theorem 14.54s
% Output     : CNFRefutation 14.86s
% Verified   : 
% Statistics : Number of formulae       :  197 (2110 expanded)
%              Number of leaves         :   37 ( 759 expanded)
%              Depth                    :   26
%              Number of atoms          :  646 (8061 expanded)
%              Number of equality atoms :   75 (1005 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_163,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => k3_orders_2(A,k1_struct_0(A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_orders_2)).

tff(f_70,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k3_orders_2(A,B,C),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).

tff(f_120,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ~ ( B != k1_xboole_0
          & ! [C] :
              ( m1_subset_1(C,A)
             => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_146,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r2_hidden(B,k3_orders_2(A,D,C))
                  <=> ( r2_orders_2(A,B,C)
                      & r2_hidden(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_orders_2(A,B,C)
              <=> ( r1_orders_2(A,B,C)
                  & B != C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

tff(c_56,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_26,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_92,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,B_58)
      | ~ m1_subset_1(A_57,k1_zfmisc_1(B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_105,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(resolution,[status(thm)],[c_26,c_92])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_62,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_60,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_58,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_54,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_42,plain,(
    ! [A_27,B_28,C_29] :
      ( m1_subset_1(k3_orders_2(A_27,B_28,C_29),k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ m1_subset_1(C_29,u1_struct_0(A_27))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_orders_2(A_27)
      | ~ v5_orders_2(A_27)
      | ~ v4_orders_2(A_27)
      | ~ v3_orders_2(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_44,plain,(
    ! [A_30] :
      ( l1_struct_0(A_30)
      | ~ l1_orders_2(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_75,plain,(
    ! [A_51] :
      ( k1_struct_0(A_51) = k1_xboole_0
      | ~ l1_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_80,plain,(
    ! [A_52] :
      ( k1_struct_0(A_52) = k1_xboole_0
      | ~ l1_orders_2(A_52) ) ),
    inference(resolution,[status(thm)],[c_44,c_75])).

tff(c_84,plain,(
    k1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_80])).

tff(c_52,plain,(
    k3_orders_2('#skF_2',k1_struct_0('#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_89,plain,(
    k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_52])).

tff(c_24,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1('#skF_1'(A_10,B_11),A_10)
      | k1_xboole_0 = B_11
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_14,plain,(
    ! [B_5,A_4] :
      ( r2_hidden(B_5,A_4)
      | ~ m1_subset_1(B_5,A_4)
      | v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_465,plain,(
    ! [B_130,D_131,A_132,C_133] :
      ( r2_hidden(B_130,D_131)
      | ~ r2_hidden(B_130,k3_orders_2(A_132,D_131,C_133))
      | ~ m1_subset_1(D_131,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ m1_subset_1(C_133,u1_struct_0(A_132))
      | ~ m1_subset_1(B_130,u1_struct_0(A_132))
      | ~ l1_orders_2(A_132)
      | ~ v5_orders_2(A_132)
      | ~ v4_orders_2(A_132)
      | ~ v3_orders_2(A_132)
      | v2_struct_0(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_15315,plain,(
    ! [B_1070,D_1071,A_1072,C_1073] :
      ( r2_hidden(B_1070,D_1071)
      | ~ m1_subset_1(D_1071,k1_zfmisc_1(u1_struct_0(A_1072)))
      | ~ m1_subset_1(C_1073,u1_struct_0(A_1072))
      | ~ m1_subset_1(B_1070,u1_struct_0(A_1072))
      | ~ l1_orders_2(A_1072)
      | ~ v5_orders_2(A_1072)
      | ~ v4_orders_2(A_1072)
      | ~ v3_orders_2(A_1072)
      | v2_struct_0(A_1072)
      | ~ m1_subset_1(B_1070,k3_orders_2(A_1072,D_1071,C_1073))
      | v1_xboole_0(k3_orders_2(A_1072,D_1071,C_1073)) ) ),
    inference(resolution,[status(thm)],[c_14,c_465])).

tff(c_21738,plain,(
    ! [B_1389,C_1390,A_1391] :
      ( r2_hidden(B_1389,k1_xboole_0)
      | ~ m1_subset_1(C_1390,u1_struct_0(A_1391))
      | ~ m1_subset_1(B_1389,u1_struct_0(A_1391))
      | ~ l1_orders_2(A_1391)
      | ~ v5_orders_2(A_1391)
      | ~ v4_orders_2(A_1391)
      | ~ v3_orders_2(A_1391)
      | v2_struct_0(A_1391)
      | ~ m1_subset_1(B_1389,k3_orders_2(A_1391,k1_xboole_0,C_1390))
      | v1_xboole_0(k3_orders_2(A_1391,k1_xboole_0,C_1390)) ) ),
    inference(resolution,[status(thm)],[c_26,c_15315])).

tff(c_21775,plain,(
    ! [B_1389] :
      ( r2_hidden(B_1389,k1_xboole_0)
      | ~ m1_subset_1(B_1389,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(B_1389,k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'))
      | v1_xboole_0(k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_54,c_21738])).

tff(c_21793,plain,(
    ! [B_1389] :
      ( r2_hidden(B_1389,k1_xboole_0)
      | ~ m1_subset_1(B_1389,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(B_1389,k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'))
      | v1_xboole_0(k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_21775])).

tff(c_21794,plain,(
    ! [B_1389] :
      ( r2_hidden(B_1389,k1_xboole_0)
      | ~ m1_subset_1(B_1389,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_1389,k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'))
      | v1_xboole_0(k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_21793])).

tff(c_21795,plain,(
    v1_xboole_0(k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_21794])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_21798,plain,(
    k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_21795,c_4])).

tff(c_21802,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_21798])).

tff(c_21804,plain,(
    ~ v1_xboole_0(k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')) ),
    inference(splitRight,[status(thm)],[c_21794])).

tff(c_197,plain,(
    ! [A_88,B_89] :
      ( r2_hidden('#skF_1'(A_88,B_89),B_89)
      | k1_xboole_0 = B_89
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_12,plain,(
    ! [B_5,A_4] :
      ( m1_subset_1(B_5,A_4)
      | ~ r2_hidden(B_5,A_4)
      | v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_214,plain,(
    ! [A_88,B_89] :
      ( m1_subset_1('#skF_1'(A_88,B_89),B_89)
      | v1_xboole_0(B_89)
      | k1_xboole_0 = B_89
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_88)) ) ),
    inference(resolution,[status(thm)],[c_197,c_12])).

tff(c_24018,plain,(
    ! [B_1450] :
      ( r2_hidden(B_1450,k1_xboole_0)
      | ~ m1_subset_1(B_1450,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_1450,k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_21794])).

tff(c_24054,plain,(
    ! [A_88] :
      ( r2_hidden('#skF_1'(A_88,k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')),k1_xboole_0)
      | ~ m1_subset_1('#skF_1'(A_88,k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')),u1_struct_0('#skF_2'))
      | v1_xboole_0(k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'))
      | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'),k1_zfmisc_1(A_88)) ) ),
    inference(resolution,[status(thm)],[c_214,c_24018])).

tff(c_24327,plain,(
    ! [A_1462] :
      ( r2_hidden('#skF_1'(A_1462,k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')),k1_xboole_0)
      | ~ m1_subset_1('#skF_1'(A_1462,k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'),k1_zfmisc_1(A_1462)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_21804,c_24054])).

tff(c_24351,plain,
    ( r2_hidden('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')),k1_xboole_0)
    | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0
    | ~ m1_subset_1(k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_24,c_24327])).

tff(c_24372,plain,
    ( r2_hidden('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')),k1_xboole_0)
    | ~ m1_subset_1(k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_24351])).

tff(c_24374,plain,(
    ~ m1_subset_1(k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_24372])).

tff(c_24377,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_24374])).

tff(c_24386,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_26,c_54,c_24377])).

tff(c_24388,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_24386])).

tff(c_24389,plain,(
    r2_hidden('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_24372])).

tff(c_30,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_157,plain,(
    ! [A_73,C_74,B_75] :
      ( m1_subset_1(A_73,C_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(C_74))
      | ~ r2_hidden(A_73,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_165,plain,(
    ! [A_73,B_15,A_14] :
      ( m1_subset_1(A_73,B_15)
      | ~ r2_hidden(A_73,A_14)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(resolution,[status(thm)],[c_30,c_157])).

tff(c_24613,plain,(
    ! [B_15] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')),B_15)
      | ~ r1_tarski(k1_xboole_0,B_15) ) ),
    inference(resolution,[status(thm)],[c_24389,c_165])).

tff(c_24712,plain,(
    ! [B_1467] : m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')),B_1467) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_24613])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24993,plain,(
    ! [B_1468] : r1_tarski('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')),B_1468) ),
    inference(resolution,[status(thm)],[c_24712,c_28])).

tff(c_126,plain,(
    ! [B_62,A_63] :
      ( B_62 = A_63
      | ~ r1_tarski(B_62,A_63)
      | ~ r1_tarski(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_131,plain,(
    ! [A_13] :
      ( k1_xboole_0 = A_13
      | ~ r1_tarski(A_13,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_105,c_126])).

tff(c_25133,plain,(
    '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24993,c_131])).

tff(c_24627,plain,(
    ! [B_15] : m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')),B_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_24613])).

tff(c_25137,plain,(
    ! [B_15] : m1_subset_1(k1_xboole_0,B_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25133,c_24627])).

tff(c_183,plain,(
    ! [A_86,B_87] :
      ( m1_subset_1('#skF_1'(A_86,B_87),A_86)
      | k1_xboole_0 = B_87
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_18,plain,(
    ! [B_5,A_4] :
      ( v1_xboole_0(B_5)
      | ~ m1_subset_1(B_5,A_4)
      | ~ v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_389,plain,(
    ! [A_122,B_123] :
      ( v1_xboole_0('#skF_1'(A_122,B_123))
      | ~ v1_xboole_0(A_122)
      | k1_xboole_0 = B_123
      | ~ m1_subset_1(B_123,k1_zfmisc_1(A_122)) ) ),
    inference(resolution,[status(thm)],[c_183,c_18])).

tff(c_17101,plain,(
    ! [A_1193,B_1194] :
      ( v1_xboole_0('#skF_1'(A_1193,'#skF_1'(k1_zfmisc_1(A_1193),B_1194)))
      | ~ v1_xboole_0(A_1193)
      | '#skF_1'(k1_zfmisc_1(A_1193),B_1194) = k1_xboole_0
      | k1_xboole_0 = B_1194
      | ~ m1_subset_1(B_1194,k1_zfmisc_1(k1_zfmisc_1(A_1193))) ) ),
    inference(resolution,[status(thm)],[c_24,c_389])).

tff(c_17164,plain,(
    ! [A_1200,B_1201] :
      ( '#skF_1'(A_1200,'#skF_1'(k1_zfmisc_1(A_1200),B_1201)) = k1_xboole_0
      | ~ v1_xboole_0(A_1200)
      | '#skF_1'(k1_zfmisc_1(A_1200),B_1201) = k1_xboole_0
      | k1_xboole_0 = B_1201
      | ~ m1_subset_1(B_1201,k1_zfmisc_1(k1_zfmisc_1(A_1200))) ) ),
    inference(resolution,[status(thm)],[c_17101,c_4])).

tff(c_17221,plain,(
    ! [A_1202,A_1203] :
      ( '#skF_1'(A_1202,'#skF_1'(k1_zfmisc_1(A_1202),A_1203)) = k1_xboole_0
      | ~ v1_xboole_0(A_1202)
      | '#skF_1'(k1_zfmisc_1(A_1202),A_1203) = k1_xboole_0
      | k1_xboole_0 = A_1203
      | ~ r1_tarski(A_1203,k1_zfmisc_1(A_1202)) ) ),
    inference(resolution,[status(thm)],[c_30,c_17164])).

tff(c_20,plain,(
    ! [C_9,A_6,B_7] :
      ( r2_hidden(C_9,A_6)
      | ~ r2_hidden(C_9,B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12406,plain,(
    ! [A_859,B_860,A_861] :
      ( r2_hidden('#skF_1'(A_859,B_860),A_861)
      | ~ m1_subset_1(B_860,k1_zfmisc_1(A_861))
      | k1_xboole_0 = B_860
      | ~ m1_subset_1(B_860,k1_zfmisc_1(A_859)) ) ),
    inference(resolution,[status(thm)],[c_197,c_20])).

tff(c_167,plain,(
    ! [A_73,A_13] :
      ( m1_subset_1(A_73,A_13)
      | ~ r2_hidden(A_73,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_157])).

tff(c_12647,plain,(
    ! [A_888,B_889,A_890] :
      ( m1_subset_1('#skF_1'(A_888,B_889),A_890)
      | ~ m1_subset_1(B_889,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = B_889
      | ~ m1_subset_1(B_889,k1_zfmisc_1(A_888)) ) ),
    inference(resolution,[status(thm)],[c_12406,c_167])).

tff(c_247,plain,(
    ! [A_102,B_103,C_104] :
      ( r2_orders_2(A_102,B_103,C_104)
      | C_104 = B_103
      | ~ r1_orders_2(A_102,B_103,C_104)
      | ~ m1_subset_1(C_104,u1_struct_0(A_102))
      | ~ m1_subset_1(B_103,u1_struct_0(A_102))
      | ~ l1_orders_2(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_255,plain,(
    ! [B_103] :
      ( r2_orders_2('#skF_2',B_103,'#skF_3')
      | B_103 = '#skF_3'
      | ~ r1_orders_2('#skF_2',B_103,'#skF_3')
      | ~ m1_subset_1(B_103,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_54,c_247])).

tff(c_260,plain,(
    ! [B_103] :
      ( r2_orders_2('#skF_2',B_103,'#skF_3')
      | B_103 = '#skF_3'
      | ~ r1_orders_2('#skF_2',B_103,'#skF_3')
      | ~ m1_subset_1(B_103,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_255])).

tff(c_12687,plain,(
    ! [A_888,B_889] :
      ( r2_orders_2('#skF_2','#skF_1'(A_888,B_889),'#skF_3')
      | '#skF_1'(A_888,B_889) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_1'(A_888,B_889),'#skF_3')
      | ~ m1_subset_1(B_889,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = B_889
      | ~ m1_subset_1(B_889,k1_zfmisc_1(A_888)) ) ),
    inference(resolution,[status(thm)],[c_12647,c_260])).

tff(c_17338,plain,(
    ! [A_1202,A_1203] :
      ( r2_orders_2('#skF_2',k1_xboole_0,'#skF_3')
      | '#skF_1'(A_1202,'#skF_1'(k1_zfmisc_1(A_1202),A_1203)) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_1'(A_1202,'#skF_1'(k1_zfmisc_1(A_1202),A_1203)),'#skF_3')
      | ~ m1_subset_1('#skF_1'(k1_zfmisc_1(A_1202),A_1203),k1_zfmisc_1(k1_xboole_0))
      | '#skF_1'(k1_zfmisc_1(A_1202),A_1203) = k1_xboole_0
      | ~ m1_subset_1('#skF_1'(k1_zfmisc_1(A_1202),A_1203),k1_zfmisc_1(A_1202))
      | ~ v1_xboole_0(A_1202)
      | '#skF_1'(k1_zfmisc_1(A_1202),A_1203) = k1_xboole_0
      | k1_xboole_0 = A_1203
      | ~ r1_tarski(A_1203,k1_zfmisc_1(A_1202)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17221,c_12687])).

tff(c_17499,plain,(
    r2_orders_2('#skF_2',k1_xboole_0,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_17338])).

tff(c_40,plain,(
    ! [A_20,B_24,C_26] :
      ( r1_orders_2(A_20,B_24,C_26)
      | ~ r2_orders_2(A_20,B_24,C_26)
      | ~ m1_subset_1(C_26,u1_struct_0(A_20))
      | ~ m1_subset_1(B_24,u1_struct_0(A_20))
      | ~ l1_orders_2(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_17501,plain,
    ( r1_orders_2('#skF_2',k1_xboole_0,'#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k1_xboole_0,u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_17499,c_40])).

tff(c_17504,plain,
    ( r1_orders_2('#skF_2',k1_xboole_0,'#skF_3')
    | ~ m1_subset_1(k1_xboole_0,u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_17501])).

tff(c_17505,plain,(
    ~ m1_subset_1(k1_xboole_0,u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_17504])).

tff(c_10,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_209,plain,(
    ! [A_88,B_89,B_15] :
      ( m1_subset_1('#skF_1'(A_88,B_89),B_15)
      | ~ r1_tarski(B_89,B_15)
      | k1_xboole_0 = B_89
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_88)) ) ),
    inference(resolution,[status(thm)],[c_197,c_165])).

tff(c_19171,plain,(
    ! [B_1293,C_1294,A_1295] :
      ( r2_hidden(B_1293,k1_xboole_0)
      | ~ m1_subset_1(C_1294,u1_struct_0(A_1295))
      | ~ m1_subset_1(B_1293,u1_struct_0(A_1295))
      | ~ l1_orders_2(A_1295)
      | ~ v5_orders_2(A_1295)
      | ~ v4_orders_2(A_1295)
      | ~ v3_orders_2(A_1295)
      | v2_struct_0(A_1295)
      | ~ m1_subset_1(B_1293,k3_orders_2(A_1295,k1_xboole_0,C_1294))
      | v1_xboole_0(k3_orders_2(A_1295,k1_xboole_0,C_1294)) ) ),
    inference(resolution,[status(thm)],[c_26,c_15315])).

tff(c_19206,plain,(
    ! [B_1293] :
      ( r2_hidden(B_1293,k1_xboole_0)
      | ~ m1_subset_1(B_1293,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(B_1293,k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'))
      | v1_xboole_0(k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_54,c_19171])).

tff(c_19220,plain,(
    ! [B_1293] :
      ( r2_hidden(B_1293,k1_xboole_0)
      | ~ m1_subset_1(B_1293,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(B_1293,k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'))
      | v1_xboole_0(k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_19206])).

tff(c_19221,plain,(
    ! [B_1293] :
      ( r2_hidden(B_1293,k1_xboole_0)
      | ~ m1_subset_1(B_1293,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_1293,k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'))
      | v1_xboole_0(k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_19220])).

tff(c_19222,plain,(
    v1_xboole_0(k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_19221])).

tff(c_19225,plain,(
    k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_19222,c_4])).

tff(c_19229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_19225])).

tff(c_19232,plain,(
    ! [B_1296] :
      ( r2_hidden(B_1296,k1_xboole_0)
      | ~ m1_subset_1(B_1296,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_1296,k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_19221])).

tff(c_19290,plain,(
    ! [A_1297,B_1298] :
      ( r2_hidden('#skF_1'(A_1297,B_1298),k1_xboole_0)
      | ~ m1_subset_1('#skF_1'(A_1297,B_1298),u1_struct_0('#skF_2'))
      | ~ r1_tarski(B_1298,k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'))
      | k1_xboole_0 = B_1298
      | ~ m1_subset_1(B_1298,k1_zfmisc_1(A_1297)) ) ),
    inference(resolution,[status(thm)],[c_209,c_19232])).

tff(c_19365,plain,(
    ! [B_1299] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_2'),B_1299),k1_xboole_0)
      | ~ r1_tarski(B_1299,k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'))
      | k1_xboole_0 = B_1299
      | ~ m1_subset_1(B_1299,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_24,c_19290])).

tff(c_19371,plain,(
    ! [B_1299,B_15] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_1299),B_15)
      | ~ r1_tarski(k1_xboole_0,B_15)
      | ~ r1_tarski(B_1299,k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'))
      | k1_xboole_0 = B_1299
      | ~ m1_subset_1(B_1299,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_19365,c_165])).

tff(c_19594,plain,(
    ! [B_1306,B_1307] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_1306),B_1307)
      | ~ r1_tarski(B_1306,k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'))
      | k1_xboole_0 = B_1306
      | ~ m1_subset_1(B_1306,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_19371])).

tff(c_19956,plain,(
    ! [B_1315,B_1316] :
      ( r1_tarski('#skF_1'(u1_struct_0('#skF_2'),B_1315),B_1316)
      | ~ r1_tarski(B_1315,k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'))
      | k1_xboole_0 = B_1315
      | ~ m1_subset_1(B_1315,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_19594,c_28])).

tff(c_20091,plain,(
    ! [B_1317] :
      ( '#skF_1'(u1_struct_0('#skF_2'),B_1317) = k1_xboole_0
      | ~ r1_tarski(B_1317,k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'))
      | k1_xboole_0 = B_1317
      | ~ m1_subset_1(B_1317,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_19956,c_131])).

tff(c_20135,plain,(
    ! [B_28,C_29] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_28,C_29)) = k1_xboole_0
      | ~ r1_tarski(k3_orders_2('#skF_2',B_28,C_29),k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'))
      | k3_orders_2('#skF_2',B_28,C_29) = k1_xboole_0
      | ~ m1_subset_1(C_29,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_20091])).

tff(c_20166,plain,(
    ! [B_28,C_29] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_28,C_29)) = k1_xboole_0
      | ~ r1_tarski(k3_orders_2('#skF_2',B_28,C_29),k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'))
      | k3_orders_2('#skF_2',B_28,C_29) = k1_xboole_0
      | ~ m1_subset_1(C_29,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_20135])).

tff(c_20175,plain,(
    ! [B_1318,C_1319] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_1318,C_1319)) = k1_xboole_0
      | ~ r1_tarski(k3_orders_2('#skF_2',B_1318,C_1319),k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'))
      | k3_orders_2('#skF_2',B_1318,C_1319) = k1_xboole_0
      | ~ m1_subset_1(C_1319,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_1318,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_20166])).

tff(c_20179,plain,
    ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')) = k1_xboole_0
    | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_10,c_20175])).

tff(c_20182,plain,
    ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')) = k1_xboole_0
    | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_54,c_20179])).

tff(c_20183,plain,(
    '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_20182])).

tff(c_20320,plain,
    ( m1_subset_1(k1_xboole_0,u1_struct_0('#skF_2'))
    | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0
    | ~ m1_subset_1(k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_20183,c_24])).

tff(c_20416,plain,(
    ~ m1_subset_1(k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_17505,c_20320])).

tff(c_20420,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_20416])).

tff(c_20429,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_26,c_54,c_20420])).

tff(c_20431,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_20429])).

tff(c_20433,plain,(
    m1_subset_1(k1_xboole_0,u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_17504])).

tff(c_21743,plain,(
    ! [B_1389] :
      ( r2_hidden(B_1389,k1_xboole_0)
      | ~ m1_subset_1(B_1389,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(B_1389,k3_orders_2('#skF_2',k1_xboole_0,k1_xboole_0))
      | v1_xboole_0(k3_orders_2('#skF_2',k1_xboole_0,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_20433,c_21738])).

tff(c_21779,plain,(
    ! [B_1389] :
      ( r2_hidden(B_1389,k1_xboole_0)
      | ~ m1_subset_1(B_1389,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(B_1389,k3_orders_2('#skF_2',k1_xboole_0,k1_xboole_0))
      | v1_xboole_0(k3_orders_2('#skF_2',k1_xboole_0,k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_21743])).

tff(c_21780,plain,(
    ! [B_1389] :
      ( r2_hidden(B_1389,k1_xboole_0)
      | ~ m1_subset_1(B_1389,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_1389,k3_orders_2('#skF_2',k1_xboole_0,k1_xboole_0))
      | v1_xboole_0(k3_orders_2('#skF_2',k1_xboole_0,k1_xboole_0)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_21779])).

tff(c_21805,plain,(
    v1_xboole_0(k3_orders_2('#skF_2',k1_xboole_0,k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_21780])).

tff(c_21809,plain,(
    k3_orders_2('#skF_2',k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_21805,c_4])).

tff(c_50,plain,(
    ! [A_31,B_39,C_43,D_45] :
      ( r2_orders_2(A_31,B_39,C_43)
      | ~ r2_hidden(B_39,k3_orders_2(A_31,D_45,C_43))
      | ~ m1_subset_1(D_45,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ m1_subset_1(C_43,u1_struct_0(A_31))
      | ~ m1_subset_1(B_39,u1_struct_0(A_31))
      | ~ l1_orders_2(A_31)
      | ~ v5_orders_2(A_31)
      | ~ v4_orders_2(A_31)
      | ~ v3_orders_2(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_21838,plain,(
    ! [B_39] :
      ( r2_orders_2('#skF_2',B_39,k1_xboole_0)
      | ~ r2_hidden(B_39,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k1_xboole_0,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_39,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21809,c_50])).

tff(c_21873,plain,(
    ! [B_39] :
      ( r2_orders_2('#skF_2',B_39,k1_xboole_0)
      | ~ r2_hidden(B_39,k1_xboole_0)
      | ~ m1_subset_1(B_39,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_20433,c_26,c_21838])).

tff(c_21882,plain,(
    ! [B_1392] :
      ( r2_orders_2('#skF_2',B_1392,k1_xboole_0)
      | ~ r2_hidden(B_1392,k1_xboole_0)
      | ~ m1_subset_1(B_1392,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_21873])).

tff(c_21934,plain,
    ( r2_orders_2('#skF_2',k1_xboole_0,k1_xboole_0)
    | ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20433,c_21882])).

tff(c_21948,plain,(
    ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_21934])).

tff(c_317,plain,(
    ! [A_111,B_112,C_113] :
      ( m1_subset_1(k3_orders_2(A_111,B_112,C_113),k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ m1_subset_1(C_113,u1_struct_0(A_111))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_orders_2(A_111)
      | ~ v5_orders_2(A_111)
      | ~ v4_orders_2(A_111)
      | ~ v3_orders_2(A_111)
      | v2_struct_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_32,plain,(
    ! [A_16,C_18,B_17] :
      ( m1_subset_1(A_16,C_18)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(C_18))
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_13542,plain,(
    ! [A_945,A_946,B_947,C_948] :
      ( m1_subset_1(A_945,u1_struct_0(A_946))
      | ~ r2_hidden(A_945,k3_orders_2(A_946,B_947,C_948))
      | ~ m1_subset_1(C_948,u1_struct_0(A_946))
      | ~ m1_subset_1(B_947,k1_zfmisc_1(u1_struct_0(A_946)))
      | ~ l1_orders_2(A_946)
      | ~ v5_orders_2(A_946)
      | ~ v4_orders_2(A_946)
      | ~ v3_orders_2(A_946)
      | v2_struct_0(A_946) ) ),
    inference(resolution,[status(thm)],[c_317,c_32])).

tff(c_22526,plain,(
    ! [B_1425,A_1426,C_1427,B_1428] :
      ( m1_subset_1(B_1425,u1_struct_0(A_1426))
      | ~ m1_subset_1(C_1427,u1_struct_0(A_1426))
      | ~ m1_subset_1(B_1428,k1_zfmisc_1(u1_struct_0(A_1426)))
      | ~ l1_orders_2(A_1426)
      | ~ v5_orders_2(A_1426)
      | ~ v4_orders_2(A_1426)
      | ~ v3_orders_2(A_1426)
      | v2_struct_0(A_1426)
      | ~ m1_subset_1(B_1425,k3_orders_2(A_1426,B_1428,C_1427))
      | v1_xboole_0(k3_orders_2(A_1426,B_1428,C_1427)) ) ),
    inference(resolution,[status(thm)],[c_14,c_13542])).

tff(c_22563,plain,(
    ! [B_1425,B_1428] :
      ( m1_subset_1(B_1425,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_1428,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(B_1425,k3_orders_2('#skF_2',B_1428,'#skF_3'))
      | v1_xboole_0(k3_orders_2('#skF_2',B_1428,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_54,c_22526])).

tff(c_22581,plain,(
    ! [B_1425,B_1428] :
      ( m1_subset_1(B_1425,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_1428,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(B_1425,k3_orders_2('#skF_2',B_1428,'#skF_3'))
      | v1_xboole_0(k3_orders_2('#skF_2',B_1428,'#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_22563])).

tff(c_22583,plain,(
    ! [B_1429,B_1430] :
      ( m1_subset_1(B_1429,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_1430,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_1429,k3_orders_2('#skF_2',B_1430,'#skF_3'))
      | v1_xboole_0(k3_orders_2('#skF_2',B_1430,'#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_22581])).

tff(c_22625,plain,(
    ! [B_1429] :
      ( m1_subset_1(B_1429,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_1429,k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'))
      | v1_xboole_0(k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_26,c_22583])).

tff(c_22647,plain,(
    ! [B_1431] :
      ( m1_subset_1(B_1431,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_1431,k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_21804,c_22625])).

tff(c_22683,plain,(
    ! [A_88] :
      ( m1_subset_1('#skF_1'(A_88,k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')),u1_struct_0('#skF_2'))
      | v1_xboole_0(k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'))
      | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'),k1_zfmisc_1(A_88)) ) ),
    inference(resolution,[status(thm)],[c_214,c_22647])).

tff(c_22705,plain,(
    ! [A_1432] :
      ( m1_subset_1('#skF_1'(A_1432,k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'),k1_zfmisc_1(A_1432)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_21804,c_22683])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_1'(A_10,B_11),B_11)
      | k1_xboole_0 = B_11
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_472,plain,(
    ! [A_10,A_132,D_131,C_133] :
      ( r2_hidden('#skF_1'(A_10,k3_orders_2(A_132,D_131,C_133)),D_131)
      | ~ m1_subset_1(D_131,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ m1_subset_1(C_133,u1_struct_0(A_132))
      | ~ m1_subset_1('#skF_1'(A_10,k3_orders_2(A_132,D_131,C_133)),u1_struct_0(A_132))
      | ~ l1_orders_2(A_132)
      | ~ v5_orders_2(A_132)
      | ~ v4_orders_2(A_132)
      | ~ v3_orders_2(A_132)
      | v2_struct_0(A_132)
      | k3_orders_2(A_132,D_131,C_133) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_132,D_131,C_133),k1_zfmisc_1(A_10)) ) ),
    inference(resolution,[status(thm)],[c_22,c_465])).

tff(c_22721,plain,(
    ! [A_1432] :
      ( r2_hidden('#skF_1'(A_1432,k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')),k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'),k1_zfmisc_1(A_1432)) ) ),
    inference(resolution,[status(thm)],[c_22705,c_472])).

tff(c_22756,plain,(
    ! [A_1432] :
      ( r2_hidden('#skF_1'(A_1432,k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')),k1_xboole_0)
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'),k1_zfmisc_1(A_1432)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_54,c_26,c_22721])).

tff(c_22773,plain,(
    ! [A_1433] :
      ( r2_hidden('#skF_1'(A_1433,k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')),k1_xboole_0)
      | ~ m1_subset_1(k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'),k1_zfmisc_1(A_1433)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_64,c_22756])).

tff(c_22779,plain,(
    ! [A_1433,B_15] :
      ( m1_subset_1('#skF_1'(A_1433,k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')),B_15)
      | ~ r1_tarski(k1_xboole_0,B_15)
      | ~ m1_subset_1(k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'),k1_zfmisc_1(A_1433)) ) ),
    inference(resolution,[status(thm)],[c_22773,c_165])).

tff(c_22875,plain,(
    ! [A_1436,B_1437] :
      ( m1_subset_1('#skF_1'(A_1436,k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')),B_1437)
      | ~ m1_subset_1(k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'),k1_zfmisc_1(A_1436)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_22779])).

tff(c_23115,plain,(
    ! [A_1438,B_1439] :
      ( r1_tarski('#skF_1'(A_1438,k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')),B_1439)
      | ~ m1_subset_1(k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'),k1_zfmisc_1(A_1438)) ) ),
    inference(resolution,[status(thm)],[c_22875,c_28])).

tff(c_23289,plain,(
    ! [A_1444] :
      ( '#skF_1'(A_1444,k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'),k1_zfmisc_1(A_1444)) ) ),
    inference(resolution,[status(thm)],[c_23115,c_131])).

tff(c_23293,plain,
    ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')) = k1_xboole_0
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_23289])).

tff(c_23303,plain,
    ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')) = k1_xboole_0
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_26,c_54,c_23293])).

tff(c_23304,plain,(
    '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_23303])).

tff(c_23362,plain,
    ( r2_hidden('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',k1_xboole_0,'#skF_3')),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k1_xboole_0,u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0
    | ~ m1_subset_1(k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_23304,c_472])).

tff(c_23493,plain,
    ( r2_hidden(k1_xboole_0,k1_xboole_0)
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0
    | ~ m1_subset_1(k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_20433,c_54,c_26,c_23304,c_23362])).

tff(c_23494,plain,(
    ~ m1_subset_1(k3_orders_2('#skF_2',k1_xboole_0,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_64,c_21948,c_23493])).

tff(c_23555,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_23494])).

tff(c_23564,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_26,c_54,c_23555])).

tff(c_23566,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_23564])).

tff(c_23568,plain,(
    r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_21934])).

tff(c_23575,plain,(
    ! [B_15] :
      ( m1_subset_1(k1_xboole_0,B_15)
      | ~ r1_tarski(k1_xboole_0,B_15) ) ),
    inference(resolution,[status(thm)],[c_23568,c_165])).

tff(c_23589,plain,(
    ! [B_15] : m1_subset_1(k1_xboole_0,B_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_23575])).

tff(c_23567,plain,(
    r2_orders_2('#skF_2',k1_xboole_0,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_21934])).

tff(c_38,plain,(
    ! [A_20,C_26] :
      ( ~ r2_orders_2(A_20,C_26,C_26)
      | ~ m1_subset_1(C_26,u1_struct_0(A_20))
      | ~ l1_orders_2(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_24008,plain,
    ( ~ m1_subset_1(k1_xboole_0,u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_23567,c_38])).

tff(c_24015,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_23589,c_24008])).

tff(c_24017,plain,(
    ~ v1_xboole_0(k3_orders_2('#skF_2',k1_xboole_0,k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_21780])).

tff(c_12161,plain,(
    ! [A_837,B_838,C_839,D_840] :
      ( r2_orders_2(A_837,B_838,C_839)
      | ~ r2_hidden(B_838,k3_orders_2(A_837,D_840,C_839))
      | ~ m1_subset_1(D_840,k1_zfmisc_1(u1_struct_0(A_837)))
      | ~ m1_subset_1(C_839,u1_struct_0(A_837))
      | ~ m1_subset_1(B_838,u1_struct_0(A_837))
      | ~ l1_orders_2(A_837)
      | ~ v5_orders_2(A_837)
      | ~ v4_orders_2(A_837)
      | ~ v3_orders_2(A_837)
      | v2_struct_0(A_837) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_15648,plain,(
    ! [A_1095,B_1096,C_1097,D_1098] :
      ( r2_orders_2(A_1095,B_1096,C_1097)
      | ~ m1_subset_1(D_1098,k1_zfmisc_1(u1_struct_0(A_1095)))
      | ~ m1_subset_1(C_1097,u1_struct_0(A_1095))
      | ~ m1_subset_1(B_1096,u1_struct_0(A_1095))
      | ~ l1_orders_2(A_1095)
      | ~ v5_orders_2(A_1095)
      | ~ v4_orders_2(A_1095)
      | ~ v3_orders_2(A_1095)
      | v2_struct_0(A_1095)
      | ~ m1_subset_1(B_1096,k3_orders_2(A_1095,D_1098,C_1097))
      | v1_xboole_0(k3_orders_2(A_1095,D_1098,C_1097)) ) ),
    inference(resolution,[status(thm)],[c_14,c_12161])).

tff(c_24551,plain,(
    ! [A_1463,B_1464,C_1465] :
      ( r2_orders_2(A_1463,B_1464,C_1465)
      | ~ m1_subset_1(C_1465,u1_struct_0(A_1463))
      | ~ m1_subset_1(B_1464,u1_struct_0(A_1463))
      | ~ l1_orders_2(A_1463)
      | ~ v5_orders_2(A_1463)
      | ~ v4_orders_2(A_1463)
      | ~ v3_orders_2(A_1463)
      | v2_struct_0(A_1463)
      | ~ m1_subset_1(B_1464,k3_orders_2(A_1463,k1_xboole_0,C_1465))
      | v1_xboole_0(k3_orders_2(A_1463,k1_xboole_0,C_1465)) ) ),
    inference(resolution,[status(thm)],[c_26,c_15648])).

tff(c_24556,plain,(
    ! [B_1464] :
      ( r2_orders_2('#skF_2',B_1464,k1_xboole_0)
      | ~ m1_subset_1(B_1464,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(B_1464,k3_orders_2('#skF_2',k1_xboole_0,k1_xboole_0))
      | v1_xboole_0(k3_orders_2('#skF_2',k1_xboole_0,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_20433,c_24551])).

tff(c_24592,plain,(
    ! [B_1464] :
      ( r2_orders_2('#skF_2',B_1464,k1_xboole_0)
      | ~ m1_subset_1(B_1464,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(B_1464,k3_orders_2('#skF_2',k1_xboole_0,k1_xboole_0))
      | v1_xboole_0(k3_orders_2('#skF_2',k1_xboole_0,k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_24556])).

tff(c_26140,plain,(
    ! [B_1486] :
      ( r2_orders_2('#skF_2',B_1486,k1_xboole_0)
      | ~ m1_subset_1(B_1486,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_1486,k3_orders_2('#skF_2',k1_xboole_0,k1_xboole_0)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24017,c_64,c_24592])).

tff(c_26144,plain,
    ( r2_orders_2('#skF_2',k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_25137,c_26140])).

tff(c_26191,plain,(
    r2_orders_2('#skF_2',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25137,c_26144])).

tff(c_26208,plain,
    ( ~ m1_subset_1(k1_xboole_0,u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_26191,c_38])).

tff(c_26215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_25137,c_26208])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:11:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.54/6.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.71/6.99  
% 14.71/6.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.71/7.00  %$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 14.71/7.00  
% 14.71/7.00  %Foreground sorts:
% 14.71/7.00  
% 14.71/7.00  
% 14.71/7.00  %Background operators:
% 14.71/7.00  
% 14.71/7.00  
% 14.71/7.00  %Foreground operators:
% 14.71/7.00  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 14.71/7.00  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 14.71/7.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.71/7.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.71/7.00  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 14.71/7.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.71/7.00  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 14.71/7.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.71/7.00  tff('#skF_2', type, '#skF_2': $i).
% 14.71/7.00  tff('#skF_3', type, '#skF_3': $i).
% 14.71/7.00  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 14.71/7.00  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 14.71/7.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.71/7.00  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 14.71/7.00  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 14.71/7.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.71/7.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.71/7.00  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 14.71/7.00  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 14.71/7.00  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 14.71/7.00  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.71/7.00  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.71/7.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.71/7.00  
% 14.86/7.03  tff(f_163, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k3_orders_2(A, k1_struct_0(A), B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_orders_2)).
% 14.86/7.03  tff(f_70, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 14.86/7.03  tff(f_74, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 14.86/7.03  tff(f_116, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 14.86/7.03  tff(f_120, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 14.86/7.03  tff(f_84, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_struct_0)).
% 14.86/7.03  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_subset_1)).
% 14.86/7.03  tff(f_49, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 14.86/7.03  tff(f_146, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 14.86/7.03  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 14.86/7.03  tff(f_80, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 14.86/7.03  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.86/7.03  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 14.86/7.03  tff(f_99, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 14.86/7.03  tff(c_56, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 14.86/7.03  tff(c_26, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 14.86/7.03  tff(c_92, plain, (![A_57, B_58]: (r1_tarski(A_57, B_58) | ~m1_subset_1(A_57, k1_zfmisc_1(B_58)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 14.86/7.03  tff(c_105, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(resolution, [status(thm)], [c_26, c_92])).
% 14.86/7.03  tff(c_64, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 14.86/7.03  tff(c_62, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 14.86/7.03  tff(c_60, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 14.86/7.03  tff(c_58, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 14.86/7.03  tff(c_54, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 14.86/7.03  tff(c_42, plain, (![A_27, B_28, C_29]: (m1_subset_1(k3_orders_2(A_27, B_28, C_29), k1_zfmisc_1(u1_struct_0(A_27))) | ~m1_subset_1(C_29, u1_struct_0(A_27)) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_orders_2(A_27) | ~v5_orders_2(A_27) | ~v4_orders_2(A_27) | ~v3_orders_2(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_116])).
% 14.86/7.03  tff(c_44, plain, (![A_30]: (l1_struct_0(A_30) | ~l1_orders_2(A_30))), inference(cnfTransformation, [status(thm)], [f_120])).
% 14.86/7.03  tff(c_75, plain, (![A_51]: (k1_struct_0(A_51)=k1_xboole_0 | ~l1_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.86/7.03  tff(c_80, plain, (![A_52]: (k1_struct_0(A_52)=k1_xboole_0 | ~l1_orders_2(A_52))), inference(resolution, [status(thm)], [c_44, c_75])).
% 14.86/7.03  tff(c_84, plain, (k1_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_80])).
% 14.86/7.03  tff(c_52, plain, (k3_orders_2('#skF_2', k1_struct_0('#skF_2'), '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_163])).
% 14.86/7.03  tff(c_89, plain, (k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_84, c_52])).
% 14.86/7.03  tff(c_24, plain, (![A_10, B_11]: (m1_subset_1('#skF_1'(A_10, B_11), A_10) | k1_xboole_0=B_11 | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 14.86/7.03  tff(c_14, plain, (![B_5, A_4]: (r2_hidden(B_5, A_4) | ~m1_subset_1(B_5, A_4) | v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_49])).
% 14.86/7.03  tff(c_465, plain, (![B_130, D_131, A_132, C_133]: (r2_hidden(B_130, D_131) | ~r2_hidden(B_130, k3_orders_2(A_132, D_131, C_133)) | ~m1_subset_1(D_131, k1_zfmisc_1(u1_struct_0(A_132))) | ~m1_subset_1(C_133, u1_struct_0(A_132)) | ~m1_subset_1(B_130, u1_struct_0(A_132)) | ~l1_orders_2(A_132) | ~v5_orders_2(A_132) | ~v4_orders_2(A_132) | ~v3_orders_2(A_132) | v2_struct_0(A_132))), inference(cnfTransformation, [status(thm)], [f_146])).
% 14.86/7.03  tff(c_15315, plain, (![B_1070, D_1071, A_1072, C_1073]: (r2_hidden(B_1070, D_1071) | ~m1_subset_1(D_1071, k1_zfmisc_1(u1_struct_0(A_1072))) | ~m1_subset_1(C_1073, u1_struct_0(A_1072)) | ~m1_subset_1(B_1070, u1_struct_0(A_1072)) | ~l1_orders_2(A_1072) | ~v5_orders_2(A_1072) | ~v4_orders_2(A_1072) | ~v3_orders_2(A_1072) | v2_struct_0(A_1072) | ~m1_subset_1(B_1070, k3_orders_2(A_1072, D_1071, C_1073)) | v1_xboole_0(k3_orders_2(A_1072, D_1071, C_1073)))), inference(resolution, [status(thm)], [c_14, c_465])).
% 14.86/7.03  tff(c_21738, plain, (![B_1389, C_1390, A_1391]: (r2_hidden(B_1389, k1_xboole_0) | ~m1_subset_1(C_1390, u1_struct_0(A_1391)) | ~m1_subset_1(B_1389, u1_struct_0(A_1391)) | ~l1_orders_2(A_1391) | ~v5_orders_2(A_1391) | ~v4_orders_2(A_1391) | ~v3_orders_2(A_1391) | v2_struct_0(A_1391) | ~m1_subset_1(B_1389, k3_orders_2(A_1391, k1_xboole_0, C_1390)) | v1_xboole_0(k3_orders_2(A_1391, k1_xboole_0, C_1390)))), inference(resolution, [status(thm)], [c_26, c_15315])).
% 14.86/7.03  tff(c_21775, plain, (![B_1389]: (r2_hidden(B_1389, k1_xboole_0) | ~m1_subset_1(B_1389, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(B_1389, k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')) | v1_xboole_0(k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')))), inference(resolution, [status(thm)], [c_54, c_21738])).
% 14.86/7.03  tff(c_21793, plain, (![B_1389]: (r2_hidden(B_1389, k1_xboole_0) | ~m1_subset_1(B_1389, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(B_1389, k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')) | v1_xboole_0(k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_21775])).
% 14.86/7.03  tff(c_21794, plain, (![B_1389]: (r2_hidden(B_1389, k1_xboole_0) | ~m1_subset_1(B_1389, u1_struct_0('#skF_2')) | ~m1_subset_1(B_1389, k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')) | v1_xboole_0(k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_64, c_21793])).
% 14.86/7.03  tff(c_21795, plain, (v1_xboole_0(k3_orders_2('#skF_2', k1_xboole_0, '#skF_3'))), inference(splitLeft, [status(thm)], [c_21794])).
% 14.86/7.03  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 14.86/7.03  tff(c_21798, plain, (k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_21795, c_4])).
% 14.86/7.03  tff(c_21802, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_21798])).
% 14.86/7.03  tff(c_21804, plain, (~v1_xboole_0(k3_orders_2('#skF_2', k1_xboole_0, '#skF_3'))), inference(splitRight, [status(thm)], [c_21794])).
% 14.86/7.03  tff(c_197, plain, (![A_88, B_89]: (r2_hidden('#skF_1'(A_88, B_89), B_89) | k1_xboole_0=B_89 | ~m1_subset_1(B_89, k1_zfmisc_1(A_88)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 14.86/7.03  tff(c_12, plain, (![B_5, A_4]: (m1_subset_1(B_5, A_4) | ~r2_hidden(B_5, A_4) | v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_49])).
% 14.86/7.03  tff(c_214, plain, (![A_88, B_89]: (m1_subset_1('#skF_1'(A_88, B_89), B_89) | v1_xboole_0(B_89) | k1_xboole_0=B_89 | ~m1_subset_1(B_89, k1_zfmisc_1(A_88)))), inference(resolution, [status(thm)], [c_197, c_12])).
% 14.86/7.03  tff(c_24018, plain, (![B_1450]: (r2_hidden(B_1450, k1_xboole_0) | ~m1_subset_1(B_1450, u1_struct_0('#skF_2')) | ~m1_subset_1(B_1450, k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')))), inference(splitRight, [status(thm)], [c_21794])).
% 14.86/7.03  tff(c_24054, plain, (![A_88]: (r2_hidden('#skF_1'(A_88, k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')), k1_xboole_0) | ~m1_subset_1('#skF_1'(A_88, k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')), u1_struct_0('#skF_2')) | v1_xboole_0(k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')) | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', k1_xboole_0, '#skF_3'), k1_zfmisc_1(A_88)))), inference(resolution, [status(thm)], [c_214, c_24018])).
% 14.86/7.03  tff(c_24327, plain, (![A_1462]: (r2_hidden('#skF_1'(A_1462, k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')), k1_xboole_0) | ~m1_subset_1('#skF_1'(A_1462, k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')), u1_struct_0('#skF_2')) | ~m1_subset_1(k3_orders_2('#skF_2', k1_xboole_0, '#skF_3'), k1_zfmisc_1(A_1462)))), inference(negUnitSimplification, [status(thm)], [c_89, c_21804, c_24054])).
% 14.86/7.03  tff(c_24351, plain, (r2_hidden('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')), k1_xboole_0) | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', k1_xboole_0, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_24, c_24327])).
% 14.86/7.03  tff(c_24372, plain, (r2_hidden('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')), k1_xboole_0) | ~m1_subset_1(k3_orders_2('#skF_2', k1_xboole_0, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_89, c_24351])).
% 14.86/7.03  tff(c_24374, plain, (~m1_subset_1(k3_orders_2('#skF_2', k1_xboole_0, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_24372])).
% 14.86/7.03  tff(c_24377, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_24374])).
% 14.86/7.03  tff(c_24386, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_26, c_54, c_24377])).
% 14.86/7.03  tff(c_24388, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_24386])).
% 14.86/7.03  tff(c_24389, plain, (r2_hidden('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')), k1_xboole_0)), inference(splitRight, [status(thm)], [c_24372])).
% 14.86/7.03  tff(c_30, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_74])).
% 14.86/7.03  tff(c_157, plain, (![A_73, C_74, B_75]: (m1_subset_1(A_73, C_74) | ~m1_subset_1(B_75, k1_zfmisc_1(C_74)) | ~r2_hidden(A_73, B_75))), inference(cnfTransformation, [status(thm)], [f_80])).
% 14.86/7.03  tff(c_165, plain, (![A_73, B_15, A_14]: (m1_subset_1(A_73, B_15) | ~r2_hidden(A_73, A_14) | ~r1_tarski(A_14, B_15))), inference(resolution, [status(thm)], [c_30, c_157])).
% 14.86/7.03  tff(c_24613, plain, (![B_15]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')), B_15) | ~r1_tarski(k1_xboole_0, B_15))), inference(resolution, [status(thm)], [c_24389, c_165])).
% 14.86/7.03  tff(c_24712, plain, (![B_1467]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')), B_1467))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_24613])).
% 14.86/7.03  tff(c_28, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 14.86/7.03  tff(c_24993, plain, (![B_1468]: (r1_tarski('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')), B_1468))), inference(resolution, [status(thm)], [c_24712, c_28])).
% 14.86/7.03  tff(c_126, plain, (![B_62, A_63]: (B_62=A_63 | ~r1_tarski(B_62, A_63) | ~r1_tarski(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_36])).
% 14.86/7.03  tff(c_131, plain, (![A_13]: (k1_xboole_0=A_13 | ~r1_tarski(A_13, k1_xboole_0))), inference(resolution, [status(thm)], [c_105, c_126])).
% 14.86/7.03  tff(c_25133, plain, ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', k1_xboole_0, '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_24993, c_131])).
% 14.86/7.03  tff(c_24627, plain, (![B_15]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')), B_15))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_24613])).
% 14.86/7.03  tff(c_25137, plain, (![B_15]: (m1_subset_1(k1_xboole_0, B_15))), inference(demodulation, [status(thm), theory('equality')], [c_25133, c_24627])).
% 14.86/7.03  tff(c_183, plain, (![A_86, B_87]: (m1_subset_1('#skF_1'(A_86, B_87), A_86) | k1_xboole_0=B_87 | ~m1_subset_1(B_87, k1_zfmisc_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 14.86/7.03  tff(c_18, plain, (![B_5, A_4]: (v1_xboole_0(B_5) | ~m1_subset_1(B_5, A_4) | ~v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_49])).
% 14.86/7.03  tff(c_389, plain, (![A_122, B_123]: (v1_xboole_0('#skF_1'(A_122, B_123)) | ~v1_xboole_0(A_122) | k1_xboole_0=B_123 | ~m1_subset_1(B_123, k1_zfmisc_1(A_122)))), inference(resolution, [status(thm)], [c_183, c_18])).
% 14.86/7.03  tff(c_17101, plain, (![A_1193, B_1194]: (v1_xboole_0('#skF_1'(A_1193, '#skF_1'(k1_zfmisc_1(A_1193), B_1194))) | ~v1_xboole_0(A_1193) | '#skF_1'(k1_zfmisc_1(A_1193), B_1194)=k1_xboole_0 | k1_xboole_0=B_1194 | ~m1_subset_1(B_1194, k1_zfmisc_1(k1_zfmisc_1(A_1193))))), inference(resolution, [status(thm)], [c_24, c_389])).
% 14.86/7.03  tff(c_17164, plain, (![A_1200, B_1201]: ('#skF_1'(A_1200, '#skF_1'(k1_zfmisc_1(A_1200), B_1201))=k1_xboole_0 | ~v1_xboole_0(A_1200) | '#skF_1'(k1_zfmisc_1(A_1200), B_1201)=k1_xboole_0 | k1_xboole_0=B_1201 | ~m1_subset_1(B_1201, k1_zfmisc_1(k1_zfmisc_1(A_1200))))), inference(resolution, [status(thm)], [c_17101, c_4])).
% 14.86/7.03  tff(c_17221, plain, (![A_1202, A_1203]: ('#skF_1'(A_1202, '#skF_1'(k1_zfmisc_1(A_1202), A_1203))=k1_xboole_0 | ~v1_xboole_0(A_1202) | '#skF_1'(k1_zfmisc_1(A_1202), A_1203)=k1_xboole_0 | k1_xboole_0=A_1203 | ~r1_tarski(A_1203, k1_zfmisc_1(A_1202)))), inference(resolution, [status(thm)], [c_30, c_17164])).
% 14.86/7.03  tff(c_20, plain, (![C_9, A_6, B_7]: (r2_hidden(C_9, A_6) | ~r2_hidden(C_9, B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.86/7.03  tff(c_12406, plain, (![A_859, B_860, A_861]: (r2_hidden('#skF_1'(A_859, B_860), A_861) | ~m1_subset_1(B_860, k1_zfmisc_1(A_861)) | k1_xboole_0=B_860 | ~m1_subset_1(B_860, k1_zfmisc_1(A_859)))), inference(resolution, [status(thm)], [c_197, c_20])).
% 14.86/7.03  tff(c_167, plain, (![A_73, A_13]: (m1_subset_1(A_73, A_13) | ~r2_hidden(A_73, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_157])).
% 14.86/7.03  tff(c_12647, plain, (![A_888, B_889, A_890]: (m1_subset_1('#skF_1'(A_888, B_889), A_890) | ~m1_subset_1(B_889, k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0=B_889 | ~m1_subset_1(B_889, k1_zfmisc_1(A_888)))), inference(resolution, [status(thm)], [c_12406, c_167])).
% 14.86/7.03  tff(c_247, plain, (![A_102, B_103, C_104]: (r2_orders_2(A_102, B_103, C_104) | C_104=B_103 | ~r1_orders_2(A_102, B_103, C_104) | ~m1_subset_1(C_104, u1_struct_0(A_102)) | ~m1_subset_1(B_103, u1_struct_0(A_102)) | ~l1_orders_2(A_102))), inference(cnfTransformation, [status(thm)], [f_99])).
% 14.86/7.03  tff(c_255, plain, (![B_103]: (r2_orders_2('#skF_2', B_103, '#skF_3') | B_103='#skF_3' | ~r1_orders_2('#skF_2', B_103, '#skF_3') | ~m1_subset_1(B_103, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_247])).
% 14.86/7.03  tff(c_260, plain, (![B_103]: (r2_orders_2('#skF_2', B_103, '#skF_3') | B_103='#skF_3' | ~r1_orders_2('#skF_2', B_103, '#skF_3') | ~m1_subset_1(B_103, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_255])).
% 14.86/7.03  tff(c_12687, plain, (![A_888, B_889]: (r2_orders_2('#skF_2', '#skF_1'(A_888, B_889), '#skF_3') | '#skF_1'(A_888, B_889)='#skF_3' | ~r1_orders_2('#skF_2', '#skF_1'(A_888, B_889), '#skF_3') | ~m1_subset_1(B_889, k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0=B_889 | ~m1_subset_1(B_889, k1_zfmisc_1(A_888)))), inference(resolution, [status(thm)], [c_12647, c_260])).
% 14.86/7.03  tff(c_17338, plain, (![A_1202, A_1203]: (r2_orders_2('#skF_2', k1_xboole_0, '#skF_3') | '#skF_1'(A_1202, '#skF_1'(k1_zfmisc_1(A_1202), A_1203))='#skF_3' | ~r1_orders_2('#skF_2', '#skF_1'(A_1202, '#skF_1'(k1_zfmisc_1(A_1202), A_1203)), '#skF_3') | ~m1_subset_1('#skF_1'(k1_zfmisc_1(A_1202), A_1203), k1_zfmisc_1(k1_xboole_0)) | '#skF_1'(k1_zfmisc_1(A_1202), A_1203)=k1_xboole_0 | ~m1_subset_1('#skF_1'(k1_zfmisc_1(A_1202), A_1203), k1_zfmisc_1(A_1202)) | ~v1_xboole_0(A_1202) | '#skF_1'(k1_zfmisc_1(A_1202), A_1203)=k1_xboole_0 | k1_xboole_0=A_1203 | ~r1_tarski(A_1203, k1_zfmisc_1(A_1202)))), inference(superposition, [status(thm), theory('equality')], [c_17221, c_12687])).
% 14.86/7.03  tff(c_17499, plain, (r2_orders_2('#skF_2', k1_xboole_0, '#skF_3')), inference(splitLeft, [status(thm)], [c_17338])).
% 14.86/7.03  tff(c_40, plain, (![A_20, B_24, C_26]: (r1_orders_2(A_20, B_24, C_26) | ~r2_orders_2(A_20, B_24, C_26) | ~m1_subset_1(C_26, u1_struct_0(A_20)) | ~m1_subset_1(B_24, u1_struct_0(A_20)) | ~l1_orders_2(A_20))), inference(cnfTransformation, [status(thm)], [f_99])).
% 14.86/7.03  tff(c_17501, plain, (r1_orders_2('#skF_2', k1_xboole_0, '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(k1_xboole_0, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_17499, c_40])).
% 14.86/7.03  tff(c_17504, plain, (r1_orders_2('#skF_2', k1_xboole_0, '#skF_3') | ~m1_subset_1(k1_xboole_0, u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_17501])).
% 14.86/7.03  tff(c_17505, plain, (~m1_subset_1(k1_xboole_0, u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_17504])).
% 14.86/7.03  tff(c_10, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 14.86/7.03  tff(c_209, plain, (![A_88, B_89, B_15]: (m1_subset_1('#skF_1'(A_88, B_89), B_15) | ~r1_tarski(B_89, B_15) | k1_xboole_0=B_89 | ~m1_subset_1(B_89, k1_zfmisc_1(A_88)))), inference(resolution, [status(thm)], [c_197, c_165])).
% 14.86/7.03  tff(c_19171, plain, (![B_1293, C_1294, A_1295]: (r2_hidden(B_1293, k1_xboole_0) | ~m1_subset_1(C_1294, u1_struct_0(A_1295)) | ~m1_subset_1(B_1293, u1_struct_0(A_1295)) | ~l1_orders_2(A_1295) | ~v5_orders_2(A_1295) | ~v4_orders_2(A_1295) | ~v3_orders_2(A_1295) | v2_struct_0(A_1295) | ~m1_subset_1(B_1293, k3_orders_2(A_1295, k1_xboole_0, C_1294)) | v1_xboole_0(k3_orders_2(A_1295, k1_xboole_0, C_1294)))), inference(resolution, [status(thm)], [c_26, c_15315])).
% 14.86/7.03  tff(c_19206, plain, (![B_1293]: (r2_hidden(B_1293, k1_xboole_0) | ~m1_subset_1(B_1293, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(B_1293, k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')) | v1_xboole_0(k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')))), inference(resolution, [status(thm)], [c_54, c_19171])).
% 14.86/7.03  tff(c_19220, plain, (![B_1293]: (r2_hidden(B_1293, k1_xboole_0) | ~m1_subset_1(B_1293, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(B_1293, k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')) | v1_xboole_0(k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_19206])).
% 14.86/7.03  tff(c_19221, plain, (![B_1293]: (r2_hidden(B_1293, k1_xboole_0) | ~m1_subset_1(B_1293, u1_struct_0('#skF_2')) | ~m1_subset_1(B_1293, k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')) | v1_xboole_0(k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_64, c_19220])).
% 14.86/7.03  tff(c_19222, plain, (v1_xboole_0(k3_orders_2('#skF_2', k1_xboole_0, '#skF_3'))), inference(splitLeft, [status(thm)], [c_19221])).
% 14.86/7.03  tff(c_19225, plain, (k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_19222, c_4])).
% 14.86/7.03  tff(c_19229, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_19225])).
% 14.86/7.03  tff(c_19232, plain, (![B_1296]: (r2_hidden(B_1296, k1_xboole_0) | ~m1_subset_1(B_1296, u1_struct_0('#skF_2')) | ~m1_subset_1(B_1296, k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')))), inference(splitRight, [status(thm)], [c_19221])).
% 14.86/7.03  tff(c_19290, plain, (![A_1297, B_1298]: (r2_hidden('#skF_1'(A_1297, B_1298), k1_xboole_0) | ~m1_subset_1('#skF_1'(A_1297, B_1298), u1_struct_0('#skF_2')) | ~r1_tarski(B_1298, k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')) | k1_xboole_0=B_1298 | ~m1_subset_1(B_1298, k1_zfmisc_1(A_1297)))), inference(resolution, [status(thm)], [c_209, c_19232])).
% 14.86/7.03  tff(c_19365, plain, (![B_1299]: (r2_hidden('#skF_1'(u1_struct_0('#skF_2'), B_1299), k1_xboole_0) | ~r1_tarski(B_1299, k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')) | k1_xboole_0=B_1299 | ~m1_subset_1(B_1299, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_24, c_19290])).
% 14.86/7.03  tff(c_19371, plain, (![B_1299, B_15]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_1299), B_15) | ~r1_tarski(k1_xboole_0, B_15) | ~r1_tarski(B_1299, k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')) | k1_xboole_0=B_1299 | ~m1_subset_1(B_1299, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_19365, c_165])).
% 14.86/7.03  tff(c_19594, plain, (![B_1306, B_1307]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_1306), B_1307) | ~r1_tarski(B_1306, k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')) | k1_xboole_0=B_1306 | ~m1_subset_1(B_1306, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_19371])).
% 14.86/7.03  tff(c_19956, plain, (![B_1315, B_1316]: (r1_tarski('#skF_1'(u1_struct_0('#skF_2'), B_1315), B_1316) | ~r1_tarski(B_1315, k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')) | k1_xboole_0=B_1315 | ~m1_subset_1(B_1315, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_19594, c_28])).
% 14.86/7.03  tff(c_20091, plain, (![B_1317]: ('#skF_1'(u1_struct_0('#skF_2'), B_1317)=k1_xboole_0 | ~r1_tarski(B_1317, k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')) | k1_xboole_0=B_1317 | ~m1_subset_1(B_1317, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_19956, c_131])).
% 14.86/7.03  tff(c_20135, plain, (![B_28, C_29]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_28, C_29))=k1_xboole_0 | ~r1_tarski(k3_orders_2('#skF_2', B_28, C_29), k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')) | k3_orders_2('#skF_2', B_28, C_29)=k1_xboole_0 | ~m1_subset_1(C_29, u1_struct_0('#skF_2')) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_20091])).
% 14.86/7.03  tff(c_20166, plain, (![B_28, C_29]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_28, C_29))=k1_xboole_0 | ~r1_tarski(k3_orders_2('#skF_2', B_28, C_29), k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')) | k3_orders_2('#skF_2', B_28, C_29)=k1_xboole_0 | ~m1_subset_1(C_29, u1_struct_0('#skF_2')) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_20135])).
% 14.86/7.03  tff(c_20175, plain, (![B_1318, C_1319]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_1318, C_1319))=k1_xboole_0 | ~r1_tarski(k3_orders_2('#skF_2', B_1318, C_1319), k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')) | k3_orders_2('#skF_2', B_1318, C_1319)=k1_xboole_0 | ~m1_subset_1(C_1319, u1_struct_0('#skF_2')) | ~m1_subset_1(B_1318, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_20166])).
% 14.86/7.03  tff(c_20179, plain, ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', k1_xboole_0, '#skF_3'))=k1_xboole_0 | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0 | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_10, c_20175])).
% 14.86/7.03  tff(c_20182, plain, ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', k1_xboole_0, '#skF_3'))=k1_xboole_0 | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_54, c_20179])).
% 14.86/7.03  tff(c_20183, plain, ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', k1_xboole_0, '#skF_3'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_89, c_20182])).
% 14.86/7.03  tff(c_20320, plain, (m1_subset_1(k1_xboole_0, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', k1_xboole_0, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_20183, c_24])).
% 14.86/7.03  tff(c_20416, plain, (~m1_subset_1(k3_orders_2('#skF_2', k1_xboole_0, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_89, c_17505, c_20320])).
% 14.86/7.03  tff(c_20420, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_20416])).
% 14.86/7.03  tff(c_20429, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_26, c_54, c_20420])).
% 14.86/7.03  tff(c_20431, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_20429])).
% 14.86/7.03  tff(c_20433, plain, (m1_subset_1(k1_xboole_0, u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_17504])).
% 14.86/7.03  tff(c_21743, plain, (![B_1389]: (r2_hidden(B_1389, k1_xboole_0) | ~m1_subset_1(B_1389, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(B_1389, k3_orders_2('#skF_2', k1_xboole_0, k1_xboole_0)) | v1_xboole_0(k3_orders_2('#skF_2', k1_xboole_0, k1_xboole_0)))), inference(resolution, [status(thm)], [c_20433, c_21738])).
% 14.86/7.03  tff(c_21779, plain, (![B_1389]: (r2_hidden(B_1389, k1_xboole_0) | ~m1_subset_1(B_1389, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(B_1389, k3_orders_2('#skF_2', k1_xboole_0, k1_xboole_0)) | v1_xboole_0(k3_orders_2('#skF_2', k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_21743])).
% 14.86/7.03  tff(c_21780, plain, (![B_1389]: (r2_hidden(B_1389, k1_xboole_0) | ~m1_subset_1(B_1389, u1_struct_0('#skF_2')) | ~m1_subset_1(B_1389, k3_orders_2('#skF_2', k1_xboole_0, k1_xboole_0)) | v1_xboole_0(k3_orders_2('#skF_2', k1_xboole_0, k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_64, c_21779])).
% 14.86/7.03  tff(c_21805, plain, (v1_xboole_0(k3_orders_2('#skF_2', k1_xboole_0, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_21780])).
% 14.86/7.03  tff(c_21809, plain, (k3_orders_2('#skF_2', k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_21805, c_4])).
% 14.86/7.03  tff(c_50, plain, (![A_31, B_39, C_43, D_45]: (r2_orders_2(A_31, B_39, C_43) | ~r2_hidden(B_39, k3_orders_2(A_31, D_45, C_43)) | ~m1_subset_1(D_45, k1_zfmisc_1(u1_struct_0(A_31))) | ~m1_subset_1(C_43, u1_struct_0(A_31)) | ~m1_subset_1(B_39, u1_struct_0(A_31)) | ~l1_orders_2(A_31) | ~v5_orders_2(A_31) | ~v4_orders_2(A_31) | ~v3_orders_2(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_146])).
% 14.86/7.03  tff(c_21838, plain, (![B_39]: (r2_orders_2('#skF_2', B_39, k1_xboole_0) | ~r2_hidden(B_39, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_xboole_0, u1_struct_0('#skF_2')) | ~m1_subset_1(B_39, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_21809, c_50])).
% 14.86/7.03  tff(c_21873, plain, (![B_39]: (r2_orders_2('#skF_2', B_39, k1_xboole_0) | ~r2_hidden(B_39, k1_xboole_0) | ~m1_subset_1(B_39, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_20433, c_26, c_21838])).
% 14.86/7.03  tff(c_21882, plain, (![B_1392]: (r2_orders_2('#skF_2', B_1392, k1_xboole_0) | ~r2_hidden(B_1392, k1_xboole_0) | ~m1_subset_1(B_1392, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_64, c_21873])).
% 14.86/7.03  tff(c_21934, plain, (r2_orders_2('#skF_2', k1_xboole_0, k1_xboole_0) | ~r2_hidden(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_20433, c_21882])).
% 14.86/7.03  tff(c_21948, plain, (~r2_hidden(k1_xboole_0, k1_xboole_0)), inference(splitLeft, [status(thm)], [c_21934])).
% 14.86/7.03  tff(c_317, plain, (![A_111, B_112, C_113]: (m1_subset_1(k3_orders_2(A_111, B_112, C_113), k1_zfmisc_1(u1_struct_0(A_111))) | ~m1_subset_1(C_113, u1_struct_0(A_111)) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_orders_2(A_111) | ~v5_orders_2(A_111) | ~v4_orders_2(A_111) | ~v3_orders_2(A_111) | v2_struct_0(A_111))), inference(cnfTransformation, [status(thm)], [f_116])).
% 14.86/7.03  tff(c_32, plain, (![A_16, C_18, B_17]: (m1_subset_1(A_16, C_18) | ~m1_subset_1(B_17, k1_zfmisc_1(C_18)) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_80])).
% 14.86/7.03  tff(c_13542, plain, (![A_945, A_946, B_947, C_948]: (m1_subset_1(A_945, u1_struct_0(A_946)) | ~r2_hidden(A_945, k3_orders_2(A_946, B_947, C_948)) | ~m1_subset_1(C_948, u1_struct_0(A_946)) | ~m1_subset_1(B_947, k1_zfmisc_1(u1_struct_0(A_946))) | ~l1_orders_2(A_946) | ~v5_orders_2(A_946) | ~v4_orders_2(A_946) | ~v3_orders_2(A_946) | v2_struct_0(A_946))), inference(resolution, [status(thm)], [c_317, c_32])).
% 14.86/7.03  tff(c_22526, plain, (![B_1425, A_1426, C_1427, B_1428]: (m1_subset_1(B_1425, u1_struct_0(A_1426)) | ~m1_subset_1(C_1427, u1_struct_0(A_1426)) | ~m1_subset_1(B_1428, k1_zfmisc_1(u1_struct_0(A_1426))) | ~l1_orders_2(A_1426) | ~v5_orders_2(A_1426) | ~v4_orders_2(A_1426) | ~v3_orders_2(A_1426) | v2_struct_0(A_1426) | ~m1_subset_1(B_1425, k3_orders_2(A_1426, B_1428, C_1427)) | v1_xboole_0(k3_orders_2(A_1426, B_1428, C_1427)))), inference(resolution, [status(thm)], [c_14, c_13542])).
% 14.86/7.03  tff(c_22563, plain, (![B_1425, B_1428]: (m1_subset_1(B_1425, u1_struct_0('#skF_2')) | ~m1_subset_1(B_1428, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(B_1425, k3_orders_2('#skF_2', B_1428, '#skF_3')) | v1_xboole_0(k3_orders_2('#skF_2', B_1428, '#skF_3')))), inference(resolution, [status(thm)], [c_54, c_22526])).
% 14.86/7.03  tff(c_22581, plain, (![B_1425, B_1428]: (m1_subset_1(B_1425, u1_struct_0('#skF_2')) | ~m1_subset_1(B_1428, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | ~m1_subset_1(B_1425, k3_orders_2('#skF_2', B_1428, '#skF_3')) | v1_xboole_0(k3_orders_2('#skF_2', B_1428, '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_22563])).
% 14.86/7.03  tff(c_22583, plain, (![B_1429, B_1430]: (m1_subset_1(B_1429, u1_struct_0('#skF_2')) | ~m1_subset_1(B_1430, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_1429, k3_orders_2('#skF_2', B_1430, '#skF_3')) | v1_xboole_0(k3_orders_2('#skF_2', B_1430, '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_64, c_22581])).
% 14.86/7.03  tff(c_22625, plain, (![B_1429]: (m1_subset_1(B_1429, u1_struct_0('#skF_2')) | ~m1_subset_1(B_1429, k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')) | v1_xboole_0(k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')))), inference(resolution, [status(thm)], [c_26, c_22583])).
% 14.86/7.03  tff(c_22647, plain, (![B_1431]: (m1_subset_1(B_1431, u1_struct_0('#skF_2')) | ~m1_subset_1(B_1431, k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_21804, c_22625])).
% 14.86/7.03  tff(c_22683, plain, (![A_88]: (m1_subset_1('#skF_1'(A_88, k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')), u1_struct_0('#skF_2')) | v1_xboole_0(k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')) | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', k1_xboole_0, '#skF_3'), k1_zfmisc_1(A_88)))), inference(resolution, [status(thm)], [c_214, c_22647])).
% 14.86/7.03  tff(c_22705, plain, (![A_1432]: (m1_subset_1('#skF_1'(A_1432, k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')), u1_struct_0('#skF_2')) | ~m1_subset_1(k3_orders_2('#skF_2', k1_xboole_0, '#skF_3'), k1_zfmisc_1(A_1432)))), inference(negUnitSimplification, [status(thm)], [c_89, c_21804, c_22683])).
% 14.86/7.03  tff(c_22, plain, (![A_10, B_11]: (r2_hidden('#skF_1'(A_10, B_11), B_11) | k1_xboole_0=B_11 | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 14.86/7.03  tff(c_472, plain, (![A_10, A_132, D_131, C_133]: (r2_hidden('#skF_1'(A_10, k3_orders_2(A_132, D_131, C_133)), D_131) | ~m1_subset_1(D_131, k1_zfmisc_1(u1_struct_0(A_132))) | ~m1_subset_1(C_133, u1_struct_0(A_132)) | ~m1_subset_1('#skF_1'(A_10, k3_orders_2(A_132, D_131, C_133)), u1_struct_0(A_132)) | ~l1_orders_2(A_132) | ~v5_orders_2(A_132) | ~v4_orders_2(A_132) | ~v3_orders_2(A_132) | v2_struct_0(A_132) | k3_orders_2(A_132, D_131, C_133)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_132, D_131, C_133), k1_zfmisc_1(A_10)))), inference(resolution, [status(thm)], [c_22, c_465])).
% 14.86/7.03  tff(c_22721, plain, (![A_1432]: (r2_hidden('#skF_1'(A_1432, k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')), k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', k1_xboole_0, '#skF_3'), k1_zfmisc_1(A_1432)))), inference(resolution, [status(thm)], [c_22705, c_472])).
% 14.86/7.03  tff(c_22756, plain, (![A_1432]: (r2_hidden('#skF_1'(A_1432, k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')), k1_xboole_0) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', k1_xboole_0, '#skF_3'), k1_zfmisc_1(A_1432)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_54, c_26, c_22721])).
% 14.86/7.03  tff(c_22773, plain, (![A_1433]: (r2_hidden('#skF_1'(A_1433, k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')), k1_xboole_0) | ~m1_subset_1(k3_orders_2('#skF_2', k1_xboole_0, '#skF_3'), k1_zfmisc_1(A_1433)))), inference(negUnitSimplification, [status(thm)], [c_89, c_64, c_22756])).
% 14.86/7.03  tff(c_22779, plain, (![A_1433, B_15]: (m1_subset_1('#skF_1'(A_1433, k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')), B_15) | ~r1_tarski(k1_xboole_0, B_15) | ~m1_subset_1(k3_orders_2('#skF_2', k1_xboole_0, '#skF_3'), k1_zfmisc_1(A_1433)))), inference(resolution, [status(thm)], [c_22773, c_165])).
% 14.86/7.03  tff(c_22875, plain, (![A_1436, B_1437]: (m1_subset_1('#skF_1'(A_1436, k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')), B_1437) | ~m1_subset_1(k3_orders_2('#skF_2', k1_xboole_0, '#skF_3'), k1_zfmisc_1(A_1436)))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_22779])).
% 14.86/7.03  tff(c_23115, plain, (![A_1438, B_1439]: (r1_tarski('#skF_1'(A_1438, k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')), B_1439) | ~m1_subset_1(k3_orders_2('#skF_2', k1_xboole_0, '#skF_3'), k1_zfmisc_1(A_1438)))), inference(resolution, [status(thm)], [c_22875, c_28])).
% 14.86/7.03  tff(c_23289, plain, (![A_1444]: ('#skF_1'(A_1444, k3_orders_2('#skF_2', k1_xboole_0, '#skF_3'))=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', k1_xboole_0, '#skF_3'), k1_zfmisc_1(A_1444)))), inference(resolution, [status(thm)], [c_23115, c_131])).
% 14.86/7.03  tff(c_23293, plain, ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', k1_xboole_0, '#skF_3'))=k1_xboole_0 | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_23289])).
% 14.86/7.03  tff(c_23303, plain, ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', k1_xboole_0, '#skF_3'))=k1_xboole_0 | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_26, c_54, c_23293])).
% 14.86/7.03  tff(c_23304, plain, ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', k1_xboole_0, '#skF_3'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_64, c_23303])).
% 14.86/7.03  tff(c_23362, plain, (r2_hidden('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')), k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(k1_xboole_0, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', k1_xboole_0, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_23304, c_472])).
% 14.86/7.03  tff(c_23493, plain, (r2_hidden(k1_xboole_0, k1_xboole_0) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', k1_xboole_0, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_20433, c_54, c_26, c_23304, c_23362])).
% 14.86/7.03  tff(c_23494, plain, (~m1_subset_1(k3_orders_2('#skF_2', k1_xboole_0, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_89, c_64, c_21948, c_23493])).
% 14.86/7.03  tff(c_23555, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_23494])).
% 14.86/7.03  tff(c_23564, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_26, c_54, c_23555])).
% 14.86/7.03  tff(c_23566, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_23564])).
% 14.86/7.03  tff(c_23568, plain, (r2_hidden(k1_xboole_0, k1_xboole_0)), inference(splitRight, [status(thm)], [c_21934])).
% 14.86/7.03  tff(c_23575, plain, (![B_15]: (m1_subset_1(k1_xboole_0, B_15) | ~r1_tarski(k1_xboole_0, B_15))), inference(resolution, [status(thm)], [c_23568, c_165])).
% 14.86/7.03  tff(c_23589, plain, (![B_15]: (m1_subset_1(k1_xboole_0, B_15))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_23575])).
% 14.86/7.03  tff(c_23567, plain, (r2_orders_2('#skF_2', k1_xboole_0, k1_xboole_0)), inference(splitRight, [status(thm)], [c_21934])).
% 14.86/7.03  tff(c_38, plain, (![A_20, C_26]: (~r2_orders_2(A_20, C_26, C_26) | ~m1_subset_1(C_26, u1_struct_0(A_20)) | ~l1_orders_2(A_20))), inference(cnfTransformation, [status(thm)], [f_99])).
% 14.86/7.03  tff(c_24008, plain, (~m1_subset_1(k1_xboole_0, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_23567, c_38])).
% 14.86/7.03  tff(c_24015, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_23589, c_24008])).
% 14.86/7.03  tff(c_24017, plain, (~v1_xboole_0(k3_orders_2('#skF_2', k1_xboole_0, k1_xboole_0))), inference(splitRight, [status(thm)], [c_21780])).
% 14.86/7.03  tff(c_12161, plain, (![A_837, B_838, C_839, D_840]: (r2_orders_2(A_837, B_838, C_839) | ~r2_hidden(B_838, k3_orders_2(A_837, D_840, C_839)) | ~m1_subset_1(D_840, k1_zfmisc_1(u1_struct_0(A_837))) | ~m1_subset_1(C_839, u1_struct_0(A_837)) | ~m1_subset_1(B_838, u1_struct_0(A_837)) | ~l1_orders_2(A_837) | ~v5_orders_2(A_837) | ~v4_orders_2(A_837) | ~v3_orders_2(A_837) | v2_struct_0(A_837))), inference(cnfTransformation, [status(thm)], [f_146])).
% 14.86/7.03  tff(c_15648, plain, (![A_1095, B_1096, C_1097, D_1098]: (r2_orders_2(A_1095, B_1096, C_1097) | ~m1_subset_1(D_1098, k1_zfmisc_1(u1_struct_0(A_1095))) | ~m1_subset_1(C_1097, u1_struct_0(A_1095)) | ~m1_subset_1(B_1096, u1_struct_0(A_1095)) | ~l1_orders_2(A_1095) | ~v5_orders_2(A_1095) | ~v4_orders_2(A_1095) | ~v3_orders_2(A_1095) | v2_struct_0(A_1095) | ~m1_subset_1(B_1096, k3_orders_2(A_1095, D_1098, C_1097)) | v1_xboole_0(k3_orders_2(A_1095, D_1098, C_1097)))), inference(resolution, [status(thm)], [c_14, c_12161])).
% 14.86/7.03  tff(c_24551, plain, (![A_1463, B_1464, C_1465]: (r2_orders_2(A_1463, B_1464, C_1465) | ~m1_subset_1(C_1465, u1_struct_0(A_1463)) | ~m1_subset_1(B_1464, u1_struct_0(A_1463)) | ~l1_orders_2(A_1463) | ~v5_orders_2(A_1463) | ~v4_orders_2(A_1463) | ~v3_orders_2(A_1463) | v2_struct_0(A_1463) | ~m1_subset_1(B_1464, k3_orders_2(A_1463, k1_xboole_0, C_1465)) | v1_xboole_0(k3_orders_2(A_1463, k1_xboole_0, C_1465)))), inference(resolution, [status(thm)], [c_26, c_15648])).
% 14.86/7.03  tff(c_24556, plain, (![B_1464]: (r2_orders_2('#skF_2', B_1464, k1_xboole_0) | ~m1_subset_1(B_1464, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(B_1464, k3_orders_2('#skF_2', k1_xboole_0, k1_xboole_0)) | v1_xboole_0(k3_orders_2('#skF_2', k1_xboole_0, k1_xboole_0)))), inference(resolution, [status(thm)], [c_20433, c_24551])).
% 14.86/7.03  tff(c_24592, plain, (![B_1464]: (r2_orders_2('#skF_2', B_1464, k1_xboole_0) | ~m1_subset_1(B_1464, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(B_1464, k3_orders_2('#skF_2', k1_xboole_0, k1_xboole_0)) | v1_xboole_0(k3_orders_2('#skF_2', k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_24556])).
% 14.86/7.03  tff(c_26140, plain, (![B_1486]: (r2_orders_2('#skF_2', B_1486, k1_xboole_0) | ~m1_subset_1(B_1486, u1_struct_0('#skF_2')) | ~m1_subset_1(B_1486, k3_orders_2('#skF_2', k1_xboole_0, k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_24017, c_64, c_24592])).
% 14.86/7.03  tff(c_26144, plain, (r2_orders_2('#skF_2', k1_xboole_0, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_25137, c_26140])).
% 14.86/7.03  tff(c_26191, plain, (r2_orders_2('#skF_2', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_25137, c_26144])).
% 14.86/7.03  tff(c_26208, plain, (~m1_subset_1(k1_xboole_0, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_26191, c_38])).
% 14.86/7.03  tff(c_26215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_25137, c_26208])).
% 14.86/7.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.86/7.03  
% 14.86/7.03  Inference rules
% 14.86/7.03  ----------------------
% 14.86/7.03  #Ref     : 0
% 14.86/7.03  #Sup     : 5864
% 14.86/7.03  #Fact    : 0
% 14.86/7.03  #Define  : 0
% 14.86/7.03  #Split   : 47
% 14.86/7.03  #Chain   : 0
% 14.86/7.03  #Close   : 0
% 14.86/7.03  
% 14.86/7.03  Ordering : KBO
% 14.86/7.03  
% 14.86/7.03  Simplification rules
% 14.86/7.03  ----------------------
% 14.86/7.03  #Subsume      : 1711
% 14.86/7.03  #Demod        : 2865
% 14.86/7.03  #Tautology    : 1052
% 14.86/7.03  #SimpNegUnit  : 768
% 14.86/7.03  #BackRed      : 93
% 14.86/7.03  
% 14.86/7.03  #Partial instantiations: 0
% 14.86/7.03  #Strategies tried      : 1
% 14.86/7.03  
% 14.86/7.03  Timing (in seconds)
% 14.86/7.03  ----------------------
% 14.86/7.03  Preprocessing        : 0.33
% 14.86/7.03  Parsing              : 0.18
% 14.86/7.03  CNF conversion       : 0.03
% 14.86/7.03  Main loop            : 5.91
% 14.86/7.03  Inferencing          : 1.07
% 14.86/7.03  Reduction            : 1.23
% 14.86/7.03  Demodulation         : 0.81
% 14.86/7.03  BG Simplification    : 0.12
% 14.86/7.03  Subsumption          : 3.16
% 14.86/7.03  Abstraction          : 0.19
% 14.86/7.03  MUC search           : 0.00
% 14.86/7.03  Cooper               : 0.00
% 14.86/7.03  Total                : 6.31
% 14.86/7.03  Index Insertion      : 0.00
% 14.86/7.03  Index Deletion       : 0.00
% 14.86/7.03  Index Matching       : 0.00
% 14.86/7.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
