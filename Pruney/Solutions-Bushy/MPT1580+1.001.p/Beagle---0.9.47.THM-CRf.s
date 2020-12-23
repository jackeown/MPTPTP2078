%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1580+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:06 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   52 (  91 expanded)
%              Number of leaves         :   25 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :   89 ( 227 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_yellow_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(m1_yellow_0,type,(
    m1_yellow_0: ( $i * $i ) > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_yellow_0(B,A) )
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(B))
               => m1_subset_1(C,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_yellow_0)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_yellow_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_0)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ( m1_yellow_0(B,A)
          <=> ( r1_tarski(u1_struct_0(B),u1_struct_0(A))
              & r1_tarski(u1_orders_2(B),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_yellow_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_54,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_30,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_26,plain,(
    m1_yellow_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_34,plain,(
    ! [B_21,A_22] :
      ( l1_orders_2(B_21)
      | ~ m1_yellow_0(B_21,A_22)
      | ~ l1_orders_2(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_37,plain,
    ( l1_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_34])).

tff(c_40,plain,(
    l1_orders_2('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_37])).

tff(c_8,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_6,plain,(
    ! [B_3,A_1] :
      ( r1_tarski(u1_struct_0(B_3),u1_struct_0(A_1))
      | ~ m1_yellow_0(B_3,A_1)
      | ~ l1_orders_2(B_3)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( r2_hidden(A_9,B_10)
      | v1_xboole_0(B_10)
      | ~ m1_subset_1(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_49,plain,(
    ! [A_30,C_31,B_32] :
      ( m1_subset_1(A_30,C_31)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(C_31))
      | ~ r2_hidden(A_30,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_53,plain,(
    ! [A_33,B_34,A_35] :
      ( m1_subset_1(A_33,B_34)
      | ~ r2_hidden(A_33,A_35)
      | ~ r1_tarski(A_35,B_34) ) ),
    inference(resolution,[status(thm)],[c_18,c_49])).

tff(c_58,plain,(
    ! [A_38,B_39,B_40] :
      ( m1_subset_1(A_38,B_39)
      | ~ r1_tarski(B_40,B_39)
      | v1_xboole_0(B_40)
      | ~ m1_subset_1(A_38,B_40) ) ),
    inference(resolution,[status(thm)],[c_14,c_53])).

tff(c_72,plain,(
    ! [A_48,A_49,B_50] :
      ( m1_subset_1(A_48,u1_struct_0(A_49))
      | v1_xboole_0(u1_struct_0(B_50))
      | ~ m1_subset_1(A_48,u1_struct_0(B_50))
      | ~ m1_yellow_0(B_50,A_49)
      | ~ l1_orders_2(B_50)
      | ~ l1_orders_2(A_49) ) ),
    inference(resolution,[status(thm)],[c_6,c_58])).

tff(c_74,plain,(
    ! [A_49] :
      ( m1_subset_1('#skF_3',u1_struct_0(A_49))
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ m1_yellow_0('#skF_2',A_49)
      | ~ l1_orders_2('#skF_2')
      | ~ l1_orders_2(A_49) ) ),
    inference(resolution,[status(thm)],[c_24,c_72])).

tff(c_77,plain,(
    ! [A_49] :
      ( m1_subset_1('#skF_3',u1_struct_0(A_49))
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ m1_yellow_0('#skF_2',A_49)
      | ~ l1_orders_2(A_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_74])).

tff(c_78,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_12,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(u1_struct_0(A_8))
      | ~ l1_struct_0(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_81,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_12])).

tff(c_84,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_81])).

tff(c_87,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_84])).

tff(c_91,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_87])).

tff(c_94,plain,(
    ! [A_51] :
      ( m1_subset_1('#skF_3',u1_struct_0(A_51))
      | ~ m1_yellow_0('#skF_2',A_51)
      | ~ l1_orders_2(A_51) ) ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_22,plain,(
    ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_99,plain,
    ( ~ m1_yellow_0('#skF_2','#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_94,c_22])).

tff(c_104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_99])).

%------------------------------------------------------------------------------
