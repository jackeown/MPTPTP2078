%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1567+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:04 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 107 expanded)
%              Number of leaves         :   26 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :   91 ( 284 expanded)
%              Number of equality atoms :    5 (  22 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_yellow_0 > r1_yellow_0 > m1_subset_1 > v5_orders_2 > v2_yellow_0 > v2_struct_0 > l1_orders_2 > k2_yellow_0 > #nlpp > u1_struct_0 > k4_yellow_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff(v2_yellow_0,type,(
    v2_yellow_0: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k2_yellow_0,type,(
    k2_yellow_0: ( $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k4_yellow_0,type,(
    k4_yellow_0: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v5_orders_2(A)
          & v2_yellow_0(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => r1_orders_2(A,B,k4_yellow_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_yellow_0)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( r2_lattice3(A,k1_xboole_0,B)
            & r1_lattice3(A,k1_xboole_0,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v2_yellow_0(A)
        & l1_orders_2(A) )
     => ( r2_yellow_0(A,k1_xboole_0)
        & r1_yellow_0(A,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_yellow_0)).

tff(f_28,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k4_yellow_0(A) = k2_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_yellow_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k2_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_0)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( ( B = k2_yellow_0(A,C)
                  & r2_yellow_0(A,C) )
               => ( r1_lattice3(A,C,B)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r1_lattice3(A,C,D)
                       => r1_orders_2(A,D,B) ) ) ) )
              & ( ( r1_lattice3(A,C,B)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r1_lattice3(A,C,D)
                       => r1_orders_2(A,D,B) ) ) )
               => ( B = k2_yellow_0(A,C)
                  & r2_yellow_0(A,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_yellow_0)).

tff(c_32,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_34,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_56,plain,(
    ! [A_34,B_35] :
      ( r1_lattice3(A_34,k1_xboole_0,B_35)
      | ~ m1_subset_1(B_35,u1_struct_0(A_34))
      | ~ l1_orders_2(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_65,plain,
    ( r1_lattice3('#skF_2',k1_xboole_0,'#skF_3')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_56])).

tff(c_72,plain,(
    r1_lattice3('#skF_2',k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_65])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_38,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_36,plain,(
    v2_yellow_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_24,plain,(
    ! [A_26] :
      ( r2_yellow_0(A_26,k1_xboole_0)
      | ~ l1_orders_2(A_26)
      | ~ v2_yellow_0(A_26)
      | ~ v5_orders_2(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_41,plain,(
    ! [A_31] :
      ( k2_yellow_0(A_31,k1_xboole_0) = k4_yellow_0(A_31)
      | ~ l1_orders_2(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_45,plain,(
    k2_yellow_0('#skF_2',k1_xboole_0) = k4_yellow_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_41])).

tff(c_50,plain,(
    ! [A_32,B_33] :
      ( m1_subset_1(k2_yellow_0(A_32,B_33),u1_struct_0(A_32))
      | ~ l1_orders_2(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_53,plain,
    ( m1_subset_1(k4_yellow_0('#skF_2'),u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_50])).

tff(c_55,plain,(
    m1_subset_1(k4_yellow_0('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_53])).

tff(c_144,plain,(
    ! [A_78,D_79,C_80] :
      ( r1_orders_2(A_78,D_79,k2_yellow_0(A_78,C_80))
      | ~ r1_lattice3(A_78,C_80,D_79)
      | ~ m1_subset_1(D_79,u1_struct_0(A_78))
      | ~ r2_yellow_0(A_78,C_80)
      | ~ m1_subset_1(k2_yellow_0(A_78,C_80),u1_struct_0(A_78))
      | ~ l1_orders_2(A_78)
      | ~ v5_orders_2(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_148,plain,(
    ! [D_79] :
      ( r1_orders_2('#skF_2',D_79,k2_yellow_0('#skF_2',k1_xboole_0))
      | ~ r1_lattice3('#skF_2',k1_xboole_0,D_79)
      | ~ m1_subset_1(D_79,u1_struct_0('#skF_2'))
      | ~ r2_yellow_0('#skF_2',k1_xboole_0)
      | ~ m1_subset_1(k4_yellow_0('#skF_2'),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_144])).

tff(c_151,plain,(
    ! [D_79] :
      ( r1_orders_2('#skF_2',D_79,k4_yellow_0('#skF_2'))
      | ~ r1_lattice3('#skF_2',k1_xboole_0,D_79)
      | ~ m1_subset_1(D_79,u1_struct_0('#skF_2'))
      | ~ r2_yellow_0('#skF_2',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_55,c_45,c_148])).

tff(c_152,plain,(
    ~ r2_yellow_0('#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_155,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ v2_yellow_0('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_152])).

tff(c_158,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_155])).

tff(c_160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_158])).

tff(c_179,plain,(
    ! [D_84] :
      ( r1_orders_2('#skF_2',D_84,k4_yellow_0('#skF_2'))
      | ~ r1_lattice3('#skF_2',k1_xboole_0,D_84)
      | ~ m1_subset_1(D_84,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_30,plain,(
    ~ r1_orders_2('#skF_2','#skF_3',k4_yellow_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_190,plain,
    ( ~ r1_lattice3('#skF_2',k1_xboole_0,'#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_179,c_30])).

tff(c_200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_72,c_190])).

%------------------------------------------------------------------------------
