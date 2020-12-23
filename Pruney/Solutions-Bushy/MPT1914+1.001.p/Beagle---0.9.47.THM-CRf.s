%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1914+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:41 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   36 (  40 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :   60 (  68 expanded)
%              Number of equality atoms :   23 (  25 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > v1_orders_2 > l1_orders_2 > k3_relset_1 > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k7_lattice3 > k1_zfmisc_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_relset_1,type,(
    k3_relset_1: ( $i * $i * $i ) > $i )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff(k7_lattice3,type,(
    k7_lattice3: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_58,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => u1_struct_0(A) = u1_struct_0(k7_lattice3(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_yellow_6)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(k7_lattice3(A))
        & l1_orders_2(k7_lattice3(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattice3)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_30,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(A)
       => A = g1_orders_2(u1_struct_0(A),u1_orders_2(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

tff(f_34,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k7_lattice3(A) = g1_orders_2(u1_struct_0(A),k3_relset_1(u1_struct_0(A),u1_struct_0(A),u1_orders_2(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_lattice3)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(c_18,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [A_3] :
      ( l1_orders_2(k7_lattice3(A_3))
      | ~ l1_orders_2(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    ! [A_3] :
      ( v1_orders_2(k7_lattice3(A_3))
      | ~ l1_orders_2(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_10,plain,(
    ! [A_4] :
      ( m1_subset_1(u1_orders_2(A_4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4),u1_struct_0(A_4))))
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_orders_2(u1_struct_0(A_1),u1_orders_2(A_1)) = A_1
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_49,plain,(
    ! [A_23] :
      ( g1_orders_2(u1_struct_0(A_23),k3_relset_1(u1_struct_0(A_23),u1_struct_0(A_23),u1_orders_2(A_23))) = k7_lattice3(A_23)
      | ~ l1_orders_2(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [C_9,A_5,D_10,B_6] :
      ( C_9 = A_5
      | g1_orders_2(C_9,D_10) != g1_orders_2(A_5,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(k2_zfmisc_1(A_5,A_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_66,plain,(
    ! [A_24,A_25,B_26] :
      ( u1_struct_0(A_24) = A_25
      | k7_lattice3(A_24) != g1_orders_2(A_25,B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(k2_zfmisc_1(A_25,A_25)))
      | ~ l1_orders_2(A_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_14])).

tff(c_131,plain,(
    ! [A_47,A_46] :
      ( u1_struct_0(A_47) = u1_struct_0(A_46)
      | k7_lattice3(A_46) != A_47
      | ~ m1_subset_1(u1_orders_2(A_47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_47),u1_struct_0(A_47))))
      | ~ l1_orders_2(A_46)
      | ~ v1_orders_2(A_47)
      | ~ l1_orders_2(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_66])).

tff(c_136,plain,(
    ! [A_49,A_48] :
      ( u1_struct_0(A_49) = u1_struct_0(A_48)
      | k7_lattice3(A_48) != A_49
      | ~ l1_orders_2(A_48)
      | ~ v1_orders_2(A_49)
      | ~ l1_orders_2(A_49) ) ),
    inference(resolution,[status(thm)],[c_10,c_131])).

tff(c_144,plain,(
    ! [A_50] :
      ( u1_struct_0(A_50) = u1_struct_0('#skF_1')
      | k7_lattice3('#skF_1') != A_50
      | ~ v1_orders_2(A_50)
      | ~ l1_orders_2(A_50) ) ),
    inference(resolution,[status(thm)],[c_18,c_136])).

tff(c_149,plain,(
    ! [A_51] :
      ( u1_struct_0(k7_lattice3(A_51)) = u1_struct_0('#skF_1')
      | k7_lattice3(A_51) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(k7_lattice3(A_51))
      | ~ l1_orders_2(A_51) ) ),
    inference(resolution,[status(thm)],[c_8,c_144])).

tff(c_154,plain,(
    ! [A_52] :
      ( u1_struct_0(k7_lattice3(A_52)) = u1_struct_0('#skF_1')
      | k7_lattice3(A_52) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_52) ) ),
    inference(resolution,[status(thm)],[c_6,c_149])).

tff(c_16,plain,(
    u1_struct_0(k7_lattice3('#skF_1')) != u1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_178,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_16])).

tff(c_186,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_178])).

%------------------------------------------------------------------------------
