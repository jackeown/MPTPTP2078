%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1957+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:43 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   43 (  48 expanded)
%              Number of leaves         :   24 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :   52 (  59 expanded)
%              Number of equality atoms :   26 (  28 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > v1_orders_2 > l1_orders_2 > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k9_setfam_1 > k3_yellow_1 > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

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

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_51,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_53,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_32,axiom,(
    ! [A] : k2_yellow_1(A) = g1_orders_2(A,k1_yellow_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).

tff(f_30,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(A)
       => A = g1_orders_2(u1_struct_0(A),u1_orders_2(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(f_56,negated_conjecture,(
    ~ ! [A] : u1_struct_0(k3_yellow_1(A)) = k9_setfam_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_waybel_7)).

tff(c_16,plain,(
    ! [A_11] : k9_setfam_1(A_11) = k1_zfmisc_1(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    ! [A_12] : k2_yellow_1(k9_setfam_1(A_12)) = k3_yellow_1(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ! [A_12] : k2_yellow_1(k1_zfmisc_1(A_12)) = k3_yellow_1(A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18])).

tff(c_8,plain,(
    ! [A_3] : l1_orders_2(k2_yellow_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_10,plain,(
    ! [A_4] :
      ( m1_subset_1(u1_orders_2(A_4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4),u1_struct_0(A_4))))
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_6,plain,(
    ! [A_3] : v1_orders_2(k2_yellow_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4,plain,(
    ! [A_2] : g1_orders_2(A_2,k1_yellow_1(A_2)) = k2_yellow_1(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_orders_2(u1_struct_0(A_1),u1_orders_2(A_1)) = A_1
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_72,plain,(
    ! [C_22,A_23,D_24,B_25] :
      ( C_22 = A_23
      | g1_orders_2(C_22,D_24) != g1_orders_2(A_23,B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k2_zfmisc_1(A_23,A_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_210,plain,(
    ! [A_73,C_74,D_75] :
      ( u1_struct_0(A_73) = C_74
      | g1_orders_2(C_74,D_75) != A_73
      | ~ m1_subset_1(u1_orders_2(A_73),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_73),u1_struct_0(A_73))))
      | ~ v1_orders_2(A_73)
      | ~ l1_orders_2(A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_72])).

tff(c_214,plain,(
    ! [A_73,A_2] :
      ( u1_struct_0(A_73) = A_2
      | k2_yellow_1(A_2) != A_73
      | ~ m1_subset_1(u1_orders_2(A_73),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_73),u1_struct_0(A_73))))
      | ~ v1_orders_2(A_73)
      | ~ l1_orders_2(A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_210])).

tff(c_230,plain,(
    ! [A_2] :
      ( u1_struct_0(k2_yellow_1(A_2)) = A_2
      | ~ m1_subset_1(u1_orders_2(k2_yellow_1(A_2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k2_yellow_1(A_2)),u1_struct_0(k2_yellow_1(A_2)))))
      | ~ v1_orders_2(k2_yellow_1(A_2))
      | ~ l1_orders_2(k2_yellow_1(A_2)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_214])).

tff(c_236,plain,(
    ! [A_83] :
      ( u1_struct_0(k2_yellow_1(A_83)) = A_83
      | ~ m1_subset_1(u1_orders_2(k2_yellow_1(A_83)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k2_yellow_1(A_83)),u1_struct_0(k2_yellow_1(A_83))))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_6,c_230])).

tff(c_239,plain,(
    ! [A_83] :
      ( u1_struct_0(k2_yellow_1(A_83)) = A_83
      | ~ l1_orders_2(k2_yellow_1(A_83)) ) ),
    inference(resolution,[status(thm)],[c_10,c_236])).

tff(c_257,plain,(
    ! [A_84] : u1_struct_0(k2_yellow_1(A_84)) = A_84 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_239])).

tff(c_275,plain,(
    ! [A_12] : u1_struct_0(k3_yellow_1(A_12)) = k1_zfmisc_1(A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_257])).

tff(c_20,plain,(
    u1_struct_0(k3_yellow_1('#skF_1')) != k9_setfam_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_21,plain,(
    u1_struct_0(k3_yellow_1('#skF_1')) != k1_zfmisc_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_20])).

tff(c_286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_21])).

%------------------------------------------------------------------------------
