%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1966+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:43 EST 2020

% Result     : Theorem 6.23s
% Output     : CNFRefutation 6.49s
% Verified   : 
% Statistics : Number of formulae       :  244 (1975 expanded)
%              Number of leaves         :   58 ( 719 expanded)
%              Depth                    :   21
%              Number of atoms          :  660 (6005 expanded)
%              Number of equality atoms :   98 ( 702 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > v9_waybel_1 > v5_orders_2 > v4_orders_2 > v3_yellow_0 > v3_orders_2 > v2_yellow_0 > v2_waybel_1 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > v1_lattice3 > v1_finset_1 > v11_waybel_1 > v10_waybel_1 > l1_orders_2 > k8_setfam_1 > k6_setfam_1 > k2_yellow_0 > #nlpp > u1_struct_0 > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k1_zfmisc_1 > k1_setfam_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v11_waybel_1,type,(
    v11_waybel_1: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v3_yellow_0,type,(
    v3_yellow_0: $i > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v10_waybel_1,type,(
    v10_waybel_1: $i > $o )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(v2_waybel_1,type,(
    v2_waybel_1: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff(v2_yellow_0,type,(
    v2_yellow_0: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k2_yellow_0,type,(
    k2_yellow_0: ( $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(v9_waybel_1,type,(
    v9_waybel_1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k4_yellow_0,type,(
    k4_yellow_0: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_218,negated_conjecture,(
    ~ ! [A,B] :
        ( ( ~ v1_xboole_0(B)
          & v13_waybel_0(B,k3_yellow_1(A))
          & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A)))) )
       => ( v2_waybel_0(B,k3_yellow_1(A))
        <=> ! [C] :
              ( ( v1_finset_1(C)
                & m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A))) )
             => ( r1_tarski(C,B)
               => r2_hidden(k8_setfam_1(A,C),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_waybel_7)).

tff(f_105,axiom,(
    ! [A] :
      ( ~ v2_struct_0(k3_yellow_1(A))
      & v1_orders_2(k3_yellow_1(A))
      & v3_orders_2(k3_yellow_1(A))
      & v4_orders_2(k3_yellow_1(A))
      & v5_orders_2(k3_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_yellow_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_orders_2(k3_yellow_1(A))
      & l1_orders_2(k3_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_1)).

tff(f_94,axiom,(
    ! [A] :
      ( v1_orders_2(k3_yellow_1(A))
      & v11_waybel_1(k3_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_waybel_7)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( ( ~ v2_struct_0(A)
          & v11_waybel_1(A) )
       => ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_lattice3(A)
          & v2_lattice3(A)
          & v3_yellow_0(A)
          & v2_waybel_1(A)
          & v10_waybel_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc8_waybel_1)).

tff(f_111,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_187,axiom,(
    ! [A] : u1_struct_0(k3_yellow_1(A)) = k9_setfam_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_waybel_7)).

tff(f_155,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_185,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v13_waybel_0(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( v2_waybel_0(B,A)
          <=> ! [C] :
                ( ( v1_finset_1(C)
                  & m1_subset_1(C,k1_zfmisc_1(B)) )
               => ( C != k1_xboole_0
                 => r2_hidden(k2_yellow_0(A,C),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_waybel_0)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_126,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(B)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A)))) )
     => k2_yellow_0(k3_yellow_1(A),B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_yellow_1)).

tff(f_191,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_36,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( ( ~ v2_struct_0(A)
          & v11_waybel_1(A) )
       => ( ~ v2_struct_0(A)
          & v9_waybel_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc10_waybel_1)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( ( ~ v2_struct_0(A)
          & v9_waybel_1(A) )
       => ( ~ v2_struct_0(A)
          & v2_yellow_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc7_waybel_1)).

tff(f_113,axiom,(
    ! [A] : k4_yellow_0(k3_yellow_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_yellow_1)).

tff(f_151,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v2_yellow_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v2_waybel_0(B,A)
            & v13_waybel_0(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => r2_hidden(k4_yellow_0(A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_waybel_4)).

tff(f_90,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(c_88,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_96,plain,
    ( v1_finset_1('#skF_4')
    | ~ v2_waybel_0('#skF_3',k3_yellow_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_169,plain,(
    ~ v2_waybel_0('#skF_3',k3_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_46,plain,(
    ! [A_8] : v3_orders_2(k3_yellow_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_48,plain,(
    ! [A_8] : v4_orders_2(k3_yellow_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_50,plain,(
    ! [A_8] : v5_orders_2(k3_yellow_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_34,plain,(
    ! [A_6] : l1_orders_2(k3_yellow_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_40,plain,(
    ! [A_7] : v11_waybel_1(k3_yellow_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_182,plain,(
    ! [A_58] :
      ( v2_lattice3(A_58)
      | ~ v11_waybel_1(A_58)
      | v2_struct_0(A_58)
      | ~ l1_orders_2(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_42,plain,(
    ! [A_8] : ~ v2_struct_0(k3_yellow_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_185,plain,(
    ! [A_8] :
      ( v2_lattice3(k3_yellow_1(A_8))
      | ~ v11_waybel_1(k3_yellow_1(A_8))
      | ~ l1_orders_2(k3_yellow_1(A_8)) ) ),
    inference(resolution,[status(thm)],[c_182,c_42])).

tff(c_188,plain,(
    ! [A_8] : v2_lattice3(k3_yellow_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_40,c_185])).

tff(c_86,plain,(
    v13_waybel_0('#skF_3',k3_yellow_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_54,plain,(
    ! [A_11] : k9_setfam_1(A_11) = k1_zfmisc_1(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_78,plain,(
    ! [A_33] : u1_struct_0(k3_yellow_1(A_33)) = k9_setfam_1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_84,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_109,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k9_setfam_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_84])).

tff(c_112,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_109])).

tff(c_111,plain,(
    ! [A_33] : u1_struct_0(k3_yellow_1(A_33)) = k1_zfmisc_1(A_33) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_78])).

tff(c_172,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(A_55,B_56)
      | ~ m1_subset_1(A_55,k1_zfmisc_1(B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_180,plain,(
    r1_tarski('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_112,c_172])).

tff(c_66,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(A_21,k1_zfmisc_1(B_22))
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_697,plain,(
    ! [A_123,B_124] :
      ( m1_subset_1('#skF_1'(A_123,B_124),k1_zfmisc_1(B_124))
      | v2_waybel_0(B_124,A_123)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ v13_waybel_0(B_124,A_123)
      | v1_xboole_0(B_124)
      | ~ l1_orders_2(A_123)
      | ~ v2_lattice3(A_123)
      | ~ v5_orders_2(A_123)
      | ~ v4_orders_2(A_123)
      | ~ v3_orders_2(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_64,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(A_21,B_22)
      | ~ m1_subset_1(A_21,k1_zfmisc_1(B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_804,plain,(
    ! [A_137,B_138] :
      ( r1_tarski('#skF_1'(A_137,B_138),B_138)
      | v2_waybel_0(B_138,A_137)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ v13_waybel_0(B_138,A_137)
      | v1_xboole_0(B_138)
      | ~ l1_orders_2(A_137)
      | ~ v2_lattice3(A_137)
      | ~ v5_orders_2(A_137)
      | ~ v4_orders_2(A_137)
      | ~ v3_orders_2(A_137) ) ),
    inference(resolution,[status(thm)],[c_697,c_64])).

tff(c_814,plain,(
    ! [A_137,A_21] :
      ( r1_tarski('#skF_1'(A_137,A_21),A_21)
      | v2_waybel_0(A_21,A_137)
      | ~ v13_waybel_0(A_21,A_137)
      | v1_xboole_0(A_21)
      | ~ l1_orders_2(A_137)
      | ~ v2_lattice3(A_137)
      | ~ v5_orders_2(A_137)
      | ~ v4_orders_2(A_137)
      | ~ v3_orders_2(A_137)
      | ~ r1_tarski(A_21,u1_struct_0(A_137)) ) ),
    inference(resolution,[status(thm)],[c_66,c_804])).

tff(c_217,plain,(
    ! [A_71,C_72,B_73] :
      ( r1_tarski(A_71,C_72)
      | ~ r1_tarski(B_73,C_72)
      | ~ r1_tarski(A_71,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_220,plain,(
    ! [A_71] :
      ( r1_tarski(A_71,k1_zfmisc_1('#skF_2'))
      | ~ r1_tarski(A_71,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_180,c_217])).

tff(c_552,plain,(
    ! [A_105,B_106] :
      ( v1_finset_1('#skF_1'(A_105,B_106))
      | v2_waybel_0(B_106,A_105)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ v13_waybel_0(B_106,A_105)
      | v1_xboole_0(B_106)
      | ~ l1_orders_2(A_105)
      | ~ v2_lattice3(A_105)
      | ~ v5_orders_2(A_105)
      | ~ v4_orders_2(A_105)
      | ~ v3_orders_2(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_559,plain,(
    ! [A_33,B_106] :
      ( v1_finset_1('#skF_1'(k3_yellow_1(A_33),B_106))
      | v2_waybel_0(B_106,k3_yellow_1(A_33))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(k1_zfmisc_1(A_33)))
      | ~ v13_waybel_0(B_106,k3_yellow_1(A_33))
      | v1_xboole_0(B_106)
      | ~ l1_orders_2(k3_yellow_1(A_33))
      | ~ v2_lattice3(k3_yellow_1(A_33))
      | ~ v5_orders_2(k3_yellow_1(A_33))
      | ~ v4_orders_2(k3_yellow_1(A_33))
      | ~ v3_orders_2(k3_yellow_1(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_552])).

tff(c_633,plain,(
    ! [A_109,B_110] :
      ( v1_finset_1('#skF_1'(k3_yellow_1(A_109),B_110))
      | v2_waybel_0(B_110,k3_yellow_1(A_109))
      | ~ m1_subset_1(B_110,k1_zfmisc_1(k1_zfmisc_1(A_109)))
      | ~ v13_waybel_0(B_110,k3_yellow_1(A_109))
      | v1_xboole_0(B_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_50,c_188,c_34,c_559])).

tff(c_640,plain,
    ( v1_finset_1('#skF_1'(k3_yellow_1('#skF_2'),'#skF_3'))
    | v2_waybel_0('#skF_3',k3_yellow_1('#skF_2'))
    | ~ v13_waybel_0('#skF_3',k3_yellow_1('#skF_2'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_112,c_633])).

tff(c_644,plain,
    ( v1_finset_1('#skF_1'(k3_yellow_1('#skF_2'),'#skF_3'))
    | v2_waybel_0('#skF_3',k3_yellow_1('#skF_2'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_640])).

tff(c_645,plain,(
    v1_finset_1('#skF_1'(k3_yellow_1('#skF_2'),'#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_169,c_644])).

tff(c_653,plain,(
    ! [A_115,B_116] :
      ( '#skF_1'(A_115,B_116) != k1_xboole_0
      | v2_waybel_0(B_116,A_115)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ v13_waybel_0(B_116,A_115)
      | v1_xboole_0(B_116)
      | ~ l1_orders_2(A_115)
      | ~ v2_lattice3(A_115)
      | ~ v5_orders_2(A_115)
      | ~ v4_orders_2(A_115)
      | ~ v3_orders_2(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_660,plain,(
    ! [A_33,B_116] :
      ( '#skF_1'(k3_yellow_1(A_33),B_116) != k1_xboole_0
      | v2_waybel_0(B_116,k3_yellow_1(A_33))
      | ~ m1_subset_1(B_116,k1_zfmisc_1(k1_zfmisc_1(A_33)))
      | ~ v13_waybel_0(B_116,k3_yellow_1(A_33))
      | v1_xboole_0(B_116)
      | ~ l1_orders_2(k3_yellow_1(A_33))
      | ~ v2_lattice3(k3_yellow_1(A_33))
      | ~ v5_orders_2(k3_yellow_1(A_33))
      | ~ v4_orders_2(k3_yellow_1(A_33))
      | ~ v3_orders_2(k3_yellow_1(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_653])).

tff(c_676,plain,(
    ! [A_119,B_120] :
      ( '#skF_1'(k3_yellow_1(A_119),B_120) != k1_xboole_0
      | v2_waybel_0(B_120,k3_yellow_1(A_119))
      | ~ m1_subset_1(B_120,k1_zfmisc_1(k1_zfmisc_1(A_119)))
      | ~ v13_waybel_0(B_120,k3_yellow_1(A_119))
      | v1_xboole_0(B_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_50,c_188,c_34,c_660])).

tff(c_683,plain,
    ( '#skF_1'(k3_yellow_1('#skF_2'),'#skF_3') != k1_xboole_0
    | v2_waybel_0('#skF_3',k3_yellow_1('#skF_2'))
    | ~ v13_waybel_0('#skF_3',k3_yellow_1('#skF_2'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_112,c_676])).

tff(c_687,plain,
    ( '#skF_1'(k3_yellow_1('#skF_2'),'#skF_3') != k1_xboole_0
    | v2_waybel_0('#skF_3',k3_yellow_1('#skF_2'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_683])).

tff(c_688,plain,(
    '#skF_1'(k3_yellow_1('#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_169,c_687])).

tff(c_812,plain,(
    ! [A_33,B_138] :
      ( r1_tarski('#skF_1'(k3_yellow_1(A_33),B_138),B_138)
      | v2_waybel_0(B_138,k3_yellow_1(A_33))
      | ~ m1_subset_1(B_138,k1_zfmisc_1(k1_zfmisc_1(A_33)))
      | ~ v13_waybel_0(B_138,k3_yellow_1(A_33))
      | v1_xboole_0(B_138)
      | ~ l1_orders_2(k3_yellow_1(A_33))
      | ~ v2_lattice3(k3_yellow_1(A_33))
      | ~ v5_orders_2(k3_yellow_1(A_33))
      | ~ v4_orders_2(k3_yellow_1(A_33))
      | ~ v3_orders_2(k3_yellow_1(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_804])).

tff(c_817,plain,(
    ! [A_139,B_140] :
      ( r1_tarski('#skF_1'(k3_yellow_1(A_139),B_140),B_140)
      | v2_waybel_0(B_140,k3_yellow_1(A_139))
      | ~ m1_subset_1(B_140,k1_zfmisc_1(k1_zfmisc_1(A_139)))
      | ~ v13_waybel_0(B_140,k3_yellow_1(A_139))
      | v1_xboole_0(B_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_50,c_188,c_34,c_812])).

tff(c_236,plain,(
    ! [A_77,B_78] :
      ( k6_setfam_1(A_77,B_78) = k1_setfam_1(B_78)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(k1_zfmisc_1(A_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_252,plain,(
    ! [A_79,A_80] :
      ( k6_setfam_1(A_79,A_80) = k1_setfam_1(A_80)
      | ~ r1_tarski(A_80,k1_zfmisc_1(A_79)) ) ),
    inference(resolution,[status(thm)],[c_66,c_236])).

tff(c_259,plain,(
    ! [A_71] :
      ( k6_setfam_1('#skF_2',A_71) = k1_setfam_1(A_71)
      | ~ r1_tarski(A_71,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_220,c_252])).

tff(c_855,plain,(
    ! [A_139] :
      ( k6_setfam_1('#skF_2','#skF_1'(k3_yellow_1(A_139),'#skF_3')) = k1_setfam_1('#skF_1'(k3_yellow_1(A_139),'#skF_3'))
      | v2_waybel_0('#skF_3',k3_yellow_1(A_139))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(A_139)))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(A_139))
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_817,c_259])).

tff(c_889,plain,(
    ! [A_144] :
      ( k6_setfam_1('#skF_2','#skF_1'(k3_yellow_1(A_144),'#skF_3')) = k1_setfam_1('#skF_1'(k3_yellow_1(A_144),'#skF_3'))
      | v2_waybel_0('#skF_3',k3_yellow_1(A_144))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(A_144)))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(A_144)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_855])).

tff(c_895,plain,
    ( k6_setfam_1('#skF_2','#skF_1'(k3_yellow_1('#skF_2'),'#skF_3')) = k1_setfam_1('#skF_1'(k3_yellow_1('#skF_2'),'#skF_3'))
    | v2_waybel_0('#skF_3',k3_yellow_1('#skF_2'))
    | ~ v13_waybel_0('#skF_3',k3_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_112,c_889])).

tff(c_899,plain,
    ( k6_setfam_1('#skF_2','#skF_1'(k3_yellow_1('#skF_2'),'#skF_3')) = k1_setfam_1('#skF_1'(k3_yellow_1('#skF_2'),'#skF_3'))
    | v2_waybel_0('#skF_3',k3_yellow_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_895])).

tff(c_900,plain,(
    k6_setfam_1('#skF_2','#skF_1'(k3_yellow_1('#skF_2'),'#skF_3')) = k1_setfam_1('#skF_1'(k3_yellow_1('#skF_2'),'#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_899])).

tff(c_271,plain,(
    ! [A_84,B_85] :
      ( k8_setfam_1(A_84,B_85) = k6_setfam_1(A_84,B_85)
      | k1_xboole_0 = B_85
      | ~ m1_subset_1(B_85,k1_zfmisc_1(k1_zfmisc_1(A_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_378,plain,(
    ! [A_93,A_94] :
      ( k8_setfam_1(A_93,A_94) = k6_setfam_1(A_93,A_94)
      | k1_xboole_0 = A_94
      | ~ r1_tarski(A_94,k1_zfmisc_1(A_93)) ) ),
    inference(resolution,[status(thm)],[c_66,c_271])).

tff(c_385,plain,(
    ! [A_71] :
      ( k8_setfam_1('#skF_2',A_71) = k6_setfam_1('#skF_2',A_71)
      | k1_xboole_0 = A_71
      | ~ r1_tarski(A_71,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_220,c_378])).

tff(c_839,plain,(
    ! [A_139] :
      ( k8_setfam_1('#skF_2','#skF_1'(k3_yellow_1(A_139),'#skF_3')) = k6_setfam_1('#skF_2','#skF_1'(k3_yellow_1(A_139),'#skF_3'))
      | '#skF_1'(k3_yellow_1(A_139),'#skF_3') = k1_xboole_0
      | v2_waybel_0('#skF_3',k3_yellow_1(A_139))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(A_139)))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(A_139))
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_817,c_385])).

tff(c_1220,plain,(
    ! [A_178] :
      ( k8_setfam_1('#skF_2','#skF_1'(k3_yellow_1(A_178),'#skF_3')) = k6_setfam_1('#skF_2','#skF_1'(k3_yellow_1(A_178),'#skF_3'))
      | '#skF_1'(k3_yellow_1(A_178),'#skF_3') = k1_xboole_0
      | v2_waybel_0('#skF_3',k3_yellow_1(A_178))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(A_178)))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(A_178)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_839])).

tff(c_1226,plain,
    ( k8_setfam_1('#skF_2','#skF_1'(k3_yellow_1('#skF_2'),'#skF_3')) = k6_setfam_1('#skF_2','#skF_1'(k3_yellow_1('#skF_2'),'#skF_3'))
    | '#skF_1'(k3_yellow_1('#skF_2'),'#skF_3') = k1_xboole_0
    | v2_waybel_0('#skF_3',k3_yellow_1('#skF_2'))
    | ~ v13_waybel_0('#skF_3',k3_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_112,c_1220])).

tff(c_1230,plain,
    ( k8_setfam_1('#skF_2','#skF_1'(k3_yellow_1('#skF_2'),'#skF_3')) = k1_setfam_1('#skF_1'(k3_yellow_1('#skF_2'),'#skF_3'))
    | '#skF_1'(k3_yellow_1('#skF_2'),'#skF_3') = k1_xboole_0
    | v2_waybel_0('#skF_3',k3_yellow_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_900,c_1226])).

tff(c_1231,plain,(
    k8_setfam_1('#skF_2','#skF_1'(k3_yellow_1('#skF_2'),'#skF_3')) = k1_setfam_1('#skF_1'(k3_yellow_1('#skF_2'),'#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_688,c_1230])).

tff(c_108,plain,(
    ! [C_39] :
      ( v2_waybel_0('#skF_3',k3_yellow_1('#skF_2'))
      | r2_hidden(k8_setfam_1('#skF_2',C_39),'#skF_3')
      | ~ r1_tarski(C_39,'#skF_3')
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ v1_finset_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_345,plain,(
    ! [C_89] :
      ( r2_hidden(k8_setfam_1('#skF_2',C_89),'#skF_3')
      | ~ r1_tarski(C_89,'#skF_3')
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ v1_finset_1(C_89) ) ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_108])).

tff(c_353,plain,(
    ! [A_21] :
      ( r2_hidden(k8_setfam_1('#skF_2',A_21),'#skF_3')
      | ~ r1_tarski(A_21,'#skF_3')
      | ~ v1_finset_1(A_21)
      | ~ r1_tarski(A_21,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_66,c_345])).

tff(c_1235,plain,
    ( r2_hidden(k1_setfam_1('#skF_1'(k3_yellow_1('#skF_2'),'#skF_3')),'#skF_3')
    | ~ r1_tarski('#skF_1'(k3_yellow_1('#skF_2'),'#skF_3'),'#skF_3')
    | ~ v1_finset_1('#skF_1'(k3_yellow_1('#skF_2'),'#skF_3'))
    | ~ r1_tarski('#skF_1'(k3_yellow_1('#skF_2'),'#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1231,c_353])).

tff(c_1239,plain,
    ( r2_hidden(k1_setfam_1('#skF_1'(k3_yellow_1('#skF_2'),'#skF_3')),'#skF_3')
    | ~ r1_tarski('#skF_1'(k3_yellow_1('#skF_2'),'#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_1'(k3_yellow_1('#skF_2'),'#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_645,c_1235])).

tff(c_1241,plain,(
    ~ r1_tarski('#skF_1'(k3_yellow_1('#skF_2'),'#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1239])).

tff(c_1263,plain,(
    ~ r1_tarski('#skF_1'(k3_yellow_1('#skF_2'),'#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_220,c_1241])).

tff(c_1266,plain,
    ( v2_waybel_0('#skF_3',k3_yellow_1('#skF_2'))
    | ~ v13_waybel_0('#skF_3',k3_yellow_1('#skF_2'))
    | v1_xboole_0('#skF_3')
    | ~ l1_orders_2(k3_yellow_1('#skF_2'))
    | ~ v2_lattice3(k3_yellow_1('#skF_2'))
    | ~ v5_orders_2(k3_yellow_1('#skF_2'))
    | ~ v4_orders_2(k3_yellow_1('#skF_2'))
    | ~ v3_orders_2(k3_yellow_1('#skF_2'))
    | ~ r1_tarski('#skF_3',u1_struct_0(k3_yellow_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_814,c_1263])).

tff(c_1278,plain,
    ( v2_waybel_0('#skF_3',k3_yellow_1('#skF_2'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_111,c_46,c_48,c_50,c_188,c_34,c_86,c_1266])).

tff(c_1280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_169,c_1278])).

tff(c_1281,plain,
    ( ~ r1_tarski('#skF_1'(k3_yellow_1('#skF_2'),'#skF_3'),'#skF_3')
    | r2_hidden(k1_setfam_1('#skF_1'(k3_yellow_1('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1239])).

tff(c_1332,plain,(
    ~ r1_tarski('#skF_1'(k3_yellow_1('#skF_2'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1281])).

tff(c_1335,plain,
    ( v2_waybel_0('#skF_3',k3_yellow_1('#skF_2'))
    | ~ v13_waybel_0('#skF_3',k3_yellow_1('#skF_2'))
    | v1_xboole_0('#skF_3')
    | ~ l1_orders_2(k3_yellow_1('#skF_2'))
    | ~ v2_lattice3(k3_yellow_1('#skF_2'))
    | ~ v5_orders_2(k3_yellow_1('#skF_2'))
    | ~ v4_orders_2(k3_yellow_1('#skF_2'))
    | ~ v3_orders_2(k3_yellow_1('#skF_2'))
    | ~ r1_tarski('#skF_3',u1_struct_0(k3_yellow_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_814,c_1332])).

tff(c_1347,plain,
    ( v2_waybel_0('#skF_3',k3_yellow_1('#skF_2'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_111,c_46,c_48,c_50,c_188,c_34,c_86,c_1335])).

tff(c_1349,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_169,c_1347])).

tff(c_1350,plain,(
    r2_hidden(k1_setfam_1('#skF_1'(k3_yellow_1('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1281])).

tff(c_1282,plain,(
    r1_tarski('#skF_1'(k3_yellow_1('#skF_2'),'#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1239])).

tff(c_60,plain,(
    ! [A_16,B_17] :
      ( k2_yellow_0(k3_yellow_1(A_16),B_17) = k1_setfam_1(B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_16))))
      | v1_xboole_0(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_110,plain,(
    ! [A_16,B_17] :
      ( k2_yellow_0(k3_yellow_1(A_16),B_17) = k1_setfam_1(B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k9_setfam_1(A_16)))
      | v1_xboole_0(B_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_60])).

tff(c_282,plain,(
    ! [A_86,B_87] :
      ( k2_yellow_0(k3_yellow_1(A_86),B_87) = k1_setfam_1(B_87)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(k1_zfmisc_1(A_86)))
      | v1_xboole_0(B_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_110])).

tff(c_290,plain,(
    ! [A_86,A_21] :
      ( k2_yellow_0(k3_yellow_1(A_86),A_21) = k1_setfam_1(A_21)
      | v1_xboole_0(A_21)
      | ~ r1_tarski(A_21,k1_zfmisc_1(A_86)) ) ),
    inference(resolution,[status(thm)],[c_66,c_282])).

tff(c_1300,plain,
    ( k2_yellow_0(k3_yellow_1('#skF_2'),'#skF_1'(k3_yellow_1('#skF_2'),'#skF_3')) = k1_setfam_1('#skF_1'(k3_yellow_1('#skF_2'),'#skF_3'))
    | v1_xboole_0('#skF_1'(k3_yellow_1('#skF_2'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_1282,c_290])).

tff(c_1395,plain,(
    v1_xboole_0('#skF_1'(k3_yellow_1('#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1300])).

tff(c_80,plain,(
    ! [A_34] :
      ( k1_xboole_0 = A_34
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_1400,plain,(
    '#skF_1'(k3_yellow_1('#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1395,c_80])).

tff(c_1405,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_688,c_1400])).

tff(c_1406,plain,(
    k2_yellow_0(k3_yellow_1('#skF_2'),'#skF_1'(k3_yellow_1('#skF_2'),'#skF_3')) = k1_setfam_1('#skF_1'(k3_yellow_1('#skF_2'),'#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1300])).

tff(c_70,plain,(
    ! [A_23,B_29] :
      ( ~ r2_hidden(k2_yellow_0(A_23,'#skF_1'(A_23,B_29)),B_29)
      | v2_waybel_0(B_29,A_23)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ v13_waybel_0(B_29,A_23)
      | v1_xboole_0(B_29)
      | ~ l1_orders_2(A_23)
      | ~ v2_lattice3(A_23)
      | ~ v5_orders_2(A_23)
      | ~ v4_orders_2(A_23)
      | ~ v3_orders_2(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_1426,plain,
    ( ~ r2_hidden(k1_setfam_1('#skF_1'(k3_yellow_1('#skF_2'),'#skF_3')),'#skF_3')
    | v2_waybel_0('#skF_3',k3_yellow_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1('#skF_2'))))
    | ~ v13_waybel_0('#skF_3',k3_yellow_1('#skF_2'))
    | v1_xboole_0('#skF_3')
    | ~ l1_orders_2(k3_yellow_1('#skF_2'))
    | ~ v2_lattice3(k3_yellow_1('#skF_2'))
    | ~ v5_orders_2(k3_yellow_1('#skF_2'))
    | ~ v4_orders_2(k3_yellow_1('#skF_2'))
    | ~ v3_orders_2(k3_yellow_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1406,c_70])).

tff(c_1448,plain,
    ( v2_waybel_0('#skF_3',k3_yellow_1('#skF_2'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_50,c_188,c_34,c_86,c_112,c_111,c_1350,c_1426])).

tff(c_1450,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_169,c_1448])).

tff(c_1452,plain,(
    v2_waybel_0('#skF_3',k3_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_92,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ v2_waybel_0('#skF_3',k3_yellow_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_1453,plain,(
    ~ v2_waybel_0('#skF_3',k3_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_1455,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1452,c_1453])).

tff(c_1456,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_1482,plain,(
    ! [A_195] :
      ( v9_waybel_1(A_195)
      | ~ v11_waybel_1(A_195)
      | v2_struct_0(A_195)
      | ~ l1_orders_2(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_6,plain,(
    ! [A_2] :
      ( v2_yellow_0(A_2)
      | ~ v9_waybel_1(A_2)
      | v2_struct_0(A_2)
      | ~ l1_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1486,plain,(
    ! [A_195] :
      ( v2_yellow_0(A_195)
      | ~ v11_waybel_1(A_195)
      | v2_struct_0(A_195)
      | ~ l1_orders_2(A_195) ) ),
    inference(resolution,[status(thm)],[c_1482,c_6])).

tff(c_94,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_1498,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1452,c_94])).

tff(c_2623,plain,(
    ! [A_317,B_318] :
      ( k2_yellow_0(k3_yellow_1(A_317),B_318) = k1_setfam_1(B_318)
      | ~ m1_subset_1(B_318,k1_zfmisc_1(k1_zfmisc_1(A_317)))
      | v1_xboole_0(B_318) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_110])).

tff(c_2634,plain,
    ( k2_yellow_0(k3_yellow_1('#skF_2'),'#skF_4') = k1_setfam_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1498,c_2623])).

tff(c_2647,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2634])).

tff(c_2654,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2647,c_80])).

tff(c_1554,plain,(
    ! [A_212,B_213] :
      ( k6_setfam_1(A_212,B_213) = k1_setfam_1(B_213)
      | ~ m1_subset_1(B_213,k1_zfmisc_1(k1_zfmisc_1(A_212))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1565,plain,(
    k6_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1498,c_1554])).

tff(c_1632,plain,(
    ! [A_220,B_221] :
      ( k8_setfam_1(A_220,B_221) = k6_setfam_1(A_220,B_221)
      | k1_xboole_0 = B_221
      | ~ m1_subset_1(B_221,k1_zfmisc_1(k1_zfmisc_1(A_220))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1635,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k6_setfam_1('#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1498,c_1632])).

tff(c_1644,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1565,c_1635])).

tff(c_1648,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1644])).

tff(c_1460,plain,(
    ! [A_188,B_189] :
      ( r1_tarski(A_188,B_189)
      | ~ m1_subset_1(A_188,k1_zfmisc_1(B_189)) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1468,plain,(
    r1_tarski('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_112,c_1460])).

tff(c_1519,plain,(
    ! [A_206,C_207,B_208] :
      ( r1_tarski(A_206,C_207)
      | ~ r1_tarski(B_208,C_207)
      | ~ r1_tarski(A_206,B_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1543,plain,(
    ! [A_211] :
      ( r1_tarski(A_211,k1_zfmisc_1('#skF_2'))
      | ~ r1_tarski(A_211,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1468,c_1519])).

tff(c_1513,plain,(
    ! [A_204] :
      ( k8_setfam_1(A_204,k1_xboole_0) = A_204
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_204))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1517,plain,(
    ! [A_204] :
      ( k8_setfam_1(A_204,k1_xboole_0) = A_204
      | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(A_204)) ) ),
    inference(resolution,[status(thm)],[c_66,c_1513])).

tff(c_1551,plain,
    ( k8_setfam_1('#skF_2',k1_xboole_0) = '#skF_2'
    | ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_1543,c_1517])).

tff(c_1553,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1551])).

tff(c_1650,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1648,c_1553])).

tff(c_1659,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1456,c_1650])).

tff(c_1660,plain,(
    k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1644])).

tff(c_90,plain,
    ( ~ r2_hidden(k8_setfam_1('#skF_2','#skF_4'),'#skF_3')
    | ~ v2_waybel_0('#skF_3',k3_yellow_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_1471,plain,(
    ~ r2_hidden(k8_setfam_1('#skF_2','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1452,c_90])).

tff(c_1663,plain,(
    ~ r2_hidden(k1_setfam_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1660,c_1471])).

tff(c_1661,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1644])).

tff(c_1474,plain,(
    ! [A_193] :
      ( v2_lattice3(A_193)
      | ~ v11_waybel_1(A_193)
      | v2_struct_0(A_193)
      | ~ l1_orders_2(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1477,plain,(
    ! [A_8] :
      ( v2_lattice3(k3_yellow_1(A_8))
      | ~ v11_waybel_1(k3_yellow_1(A_8))
      | ~ l1_orders_2(k3_yellow_1(A_8)) ) ),
    inference(resolution,[status(thm)],[c_1474,c_42])).

tff(c_1480,plain,(
    ! [A_8] : v2_lattice3(k3_yellow_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_40,c_1477])).

tff(c_1451,plain,(
    v1_finset_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_1682,plain,(
    ! [A_222,B_223] :
      ( k2_yellow_0(k3_yellow_1(A_222),B_223) = k1_setfam_1(B_223)
      | ~ m1_subset_1(B_223,k1_zfmisc_1(k1_zfmisc_1(A_222)))
      | v1_xboole_0(B_223) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_110])).

tff(c_1693,plain,
    ( k2_yellow_0(k3_yellow_1('#skF_2'),'#skF_4') = k1_setfam_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1498,c_1682])).

tff(c_1708,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1693])).

tff(c_1713,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1708,c_80])).

tff(c_1718,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1661,c_1713])).

tff(c_1719,plain,(
    k2_yellow_0(k3_yellow_1('#skF_2'),'#skF_4') = k1_setfam_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1693])).

tff(c_2297,plain,(
    ! [A_282,C_283,B_284] :
      ( r2_hidden(k2_yellow_0(A_282,C_283),B_284)
      | k1_xboole_0 = C_283
      | ~ m1_subset_1(C_283,k1_zfmisc_1(B_284))
      | ~ v1_finset_1(C_283)
      | ~ v2_waybel_0(B_284,A_282)
      | ~ m1_subset_1(B_284,k1_zfmisc_1(u1_struct_0(A_282)))
      | ~ v13_waybel_0(B_284,A_282)
      | v1_xboole_0(B_284)
      | ~ l1_orders_2(A_282)
      | ~ v2_lattice3(A_282)
      | ~ v5_orders_2(A_282)
      | ~ v4_orders_2(A_282)
      | ~ v3_orders_2(A_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_2451,plain,(
    ! [A_302,C_303,A_304] :
      ( r2_hidden(k2_yellow_0(A_302,C_303),A_304)
      | k1_xboole_0 = C_303
      | ~ m1_subset_1(C_303,k1_zfmisc_1(A_304))
      | ~ v1_finset_1(C_303)
      | ~ v2_waybel_0(A_304,A_302)
      | ~ v13_waybel_0(A_304,A_302)
      | v1_xboole_0(A_304)
      | ~ l1_orders_2(A_302)
      | ~ v2_lattice3(A_302)
      | ~ v5_orders_2(A_302)
      | ~ v4_orders_2(A_302)
      | ~ v3_orders_2(A_302)
      | ~ r1_tarski(A_304,u1_struct_0(A_302)) ) ),
    inference(resolution,[status(thm)],[c_66,c_2297])).

tff(c_2464,plain,(
    ! [A_304] :
      ( r2_hidden(k1_setfam_1('#skF_4'),A_304)
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_304))
      | ~ v1_finset_1('#skF_4')
      | ~ v2_waybel_0(A_304,k3_yellow_1('#skF_2'))
      | ~ v13_waybel_0(A_304,k3_yellow_1('#skF_2'))
      | v1_xboole_0(A_304)
      | ~ l1_orders_2(k3_yellow_1('#skF_2'))
      | ~ v2_lattice3(k3_yellow_1('#skF_2'))
      | ~ v5_orders_2(k3_yellow_1('#skF_2'))
      | ~ v4_orders_2(k3_yellow_1('#skF_2'))
      | ~ v3_orders_2(k3_yellow_1('#skF_2'))
      | ~ r1_tarski(A_304,u1_struct_0(k3_yellow_1('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1719,c_2451])).

tff(c_2474,plain,(
    ! [A_304] :
      ( r2_hidden(k1_setfam_1('#skF_4'),A_304)
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_304))
      | ~ v2_waybel_0(A_304,k3_yellow_1('#skF_2'))
      | ~ v13_waybel_0(A_304,k3_yellow_1('#skF_2'))
      | v1_xboole_0(A_304)
      | ~ r1_tarski(A_304,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_46,c_48,c_50,c_1480,c_34,c_1451,c_2464])).

tff(c_2479,plain,(
    ! [A_305] :
      ( r2_hidden(k1_setfam_1('#skF_4'),A_305)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_305))
      | ~ v2_waybel_0(A_305,k3_yellow_1('#skF_2'))
      | ~ v13_waybel_0(A_305,k3_yellow_1('#skF_2'))
      | v1_xboole_0(A_305)
      | ~ r1_tarski(A_305,k1_zfmisc_1('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1661,c_2474])).

tff(c_2486,plain,
    ( r2_hidden(k1_setfam_1('#skF_4'),'#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3'))
    | ~ v13_waybel_0('#skF_3',k3_yellow_1('#skF_2'))
    | v1_xboole_0('#skF_3')
    | ~ r1_tarski('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1452,c_2479])).

tff(c_2490,plain,
    ( r2_hidden(k1_setfam_1('#skF_4'),'#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1468,c_86,c_2486])).

tff(c_2491,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_1663,c_2490])).

tff(c_2494,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_2491])).

tff(c_2498,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1456,c_2494])).

tff(c_2499,plain,(
    k8_setfam_1('#skF_2',k1_xboole_0) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1551])).

tff(c_2657,plain,(
    k8_setfam_1('#skF_2','#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2654,c_2499])).

tff(c_2700,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2657,c_1471])).

tff(c_56,plain,(
    ! [A_12] : k4_yellow_0(k3_yellow_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2955,plain,(
    ! [A_342,B_343] :
      ( r2_hidden(k4_yellow_0(A_342),B_343)
      | ~ m1_subset_1(B_343,k1_zfmisc_1(u1_struct_0(A_342)))
      | ~ v13_waybel_0(B_343,A_342)
      | ~ v2_waybel_0(B_343,A_342)
      | v1_xboole_0(B_343)
      | ~ l1_orders_2(A_342)
      | ~ v2_yellow_0(A_342)
      | ~ v5_orders_2(A_342)
      | ~ v4_orders_2(A_342)
      | ~ v3_orders_2(A_342)
      | v2_struct_0(A_342) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2966,plain,(
    ! [A_33,B_343] :
      ( r2_hidden(k4_yellow_0(k3_yellow_1(A_33)),B_343)
      | ~ m1_subset_1(B_343,k1_zfmisc_1(k1_zfmisc_1(A_33)))
      | ~ v13_waybel_0(B_343,k3_yellow_1(A_33))
      | ~ v2_waybel_0(B_343,k3_yellow_1(A_33))
      | v1_xboole_0(B_343)
      | ~ l1_orders_2(k3_yellow_1(A_33))
      | ~ v2_yellow_0(k3_yellow_1(A_33))
      | ~ v5_orders_2(k3_yellow_1(A_33))
      | ~ v4_orders_2(k3_yellow_1(A_33))
      | ~ v3_orders_2(k3_yellow_1(A_33))
      | v2_struct_0(k3_yellow_1(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_2955])).

tff(c_2970,plain,(
    ! [A_33,B_343] :
      ( r2_hidden(A_33,B_343)
      | ~ m1_subset_1(B_343,k1_zfmisc_1(k1_zfmisc_1(A_33)))
      | ~ v13_waybel_0(B_343,k3_yellow_1(A_33))
      | ~ v2_waybel_0(B_343,k3_yellow_1(A_33))
      | v1_xboole_0(B_343)
      | ~ v2_yellow_0(k3_yellow_1(A_33))
      | v2_struct_0(k3_yellow_1(A_33)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_50,c_34,c_56,c_2966])).

tff(c_2997,plain,(
    ! [A_350,B_351] :
      ( r2_hidden(A_350,B_351)
      | ~ m1_subset_1(B_351,k1_zfmisc_1(k1_zfmisc_1(A_350)))
      | ~ v13_waybel_0(B_351,k3_yellow_1(A_350))
      | ~ v2_waybel_0(B_351,k3_yellow_1(A_350))
      | v1_xboole_0(B_351)
      | ~ v2_yellow_0(k3_yellow_1(A_350)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_2970])).

tff(c_3011,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | ~ v13_waybel_0('#skF_3',k3_yellow_1('#skF_2'))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1('#skF_2'))
    | v1_xboole_0('#skF_3')
    | ~ v2_yellow_0(k3_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_112,c_2997])).

tff(c_3018,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | v1_xboole_0('#skF_3')
    | ~ v2_yellow_0(k3_yellow_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1452,c_86,c_3011])).

tff(c_3019,plain,(
    ~ v2_yellow_0(k3_yellow_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_2700,c_3018])).

tff(c_3022,plain,
    ( ~ v11_waybel_1(k3_yellow_1('#skF_2'))
    | v2_struct_0(k3_yellow_1('#skF_2'))
    | ~ l1_orders_2(k3_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1486,c_3019])).

tff(c_3025,plain,(
    v2_struct_0(k3_yellow_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_40,c_3022])).

tff(c_3027,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_3025])).

tff(c_3029,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2634])).

tff(c_2536,plain,(
    ! [A_309,B_310] :
      ( k6_setfam_1(A_309,B_310) = k1_setfam_1(B_310)
      | ~ m1_subset_1(B_310,k1_zfmisc_1(k1_zfmisc_1(A_309))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2547,plain,(
    k6_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1498,c_2536])).

tff(c_3030,plain,(
    ! [A_352,B_353] :
      ( k8_setfam_1(A_352,B_353) = k6_setfam_1(A_352,B_353)
      | k1_xboole_0 = B_353
      | ~ m1_subset_1(B_353,k1_zfmisc_1(k1_zfmisc_1(A_352))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3033,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k6_setfam_1('#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1498,c_3030])).

tff(c_3042,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2547,c_3033])).

tff(c_3050,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3042])).

tff(c_36,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_132,plain,(
    ! [A_48] :
      ( k1_xboole_0 = A_48
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_136,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_132])).

tff(c_137,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_36])).

tff(c_3060,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3050,c_137])).

tff(c_3066,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3029,c_3060])).

tff(c_3067,plain,(
    k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_3042])).

tff(c_3069,plain,(
    ~ r2_hidden(k1_setfam_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3067,c_1471])).

tff(c_3068,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3042])).

tff(c_3028,plain,(
    k2_yellow_0(k3_yellow_1('#skF_2'),'#skF_4') = k1_setfam_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2634])).

tff(c_3586,plain,(
    ! [A_405,C_406,B_407] :
      ( r2_hidden(k2_yellow_0(A_405,C_406),B_407)
      | k1_xboole_0 = C_406
      | ~ m1_subset_1(C_406,k1_zfmisc_1(B_407))
      | ~ v1_finset_1(C_406)
      | ~ v2_waybel_0(B_407,A_405)
      | ~ m1_subset_1(B_407,k1_zfmisc_1(u1_struct_0(A_405)))
      | ~ v13_waybel_0(B_407,A_405)
      | v1_xboole_0(B_407)
      | ~ l1_orders_2(A_405)
      | ~ v2_lattice3(A_405)
      | ~ v5_orders_2(A_405)
      | ~ v4_orders_2(A_405)
      | ~ v3_orders_2(A_405) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_3594,plain,(
    ! [A_33,C_406,B_407] :
      ( r2_hidden(k2_yellow_0(k3_yellow_1(A_33),C_406),B_407)
      | k1_xboole_0 = C_406
      | ~ m1_subset_1(C_406,k1_zfmisc_1(B_407))
      | ~ v1_finset_1(C_406)
      | ~ v2_waybel_0(B_407,k3_yellow_1(A_33))
      | ~ m1_subset_1(B_407,k1_zfmisc_1(k1_zfmisc_1(A_33)))
      | ~ v13_waybel_0(B_407,k3_yellow_1(A_33))
      | v1_xboole_0(B_407)
      | ~ l1_orders_2(k3_yellow_1(A_33))
      | ~ v2_lattice3(k3_yellow_1(A_33))
      | ~ v5_orders_2(k3_yellow_1(A_33))
      | ~ v4_orders_2(k3_yellow_1(A_33))
      | ~ v3_orders_2(k3_yellow_1(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_3586])).

tff(c_3788,plain,(
    ! [A_426,C_427,B_428] :
      ( r2_hidden(k2_yellow_0(k3_yellow_1(A_426),C_427),B_428)
      | k1_xboole_0 = C_427
      | ~ m1_subset_1(C_427,k1_zfmisc_1(B_428))
      | ~ v1_finset_1(C_427)
      | ~ v2_waybel_0(B_428,k3_yellow_1(A_426))
      | ~ m1_subset_1(B_428,k1_zfmisc_1(k1_zfmisc_1(A_426)))
      | ~ v13_waybel_0(B_428,k3_yellow_1(A_426))
      | v1_xboole_0(B_428) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_50,c_1480,c_34,c_3594])).

tff(c_3801,plain,(
    ! [B_428] :
      ( r2_hidden(k1_setfam_1('#skF_4'),B_428)
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(B_428))
      | ~ v1_finset_1('#skF_4')
      | ~ v2_waybel_0(B_428,k3_yellow_1('#skF_2'))
      | ~ m1_subset_1(B_428,k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ v13_waybel_0(B_428,k3_yellow_1('#skF_2'))
      | v1_xboole_0(B_428) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3028,c_3788])).

tff(c_3809,plain,(
    ! [B_428] :
      ( r2_hidden(k1_setfam_1('#skF_4'),B_428)
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(B_428))
      | ~ v2_waybel_0(B_428,k3_yellow_1('#skF_2'))
      | ~ m1_subset_1(B_428,k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ v13_waybel_0(B_428,k3_yellow_1('#skF_2'))
      | v1_xboole_0(B_428) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1451,c_3801])).

tff(c_3812,plain,(
    ! [B_429] :
      ( r2_hidden(k1_setfam_1('#skF_4'),B_429)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(B_429))
      | ~ v2_waybel_0(B_429,k3_yellow_1('#skF_2'))
      | ~ m1_subset_1(B_429,k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ v13_waybel_0(B_429,k3_yellow_1('#skF_2'))
      | v1_xboole_0(B_429) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3068,c_3809])).

tff(c_3826,plain,
    ( r2_hidden(k1_setfam_1('#skF_4'),'#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3'))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1('#skF_2'))
    | ~ v13_waybel_0('#skF_3',k3_yellow_1('#skF_2'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_112,c_3812])).

tff(c_3833,plain,
    ( r2_hidden(k1_setfam_1('#skF_4'),'#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1452,c_3826])).

tff(c_3834,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_3069,c_3833])).

tff(c_3837,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_3834])).

tff(c_3841,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1456,c_3837])).

%------------------------------------------------------------------------------
