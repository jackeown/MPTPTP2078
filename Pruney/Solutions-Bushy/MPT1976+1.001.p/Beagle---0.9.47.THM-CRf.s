%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1976+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:44 EST 2020

% Result     : Theorem 12.93s
% Output     : CNFRefutation 12.99s
% Verified   : 
% Statistics : Number of formulae       :  147 (1040 expanded)
%              Number of leaves         :   53 ( 403 expanded)
%              Depth                    :   19
%              Number of atoms          :  404 (2529 expanded)
%              Number of equality atoms :   43 ( 632 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_7 > v2_waybel_0 > v1_partfun1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v8_relat_2 > v5_orders_2 > v4_relat_2 > v4_orders_2 > v3_yellow_0 > v3_orders_2 > v2_waybel_1 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_relat_2 > v1_orders_2 > v1_lattice3 > v11_waybel_1 > v10_waybel_1 > l1_orders_2 > k7_waybel_1 > k6_subset_1 > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k9_setfam_1 > k3_yellow_1 > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v11_waybel_1,type,(
    v11_waybel_1: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(v10_waybel_1,type,(
    v10_waybel_1: $i > $o )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(v2_waybel_1,type,(
    v2_waybel_1: $i > $o )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff(k7_waybel_1,type,(
    k7_waybel_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v2_waybel_7,type,(
    v2_waybel_7: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_161,negated_conjecture,(
    ~ ! [A,B] :
        ( ( ~ v1_xboole_0(B)
          & v2_waybel_0(B,k3_yellow_1(A))
          & v13_waybel_0(B,k3_yellow_1(A))
          & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A)))) )
       => ( v2_waybel_7(B,k3_yellow_1(A))
        <=> ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(A))
             => ( r2_hidden(C,B)
                | r2_hidden(k6_subset_1(A,C),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_waybel_7)).

tff(f_87,axiom,(
    ! [A] :
      ( ~ v2_struct_0(k3_yellow_1(A))
      & v1_orders_2(k3_yellow_1(A))
      & v3_orders_2(k3_yellow_1(A))
      & v4_orders_2(k3_yellow_1(A))
      & v5_orders_2(k3_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_yellow_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_orders_2(k3_yellow_1(A))
      & v11_waybel_1(k3_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_waybel_7)).

tff(f_98,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_133,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_56,axiom,(
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

tff(f_30,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(A)
       => A = g1_orders_2(u1_struct_0(A),u1_orders_2(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_2(k1_yellow_1(A))
      & v4_relat_2(k1_yellow_1(A))
      & v8_relat_2(k1_yellow_1(A))
      & v1_partfun1(k1_yellow_1(A),A)
      & m1_subset_1(k1_yellow_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_1)).

tff(f_58,axiom,(
    ! [A] : k2_yellow_1(A) = g1_orders_2(A,k1_yellow_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(f_131,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v11_waybel_1(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v2_waybel_0(B,A)
            & v13_waybel_0(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( v2_waybel_7(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r2_hidden(C,B)
                  | r2_hidden(k7_waybel_1(A,C),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_waybel_7)).

tff(f_142,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,u1_struct_0(k3_yellow_1(A)))
     => k7_waybel_1(k3_yellow_1(A),B) = k6_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_waybel_7)).

tff(c_78,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_82,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | ~ v2_waybel_7('#skF_3',k3_yellow_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_144,plain,(
    ~ v2_waybel_7('#skF_3',k3_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_46,plain,(
    ! [A_7] : v3_orders_2(k3_yellow_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_48,plain,(
    ! [A_7] : v4_orders_2(k3_yellow_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_50,plain,(
    ! [A_7] : v5_orders_2(k3_yellow_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_40,plain,(
    ! [A_6] : v11_waybel_1(k3_yellow_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_56,plain,(
    ! [A_14] : k9_setfam_1(A_14) = k1_zfmisc_1(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_66,plain,(
    ! [A_25] : k2_yellow_1(k9_setfam_1(A_25)) = k3_yellow_1(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_119,plain,(
    ! [A_48] : k2_yellow_1(k1_zfmisc_1(A_48)) = k3_yellow_1(A_48) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_66])).

tff(c_36,plain,(
    ! [A_5] : l1_orders_2(k2_yellow_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_124,plain,(
    ! [A_48] : l1_orders_2(k3_yellow_1(A_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_36])).

tff(c_154,plain,(
    ! [A_55] :
      ( v1_lattice3(A_55)
      | ~ v11_waybel_1(A_55)
      | v2_struct_0(A_55)
      | ~ l1_orders_2(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_42,plain,(
    ! [A_7] : ~ v2_struct_0(k3_yellow_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_157,plain,(
    ! [A_7] :
      ( v1_lattice3(k3_yellow_1(A_7))
      | ~ v11_waybel_1(k3_yellow_1(A_7))
      | ~ l1_orders_2(k3_yellow_1(A_7)) ) ),
    inference(resolution,[status(thm)],[c_154,c_42])).

tff(c_160,plain,(
    ! [A_7] : v1_lattice3(k3_yellow_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_40,c_157])).

tff(c_162,plain,(
    ! [A_57] :
      ( v2_lattice3(A_57)
      | ~ v11_waybel_1(A_57)
      | v2_struct_0(A_57)
      | ~ l1_orders_2(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_165,plain,(
    ! [A_7] :
      ( v2_lattice3(k3_yellow_1(A_7))
      | ~ v11_waybel_1(k3_yellow_1(A_7))
      | ~ l1_orders_2(k3_yellow_1(A_7)) ) ),
    inference(resolution,[status(thm)],[c_162,c_42])).

tff(c_168,plain,(
    ! [A_7] : v2_lattice3(k3_yellow_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_40,c_165])).

tff(c_76,plain,(
    v2_waybel_0('#skF_3',k3_yellow_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_74,plain,(
    v13_waybel_0('#skF_3',k3_yellow_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_95,plain,(
    ! [A_25] : k2_yellow_1(k1_zfmisc_1(A_25)) = k3_yellow_1(A_25) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_66])).

tff(c_34,plain,(
    ! [A_5] : v1_orders_2(k2_yellow_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_orders_2(u1_struct_0(A_1),u1_orders_2(A_1)) = A_1
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_32,plain,(
    ! [A_4] : m1_subset_1(k1_yellow_1(A_4),k1_zfmisc_1(k2_zfmisc_1(A_4,A_4))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_22,plain,(
    ! [A_3] : g1_orders_2(A_3,k1_yellow_1(A_3)) = k2_yellow_1(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_230,plain,(
    ! [C_78,A_79,D_80,B_81] :
      ( C_78 = A_79
      | g1_orders_2(C_78,D_80) != g1_orders_2(A_79,B_81)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(k2_zfmisc_1(A_79,A_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_238,plain,(
    ! [C_78,A_3,D_80] :
      ( C_78 = A_3
      | k2_yellow_1(A_3) != g1_orders_2(C_78,D_80)
      | ~ m1_subset_1(k1_yellow_1(A_3),k1_zfmisc_1(k2_zfmisc_1(A_3,A_3))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_230])).

tff(c_241,plain,(
    ! [C_82,A_83,D_84] :
      ( C_82 = A_83
      | k2_yellow_1(A_83) != g1_orders_2(C_82,D_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_238])).

tff(c_244,plain,(
    ! [A_1,A_83] :
      ( u1_struct_0(A_1) = A_83
      | k2_yellow_1(A_83) != A_1
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_241])).

tff(c_291,plain,(
    ! [A_83] :
      ( u1_struct_0(k2_yellow_1(A_83)) = A_83
      | ~ v1_orders_2(k2_yellow_1(A_83))
      | ~ l1_orders_2(k2_yellow_1(A_83)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_244])).

tff(c_297,plain,(
    ! [A_99] : u1_struct_0(k2_yellow_1(A_99)) = A_99 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_291])).

tff(c_309,plain,(
    ! [A_25] : u1_struct_0(k3_yellow_1(A_25)) = k1_zfmisc_1(A_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_297])).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_315,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_72])).

tff(c_421,plain,(
    ! [A_108,B_109] :
      ( m1_subset_1('#skF_1'(A_108,B_109),u1_struct_0(A_108))
      | v2_waybel_7(B_109,A_108)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ v13_waybel_0(B_109,A_108)
      | ~ v2_waybel_0(B_109,A_108)
      | v1_xboole_0(B_109)
      | ~ l1_orders_2(A_108)
      | ~ v2_lattice3(A_108)
      | ~ v1_lattice3(A_108)
      | ~ v11_waybel_1(A_108)
      | ~ v5_orders_2(A_108)
      | ~ v4_orders_2(A_108)
      | ~ v3_orders_2(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_424,plain,(
    ! [A_25,B_109] :
      ( m1_subset_1('#skF_1'(k3_yellow_1(A_25),B_109),k1_zfmisc_1(A_25))
      | v2_waybel_7(B_109,k3_yellow_1(A_25))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_25))))
      | ~ v13_waybel_0(B_109,k3_yellow_1(A_25))
      | ~ v2_waybel_0(B_109,k3_yellow_1(A_25))
      | v1_xboole_0(B_109)
      | ~ l1_orders_2(k3_yellow_1(A_25))
      | ~ v2_lattice3(k3_yellow_1(A_25))
      | ~ v1_lattice3(k3_yellow_1(A_25))
      | ~ v11_waybel_1(k3_yellow_1(A_25))
      | ~ v5_orders_2(k3_yellow_1(A_25))
      | ~ v4_orders_2(k3_yellow_1(A_25))
      | ~ v3_orders_2(k3_yellow_1(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_421])).

tff(c_429,plain,(
    ! [A_25,B_109] :
      ( m1_subset_1('#skF_1'(k3_yellow_1(A_25),B_109),k1_zfmisc_1(A_25))
      | v2_waybel_7(B_109,k3_yellow_1(A_25))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(k1_zfmisc_1(A_25)))
      | ~ v13_waybel_0(B_109,k3_yellow_1(A_25))
      | ~ v2_waybel_0(B_109,k3_yellow_1(A_25))
      | v1_xboole_0(B_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_50,c_40,c_160,c_168,c_124,c_309,c_424])).

tff(c_94,plain,(
    ! [C_32] :
      ( v2_waybel_7('#skF_3',k3_yellow_1('#skF_2'))
      | r2_hidden(k6_subset_1('#skF_2',C_32),'#skF_3')
      | r2_hidden(C_32,'#skF_3')
      | ~ m1_subset_1(C_32,k1_zfmisc_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_282,plain,(
    ! [C_32] :
      ( r2_hidden(k6_subset_1('#skF_2',C_32),'#skF_3')
      | r2_hidden(C_32,'#skF_3')
      | ~ m1_subset_1(C_32,k1_zfmisc_1('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_94])).

tff(c_293,plain,(
    ! [A_83] : u1_struct_0(k2_yellow_1(A_83)) = A_83 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_291])).

tff(c_427,plain,(
    ! [A_83,B_109] :
      ( m1_subset_1('#skF_1'(k2_yellow_1(A_83),B_109),A_83)
      | v2_waybel_7(B_109,k2_yellow_1(A_83))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(k2_yellow_1(A_83))))
      | ~ v13_waybel_0(B_109,k2_yellow_1(A_83))
      | ~ v2_waybel_0(B_109,k2_yellow_1(A_83))
      | v1_xboole_0(B_109)
      | ~ l1_orders_2(k2_yellow_1(A_83))
      | ~ v2_lattice3(k2_yellow_1(A_83))
      | ~ v1_lattice3(k2_yellow_1(A_83))
      | ~ v11_waybel_1(k2_yellow_1(A_83))
      | ~ v5_orders_2(k2_yellow_1(A_83))
      | ~ v4_orders_2(k2_yellow_1(A_83))
      | ~ v3_orders_2(k2_yellow_1(A_83)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_421])).

tff(c_5949,plain,(
    ! [A_516,B_517] :
      ( m1_subset_1('#skF_1'(k2_yellow_1(A_516),B_517),A_516)
      | v2_waybel_7(B_517,k2_yellow_1(A_516))
      | ~ m1_subset_1(B_517,k1_zfmisc_1(A_516))
      | ~ v13_waybel_0(B_517,k2_yellow_1(A_516))
      | ~ v2_waybel_0(B_517,k2_yellow_1(A_516))
      | v1_xboole_0(B_517)
      | ~ v2_lattice3(k2_yellow_1(A_516))
      | ~ v1_lattice3(k2_yellow_1(A_516))
      | ~ v11_waybel_1(k2_yellow_1(A_516))
      | ~ v5_orders_2(k2_yellow_1(A_516))
      | ~ v4_orders_2(k2_yellow_1(A_516))
      | ~ v3_orders_2(k2_yellow_1(A_516)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_293,c_427])).

tff(c_70,plain,(
    ! [A_28,B_29] :
      ( k7_waybel_1(k3_yellow_1(A_28),B_29) = k6_subset_1(A_28,B_29)
      | ~ m1_subset_1(B_29,u1_struct_0(k3_yellow_1(A_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_314,plain,(
    ! [A_28,B_29] :
      ( k7_waybel_1(k3_yellow_1(A_28),B_29) = k6_subset_1(A_28,B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_28)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_70])).

tff(c_5961,plain,(
    ! [A_28,B_517] :
      ( k7_waybel_1(k3_yellow_1(A_28),'#skF_1'(k2_yellow_1(k1_zfmisc_1(A_28)),B_517)) = k6_subset_1(A_28,'#skF_1'(k2_yellow_1(k1_zfmisc_1(A_28)),B_517))
      | v2_waybel_7(B_517,k2_yellow_1(k1_zfmisc_1(A_28)))
      | ~ m1_subset_1(B_517,k1_zfmisc_1(k1_zfmisc_1(A_28)))
      | ~ v13_waybel_0(B_517,k2_yellow_1(k1_zfmisc_1(A_28)))
      | ~ v2_waybel_0(B_517,k2_yellow_1(k1_zfmisc_1(A_28)))
      | v1_xboole_0(B_517)
      | ~ v2_lattice3(k2_yellow_1(k1_zfmisc_1(A_28)))
      | ~ v1_lattice3(k2_yellow_1(k1_zfmisc_1(A_28)))
      | ~ v11_waybel_1(k2_yellow_1(k1_zfmisc_1(A_28)))
      | ~ v5_orders_2(k2_yellow_1(k1_zfmisc_1(A_28)))
      | ~ v4_orders_2(k2_yellow_1(k1_zfmisc_1(A_28)))
      | ~ v3_orders_2(k2_yellow_1(k1_zfmisc_1(A_28))) ) ),
    inference(resolution,[status(thm)],[c_5949,c_314])).

tff(c_7361,plain,(
    ! [A_622,B_623] :
      ( k7_waybel_1(k3_yellow_1(A_622),'#skF_1'(k3_yellow_1(A_622),B_623)) = k6_subset_1(A_622,'#skF_1'(k3_yellow_1(A_622),B_623))
      | v2_waybel_7(B_623,k3_yellow_1(A_622))
      | ~ m1_subset_1(B_623,k1_zfmisc_1(k1_zfmisc_1(A_622)))
      | ~ v13_waybel_0(B_623,k3_yellow_1(A_622))
      | ~ v2_waybel_0(B_623,k3_yellow_1(A_622))
      | v1_xboole_0(B_623) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_95,c_48,c_95,c_50,c_95,c_40,c_95,c_160,c_95,c_168,c_95,c_95,c_95,c_95,c_95,c_95,c_5961])).

tff(c_60,plain,(
    ! [A_15,B_21] :
      ( ~ r2_hidden(k7_waybel_1(A_15,'#skF_1'(A_15,B_21)),B_21)
      | v2_waybel_7(B_21,A_15)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ v13_waybel_0(B_21,A_15)
      | ~ v2_waybel_0(B_21,A_15)
      | v1_xboole_0(B_21)
      | ~ l1_orders_2(A_15)
      | ~ v2_lattice3(A_15)
      | ~ v1_lattice3(A_15)
      | ~ v11_waybel_1(A_15)
      | ~ v5_orders_2(A_15)
      | ~ v4_orders_2(A_15)
      | ~ v3_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_7370,plain,(
    ! [A_622,B_623] :
      ( ~ r2_hidden(k6_subset_1(A_622,'#skF_1'(k3_yellow_1(A_622),B_623)),B_623)
      | v2_waybel_7(B_623,k3_yellow_1(A_622))
      | ~ m1_subset_1(B_623,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_622))))
      | ~ v13_waybel_0(B_623,k3_yellow_1(A_622))
      | ~ v2_waybel_0(B_623,k3_yellow_1(A_622))
      | v1_xboole_0(B_623)
      | ~ l1_orders_2(k3_yellow_1(A_622))
      | ~ v2_lattice3(k3_yellow_1(A_622))
      | ~ v1_lattice3(k3_yellow_1(A_622))
      | ~ v11_waybel_1(k3_yellow_1(A_622))
      | ~ v5_orders_2(k3_yellow_1(A_622))
      | ~ v4_orders_2(k3_yellow_1(A_622))
      | ~ v3_orders_2(k3_yellow_1(A_622))
      | v2_waybel_7(B_623,k3_yellow_1(A_622))
      | ~ m1_subset_1(B_623,k1_zfmisc_1(k1_zfmisc_1(A_622)))
      | ~ v13_waybel_0(B_623,k3_yellow_1(A_622))
      | ~ v2_waybel_0(B_623,k3_yellow_1(A_622))
      | v1_xboole_0(B_623) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7361,c_60])).

tff(c_7890,plain,(
    ! [A_645,B_646] :
      ( ~ r2_hidden(k6_subset_1(A_645,'#skF_1'(k3_yellow_1(A_645),B_646)),B_646)
      | v2_waybel_7(B_646,k3_yellow_1(A_645))
      | ~ m1_subset_1(B_646,k1_zfmisc_1(k1_zfmisc_1(A_645)))
      | ~ v13_waybel_0(B_646,k3_yellow_1(A_645))
      | ~ v2_waybel_0(B_646,k3_yellow_1(A_645))
      | v1_xboole_0(B_646) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_50,c_40,c_160,c_168,c_124,c_309,c_7370])).

tff(c_7894,plain,
    ( v2_waybel_7('#skF_3',k3_yellow_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | ~ v13_waybel_0('#skF_3',k3_yellow_1('#skF_2'))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1('#skF_2'))
    | v1_xboole_0('#skF_3')
    | r2_hidden('#skF_1'(k3_yellow_1('#skF_2'),'#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_1'(k3_yellow_1('#skF_2'),'#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_282,c_7890])).

tff(c_7897,plain,
    ( v2_waybel_7('#skF_3',k3_yellow_1('#skF_2'))
    | v1_xboole_0('#skF_3')
    | r2_hidden('#skF_1'(k3_yellow_1('#skF_2'),'#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_1'(k3_yellow_1('#skF_2'),'#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_315,c_7894])).

tff(c_7898,plain,
    ( r2_hidden('#skF_1'(k3_yellow_1('#skF_2'),'#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_1'(k3_yellow_1('#skF_2'),'#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_144,c_7897])).

tff(c_7900,plain,(
    ~ m1_subset_1('#skF_1'(k3_yellow_1('#skF_2'),'#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_7898])).

tff(c_7903,plain,
    ( v2_waybel_7('#skF_3',k3_yellow_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | ~ v13_waybel_0('#skF_3',k3_yellow_1('#skF_2'))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1('#skF_2'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_429,c_7900])).

tff(c_7906,plain,
    ( v2_waybel_7('#skF_3',k3_yellow_1('#skF_2'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_315,c_7903])).

tff(c_7908,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_144,c_7906])).

tff(c_7909,plain,(
    r2_hidden('#skF_1'(k3_yellow_1('#skF_2'),'#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_7898])).

tff(c_62,plain,(
    ! [A_15,B_21] :
      ( ~ r2_hidden('#skF_1'(A_15,B_21),B_21)
      | v2_waybel_7(B_21,A_15)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ v13_waybel_0(B_21,A_15)
      | ~ v2_waybel_0(B_21,A_15)
      | v1_xboole_0(B_21)
      | ~ l1_orders_2(A_15)
      | ~ v2_lattice3(A_15)
      | ~ v1_lattice3(A_15)
      | ~ v11_waybel_1(A_15)
      | ~ v5_orders_2(A_15)
      | ~ v4_orders_2(A_15)
      | ~ v3_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_7912,plain,
    ( v2_waybel_7('#skF_3',k3_yellow_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1('#skF_2'))))
    | ~ v13_waybel_0('#skF_3',k3_yellow_1('#skF_2'))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1('#skF_2'))
    | v1_xboole_0('#skF_3')
    | ~ l1_orders_2(k3_yellow_1('#skF_2'))
    | ~ v2_lattice3(k3_yellow_1('#skF_2'))
    | ~ v1_lattice3(k3_yellow_1('#skF_2'))
    | ~ v11_waybel_1(k3_yellow_1('#skF_2'))
    | ~ v5_orders_2(k3_yellow_1('#skF_2'))
    | ~ v4_orders_2(k3_yellow_1('#skF_2'))
    | ~ v3_orders_2(k3_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_7909,c_62])).

tff(c_7918,plain,
    ( v2_waybel_7('#skF_3',k3_yellow_1('#skF_2'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_50,c_40,c_160,c_168,c_124,c_76,c_74,c_315,c_309,c_7912])).

tff(c_7920,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_144,c_7918])).

tff(c_7921,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_7922,plain,(
    v2_waybel_7('#skF_3',k3_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_80,plain,
    ( ~ r2_hidden(k6_subset_1('#skF_2','#skF_4'),'#skF_3')
    | ~ v2_waybel_7('#skF_3',k3_yellow_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_7938,plain,(
    ~ r2_hidden(k6_subset_1('#skF_2','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7922,c_80])).

tff(c_8010,plain,(
    ! [C_672,A_673,D_674,B_675] :
      ( C_672 = A_673
      | g1_orders_2(C_672,D_674) != g1_orders_2(A_673,B_675)
      | ~ m1_subset_1(B_675,k1_zfmisc_1(k2_zfmisc_1(A_673,A_673))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_8018,plain,(
    ! [C_672,A_3,D_674] :
      ( C_672 = A_3
      | k2_yellow_1(A_3) != g1_orders_2(C_672,D_674)
      | ~ m1_subset_1(k1_yellow_1(A_3),k1_zfmisc_1(k2_zfmisc_1(A_3,A_3))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_8010])).

tff(c_8021,plain,(
    ! [C_676,A_677,D_678] :
      ( C_676 = A_677
      | k2_yellow_1(A_677) != g1_orders_2(C_676,D_678) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_8018])).

tff(c_8024,plain,(
    ! [A_1,A_677] :
      ( u1_struct_0(A_1) = A_677
      | k2_yellow_1(A_677) != A_1
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_8021])).

tff(c_8071,plain,(
    ! [A_677] :
      ( u1_struct_0(k2_yellow_1(A_677)) = A_677
      | ~ v1_orders_2(k2_yellow_1(A_677))
      | ~ l1_orders_2(k2_yellow_1(A_677)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_8024])).

tff(c_8077,plain,(
    ! [A_695] : u1_struct_0(k2_yellow_1(A_695)) = A_695 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_8071])).

tff(c_8089,plain,(
    ! [A_25] : u1_struct_0(k3_yellow_1(A_25)) = k1_zfmisc_1(A_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_8077])).

tff(c_8095,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8089,c_72])).

tff(c_84,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | ~ v2_waybel_7('#skF_3',k3_yellow_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_7923,plain,(
    ~ v2_waybel_7('#skF_3',k3_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_7925,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7922,c_7923])).

tff(c_7926,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_8374,plain,(
    ! [A_721,B_722] :
      ( k7_waybel_1(k3_yellow_1(A_721),B_722) = k6_subset_1(A_721,B_722)
      | ~ m1_subset_1(B_722,k1_zfmisc_1(A_721)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8089,c_70])).

tff(c_8385,plain,(
    k7_waybel_1(k3_yellow_1('#skF_2'),'#skF_4') = k6_subset_1('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_7926,c_8374])).

tff(c_7941,plain,(
    ! [A_653] :
      ( v1_lattice3(A_653)
      | ~ v11_waybel_1(A_653)
      | v2_struct_0(A_653)
      | ~ l1_orders_2(A_653) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_7944,plain,(
    ! [A_7] :
      ( v1_lattice3(k3_yellow_1(A_7))
      | ~ v11_waybel_1(k3_yellow_1(A_7))
      | ~ l1_orders_2(k3_yellow_1(A_7)) ) ),
    inference(resolution,[status(thm)],[c_7941,c_42])).

tff(c_7947,plain,(
    ! [A_7] : v1_lattice3(k3_yellow_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_40,c_7944])).

tff(c_7951,plain,(
    ! [A_657] :
      ( v2_lattice3(A_657)
      | ~ v11_waybel_1(A_657)
      | v2_struct_0(A_657)
      | ~ l1_orders_2(A_657) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_7954,plain,(
    ! [A_7] :
      ( v2_lattice3(k3_yellow_1(A_7))
      | ~ v11_waybel_1(k3_yellow_1(A_7))
      | ~ l1_orders_2(k3_yellow_1(A_7)) ) ),
    inference(resolution,[status(thm)],[c_7951,c_42])).

tff(c_7957,plain,(
    ! [A_7] : v2_lattice3(k3_yellow_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_40,c_7954])).

tff(c_8347,plain,(
    ! [A_714,C_715,B_716] :
      ( r2_hidden(k7_waybel_1(A_714,C_715),B_716)
      | r2_hidden(C_715,B_716)
      | ~ m1_subset_1(C_715,u1_struct_0(A_714))
      | ~ v2_waybel_7(B_716,A_714)
      | ~ m1_subset_1(B_716,k1_zfmisc_1(u1_struct_0(A_714)))
      | ~ v13_waybel_0(B_716,A_714)
      | ~ v2_waybel_0(B_716,A_714)
      | v1_xboole_0(B_716)
      | ~ l1_orders_2(A_714)
      | ~ v2_lattice3(A_714)
      | ~ v1_lattice3(A_714)
      | ~ v11_waybel_1(A_714)
      | ~ v5_orders_2(A_714)
      | ~ v4_orders_2(A_714)
      | ~ v3_orders_2(A_714) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_8349,plain,(
    ! [A_25,C_715,B_716] :
      ( r2_hidden(k7_waybel_1(k3_yellow_1(A_25),C_715),B_716)
      | r2_hidden(C_715,B_716)
      | ~ m1_subset_1(C_715,u1_struct_0(k3_yellow_1(A_25)))
      | ~ v2_waybel_7(B_716,k3_yellow_1(A_25))
      | ~ m1_subset_1(B_716,k1_zfmisc_1(k1_zfmisc_1(A_25)))
      | ~ v13_waybel_0(B_716,k3_yellow_1(A_25))
      | ~ v2_waybel_0(B_716,k3_yellow_1(A_25))
      | v1_xboole_0(B_716)
      | ~ l1_orders_2(k3_yellow_1(A_25))
      | ~ v2_lattice3(k3_yellow_1(A_25))
      | ~ v1_lattice3(k3_yellow_1(A_25))
      | ~ v11_waybel_1(k3_yellow_1(A_25))
      | ~ v5_orders_2(k3_yellow_1(A_25))
      | ~ v4_orders_2(k3_yellow_1(A_25))
      | ~ v3_orders_2(k3_yellow_1(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8089,c_8347])).

tff(c_14139,plain,(
    ! [A_1208,C_1209,B_1210] :
      ( r2_hidden(k7_waybel_1(k3_yellow_1(A_1208),C_1209),B_1210)
      | r2_hidden(C_1209,B_1210)
      | ~ m1_subset_1(C_1209,k1_zfmisc_1(A_1208))
      | ~ v2_waybel_7(B_1210,k3_yellow_1(A_1208))
      | ~ m1_subset_1(B_1210,k1_zfmisc_1(k1_zfmisc_1(A_1208)))
      | ~ v13_waybel_0(B_1210,k3_yellow_1(A_1208))
      | ~ v2_waybel_0(B_1210,k3_yellow_1(A_1208))
      | v1_xboole_0(B_1210) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_50,c_40,c_7947,c_7957,c_124,c_8089,c_8349])).

tff(c_14176,plain,(
    ! [B_1210] :
      ( r2_hidden(k6_subset_1('#skF_2','#skF_4'),B_1210)
      | r2_hidden('#skF_4',B_1210)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
      | ~ v2_waybel_7(B_1210,k3_yellow_1('#skF_2'))
      | ~ m1_subset_1(B_1210,k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ v13_waybel_0(B_1210,k3_yellow_1('#skF_2'))
      | ~ v2_waybel_0(B_1210,k3_yellow_1('#skF_2'))
      | v1_xboole_0(B_1210) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8385,c_14139])).

tff(c_14656,plain,(
    ! [B_1215] :
      ( r2_hidden(k6_subset_1('#skF_2','#skF_4'),B_1215)
      | r2_hidden('#skF_4',B_1215)
      | ~ v2_waybel_7(B_1215,k3_yellow_1('#skF_2'))
      | ~ m1_subset_1(B_1215,k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ v13_waybel_0(B_1215,k3_yellow_1('#skF_2'))
      | ~ v2_waybel_0(B_1215,k3_yellow_1('#skF_2'))
      | v1_xboole_0(B_1215) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7926,c_14176])).

tff(c_14667,plain,
    ( r2_hidden(k6_subset_1('#skF_2','#skF_4'),'#skF_3')
    | r2_hidden('#skF_4','#skF_3')
    | ~ v2_waybel_7('#skF_3',k3_yellow_1('#skF_2'))
    | ~ v13_waybel_0('#skF_3',k3_yellow_1('#skF_2'))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1('#skF_2'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_8095,c_14656])).

tff(c_14674,plain,
    ( r2_hidden(k6_subset_1('#skF_2','#skF_4'),'#skF_3')
    | r2_hidden('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_7922,c_14667])).

tff(c_14676,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_7921,c_7938,c_14674])).

%------------------------------------------------------------------------------
