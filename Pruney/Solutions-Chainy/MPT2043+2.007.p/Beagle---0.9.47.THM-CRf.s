%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:23 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 107 expanded)
%              Number of leaves         :   46 (  61 expanded)
%              Depth                    :    9
%              Number of atoms          :  136 ( 212 expanded)
%              Number of equality atoms :   14 (  27 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v3_lattices > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > v1_orders_2 > v13_lattices > v10_lattices > l3_lattices > l1_orders_2 > #nlpp > u1_struct_0 > k9_setfam_1 > k5_lattices > k3_yellow_1 > k3_yellow_0 > k3_lattice3 > k1_zfmisc_1 > k1_lattice3 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_lattice3,type,(
    k3_lattice3: $i > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_lattice3,type,(
    k1_lattice3: $i > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v13_lattices,type,(
    v13_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(v3_lattices,type,(
    v3_lattices: $i > $o )).

tff(k5_lattices,type,(
    k5_lattices: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_subset_1(B,u1_struct_0(k3_yellow_1(A)))
              & v2_waybel_0(B,k3_yellow_1(A))
              & v13_waybel_0(B,k3_yellow_1(A))
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A)))) )
           => ! [C] :
                ~ ( r2_hidden(C,B)
                  & v1_xboole_0(C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).

tff(f_36,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_93,axiom,(
    ! [A] : u1_struct_0(k3_yellow_1(A)) = k9_setfam_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_waybel_7)).

tff(f_89,axiom,(
    ! [A] :
      ( ~ v2_struct_0(k3_yellow_1(A))
      & v1_orders_2(k3_yellow_1(A))
      & v3_orders_2(k3_yellow_1(A))
      & v4_orders_2(k3_yellow_1(A))
      & v5_orders_2(k3_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_yellow_1)).

tff(f_45,axiom,(
    ! [A] :
      ( ~ v2_struct_0(k1_lattice3(A))
      & v3_lattices(k1_lattice3(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_lattice3)).

tff(f_49,axiom,(
    ! [A] :
      ( v3_lattices(k1_lattice3(A))
      & v10_lattices(k1_lattice3(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_lattice3)).

tff(f_53,axiom,(
    ! [A] :
      ( v13_lattices(k1_lattice3(A))
      & k5_lattices(k1_lattice3(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_lattice3)).

tff(f_40,axiom,(
    ! [A] :
      ( v3_lattices(k1_lattice3(A))
      & l3_lattices(k1_lattice3(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_lattice3)).

tff(f_55,axiom,(
    ! [A] : k3_yellow_1(A) = k3_lattice3(k1_lattice3(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v13_lattices(A)
        & l3_lattices(A) )
     => ( v1_orders_2(k3_lattice3(A))
        & v3_orders_2(k3_lattice3(A))
        & v4_orders_2(k3_lattice3(A))
        & v5_orders_2(k3_lattice3(A))
        & v1_yellow_0(k3_lattice3(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_yellow_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_orders_2(k3_yellow_1(A))
      & l1_orders_2(k3_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_91,axiom,(
    ! [A] : k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow_1)).

tff(f_121,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v2_waybel_0(B,A)
            & v13_waybel_0(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( v1_subset_1(B,u1_struct_0(A))
          <=> ~ r2_hidden(k3_yellow_0(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_66,plain,(
    v2_waybel_0('#skF_2',k3_yellow_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_64,plain,(
    v13_waybel_0('#skF_2',k3_yellow_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_6,plain,(
    ! [A_4] : k9_setfam_1(A_4) = k1_zfmisc_1(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_52,plain,(
    ! [A_14] : u1_struct_0(k3_yellow_1(A_14)) = k9_setfam_1(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_68,plain,(
    v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_74,plain,(
    v1_subset_1('#skF_2',k9_setfam_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_68])).

tff(c_80,plain,(
    v1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_74])).

tff(c_60,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_62,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_73,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k9_setfam_1('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_62])).

tff(c_79,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_73])).

tff(c_40,plain,(
    ! [A_12] : ~ v2_struct_0(k3_yellow_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_44,plain,(
    ! [A_12] : v3_orders_2(k3_yellow_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_46,plain,(
    ! [A_12] : v4_orders_2(k3_yellow_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_48,plain,(
    ! [A_12] : v5_orders_2(k3_yellow_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_12,plain,(
    ! [A_6] : ~ v2_struct_0(k1_lattice3(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_7] : v10_lattices(k1_lattice3(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [A_8] : v13_lattices(k1_lattice3(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    ! [A_5] : l3_lattices(k1_lattice3(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_24,plain,(
    ! [A_9] : k3_lattice3(k1_lattice3(A_9)) = k3_yellow_1(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_177,plain,(
    ! [A_45] :
      ( v1_yellow_0(k3_lattice3(A_45))
      | ~ l3_lattices(A_45)
      | ~ v13_lattices(A_45)
      | ~ v10_lattices(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_180,plain,(
    ! [A_9] :
      ( v1_yellow_0(k3_yellow_1(A_9))
      | ~ l3_lattices(k1_lattice3(A_9))
      | ~ v13_lattices(k1_lattice3(A_9))
      | ~ v10_lattices(k1_lattice3(A_9))
      | v2_struct_0(k1_lattice3(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_177])).

tff(c_182,plain,(
    ! [A_9] :
      ( v1_yellow_0(k3_yellow_1(A_9))
      | v2_struct_0(k1_lattice3(A_9)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_10,c_180])).

tff(c_183,plain,(
    ! [A_9] : v1_yellow_0(k3_yellow_1(A_9)) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_182])).

tff(c_28,plain,(
    ! [A_10] : l1_orders_2(k3_yellow_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_78,plain,(
    ! [A_14] : u1_struct_0(k3_yellow_1(A_14)) = k1_zfmisc_1(A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_52])).

tff(c_58,plain,(
    v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_115,plain,(
    ! [A_36] :
      ( k1_xboole_0 = A_36
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_119,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_58,c_115])).

tff(c_50,plain,(
    ! [A_13] : k3_yellow_0(k3_yellow_1(A_13)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_121,plain,(
    ! [A_13] : k3_yellow_0(k3_yellow_1(A_13)) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_50])).

tff(c_221,plain,(
    ! [A_54,B_55] :
      ( ~ r2_hidden(k3_yellow_0(A_54),B_55)
      | ~ v1_subset_1(B_55,u1_struct_0(A_54))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ v13_waybel_0(B_55,A_54)
      | ~ v2_waybel_0(B_55,A_54)
      | v1_xboole_0(B_55)
      | ~ l1_orders_2(A_54)
      | ~ v1_yellow_0(A_54)
      | ~ v5_orders_2(A_54)
      | ~ v4_orders_2(A_54)
      | ~ v3_orders_2(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_224,plain,(
    ! [A_14,B_55] :
      ( ~ r2_hidden(k3_yellow_0(k3_yellow_1(A_14)),B_55)
      | ~ v1_subset_1(B_55,u1_struct_0(k3_yellow_1(A_14)))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k1_zfmisc_1(A_14)))
      | ~ v13_waybel_0(B_55,k3_yellow_1(A_14))
      | ~ v2_waybel_0(B_55,k3_yellow_1(A_14))
      | v1_xboole_0(B_55)
      | ~ l1_orders_2(k3_yellow_1(A_14))
      | ~ v1_yellow_0(k3_yellow_1(A_14))
      | ~ v5_orders_2(k3_yellow_1(A_14))
      | ~ v4_orders_2(k3_yellow_1(A_14))
      | ~ v3_orders_2(k3_yellow_1(A_14))
      | v2_struct_0(k3_yellow_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_221])).

tff(c_226,plain,(
    ! [B_55,A_14] :
      ( ~ r2_hidden('#skF_3',B_55)
      | ~ v1_subset_1(B_55,k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k1_zfmisc_1(A_14)))
      | ~ v13_waybel_0(B_55,k3_yellow_1(A_14))
      | ~ v2_waybel_0(B_55,k3_yellow_1(A_14))
      | v1_xboole_0(B_55)
      | v2_struct_0(k3_yellow_1(A_14)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_48,c_183,c_28,c_78,c_121,c_224])).

tff(c_228,plain,(
    ! [B_56,A_57] :
      ( ~ r2_hidden('#skF_3',B_56)
      | ~ v1_subset_1(B_56,k1_zfmisc_1(A_57))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k1_zfmisc_1(A_57)))
      | ~ v13_waybel_0(B_56,k3_yellow_1(A_57))
      | ~ v2_waybel_0(B_56,k3_yellow_1(A_57))
      | v1_xboole_0(B_56) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_226])).

tff(c_231,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | ~ v1_subset_1('#skF_2',k1_zfmisc_1('#skF_1'))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1('#skF_1'))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1('#skF_1'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_79,c_228])).

tff(c_234,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_80,c_60,c_231])).

tff(c_236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_234])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:15:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.30  
% 2.09/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.30  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v3_lattices > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > v1_orders_2 > v13_lattices > v10_lattices > l3_lattices > l1_orders_2 > #nlpp > u1_struct_0 > k9_setfam_1 > k5_lattices > k3_yellow_1 > k3_yellow_0 > k3_lattice3 > k1_zfmisc_1 > k1_lattice3 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.09/1.30  
% 2.09/1.30  %Foreground sorts:
% 2.09/1.30  
% 2.09/1.30  
% 2.09/1.30  %Background operators:
% 2.09/1.30  
% 2.09/1.30  
% 2.09/1.30  %Foreground operators:
% 2.09/1.30  tff(l3_lattices, type, l3_lattices: $i > $o).
% 2.09/1.30  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.09/1.30  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.09/1.30  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.09/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.30  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 2.09/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.30  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.09/1.30  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.09/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.30  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.09/1.30  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 2.09/1.30  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 2.09/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.30  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 2.09/1.30  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.09/1.30  tff(v10_lattices, type, v10_lattices: $i > $o).
% 2.09/1.30  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.09/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.09/1.30  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.09/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.30  tff(v13_lattices, type, v13_lattices: $i > $o).
% 2.09/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.30  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.09/1.30  tff(v3_lattices, type, v3_lattices: $i > $o).
% 2.09/1.30  tff(k5_lattices, type, k5_lattices: $i > $i).
% 2.09/1.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.09/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.09/1.30  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 2.09/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.09/1.30  
% 2.43/1.32  tff(f_143, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow19)).
% 2.43/1.32  tff(f_36, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 2.43/1.32  tff(f_93, axiom, (![A]: (u1_struct_0(k3_yellow_1(A)) = k9_setfam_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_waybel_7)).
% 2.43/1.32  tff(f_89, axiom, (![A]: ((((~v2_struct_0(k3_yellow_1(A)) & v1_orders_2(k3_yellow_1(A))) & v3_orders_2(k3_yellow_1(A))) & v4_orders_2(k3_yellow_1(A))) & v5_orders_2(k3_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_yellow_1)).
% 2.43/1.32  tff(f_45, axiom, (![A]: (~v2_struct_0(k1_lattice3(A)) & v3_lattices(k1_lattice3(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_lattice3)).
% 2.43/1.32  tff(f_49, axiom, (![A]: (v3_lattices(k1_lattice3(A)) & v10_lattices(k1_lattice3(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_lattice3)).
% 2.43/1.32  tff(f_53, axiom, (![A]: (v13_lattices(k1_lattice3(A)) & (k5_lattices(k1_lattice3(A)) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_lattice3)).
% 2.43/1.32  tff(f_40, axiom, (![A]: (v3_lattices(k1_lattice3(A)) & l3_lattices(k1_lattice3(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_lattice3)).
% 2.43/1.32  tff(f_55, axiom, (![A]: (k3_yellow_1(A) = k3_lattice3(k1_lattice3(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_yellow_1)).
% 2.43/1.32  tff(f_78, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v13_lattices(A)) & l3_lattices(A)) => ((((v1_orders_2(k3_lattice3(A)) & v3_orders_2(k3_lattice3(A))) & v4_orders_2(k3_lattice3(A))) & v5_orders_2(k3_lattice3(A))) & v1_yellow_0(k3_lattice3(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_yellow_1)).
% 2.43/1.32  tff(f_59, axiom, (![A]: (v1_orders_2(k3_yellow_1(A)) & l1_orders_2(k3_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow_1)).
% 2.43/1.32  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.43/1.32  tff(f_91, axiom, (![A]: (k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_yellow_1)).
% 2.43/1.32  tff(f_121, axiom, (![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_7)).
% 2.43/1.32  tff(c_70, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.43/1.32  tff(c_66, plain, (v2_waybel_0('#skF_2', k3_yellow_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.43/1.32  tff(c_64, plain, (v13_waybel_0('#skF_2', k3_yellow_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.43/1.32  tff(c_6, plain, (![A_4]: (k9_setfam_1(A_4)=k1_zfmisc_1(A_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.43/1.32  tff(c_52, plain, (![A_14]: (u1_struct_0(k3_yellow_1(A_14))=k9_setfam_1(A_14))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.43/1.32  tff(c_68, plain, (v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.43/1.32  tff(c_74, plain, (v1_subset_1('#skF_2', k9_setfam_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_68])).
% 2.43/1.32  tff(c_80, plain, (v1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_74])).
% 2.43/1.32  tff(c_60, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.43/1.32  tff(c_62, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.43/1.32  tff(c_73, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k9_setfam_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_62])).
% 2.43/1.32  tff(c_79, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_73])).
% 2.43/1.32  tff(c_40, plain, (![A_12]: (~v2_struct_0(k3_yellow_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.43/1.32  tff(c_44, plain, (![A_12]: (v3_orders_2(k3_yellow_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.43/1.32  tff(c_46, plain, (![A_12]: (v4_orders_2(k3_yellow_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.43/1.32  tff(c_48, plain, (![A_12]: (v5_orders_2(k3_yellow_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.43/1.32  tff(c_12, plain, (![A_6]: (~v2_struct_0(k1_lattice3(A_6)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.43/1.32  tff(c_18, plain, (![A_7]: (v10_lattices(k1_lattice3(A_7)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.43/1.32  tff(c_20, plain, (![A_8]: (v13_lattices(k1_lattice3(A_8)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.43/1.32  tff(c_10, plain, (![A_5]: (l3_lattices(k1_lattice3(A_5)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.43/1.32  tff(c_24, plain, (![A_9]: (k3_lattice3(k1_lattice3(A_9))=k3_yellow_1(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.43/1.32  tff(c_177, plain, (![A_45]: (v1_yellow_0(k3_lattice3(A_45)) | ~l3_lattices(A_45) | ~v13_lattices(A_45) | ~v10_lattices(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.43/1.32  tff(c_180, plain, (![A_9]: (v1_yellow_0(k3_yellow_1(A_9)) | ~l3_lattices(k1_lattice3(A_9)) | ~v13_lattices(k1_lattice3(A_9)) | ~v10_lattices(k1_lattice3(A_9)) | v2_struct_0(k1_lattice3(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_177])).
% 2.43/1.32  tff(c_182, plain, (![A_9]: (v1_yellow_0(k3_yellow_1(A_9)) | v2_struct_0(k1_lattice3(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_10, c_180])).
% 2.43/1.32  tff(c_183, plain, (![A_9]: (v1_yellow_0(k3_yellow_1(A_9)))), inference(negUnitSimplification, [status(thm)], [c_12, c_182])).
% 2.43/1.32  tff(c_28, plain, (![A_10]: (l1_orders_2(k3_yellow_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.43/1.32  tff(c_78, plain, (![A_14]: (u1_struct_0(k3_yellow_1(A_14))=k1_zfmisc_1(A_14))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_52])).
% 2.43/1.32  tff(c_58, plain, (v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.43/1.32  tff(c_115, plain, (![A_36]: (k1_xboole_0=A_36 | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.43/1.32  tff(c_119, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_58, c_115])).
% 2.43/1.32  tff(c_50, plain, (![A_13]: (k3_yellow_0(k3_yellow_1(A_13))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.43/1.32  tff(c_121, plain, (![A_13]: (k3_yellow_0(k3_yellow_1(A_13))='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_50])).
% 2.43/1.32  tff(c_221, plain, (![A_54, B_55]: (~r2_hidden(k3_yellow_0(A_54), B_55) | ~v1_subset_1(B_55, u1_struct_0(A_54)) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~v13_waybel_0(B_55, A_54) | ~v2_waybel_0(B_55, A_54) | v1_xboole_0(B_55) | ~l1_orders_2(A_54) | ~v1_yellow_0(A_54) | ~v5_orders_2(A_54) | ~v4_orders_2(A_54) | ~v3_orders_2(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.43/1.32  tff(c_224, plain, (![A_14, B_55]: (~r2_hidden(k3_yellow_0(k3_yellow_1(A_14)), B_55) | ~v1_subset_1(B_55, u1_struct_0(k3_yellow_1(A_14))) | ~m1_subset_1(B_55, k1_zfmisc_1(k1_zfmisc_1(A_14))) | ~v13_waybel_0(B_55, k3_yellow_1(A_14)) | ~v2_waybel_0(B_55, k3_yellow_1(A_14)) | v1_xboole_0(B_55) | ~l1_orders_2(k3_yellow_1(A_14)) | ~v1_yellow_0(k3_yellow_1(A_14)) | ~v5_orders_2(k3_yellow_1(A_14)) | ~v4_orders_2(k3_yellow_1(A_14)) | ~v3_orders_2(k3_yellow_1(A_14)) | v2_struct_0(k3_yellow_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_78, c_221])).
% 2.43/1.32  tff(c_226, plain, (![B_55, A_14]: (~r2_hidden('#skF_3', B_55) | ~v1_subset_1(B_55, k1_zfmisc_1(A_14)) | ~m1_subset_1(B_55, k1_zfmisc_1(k1_zfmisc_1(A_14))) | ~v13_waybel_0(B_55, k3_yellow_1(A_14)) | ~v2_waybel_0(B_55, k3_yellow_1(A_14)) | v1_xboole_0(B_55) | v2_struct_0(k3_yellow_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_48, c_183, c_28, c_78, c_121, c_224])).
% 2.43/1.32  tff(c_228, plain, (![B_56, A_57]: (~r2_hidden('#skF_3', B_56) | ~v1_subset_1(B_56, k1_zfmisc_1(A_57)) | ~m1_subset_1(B_56, k1_zfmisc_1(k1_zfmisc_1(A_57))) | ~v13_waybel_0(B_56, k3_yellow_1(A_57)) | ~v2_waybel_0(B_56, k3_yellow_1(A_57)) | v1_xboole_0(B_56))), inference(negUnitSimplification, [status(thm)], [c_40, c_226])).
% 2.43/1.32  tff(c_231, plain, (~r2_hidden('#skF_3', '#skF_2') | ~v1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')) | ~v13_waybel_0('#skF_2', k3_yellow_1('#skF_1')) | ~v2_waybel_0('#skF_2', k3_yellow_1('#skF_1')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_79, c_228])).
% 2.43/1.32  tff(c_234, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_80, c_60, c_231])).
% 2.43/1.32  tff(c_236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_234])).
% 2.43/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.32  
% 2.43/1.32  Inference rules
% 2.43/1.32  ----------------------
% 2.43/1.32  #Ref     : 0
% 2.43/1.32  #Sup     : 28
% 2.43/1.32  #Fact    : 0
% 2.43/1.32  #Define  : 0
% 2.43/1.32  #Split   : 0
% 2.43/1.32  #Chain   : 0
% 2.43/1.32  #Close   : 0
% 2.43/1.32  
% 2.43/1.32  Ordering : KBO
% 2.43/1.32  
% 2.43/1.32  Simplification rules
% 2.43/1.32  ----------------------
% 2.43/1.32  #Subsume      : 1
% 2.43/1.32  #Demod        : 52
% 2.43/1.32  #Tautology    : 25
% 2.43/1.32  #SimpNegUnit  : 9
% 2.43/1.32  #BackRed      : 3
% 2.43/1.32  
% 2.43/1.32  #Partial instantiations: 0
% 2.43/1.32  #Strategies tried      : 1
% 2.43/1.32  
% 2.43/1.32  Timing (in seconds)
% 2.43/1.32  ----------------------
% 2.43/1.32  Preprocessing        : 0.33
% 2.43/1.32  Parsing              : 0.17
% 2.43/1.32  CNF conversion       : 0.02
% 2.43/1.32  Main loop            : 0.20
% 2.43/1.32  Inferencing          : 0.08
% 2.43/1.32  Reduction            : 0.07
% 2.43/1.32  Demodulation         : 0.05
% 2.43/1.32  BG Simplification    : 0.01
% 2.43/1.32  Subsumption          : 0.03
% 2.43/1.32  Abstraction          : 0.01
% 2.43/1.32  MUC search           : 0.00
% 2.43/1.32  Cooper               : 0.00
% 2.43/1.33  Total                : 0.57
% 2.43/1.33  Index Insertion      : 0.00
% 2.43/1.33  Index Deletion       : 0.00
% 2.43/1.33  Index Matching       : 0.00
% 2.43/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
