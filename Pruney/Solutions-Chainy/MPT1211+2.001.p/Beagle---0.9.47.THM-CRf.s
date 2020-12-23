%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:18 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 127 expanded)
%              Number of leaves         :   37 (  64 expanded)
%              Depth                    :   11
%              Number of atoms          :  171 ( 373 expanded)
%              Number of equality atoms :   23 (  50 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v17_lattices > v16_lattices > v15_lattices > v11_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k2_lattices > k1_lattices > k7_lattices > #nlpp > u1_struct_0 > k6_lattices > k5_lattices > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(k6_lattices,type,(
    k6_lattices: $i > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k2_lattices,type,(
    k2_lattices: ( $i * $i * $i ) > $i )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_lattices,type,(
    k4_lattices: ( $i * $i * $i ) > $i )).

tff(k1_lattices,type,(
    k1_lattices: ( $i * $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff(r2_lattices,type,(
    r2_lattices: ( $i * $i * $i ) > $o )).

tff(v17_lattices,type,(
    v17_lattices: $i > $o )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v11_lattices,type,(
    v11_lattices: $i > $o )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_lattices,type,(
    k5_lattices: $i > $i )).

tff(k7_lattices,type,(
    k7_lattices: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v16_lattices,type,(
    v16_lattices: $i > $o )).

tff(v15_lattices,type,(
    v15_lattices: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_153,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v17_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => k4_lattices(A,k7_lattices(A,B),B) = k5_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_lattices)).

tff(f_119,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k7_lattices(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattices)).

tff(f_47,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( ( ~ v2_struct_0(A)
          & v10_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v4_lattices(A)
          & v5_lattices(A)
          & v6_lattices(A)
          & v7_lattices(A)
          & v8_lattices(A)
          & v9_lattices(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

tff(f_125,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_138,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k2_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

tff(f_63,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( ( ~ v2_struct_0(A)
          & v17_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v11_lattices(A)
          & v15_lattices(A)
          & v16_lattices(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_lattices)).

tff(f_110,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( ( ~ v2_struct_0(A)
              & v10_lattices(A)
              & v11_lattices(A)
              & v16_lattices(A)
              & l3_lattices(A) )
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( C = k7_lattices(A,B)
                <=> r2_lattices(A,C,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattices)).

tff(f_84,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_lattices(A,B,C)
              <=> ( k1_lattices(A,B,C) = k6_lattices(A)
                  & k1_lattices(A,C,B) = k6_lattices(A)
                  & k2_lattices(A,B,C) = k5_lattices(A)
                  & k2_lattices(A,C,B) = k5_lattices(A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_lattices)).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_48,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_50,plain,(
    l3_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_38,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k7_lattices(A_17,B_18),u1_struct_0(A_17))
      | ~ m1_subset_1(B_18,u1_struct_0(A_17))
      | ~ l3_lattices(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_54,plain,(
    v10_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_57,plain,(
    ! [A_24] :
      ( l1_lattices(A_24)
      | ~ l3_lattices(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_61,plain,(
    l1_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_57])).

tff(c_99,plain,(
    ! [A_49,B_50,C_51] :
      ( k4_lattices(A_49,B_50,C_51) = k2_lattices(A_49,B_50,C_51)
      | ~ m1_subset_1(C_51,u1_struct_0(A_49))
      | ~ m1_subset_1(B_50,u1_struct_0(A_49))
      | ~ l1_lattices(A_49)
      | ~ v6_lattices(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_103,plain,(
    ! [B_50] :
      ( k4_lattices('#skF_1',B_50,'#skF_2') = k2_lattices('#skF_1',B_50,'#skF_2')
      | ~ m1_subset_1(B_50,u1_struct_0('#skF_1'))
      | ~ l1_lattices('#skF_1')
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_99])).

tff(c_107,plain,(
    ! [B_50] :
      ( k4_lattices('#skF_1',B_50,'#skF_2') = k2_lattices('#skF_1',B_50,'#skF_2')
      | ~ m1_subset_1(B_50,u1_struct_0('#skF_1'))
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_103])).

tff(c_108,plain,(
    ! [B_50] :
      ( k4_lattices('#skF_1',B_50,'#skF_2') = k2_lattices('#skF_1',B_50,'#skF_2')
      | ~ m1_subset_1(B_50,u1_struct_0('#skF_1'))
      | ~ v6_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_107])).

tff(c_109,plain,(
    ~ v6_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_112,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_109])).

tff(c_115,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_112])).

tff(c_117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_115])).

tff(c_120,plain,(
    ! [B_52] :
      ( k4_lattices('#skF_1',B_52,'#skF_2') = k2_lattices('#skF_1',B_52,'#skF_2')
      | ~ m1_subset_1(B_52,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_124,plain,(
    ! [B_18] :
      ( k4_lattices('#skF_1',k7_lattices('#skF_1',B_18),'#skF_2') = k2_lattices('#skF_1',k7_lattices('#skF_1',B_18),'#skF_2')
      | ~ m1_subset_1(B_18,u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_120])).

tff(c_130,plain,(
    ! [B_18] :
      ( k4_lattices('#skF_1',k7_lattices('#skF_1',B_18),'#skF_2') = k2_lattices('#skF_1',k7_lattices('#skF_1',B_18),'#skF_2')
      | ~ m1_subset_1(B_18,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_124])).

tff(c_137,plain,(
    ! [B_53] :
      ( k4_lattices('#skF_1',k7_lattices('#skF_1',B_53),'#skF_2') = k2_lattices('#skF_1',k7_lattices('#skF_1',B_53),'#skF_2')
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_130])).

tff(c_149,plain,(
    k4_lattices('#skF_1',k7_lattices('#skF_1','#skF_2'),'#skF_2') = k2_lattices('#skF_1',k7_lattices('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_137])).

tff(c_46,plain,(
    k4_lattices('#skF_1',k7_lattices('#skF_1','#skF_2'),'#skF_2') != k5_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_150,plain,(
    k2_lattices('#skF_1',k7_lattices('#skF_1','#skF_2'),'#skF_2') != k5_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_46])).

tff(c_52,plain,(
    v17_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_86,plain,(
    ! [A_33] :
      ( v11_lattices(A_33)
      | ~ v17_lattices(A_33)
      | v2_struct_0(A_33)
      | ~ l3_lattices(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_89,plain,
    ( v11_lattices('#skF_1')
    | ~ v17_lattices('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_86,c_56])).

tff(c_92,plain,(
    v11_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_89])).

tff(c_68,plain,(
    ! [A_27] :
      ( v16_lattices(A_27)
      | ~ v17_lattices(A_27)
      | v2_struct_0(A_27)
      | ~ l3_lattices(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_71,plain,
    ( v16_lattices('#skF_1')
    | ~ v17_lattices('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_56])).

tff(c_74,plain,(
    v16_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_71])).

tff(c_165,plain,(
    ! [A_58,B_59] :
      ( r2_lattices(A_58,k7_lattices(A_58,B_59),B_59)
      | ~ m1_subset_1(k7_lattices(A_58,B_59),u1_struct_0(A_58))
      | ~ v16_lattices(A_58)
      | ~ v11_lattices(A_58)
      | ~ v10_lattices(A_58)
      | ~ m1_subset_1(B_59,u1_struct_0(A_58))
      | ~ l3_lattices(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_179,plain,(
    ! [A_63,B_64] :
      ( r2_lattices(A_63,k7_lattices(A_63,B_64),B_64)
      | ~ v16_lattices(A_63)
      | ~ v11_lattices(A_63)
      | ~ v10_lattices(A_63)
      | ~ m1_subset_1(B_64,u1_struct_0(A_63))
      | ~ l3_lattices(A_63)
      | v2_struct_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_38,c_165])).

tff(c_28,plain,(
    ! [A_3,B_7,C_9] :
      ( k2_lattices(A_3,B_7,C_9) = k5_lattices(A_3)
      | ~ r2_lattices(A_3,B_7,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0(A_3))
      | ~ m1_subset_1(B_7,u1_struct_0(A_3))
      | ~ l3_lattices(A_3)
      | v2_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_388,plain,(
    ! [A_94,B_95] :
      ( k2_lattices(A_94,k7_lattices(A_94,B_95),B_95) = k5_lattices(A_94)
      | ~ m1_subset_1(k7_lattices(A_94,B_95),u1_struct_0(A_94))
      | ~ v16_lattices(A_94)
      | ~ v11_lattices(A_94)
      | ~ v10_lattices(A_94)
      | ~ m1_subset_1(B_95,u1_struct_0(A_94))
      | ~ l3_lattices(A_94)
      | v2_struct_0(A_94) ) ),
    inference(resolution,[status(thm)],[c_179,c_28])).

tff(c_401,plain,(
    ! [A_99,B_100] :
      ( k2_lattices(A_99,k7_lattices(A_99,B_100),B_100) = k5_lattices(A_99)
      | ~ v16_lattices(A_99)
      | ~ v11_lattices(A_99)
      | ~ v10_lattices(A_99)
      | ~ m1_subset_1(B_100,u1_struct_0(A_99))
      | ~ l3_lattices(A_99)
      | v2_struct_0(A_99) ) ),
    inference(resolution,[status(thm)],[c_38,c_388])).

tff(c_405,plain,
    ( k2_lattices('#skF_1',k7_lattices('#skF_1','#skF_2'),'#skF_2') = k5_lattices('#skF_1')
    | ~ v16_lattices('#skF_1')
    | ~ v11_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_401])).

tff(c_409,plain,
    ( k2_lattices('#skF_1',k7_lattices('#skF_1','#skF_2'),'#skF_2') = k5_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_92,c_74,c_405])).

tff(c_411,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_150,c_409])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:27:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.59/1.95  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.59/1.96  
% 3.59/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.97  %$ r2_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v17_lattices > v16_lattices > v15_lattices > v11_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k2_lattices > k1_lattices > k7_lattices > #nlpp > u1_struct_0 > k6_lattices > k5_lattices > #skF_2 > #skF_1
% 3.77/1.97  
% 3.77/1.97  %Foreground sorts:
% 3.77/1.97  
% 3.77/1.97  
% 3.77/1.97  %Background operators:
% 3.77/1.97  
% 3.77/1.97  
% 3.77/1.97  %Foreground operators:
% 3.77/1.97  tff(l3_lattices, type, l3_lattices: $i > $o).
% 3.77/1.97  tff(k6_lattices, type, k6_lattices: $i > $i).
% 3.77/1.97  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.77/1.97  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 3.77/1.97  tff(l2_lattices, type, l2_lattices: $i > $o).
% 3.77/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.77/1.97  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 3.77/1.97  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 3.77/1.97  tff(l1_lattices, type, l1_lattices: $i > $o).
% 3.77/1.97  tff(r2_lattices, type, r2_lattices: ($i * $i * $i) > $o).
% 3.77/1.97  tff(v17_lattices, type, v17_lattices: $i > $o).
% 3.77/1.97  tff(v4_lattices, type, v4_lattices: $i > $o).
% 3.77/1.97  tff(v6_lattices, type, v6_lattices: $i > $o).
% 3.77/1.97  tff('#skF_2', type, '#skF_2': $i).
% 3.77/1.97  tff(v9_lattices, type, v9_lattices: $i > $o).
% 3.77/1.97  tff('#skF_1', type, '#skF_1': $i).
% 3.77/1.97  tff(v5_lattices, type, v5_lattices: $i > $o).
% 3.77/1.97  tff(v10_lattices, type, v10_lattices: $i > $o).
% 3.77/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.77/1.97  tff(v11_lattices, type, v11_lattices: $i > $o).
% 3.77/1.97  tff(v8_lattices, type, v8_lattices: $i > $o).
% 3.77/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.77/1.97  tff(k5_lattices, type, k5_lattices: $i > $i).
% 3.77/1.97  tff(k7_lattices, type, k7_lattices: ($i * $i) > $i).
% 3.77/1.97  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.77/1.97  tff(v16_lattices, type, v16_lattices: $i > $o).
% 3.77/1.97  tff(v15_lattices, type, v15_lattices: $i > $o).
% 3.77/1.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.77/1.97  tff(v7_lattices, type, v7_lattices: $i > $o).
% 3.77/1.97  
% 3.77/1.99  tff(f_153, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v17_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k4_lattices(A, k7_lattices(A, B), B) = k5_lattices(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_lattices)).
% 3.77/1.99  tff(f_119, axiom, (![A, B]: (((~v2_struct_0(A) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k7_lattices(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_lattices)).
% 3.77/1.99  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 3.77/1.99  tff(f_125, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 3.77/1.99  tff(f_138, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k2_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 3.77/1.99  tff(f_63, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v17_lattices(A)) => (((~v2_struct_0(A) & v11_lattices(A)) & v15_lattices(A)) & v16_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_lattices)).
% 3.77/1.99  tff(f_110, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (((((~v2_struct_0(A) & v10_lattices(A)) & v11_lattices(A)) & v16_lattices(A)) & l3_lattices(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k7_lattices(A, B)) <=> r2_lattices(A, C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d21_lattices)).
% 3.77/1.99  tff(f_84, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattices(A, B, C) <=> ((((k1_lattices(A, B, C) = k6_lattices(A)) & (k1_lattices(A, C, B) = k6_lattices(A))) & (k2_lattices(A, B, C) = k5_lattices(A))) & (k2_lattices(A, C, B) = k5_lattices(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_lattices)).
% 3.77/1.99  tff(c_56, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.77/1.99  tff(c_48, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.77/1.99  tff(c_50, plain, (l3_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.77/1.99  tff(c_38, plain, (![A_17, B_18]: (m1_subset_1(k7_lattices(A_17, B_18), u1_struct_0(A_17)) | ~m1_subset_1(B_18, u1_struct_0(A_17)) | ~l3_lattices(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.77/1.99  tff(c_54, plain, (v10_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.77/1.99  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.77/1.99  tff(c_57, plain, (![A_24]: (l1_lattices(A_24) | ~l3_lattices(A_24))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.77/1.99  tff(c_61, plain, (l1_lattices('#skF_1')), inference(resolution, [status(thm)], [c_50, c_57])).
% 3.77/1.99  tff(c_99, plain, (![A_49, B_50, C_51]: (k4_lattices(A_49, B_50, C_51)=k2_lattices(A_49, B_50, C_51) | ~m1_subset_1(C_51, u1_struct_0(A_49)) | ~m1_subset_1(B_50, u1_struct_0(A_49)) | ~l1_lattices(A_49) | ~v6_lattices(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.77/1.99  tff(c_103, plain, (![B_50]: (k4_lattices('#skF_1', B_50, '#skF_2')=k2_lattices('#skF_1', B_50, '#skF_2') | ~m1_subset_1(B_50, u1_struct_0('#skF_1')) | ~l1_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_99])).
% 3.77/1.99  tff(c_107, plain, (![B_50]: (k4_lattices('#skF_1', B_50, '#skF_2')=k2_lattices('#skF_1', B_50, '#skF_2') | ~m1_subset_1(B_50, u1_struct_0('#skF_1')) | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_103])).
% 3.77/1.99  tff(c_108, plain, (![B_50]: (k4_lattices('#skF_1', B_50, '#skF_2')=k2_lattices('#skF_1', B_50, '#skF_2') | ~m1_subset_1(B_50, u1_struct_0('#skF_1')) | ~v6_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_56, c_107])).
% 3.77/1.99  tff(c_109, plain, (~v6_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_108])).
% 3.77/1.99  tff(c_112, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_8, c_109])).
% 3.77/1.99  tff(c_115, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_112])).
% 3.77/1.99  tff(c_117, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_115])).
% 3.77/1.99  tff(c_120, plain, (![B_52]: (k4_lattices('#skF_1', B_52, '#skF_2')=k2_lattices('#skF_1', B_52, '#skF_2') | ~m1_subset_1(B_52, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_108])).
% 3.77/1.99  tff(c_124, plain, (![B_18]: (k4_lattices('#skF_1', k7_lattices('#skF_1', B_18), '#skF_2')=k2_lattices('#skF_1', k7_lattices('#skF_1', B_18), '#skF_2') | ~m1_subset_1(B_18, u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_120])).
% 3.77/1.99  tff(c_130, plain, (![B_18]: (k4_lattices('#skF_1', k7_lattices('#skF_1', B_18), '#skF_2')=k2_lattices('#skF_1', k7_lattices('#skF_1', B_18), '#skF_2') | ~m1_subset_1(B_18, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_124])).
% 3.77/1.99  tff(c_137, plain, (![B_53]: (k4_lattices('#skF_1', k7_lattices('#skF_1', B_53), '#skF_2')=k2_lattices('#skF_1', k7_lattices('#skF_1', B_53), '#skF_2') | ~m1_subset_1(B_53, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_56, c_130])).
% 3.77/1.99  tff(c_149, plain, (k4_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'), '#skF_2')=k2_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_48, c_137])).
% 3.77/1.99  tff(c_46, plain, (k4_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'), '#skF_2')!=k5_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.77/1.99  tff(c_150, plain, (k2_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'), '#skF_2')!=k5_lattices('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_46])).
% 3.77/1.99  tff(c_52, plain, (v17_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.77/1.99  tff(c_86, plain, (![A_33]: (v11_lattices(A_33) | ~v17_lattices(A_33) | v2_struct_0(A_33) | ~l3_lattices(A_33))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.77/1.99  tff(c_89, plain, (v11_lattices('#skF_1') | ~v17_lattices('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_86, c_56])).
% 3.77/1.99  tff(c_92, plain, (v11_lattices('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_89])).
% 3.77/1.99  tff(c_68, plain, (![A_27]: (v16_lattices(A_27) | ~v17_lattices(A_27) | v2_struct_0(A_27) | ~l3_lattices(A_27))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.77/1.99  tff(c_71, plain, (v16_lattices('#skF_1') | ~v17_lattices('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_68, c_56])).
% 3.77/1.99  tff(c_74, plain, (v16_lattices('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_71])).
% 3.77/1.99  tff(c_165, plain, (![A_58, B_59]: (r2_lattices(A_58, k7_lattices(A_58, B_59), B_59) | ~m1_subset_1(k7_lattices(A_58, B_59), u1_struct_0(A_58)) | ~v16_lattices(A_58) | ~v11_lattices(A_58) | ~v10_lattices(A_58) | ~m1_subset_1(B_59, u1_struct_0(A_58)) | ~l3_lattices(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.77/1.99  tff(c_179, plain, (![A_63, B_64]: (r2_lattices(A_63, k7_lattices(A_63, B_64), B_64) | ~v16_lattices(A_63) | ~v11_lattices(A_63) | ~v10_lattices(A_63) | ~m1_subset_1(B_64, u1_struct_0(A_63)) | ~l3_lattices(A_63) | v2_struct_0(A_63))), inference(resolution, [status(thm)], [c_38, c_165])).
% 3.77/1.99  tff(c_28, plain, (![A_3, B_7, C_9]: (k2_lattices(A_3, B_7, C_9)=k5_lattices(A_3) | ~r2_lattices(A_3, B_7, C_9) | ~m1_subset_1(C_9, u1_struct_0(A_3)) | ~m1_subset_1(B_7, u1_struct_0(A_3)) | ~l3_lattices(A_3) | v2_struct_0(A_3))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.77/1.99  tff(c_388, plain, (![A_94, B_95]: (k2_lattices(A_94, k7_lattices(A_94, B_95), B_95)=k5_lattices(A_94) | ~m1_subset_1(k7_lattices(A_94, B_95), u1_struct_0(A_94)) | ~v16_lattices(A_94) | ~v11_lattices(A_94) | ~v10_lattices(A_94) | ~m1_subset_1(B_95, u1_struct_0(A_94)) | ~l3_lattices(A_94) | v2_struct_0(A_94))), inference(resolution, [status(thm)], [c_179, c_28])).
% 3.77/1.99  tff(c_401, plain, (![A_99, B_100]: (k2_lattices(A_99, k7_lattices(A_99, B_100), B_100)=k5_lattices(A_99) | ~v16_lattices(A_99) | ~v11_lattices(A_99) | ~v10_lattices(A_99) | ~m1_subset_1(B_100, u1_struct_0(A_99)) | ~l3_lattices(A_99) | v2_struct_0(A_99))), inference(resolution, [status(thm)], [c_38, c_388])).
% 3.77/1.99  tff(c_405, plain, (k2_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'), '#skF_2')=k5_lattices('#skF_1') | ~v16_lattices('#skF_1') | ~v11_lattices('#skF_1') | ~v10_lattices('#skF_1') | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_401])).
% 3.77/1.99  tff(c_409, plain, (k2_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'), '#skF_2')=k5_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_92, c_74, c_405])).
% 3.77/1.99  tff(c_411, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_150, c_409])).
% 3.77/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.99  
% 3.77/1.99  Inference rules
% 3.77/1.99  ----------------------
% 3.77/1.99  #Ref     : 0
% 3.77/1.99  #Sup     : 75
% 3.77/1.99  #Fact    : 0
% 3.77/1.99  #Define  : 0
% 3.77/1.99  #Split   : 2
% 3.77/1.99  #Chain   : 0
% 3.77/1.99  #Close   : 0
% 3.77/1.99  
% 3.77/1.99  Ordering : KBO
% 3.77/1.99  
% 3.77/1.99  Simplification rules
% 3.77/1.99  ----------------------
% 3.77/1.99  #Subsume      : 5
% 3.77/1.99  #Demod        : 49
% 3.77/1.99  #Tautology    : 37
% 3.77/1.99  #SimpNegUnit  : 18
% 3.77/1.99  #BackRed      : 2
% 3.77/1.99  
% 3.77/1.99  #Partial instantiations: 0
% 3.77/1.99  #Strategies tried      : 1
% 3.77/1.99  
% 3.77/1.99  Timing (in seconds)
% 3.77/1.99  ----------------------
% 3.77/2.00  Preprocessing        : 0.54
% 3.77/2.00  Parsing              : 0.27
% 3.77/2.00  CNF conversion       : 0.04
% 3.77/2.00  Main loop            : 0.52
% 3.77/2.00  Inferencing          : 0.21
% 3.77/2.00  Reduction            : 0.14
% 3.77/2.00  Demodulation         : 0.10
% 3.77/2.00  BG Simplification    : 0.04
% 3.77/2.00  Subsumption          : 0.10
% 3.77/2.00  Abstraction          : 0.03
% 3.77/2.00  MUC search           : 0.00
% 3.77/2.00  Cooper               : 0.00
% 3.77/2.00  Total                : 1.11
% 3.77/2.00  Index Insertion      : 0.00
% 3.77/2.00  Index Deletion       : 0.00
% 3.77/2.00  Index Matching       : 0.00
% 3.77/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
