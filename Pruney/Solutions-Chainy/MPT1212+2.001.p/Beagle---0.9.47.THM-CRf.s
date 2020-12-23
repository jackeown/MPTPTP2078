%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:18 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.81s
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
%$ r2_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v17_lattices > v16_lattices > v15_lattices > v11_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k3_lattices > k2_lattices > k1_lattices > k7_lattices > #nlpp > u1_struct_0 > k6_lattices > k5_lattices > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(k6_lattices,type,(
    k6_lattices: $i > $i )).

tff(k3_lattices,type,(
    k3_lattices: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k2_lattices,type,(
    k2_lattices: ( $i * $i * $i ) > $i )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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
           => k3_lattices(A,k7_lattices(A,B),B) = k6_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_lattices)).

tff(f_119,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k7_lattices(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

tff(f_125,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_138,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k1_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

tff(f_63,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( ( ~ v2_struct_0(A)
          & v17_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v11_lattices(A)
          & v15_lattices(A)
          & v16_lattices(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_lattices)).

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

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_62,plain,(
    ! [A_25] :
      ( l2_lattices(A_25)
      | ~ l3_lattices(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_66,plain,(
    l2_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_62])).

tff(c_99,plain,(
    ! [A_49,B_50,C_51] :
      ( k3_lattices(A_49,B_50,C_51) = k1_lattices(A_49,B_50,C_51)
      | ~ m1_subset_1(C_51,u1_struct_0(A_49))
      | ~ m1_subset_1(B_50,u1_struct_0(A_49))
      | ~ l2_lattices(A_49)
      | ~ v4_lattices(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_103,plain,(
    ! [B_50] :
      ( k3_lattices('#skF_1',B_50,'#skF_2') = k1_lattices('#skF_1',B_50,'#skF_2')
      | ~ m1_subset_1(B_50,u1_struct_0('#skF_1'))
      | ~ l2_lattices('#skF_1')
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_99])).

tff(c_107,plain,(
    ! [B_50] :
      ( k3_lattices('#skF_1',B_50,'#skF_2') = k1_lattices('#skF_1',B_50,'#skF_2')
      | ~ m1_subset_1(B_50,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_103])).

tff(c_108,plain,(
    ! [B_50] :
      ( k3_lattices('#skF_1',B_50,'#skF_2') = k1_lattices('#skF_1',B_50,'#skF_2')
      | ~ m1_subset_1(B_50,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_107])).

tff(c_109,plain,(
    ~ v4_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_112,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_109])).

tff(c_115,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_112])).

tff(c_117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_115])).

tff(c_120,plain,(
    ! [B_52] :
      ( k3_lattices('#skF_1',B_52,'#skF_2') = k1_lattices('#skF_1',B_52,'#skF_2')
      | ~ m1_subset_1(B_52,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_124,plain,(
    ! [B_18] :
      ( k3_lattices('#skF_1',k7_lattices('#skF_1',B_18),'#skF_2') = k1_lattices('#skF_1',k7_lattices('#skF_1',B_18),'#skF_2')
      | ~ m1_subset_1(B_18,u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_120])).

tff(c_130,plain,(
    ! [B_18] :
      ( k3_lattices('#skF_1',k7_lattices('#skF_1',B_18),'#skF_2') = k1_lattices('#skF_1',k7_lattices('#skF_1',B_18),'#skF_2')
      | ~ m1_subset_1(B_18,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_124])).

tff(c_137,plain,(
    ! [B_53] :
      ( k3_lattices('#skF_1',k7_lattices('#skF_1',B_53),'#skF_2') = k1_lattices('#skF_1',k7_lattices('#skF_1',B_53),'#skF_2')
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_130])).

tff(c_149,plain,(
    k3_lattices('#skF_1',k7_lattices('#skF_1','#skF_2'),'#skF_2') = k1_lattices('#skF_1',k7_lattices('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_137])).

tff(c_46,plain,(
    k3_lattices('#skF_1',k7_lattices('#skF_1','#skF_2'),'#skF_2') != k6_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_150,plain,(
    k1_lattices('#skF_1',k7_lattices('#skF_1','#skF_2'),'#skF_2') != k6_lattices('#skF_1') ),
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

tff(c_32,plain,(
    ! [A_3,B_7,C_9] :
      ( k1_lattices(A_3,B_7,C_9) = k6_lattices(A_3)
      | ~ r2_lattices(A_3,B_7,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0(A_3))
      | ~ m1_subset_1(B_7,u1_struct_0(A_3))
      | ~ l3_lattices(A_3)
      | v2_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_246,plain,(
    ! [A_71,B_72] :
      ( k1_lattices(A_71,k7_lattices(A_71,B_72),B_72) = k6_lattices(A_71)
      | ~ m1_subset_1(k7_lattices(A_71,B_72),u1_struct_0(A_71))
      | ~ v16_lattices(A_71)
      | ~ v11_lattices(A_71)
      | ~ v10_lattices(A_71)
      | ~ m1_subset_1(B_72,u1_struct_0(A_71))
      | ~ l3_lattices(A_71)
      | v2_struct_0(A_71) ) ),
    inference(resolution,[status(thm)],[c_179,c_32])).

tff(c_281,plain,(
    ! [A_74,B_75] :
      ( k1_lattices(A_74,k7_lattices(A_74,B_75),B_75) = k6_lattices(A_74)
      | ~ v16_lattices(A_74)
      | ~ v11_lattices(A_74)
      | ~ v10_lattices(A_74)
      | ~ m1_subset_1(B_75,u1_struct_0(A_74))
      | ~ l3_lattices(A_74)
      | v2_struct_0(A_74) ) ),
    inference(resolution,[status(thm)],[c_38,c_246])).

tff(c_285,plain,
    ( k1_lattices('#skF_1',k7_lattices('#skF_1','#skF_2'),'#skF_2') = k6_lattices('#skF_1')
    | ~ v16_lattices('#skF_1')
    | ~ v11_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_281])).

tff(c_289,plain,
    ( k1_lattices('#skF_1',k7_lattices('#skF_1','#skF_2'),'#skF_2') = k6_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_92,c_74,c_285])).

tff(c_291,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_150,c_289])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:22:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.35  
% 2.70/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.35  %$ r2_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v17_lattices > v16_lattices > v15_lattices > v11_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k3_lattices > k2_lattices > k1_lattices > k7_lattices > #nlpp > u1_struct_0 > k6_lattices > k5_lattices > #skF_2 > #skF_1
% 2.70/1.35  
% 2.70/1.35  %Foreground sorts:
% 2.70/1.35  
% 2.70/1.35  
% 2.70/1.35  %Background operators:
% 2.70/1.35  
% 2.70/1.35  
% 2.70/1.35  %Foreground operators:
% 2.70/1.35  tff(l3_lattices, type, l3_lattices: $i > $o).
% 2.70/1.35  tff(k6_lattices, type, k6_lattices: $i > $i).
% 2.70/1.35  tff(k3_lattices, type, k3_lattices: ($i * $i * $i) > $i).
% 2.70/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.70/1.35  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 2.70/1.35  tff(l2_lattices, type, l2_lattices: $i > $o).
% 2.70/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.35  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 2.70/1.35  tff(l1_lattices, type, l1_lattices: $i > $o).
% 2.70/1.35  tff(r2_lattices, type, r2_lattices: ($i * $i * $i) > $o).
% 2.70/1.35  tff(v17_lattices, type, v17_lattices: $i > $o).
% 2.70/1.35  tff(v4_lattices, type, v4_lattices: $i > $o).
% 2.70/1.35  tff(v6_lattices, type, v6_lattices: $i > $o).
% 2.70/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.70/1.35  tff(v9_lattices, type, v9_lattices: $i > $o).
% 2.70/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.70/1.35  tff(v5_lattices, type, v5_lattices: $i > $o).
% 2.70/1.35  tff(v10_lattices, type, v10_lattices: $i > $o).
% 2.70/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.35  tff(v11_lattices, type, v11_lattices: $i > $o).
% 2.70/1.35  tff(v8_lattices, type, v8_lattices: $i > $o).
% 2.70/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.35  tff(k5_lattices, type, k5_lattices: $i > $i).
% 2.70/1.35  tff(k7_lattices, type, k7_lattices: ($i * $i) > $i).
% 2.70/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.70/1.35  tff(v16_lattices, type, v16_lattices: $i > $o).
% 2.70/1.35  tff(v15_lattices, type, v15_lattices: $i > $o).
% 2.70/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.70/1.35  tff(v7_lattices, type, v7_lattices: $i > $o).
% 2.70/1.35  
% 2.81/1.37  tff(f_153, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v17_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k3_lattices(A, k7_lattices(A, B), B) = k6_lattices(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_lattices)).
% 2.81/1.37  tff(f_119, axiom, (![A, B]: (((~v2_struct_0(A) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k7_lattices(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_lattices)).
% 2.81/1.37  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 2.81/1.37  tff(f_125, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 2.81/1.37  tff(f_138, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 2.81/1.37  tff(f_63, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v17_lattices(A)) => (((~v2_struct_0(A) & v11_lattices(A)) & v15_lattices(A)) & v16_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_lattices)).
% 2.81/1.37  tff(f_110, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (((((~v2_struct_0(A) & v10_lattices(A)) & v11_lattices(A)) & v16_lattices(A)) & l3_lattices(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k7_lattices(A, B)) <=> r2_lattices(A, C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d21_lattices)).
% 2.81/1.37  tff(f_84, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattices(A, B, C) <=> ((((k1_lattices(A, B, C) = k6_lattices(A)) & (k1_lattices(A, C, B) = k6_lattices(A))) & (k2_lattices(A, B, C) = k5_lattices(A))) & (k2_lattices(A, C, B) = k5_lattices(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_lattices)).
% 2.81/1.37  tff(c_56, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.81/1.37  tff(c_48, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.81/1.37  tff(c_50, plain, (l3_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.81/1.37  tff(c_38, plain, (![A_17, B_18]: (m1_subset_1(k7_lattices(A_17, B_18), u1_struct_0(A_17)) | ~m1_subset_1(B_18, u1_struct_0(A_17)) | ~l3_lattices(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.81/1.37  tff(c_54, plain, (v10_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.81/1.37  tff(c_12, plain, (![A_1]: (v4_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.81/1.37  tff(c_62, plain, (![A_25]: (l2_lattices(A_25) | ~l3_lattices(A_25))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.81/1.37  tff(c_66, plain, (l2_lattices('#skF_1')), inference(resolution, [status(thm)], [c_50, c_62])).
% 2.81/1.37  tff(c_99, plain, (![A_49, B_50, C_51]: (k3_lattices(A_49, B_50, C_51)=k1_lattices(A_49, B_50, C_51) | ~m1_subset_1(C_51, u1_struct_0(A_49)) | ~m1_subset_1(B_50, u1_struct_0(A_49)) | ~l2_lattices(A_49) | ~v4_lattices(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.81/1.37  tff(c_103, plain, (![B_50]: (k3_lattices('#skF_1', B_50, '#skF_2')=k1_lattices('#skF_1', B_50, '#skF_2') | ~m1_subset_1(B_50, u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_99])).
% 2.81/1.37  tff(c_107, plain, (![B_50]: (k3_lattices('#skF_1', B_50, '#skF_2')=k1_lattices('#skF_1', B_50, '#skF_2') | ~m1_subset_1(B_50, u1_struct_0('#skF_1')) | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_103])).
% 2.81/1.37  tff(c_108, plain, (![B_50]: (k3_lattices('#skF_1', B_50, '#skF_2')=k1_lattices('#skF_1', B_50, '#skF_2') | ~m1_subset_1(B_50, u1_struct_0('#skF_1')) | ~v4_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_56, c_107])).
% 2.81/1.37  tff(c_109, plain, (~v4_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_108])).
% 2.81/1.37  tff(c_112, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_12, c_109])).
% 2.81/1.37  tff(c_115, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_112])).
% 2.81/1.37  tff(c_117, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_115])).
% 2.81/1.37  tff(c_120, plain, (![B_52]: (k3_lattices('#skF_1', B_52, '#skF_2')=k1_lattices('#skF_1', B_52, '#skF_2') | ~m1_subset_1(B_52, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_108])).
% 2.81/1.37  tff(c_124, plain, (![B_18]: (k3_lattices('#skF_1', k7_lattices('#skF_1', B_18), '#skF_2')=k1_lattices('#skF_1', k7_lattices('#skF_1', B_18), '#skF_2') | ~m1_subset_1(B_18, u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_120])).
% 2.81/1.37  tff(c_130, plain, (![B_18]: (k3_lattices('#skF_1', k7_lattices('#skF_1', B_18), '#skF_2')=k1_lattices('#skF_1', k7_lattices('#skF_1', B_18), '#skF_2') | ~m1_subset_1(B_18, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_124])).
% 2.81/1.37  tff(c_137, plain, (![B_53]: (k3_lattices('#skF_1', k7_lattices('#skF_1', B_53), '#skF_2')=k1_lattices('#skF_1', k7_lattices('#skF_1', B_53), '#skF_2') | ~m1_subset_1(B_53, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_56, c_130])).
% 2.81/1.37  tff(c_149, plain, (k3_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'), '#skF_2')=k1_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_48, c_137])).
% 2.81/1.37  tff(c_46, plain, (k3_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'), '#skF_2')!=k6_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.81/1.37  tff(c_150, plain, (k1_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'), '#skF_2')!=k6_lattices('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_46])).
% 2.81/1.37  tff(c_52, plain, (v17_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.81/1.37  tff(c_86, plain, (![A_33]: (v11_lattices(A_33) | ~v17_lattices(A_33) | v2_struct_0(A_33) | ~l3_lattices(A_33))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.81/1.37  tff(c_89, plain, (v11_lattices('#skF_1') | ~v17_lattices('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_86, c_56])).
% 2.81/1.37  tff(c_92, plain, (v11_lattices('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_89])).
% 2.81/1.37  tff(c_68, plain, (![A_27]: (v16_lattices(A_27) | ~v17_lattices(A_27) | v2_struct_0(A_27) | ~l3_lattices(A_27))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.81/1.37  tff(c_71, plain, (v16_lattices('#skF_1') | ~v17_lattices('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_68, c_56])).
% 2.81/1.37  tff(c_74, plain, (v16_lattices('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_71])).
% 2.81/1.37  tff(c_165, plain, (![A_58, B_59]: (r2_lattices(A_58, k7_lattices(A_58, B_59), B_59) | ~m1_subset_1(k7_lattices(A_58, B_59), u1_struct_0(A_58)) | ~v16_lattices(A_58) | ~v11_lattices(A_58) | ~v10_lattices(A_58) | ~m1_subset_1(B_59, u1_struct_0(A_58)) | ~l3_lattices(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.81/1.37  tff(c_179, plain, (![A_63, B_64]: (r2_lattices(A_63, k7_lattices(A_63, B_64), B_64) | ~v16_lattices(A_63) | ~v11_lattices(A_63) | ~v10_lattices(A_63) | ~m1_subset_1(B_64, u1_struct_0(A_63)) | ~l3_lattices(A_63) | v2_struct_0(A_63))), inference(resolution, [status(thm)], [c_38, c_165])).
% 2.81/1.37  tff(c_32, plain, (![A_3, B_7, C_9]: (k1_lattices(A_3, B_7, C_9)=k6_lattices(A_3) | ~r2_lattices(A_3, B_7, C_9) | ~m1_subset_1(C_9, u1_struct_0(A_3)) | ~m1_subset_1(B_7, u1_struct_0(A_3)) | ~l3_lattices(A_3) | v2_struct_0(A_3))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.81/1.37  tff(c_246, plain, (![A_71, B_72]: (k1_lattices(A_71, k7_lattices(A_71, B_72), B_72)=k6_lattices(A_71) | ~m1_subset_1(k7_lattices(A_71, B_72), u1_struct_0(A_71)) | ~v16_lattices(A_71) | ~v11_lattices(A_71) | ~v10_lattices(A_71) | ~m1_subset_1(B_72, u1_struct_0(A_71)) | ~l3_lattices(A_71) | v2_struct_0(A_71))), inference(resolution, [status(thm)], [c_179, c_32])).
% 2.81/1.37  tff(c_281, plain, (![A_74, B_75]: (k1_lattices(A_74, k7_lattices(A_74, B_75), B_75)=k6_lattices(A_74) | ~v16_lattices(A_74) | ~v11_lattices(A_74) | ~v10_lattices(A_74) | ~m1_subset_1(B_75, u1_struct_0(A_74)) | ~l3_lattices(A_74) | v2_struct_0(A_74))), inference(resolution, [status(thm)], [c_38, c_246])).
% 2.81/1.37  tff(c_285, plain, (k1_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'), '#skF_2')=k6_lattices('#skF_1') | ~v16_lattices('#skF_1') | ~v11_lattices('#skF_1') | ~v10_lattices('#skF_1') | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_281])).
% 2.81/1.37  tff(c_289, plain, (k1_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'), '#skF_2')=k6_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_92, c_74, c_285])).
% 2.81/1.37  tff(c_291, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_150, c_289])).
% 2.81/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.37  
% 2.81/1.37  Inference rules
% 2.81/1.37  ----------------------
% 2.81/1.37  #Ref     : 0
% 2.81/1.37  #Sup     : 44
% 2.81/1.37  #Fact    : 0
% 2.81/1.37  #Define  : 0
% 2.81/1.37  #Split   : 2
% 2.81/1.37  #Chain   : 0
% 2.81/1.37  #Close   : 0
% 2.81/1.37  
% 2.81/1.37  Ordering : KBO
% 2.81/1.37  
% 2.81/1.37  Simplification rules
% 2.81/1.37  ----------------------
% 2.81/1.37  #Subsume      : 2
% 2.81/1.37  #Demod        : 35
% 2.81/1.37  #Tautology    : 17
% 2.81/1.37  #SimpNegUnit  : 14
% 2.81/1.37  #BackRed      : 1
% 2.81/1.37  
% 2.81/1.37  #Partial instantiations: 0
% 2.81/1.37  #Strategies tried      : 1
% 2.81/1.37  
% 2.81/1.37  Timing (in seconds)
% 2.81/1.37  ----------------------
% 2.81/1.37  Preprocessing        : 0.34
% 2.81/1.37  Parsing              : 0.17
% 2.81/1.37  CNF conversion       : 0.02
% 2.81/1.37  Main loop            : 0.26
% 2.81/1.38  Inferencing          : 0.10
% 2.81/1.38  Reduction            : 0.07
% 2.81/1.38  Demodulation         : 0.05
% 2.81/1.38  BG Simplification    : 0.02
% 2.81/1.38  Subsumption          : 0.05
% 2.81/1.38  Abstraction          : 0.02
% 2.81/1.38  MUC search           : 0.00
% 2.81/1.38  Cooper               : 0.00
% 2.81/1.38  Total                : 0.64
% 2.81/1.38  Index Insertion      : 0.00
% 2.81/1.38  Index Deletion       : 0.00
% 2.81/1.38  Index Matching       : 0.00
% 2.81/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
