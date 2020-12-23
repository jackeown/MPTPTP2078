%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:19 EST 2020

% Result     : Theorem 4.78s
% Output     : CNFRefutation 4.78s
% Verified   : 
% Statistics : Number of formulae       :  186 (1122 expanded)
%              Number of leaves         :   38 ( 400 expanded)
%              Depth                    :   22
%              Number of atoms          :  511 (4561 expanded)
%              Number of equality atoms :   79 ( 329 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v17_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k2_lattices > k1_lattices > k7_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(k3_lattices,type,(
    k3_lattices: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k2_lattices,type,(
    k2_lattices: ( $i * $i * $i ) > $i )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_lattices,type,(
    k4_lattices: ( $i * $i * $i ) > $i )).

tff(k1_lattices,type,(
    k1_lattices: ( $i * $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k7_lattices,type,(
    k7_lattices: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_191,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v17_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r3_lattices(A,B,C)
                 => r3_lattices(A,k7_lattices(A,C),k7_lattices(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_lattices)).

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

tff(f_90,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k1_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k3_lattices(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_lattices(A,B,C)
              <=> k1_lattices(A,B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k2_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

tff(f_154,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_lattices(A,B,C)
              <=> k2_lattices(A,B,C) = B ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).

tff(f_135,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_lattices(A,B,C)
      <=> r1_lattices(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k7_lattices(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattices)).

tff(f_171,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v17_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k7_lattices(A,k3_lattices(A,B,C)) = k4_lattices(A,k7_lattices(A,B),k7_lattices(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_lattices)).

tff(c_48,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_50,plain,(
    l3_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_54,plain,(
    v10_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_62,plain,(
    ! [A_43] :
      ( l2_lattices(A_43)
      | ~ l3_lattices(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_66,plain,(
    l2_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_62])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_143,plain,(
    ! [A_62,B_63,C_64] :
      ( k3_lattices(A_62,B_63,C_64) = k1_lattices(A_62,B_63,C_64)
      | ~ m1_subset_1(C_64,u1_struct_0(A_62))
      | ~ m1_subset_1(B_63,u1_struct_0(A_62))
      | ~ l2_lattices(A_62)
      | ~ v4_lattices(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_147,plain,(
    ! [B_63] :
      ( k3_lattices('#skF_1',B_63,'#skF_3') = k1_lattices('#skF_1',B_63,'#skF_3')
      | ~ m1_subset_1(B_63,u1_struct_0('#skF_1'))
      | ~ l2_lattices('#skF_1')
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_46,c_143])).

tff(c_153,plain,(
    ! [B_63] :
      ( k3_lattices('#skF_1',B_63,'#skF_3') = k1_lattices('#skF_1',B_63,'#skF_3')
      | ~ m1_subset_1(B_63,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_147])).

tff(c_154,plain,(
    ! [B_63] :
      ( k3_lattices('#skF_1',B_63,'#skF_3') = k1_lattices('#skF_1',B_63,'#skF_3')
      | ~ m1_subset_1(B_63,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_153])).

tff(c_159,plain,(
    ~ v4_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_178,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_159])).

tff(c_181,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_178])).

tff(c_183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_181])).

tff(c_186,plain,(
    ! [B_68] :
      ( k3_lattices('#skF_1',B_68,'#skF_3') = k1_lattices('#skF_1',B_68,'#skF_3')
      | ~ m1_subset_1(B_68,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_202,plain,(
    k3_lattices('#skF_1','#skF_2','#skF_3') = k1_lattices('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_186])).

tff(c_185,plain,(
    v4_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_149,plain,(
    ! [B_63] :
      ( k3_lattices('#skF_1',B_63,'#skF_2') = k1_lattices('#skF_1',B_63,'#skF_2')
      | ~ m1_subset_1(B_63,u1_struct_0('#skF_1'))
      | ~ l2_lattices('#skF_1')
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_143])).

tff(c_157,plain,(
    ! [B_63] :
      ( k3_lattices('#skF_1',B_63,'#skF_2') = k1_lattices('#skF_1',B_63,'#skF_2')
      | ~ m1_subset_1(B_63,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_149])).

tff(c_158,plain,(
    ! [B_63] :
      ( k3_lattices('#skF_1',B_63,'#skF_2') = k1_lattices('#skF_1',B_63,'#skF_2')
      | ~ m1_subset_1(B_63,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_157])).

tff(c_213,plain,(
    ! [B_69] :
      ( k3_lattices('#skF_1',B_69,'#skF_2') = k1_lattices('#skF_1',B_69,'#skF_2')
      | ~ m1_subset_1(B_69,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_158])).

tff(c_228,plain,(
    k3_lattices('#skF_1','#skF_3','#skF_2') = k1_lattices('#skF_1','#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_213])).

tff(c_316,plain,(
    ! [A_75,C_76,B_77] :
      ( k3_lattices(A_75,C_76,B_77) = k3_lattices(A_75,B_77,C_76)
      | ~ m1_subset_1(C_76,u1_struct_0(A_75))
      | ~ m1_subset_1(B_77,u1_struct_0(A_75))
      | ~ l2_lattices(A_75)
      | ~ v4_lattices(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_320,plain,(
    ! [B_77] :
      ( k3_lattices('#skF_1',B_77,'#skF_3') = k3_lattices('#skF_1','#skF_3',B_77)
      | ~ m1_subset_1(B_77,u1_struct_0('#skF_1'))
      | ~ l2_lattices('#skF_1')
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_46,c_316])).

tff(c_326,plain,(
    ! [B_77] :
      ( k3_lattices('#skF_1',B_77,'#skF_3') = k3_lattices('#skF_1','#skF_3',B_77)
      | ~ m1_subset_1(B_77,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_66,c_320])).

tff(c_332,plain,(
    ! [B_78] :
      ( k3_lattices('#skF_1',B_78,'#skF_3') = k3_lattices('#skF_1','#skF_3',B_78)
      | ~ m1_subset_1(B_78,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_326])).

tff(c_342,plain,(
    k3_lattices('#skF_1','#skF_2','#skF_3') = k3_lattices('#skF_1','#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_332])).

tff(c_350,plain,(
    k1_lattices('#skF_1','#skF_2','#skF_3') = k1_lattices('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_228,c_342])).

tff(c_74,plain,(
    ! [A_52,B_53,C_54] :
      ( r1_lattices(A_52,B_53,C_54)
      | k1_lattices(A_52,B_53,C_54) != C_54
      | ~ m1_subset_1(C_54,u1_struct_0(A_52))
      | ~ m1_subset_1(B_53,u1_struct_0(A_52))
      | ~ l2_lattices(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_78,plain,(
    ! [B_53] :
      ( r1_lattices('#skF_1',B_53,'#skF_3')
      | k1_lattices('#skF_1',B_53,'#skF_3') != '#skF_3'
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_1'))
      | ~ l2_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_46,c_74])).

tff(c_84,plain,(
    ! [B_53] :
      ( r1_lattices('#skF_1',B_53,'#skF_3')
      | k1_lattices('#skF_1',B_53,'#skF_3') != '#skF_3'
      | ~ m1_subset_1(B_53,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_78])).

tff(c_90,plain,(
    ! [B_55] :
      ( r1_lattices('#skF_1',B_55,'#skF_3')
      | k1_lattices('#skF_1',B_55,'#skF_3') != '#skF_3'
      | ~ m1_subset_1(B_55,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_84])).

tff(c_106,plain,
    ( r1_lattices('#skF_1','#skF_2','#skF_3')
    | k1_lattices('#skF_1','#skF_2','#skF_3') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_48,c_90])).

tff(c_108,plain,(
    k1_lattices('#skF_1','#skF_2','#skF_3') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_352,plain,(
    k1_lattices('#skF_1','#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_108])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_57,plain,(
    ! [A_42] :
      ( l1_lattices(A_42)
      | ~ l3_lattices(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_61,plain,(
    l1_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_57])).

tff(c_255,plain,(
    ! [A_71,B_72,C_73] :
      ( k4_lattices(A_71,B_72,C_73) = k2_lattices(A_71,B_72,C_73)
      | ~ m1_subset_1(C_73,u1_struct_0(A_71))
      | ~ m1_subset_1(B_72,u1_struct_0(A_71))
      | ~ l1_lattices(A_71)
      | ~ v6_lattices(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_261,plain,(
    ! [B_72] :
      ( k4_lattices('#skF_1',B_72,'#skF_2') = k2_lattices('#skF_1',B_72,'#skF_2')
      | ~ m1_subset_1(B_72,u1_struct_0('#skF_1'))
      | ~ l1_lattices('#skF_1')
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_255])).

tff(c_269,plain,(
    ! [B_72] :
      ( k4_lattices('#skF_1',B_72,'#skF_2') = k2_lattices('#skF_1',B_72,'#skF_2')
      | ~ m1_subset_1(B_72,u1_struct_0('#skF_1'))
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_261])).

tff(c_270,plain,(
    ! [B_72] :
      ( k4_lattices('#skF_1',B_72,'#skF_2') = k2_lattices('#skF_1',B_72,'#skF_2')
      | ~ m1_subset_1(B_72,u1_struct_0('#skF_1'))
      | ~ v6_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_269])).

tff(c_279,plain,(
    ~ v6_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_270])).

tff(c_283,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_279])).

tff(c_286,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_283])).

tff(c_288,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_286])).

tff(c_290,plain,(
    v6_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_270])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_408,plain,(
    ! [A_81,B_82,C_83] :
      ( r1_lattices(A_81,B_82,C_83)
      | k2_lattices(A_81,B_82,C_83) != B_82
      | ~ m1_subset_1(C_83,u1_struct_0(A_81))
      | ~ m1_subset_1(B_82,u1_struct_0(A_81))
      | ~ l3_lattices(A_81)
      | ~ v9_lattices(A_81)
      | ~ v8_lattices(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_412,plain,(
    ! [B_82] :
      ( r1_lattices('#skF_1',B_82,'#skF_3')
      | k2_lattices('#skF_1',B_82,'#skF_3') != B_82
      | ~ m1_subset_1(B_82,u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | ~ v9_lattices('#skF_1')
      | ~ v8_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_46,c_408])).

tff(c_418,plain,(
    ! [B_82] :
      ( r1_lattices('#skF_1',B_82,'#skF_3')
      | k2_lattices('#skF_1',B_82,'#skF_3') != B_82
      | ~ m1_subset_1(B_82,u1_struct_0('#skF_1'))
      | ~ v9_lattices('#skF_1')
      | ~ v8_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_412])).

tff(c_419,plain,(
    ! [B_82] :
      ( r1_lattices('#skF_1',B_82,'#skF_3')
      | k2_lattices('#skF_1',B_82,'#skF_3') != B_82
      | ~ m1_subset_1(B_82,u1_struct_0('#skF_1'))
      | ~ v9_lattices('#skF_1')
      | ~ v8_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_418])).

tff(c_574,plain,(
    ~ v8_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_419])).

tff(c_584,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_574])).

tff(c_587,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_584])).

tff(c_589,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_587])).

tff(c_591,plain,(
    v8_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_419])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_590,plain,(
    ! [B_82] :
      ( ~ v9_lattices('#skF_1')
      | r1_lattices('#skF_1',B_82,'#skF_3')
      | k2_lattices('#skF_1',B_82,'#skF_3') != B_82
      | ~ m1_subset_1(B_82,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_419])).

tff(c_592,plain,(
    ~ v9_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_590])).

tff(c_598,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_592])).

tff(c_601,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_598])).

tff(c_603,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_601])).

tff(c_605,plain,(
    v9_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_590])).

tff(c_44,plain,(
    r3_lattices('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_624,plain,(
    ! [A_96,B_97,C_98] :
      ( r1_lattices(A_96,B_97,C_98)
      | ~ r3_lattices(A_96,B_97,C_98)
      | ~ m1_subset_1(C_98,u1_struct_0(A_96))
      | ~ m1_subset_1(B_97,u1_struct_0(A_96))
      | ~ l3_lattices(A_96)
      | ~ v9_lattices(A_96)
      | ~ v8_lattices(A_96)
      | ~ v6_lattices(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_626,plain,
    ( r1_lattices('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l3_lattices('#skF_1')
    | ~ v9_lattices('#skF_1')
    | ~ v8_lattices('#skF_1')
    | ~ v6_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_624])).

tff(c_629,plain,
    ( r1_lattices('#skF_1','#skF_2','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_591,c_605,c_50,c_48,c_46,c_626])).

tff(c_630,plain,(
    r1_lattices('#skF_1','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_629])).

tff(c_20,plain,(
    ! [A_5,B_9,C_11] :
      ( k1_lattices(A_5,B_9,C_11) = C_11
      | ~ r1_lattices(A_5,B_9,C_11)
      | ~ m1_subset_1(C_11,u1_struct_0(A_5))
      | ~ m1_subset_1(B_9,u1_struct_0(A_5))
      | ~ l2_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_634,plain,
    ( k1_lattices('#skF_1','#skF_2','#skF_3') = '#skF_3'
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l2_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_630,c_20])).

tff(c_641,plain,
    ( k1_lattices('#skF_1','#skF_3','#skF_2') = '#skF_3'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_48,c_46,c_350,c_634])).

tff(c_643,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_352,c_641])).

tff(c_645,plain,(
    k1_lattices('#skF_1','#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_690,plain,(
    ! [A_105,C_106,B_107] :
      ( k3_lattices(A_105,C_106,B_107) = k3_lattices(A_105,B_107,C_106)
      | ~ m1_subset_1(C_106,u1_struct_0(A_105))
      | ~ m1_subset_1(B_107,u1_struct_0(A_105))
      | ~ l2_lattices(A_105)
      | ~ v4_lattices(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_694,plain,(
    ! [B_107] :
      ( k3_lattices('#skF_1',B_107,'#skF_3') = k3_lattices('#skF_1','#skF_3',B_107)
      | ~ m1_subset_1(B_107,u1_struct_0('#skF_1'))
      | ~ l2_lattices('#skF_1')
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_46,c_690])).

tff(c_700,plain,(
    ! [B_107] :
      ( k3_lattices('#skF_1',B_107,'#skF_3') = k3_lattices('#skF_1','#skF_3',B_107)
      | ~ m1_subset_1(B_107,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_694])).

tff(c_701,plain,(
    ! [B_107] :
      ( k3_lattices('#skF_1',B_107,'#skF_3') = k3_lattices('#skF_1','#skF_3',B_107)
      | ~ m1_subset_1(B_107,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_700])).

tff(c_706,plain,(
    ~ v4_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_701])).

tff(c_710,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_706])).

tff(c_713,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_710])).

tff(c_715,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_713])).

tff(c_717,plain,(
    v4_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_701])).

tff(c_840,plain,(
    ! [A_115,B_116,C_117] :
      ( k3_lattices(A_115,B_116,C_117) = k1_lattices(A_115,B_116,C_117)
      | ~ m1_subset_1(C_117,u1_struct_0(A_115))
      | ~ m1_subset_1(B_116,u1_struct_0(A_115))
      | ~ l2_lattices(A_115)
      | ~ v4_lattices(A_115)
      | v2_struct_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_844,plain,(
    ! [B_116] :
      ( k3_lattices('#skF_1',B_116,'#skF_3') = k1_lattices('#skF_1',B_116,'#skF_3')
      | ~ m1_subset_1(B_116,u1_struct_0('#skF_1'))
      | ~ l2_lattices('#skF_1')
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_46,c_840])).

tff(c_850,plain,(
    ! [B_116] :
      ( k3_lattices('#skF_1',B_116,'#skF_3') = k1_lattices('#skF_1',B_116,'#skF_3')
      | ~ m1_subset_1(B_116,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_717,c_66,c_844])).

tff(c_856,plain,(
    ! [B_118] :
      ( k3_lattices('#skF_1',B_118,'#skF_3') = k1_lattices('#skF_1',B_118,'#skF_3')
      | ~ m1_subset_1(B_118,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_850])).

tff(c_866,plain,(
    k3_lattices('#skF_1','#skF_2','#skF_3') = k1_lattices('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_856])).

tff(c_873,plain,(
    k3_lattices('#skF_1','#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_645,c_866])).

tff(c_718,plain,(
    ! [B_108] :
      ( k3_lattices('#skF_1',B_108,'#skF_3') = k3_lattices('#skF_1','#skF_3',B_108)
      | ~ m1_subset_1(B_108,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_701])).

tff(c_735,plain,(
    k3_lattices('#skF_1','#skF_2','#skF_3') = k3_lattices('#skF_1','#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_718])).

tff(c_874,plain,(
    k3_lattices('#skF_1','#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_873,c_735])).

tff(c_52,plain,(
    v17_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_761,plain,(
    ! [A_110,B_111,C_112] :
      ( k4_lattices(A_110,B_111,C_112) = k2_lattices(A_110,B_111,C_112)
      | ~ m1_subset_1(C_112,u1_struct_0(A_110))
      | ~ m1_subset_1(B_111,u1_struct_0(A_110))
      | ~ l1_lattices(A_110)
      | ~ v6_lattices(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_765,plain,(
    ! [B_111] :
      ( k4_lattices('#skF_1',B_111,'#skF_3') = k2_lattices('#skF_1',B_111,'#skF_3')
      | ~ m1_subset_1(B_111,u1_struct_0('#skF_1'))
      | ~ l1_lattices('#skF_1')
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_46,c_761])).

tff(c_771,plain,(
    ! [B_111] :
      ( k4_lattices('#skF_1',B_111,'#skF_3') = k2_lattices('#skF_1',B_111,'#skF_3')
      | ~ m1_subset_1(B_111,u1_struct_0('#skF_1'))
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_765])).

tff(c_772,plain,(
    ! [B_111] :
      ( k4_lattices('#skF_1',B_111,'#skF_3') = k2_lattices('#skF_1',B_111,'#skF_3')
      | ~ m1_subset_1(B_111,u1_struct_0('#skF_1'))
      | ~ v6_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_771])).

tff(c_777,plain,(
    ~ v6_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_772])).

tff(c_780,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_777])).

tff(c_783,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_780])).

tff(c_785,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_783])).

tff(c_787,plain,(
    v6_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_772])).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(k7_lattices(A_12,B_13),u1_struct_0(A_12))
      | ~ m1_subset_1(B_13,u1_struct_0(A_12))
      | ~ l3_lattices(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_644,plain,(
    r1_lattices('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_1024,plain,(
    ! [A_127,B_128,C_129] :
      ( k2_lattices(A_127,B_128,C_129) = B_128
      | ~ r1_lattices(A_127,B_128,C_129)
      | ~ m1_subset_1(C_129,u1_struct_0(A_127))
      | ~ m1_subset_1(B_128,u1_struct_0(A_127))
      | ~ l3_lattices(A_127)
      | ~ v9_lattices(A_127)
      | ~ v8_lattices(A_127)
      | v2_struct_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1030,plain,
    ( k2_lattices('#skF_1','#skF_2','#skF_3') = '#skF_2'
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l3_lattices('#skF_1')
    | ~ v9_lattices('#skF_1')
    | ~ v8_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_644,c_1024])).

tff(c_1041,plain,
    ( k2_lattices('#skF_1','#skF_2','#skF_3') = '#skF_2'
    | ~ v9_lattices('#skF_1')
    | ~ v8_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_1030])).

tff(c_1042,plain,
    ( k2_lattices('#skF_1','#skF_2','#skF_3') = '#skF_2'
    | ~ v9_lattices('#skF_1')
    | ~ v8_lattices('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1041])).

tff(c_1043,plain,(
    ~ v8_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1042])).

tff(c_1046,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_1043])).

tff(c_1049,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_1046])).

tff(c_1051,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1049])).

tff(c_1053,plain,(
    v8_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1042])).

tff(c_1052,plain,
    ( ~ v9_lattices('#skF_1')
    | k2_lattices('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1042])).

tff(c_1071,plain,(
    ~ v9_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1052])).

tff(c_1074,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_1071])).

tff(c_1077,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_1074])).

tff(c_1079,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1077])).

tff(c_1081,plain,(
    v9_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1052])).

tff(c_1091,plain,(
    ! [A_131,B_132,C_133] :
      ( r3_lattices(A_131,B_132,C_133)
      | ~ r1_lattices(A_131,B_132,C_133)
      | ~ m1_subset_1(C_133,u1_struct_0(A_131))
      | ~ m1_subset_1(B_132,u1_struct_0(A_131))
      | ~ l3_lattices(A_131)
      | ~ v9_lattices(A_131)
      | ~ v8_lattices(A_131)
      | ~ v6_lattices(A_131)
      | v2_struct_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1685,plain,(
    ! [A_186,B_187,B_188] :
      ( r3_lattices(A_186,B_187,k7_lattices(A_186,B_188))
      | ~ r1_lattices(A_186,B_187,k7_lattices(A_186,B_188))
      | ~ m1_subset_1(B_187,u1_struct_0(A_186))
      | ~ v9_lattices(A_186)
      | ~ v8_lattices(A_186)
      | ~ v6_lattices(A_186)
      | ~ m1_subset_1(B_188,u1_struct_0(A_186))
      | ~ l3_lattices(A_186)
      | v2_struct_0(A_186) ) ),
    inference(resolution,[status(thm)],[c_22,c_1091])).

tff(c_42,plain,(
    ~ r3_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_1690,plain,
    ( ~ r1_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1','#skF_2'))
    | ~ m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1'))
    | ~ v9_lattices('#skF_1')
    | ~ v8_lattices('#skF_1')
    | ~ v6_lattices('#skF_1')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1685,c_42])).

tff(c_1694,plain,
    ( ~ r1_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1','#skF_2'))
    | ~ m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_787,c_1053,c_1081,c_1690])).

tff(c_1695,plain,
    ( ~ r1_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1','#skF_2'))
    | ~ m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1694])).

tff(c_1696,plain,(
    ~ m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1695])).

tff(c_1699,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_1696])).

tff(c_1702,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_1699])).

tff(c_1704,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1702])).

tff(c_1706,plain,(
    m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1695])).

tff(c_768,plain,(
    ! [A_12,B_111,B_13] :
      ( k4_lattices(A_12,B_111,k7_lattices(A_12,B_13)) = k2_lattices(A_12,B_111,k7_lattices(A_12,B_13))
      | ~ m1_subset_1(B_111,u1_struct_0(A_12))
      | ~ l1_lattices(A_12)
      | ~ v6_lattices(A_12)
      | ~ m1_subset_1(B_13,u1_struct_0(A_12))
      | ~ l3_lattices(A_12)
      | v2_struct_0(A_12) ) ),
    inference(resolution,[status(thm)],[c_22,c_761])).

tff(c_1725,plain,(
    ! [B_13] :
      ( k4_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1',B_13)) = k2_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1',B_13))
      | ~ l1_lattices('#skF_1')
      | ~ v6_lattices('#skF_1')
      | ~ m1_subset_1(B_13,u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1706,c_768])).

tff(c_1808,plain,(
    ! [B_13] :
      ( k4_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1',B_13)) = k2_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1',B_13))
      | ~ m1_subset_1(B_13,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_787,c_61,c_1725])).

tff(c_2381,plain,(
    ! [B_207] :
      ( k4_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1',B_207)) = k2_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1',B_207))
      | ~ m1_subset_1(B_207,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1808])).

tff(c_40,plain,(
    ! [A_31,B_35,C_37] :
      ( k4_lattices(A_31,k7_lattices(A_31,B_35),k7_lattices(A_31,C_37)) = k7_lattices(A_31,k3_lattices(A_31,B_35,C_37))
      | ~ m1_subset_1(C_37,u1_struct_0(A_31))
      | ~ m1_subset_1(B_35,u1_struct_0(A_31))
      | ~ l3_lattices(A_31)
      | ~ v17_lattices(A_31)
      | ~ v10_lattices(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_2393,plain,(
    ! [B_207] :
      ( k2_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1',B_207)) = k7_lattices('#skF_1',k3_lattices('#skF_1','#skF_3',B_207))
      | ~ m1_subset_1(B_207,u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | ~ v17_lattices('#skF_1')
      | ~ v10_lattices('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ m1_subset_1(B_207,u1_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2381,c_40])).

tff(c_2416,plain,(
    ! [B_207] :
      ( k2_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1',B_207)) = k7_lattices('#skF_1',k3_lattices('#skF_1','#skF_3',B_207))
      | v2_struct_0('#skF_1')
      | ~ m1_subset_1(B_207,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_46,c_2393])).

tff(c_2438,plain,(
    ! [B_211] :
      ( k2_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1',B_211)) = k7_lattices('#skF_1',k3_lattices('#skF_1','#skF_3',B_211))
      | ~ m1_subset_1(B_211,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2416])).

tff(c_931,plain,(
    ! [A_121,B_122,C_123] :
      ( r1_lattices(A_121,B_122,C_123)
      | k2_lattices(A_121,B_122,C_123) != B_122
      | ~ m1_subset_1(C_123,u1_struct_0(A_121))
      | ~ m1_subset_1(B_122,u1_struct_0(A_121))
      | ~ l3_lattices(A_121)
      | ~ v9_lattices(A_121)
      | ~ v8_lattices(A_121)
      | v2_struct_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_938,plain,(
    ! [A_12,B_122,B_13] :
      ( r1_lattices(A_12,B_122,k7_lattices(A_12,B_13))
      | k2_lattices(A_12,B_122,k7_lattices(A_12,B_13)) != B_122
      | ~ m1_subset_1(B_122,u1_struct_0(A_12))
      | ~ v9_lattices(A_12)
      | ~ v8_lattices(A_12)
      | ~ m1_subset_1(B_13,u1_struct_0(A_12))
      | ~ l3_lattices(A_12)
      | v2_struct_0(A_12) ) ),
    inference(resolution,[status(thm)],[c_22,c_931])).

tff(c_1705,plain,(
    ~ r1_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1695])).

tff(c_1891,plain,
    ( k2_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1','#skF_2')) != k7_lattices('#skF_1','#skF_3')
    | ~ m1_subset_1(k7_lattices('#skF_1','#skF_3'),u1_struct_0('#skF_1'))
    | ~ v9_lattices('#skF_1')
    | ~ v8_lattices('#skF_1')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_938,c_1705])).

tff(c_1897,plain,
    ( k2_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1','#skF_2')) != k7_lattices('#skF_1','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_1053,c_1081,c_1706,c_1891])).

tff(c_1898,plain,(
    k2_lattices('#skF_1',k7_lattices('#skF_1','#skF_3'),k7_lattices('#skF_1','#skF_2')) != k7_lattices('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1897])).

tff(c_2447,plain,
    ( k7_lattices('#skF_1',k3_lattices('#skF_1','#skF_3','#skF_2')) != k7_lattices('#skF_1','#skF_3')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2438,c_1898])).

tff(c_2459,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_874,c_2447])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.31  % Computer   : n025.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % DateTime   : Tue Dec  1 15:00:05 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.16/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.78/1.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.78/1.88  
% 4.78/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.78/1.89  %$ r3_lattices > r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v17_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k2_lattices > k1_lattices > k7_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1
% 4.78/1.89  
% 4.78/1.89  %Foreground sorts:
% 4.78/1.89  
% 4.78/1.89  
% 4.78/1.89  %Background operators:
% 4.78/1.89  
% 4.78/1.89  
% 4.78/1.89  %Foreground operators:
% 4.78/1.89  tff(l3_lattices, type, l3_lattices: $i > $o).
% 4.78/1.89  tff(k3_lattices, type, k3_lattices: ($i * $i * $i) > $i).
% 4.78/1.89  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.78/1.89  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 4.78/1.89  tff(l2_lattices, type, l2_lattices: $i > $o).
% 4.78/1.89  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 4.78/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.78/1.89  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 4.78/1.89  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 4.78/1.89  tff(l1_lattices, type, l1_lattices: $i > $o).
% 4.78/1.89  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 4.78/1.89  tff(v17_lattices, type, v17_lattices: $i > $o).
% 4.78/1.89  tff(v4_lattices, type, v4_lattices: $i > $o).
% 4.78/1.89  tff(v6_lattices, type, v6_lattices: $i > $o).
% 4.78/1.89  tff('#skF_2', type, '#skF_2': $i).
% 4.78/1.89  tff(v9_lattices, type, v9_lattices: $i > $o).
% 4.78/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.78/1.89  tff('#skF_1', type, '#skF_1': $i).
% 4.78/1.89  tff(v5_lattices, type, v5_lattices: $i > $o).
% 4.78/1.89  tff(v10_lattices, type, v10_lattices: $i > $o).
% 4.78/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.78/1.89  tff(v8_lattices, type, v8_lattices: $i > $o).
% 4.78/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.78/1.89  tff(k7_lattices, type, k7_lattices: ($i * $i) > $i).
% 4.78/1.89  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.78/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.78/1.89  tff(v7_lattices, type, v7_lattices: $i > $o).
% 4.78/1.89  
% 4.78/1.91  tff(f_191, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v17_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_lattices(A, B, C) => r3_lattices(A, k7_lattices(A, C), k7_lattices(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_lattices)).
% 4.78/1.91  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 4.78/1.91  tff(f_90, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 4.78/1.91  tff(f_103, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 4.78/1.91  tff(f_60, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k3_lattices(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_lattices)).
% 4.78/1.91  tff(f_75, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k1_lattices(A, B, C) = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_lattices)).
% 4.78/1.91  tff(f_116, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k2_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 4.78/1.91  tff(f_154, axiom, (![A]: ((((~v2_struct_0(A) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k2_lattices(A, B, C) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 4.78/1.91  tff(f_135, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 4.78/1.91  tff(f_84, axiom, (![A, B]: (((~v2_struct_0(A) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k7_lattices(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_lattices)).
% 4.78/1.91  tff(f_171, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v17_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k7_lattices(A, k3_lattices(A, B, C)) = k4_lattices(A, k7_lattices(A, B), k7_lattices(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_lattices)).
% 4.78/1.91  tff(c_48, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.78/1.91  tff(c_56, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.78/1.91  tff(c_50, plain, (l3_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.78/1.91  tff(c_54, plain, (v10_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.78/1.91  tff(c_12, plain, (![A_1]: (v4_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.78/1.91  tff(c_62, plain, (![A_43]: (l2_lattices(A_43) | ~l3_lattices(A_43))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.78/1.91  tff(c_66, plain, (l2_lattices('#skF_1')), inference(resolution, [status(thm)], [c_50, c_62])).
% 4.78/1.91  tff(c_46, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.78/1.91  tff(c_143, plain, (![A_62, B_63, C_64]: (k3_lattices(A_62, B_63, C_64)=k1_lattices(A_62, B_63, C_64) | ~m1_subset_1(C_64, u1_struct_0(A_62)) | ~m1_subset_1(B_63, u1_struct_0(A_62)) | ~l2_lattices(A_62) | ~v4_lattices(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.78/1.91  tff(c_147, plain, (![B_63]: (k3_lattices('#skF_1', B_63, '#skF_3')=k1_lattices('#skF_1', B_63, '#skF_3') | ~m1_subset_1(B_63, u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_143])).
% 4.78/1.91  tff(c_153, plain, (![B_63]: (k3_lattices('#skF_1', B_63, '#skF_3')=k1_lattices('#skF_1', B_63, '#skF_3') | ~m1_subset_1(B_63, u1_struct_0('#skF_1')) | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_147])).
% 4.78/1.91  tff(c_154, plain, (![B_63]: (k3_lattices('#skF_1', B_63, '#skF_3')=k1_lattices('#skF_1', B_63, '#skF_3') | ~m1_subset_1(B_63, u1_struct_0('#skF_1')) | ~v4_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_56, c_153])).
% 4.78/1.91  tff(c_159, plain, (~v4_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_154])).
% 4.78/1.91  tff(c_178, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_12, c_159])).
% 4.78/1.91  tff(c_181, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_178])).
% 4.78/1.91  tff(c_183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_181])).
% 4.78/1.91  tff(c_186, plain, (![B_68]: (k3_lattices('#skF_1', B_68, '#skF_3')=k1_lattices('#skF_1', B_68, '#skF_3') | ~m1_subset_1(B_68, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_154])).
% 4.78/1.91  tff(c_202, plain, (k3_lattices('#skF_1', '#skF_2', '#skF_3')=k1_lattices('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_186])).
% 4.78/1.91  tff(c_185, plain, (v4_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_154])).
% 4.78/1.91  tff(c_149, plain, (![B_63]: (k3_lattices('#skF_1', B_63, '#skF_2')=k1_lattices('#skF_1', B_63, '#skF_2') | ~m1_subset_1(B_63, u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_143])).
% 4.78/1.91  tff(c_157, plain, (![B_63]: (k3_lattices('#skF_1', B_63, '#skF_2')=k1_lattices('#skF_1', B_63, '#skF_2') | ~m1_subset_1(B_63, u1_struct_0('#skF_1')) | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_149])).
% 4.78/1.91  tff(c_158, plain, (![B_63]: (k3_lattices('#skF_1', B_63, '#skF_2')=k1_lattices('#skF_1', B_63, '#skF_2') | ~m1_subset_1(B_63, u1_struct_0('#skF_1')) | ~v4_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_56, c_157])).
% 4.78/1.91  tff(c_213, plain, (![B_69]: (k3_lattices('#skF_1', B_69, '#skF_2')=k1_lattices('#skF_1', B_69, '#skF_2') | ~m1_subset_1(B_69, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_158])).
% 4.78/1.91  tff(c_228, plain, (k3_lattices('#skF_1', '#skF_3', '#skF_2')=k1_lattices('#skF_1', '#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_213])).
% 4.78/1.91  tff(c_316, plain, (![A_75, C_76, B_77]: (k3_lattices(A_75, C_76, B_77)=k3_lattices(A_75, B_77, C_76) | ~m1_subset_1(C_76, u1_struct_0(A_75)) | ~m1_subset_1(B_77, u1_struct_0(A_75)) | ~l2_lattices(A_75) | ~v4_lattices(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.78/1.91  tff(c_320, plain, (![B_77]: (k3_lattices('#skF_1', B_77, '#skF_3')=k3_lattices('#skF_1', '#skF_3', B_77) | ~m1_subset_1(B_77, u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_316])).
% 4.78/1.91  tff(c_326, plain, (![B_77]: (k3_lattices('#skF_1', B_77, '#skF_3')=k3_lattices('#skF_1', '#skF_3', B_77) | ~m1_subset_1(B_77, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_66, c_320])).
% 4.78/1.91  tff(c_332, plain, (![B_78]: (k3_lattices('#skF_1', B_78, '#skF_3')=k3_lattices('#skF_1', '#skF_3', B_78) | ~m1_subset_1(B_78, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_56, c_326])).
% 4.78/1.91  tff(c_342, plain, (k3_lattices('#skF_1', '#skF_2', '#skF_3')=k3_lattices('#skF_1', '#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_48, c_332])).
% 4.78/1.91  tff(c_350, plain, (k1_lattices('#skF_1', '#skF_2', '#skF_3')=k1_lattices('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_202, c_228, c_342])).
% 4.78/1.91  tff(c_74, plain, (![A_52, B_53, C_54]: (r1_lattices(A_52, B_53, C_54) | k1_lattices(A_52, B_53, C_54)!=C_54 | ~m1_subset_1(C_54, u1_struct_0(A_52)) | ~m1_subset_1(B_53, u1_struct_0(A_52)) | ~l2_lattices(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.78/1.91  tff(c_78, plain, (![B_53]: (r1_lattices('#skF_1', B_53, '#skF_3') | k1_lattices('#skF_1', B_53, '#skF_3')!='#skF_3' | ~m1_subset_1(B_53, u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_74])).
% 4.78/1.91  tff(c_84, plain, (![B_53]: (r1_lattices('#skF_1', B_53, '#skF_3') | k1_lattices('#skF_1', B_53, '#skF_3')!='#skF_3' | ~m1_subset_1(B_53, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_78])).
% 4.78/1.91  tff(c_90, plain, (![B_55]: (r1_lattices('#skF_1', B_55, '#skF_3') | k1_lattices('#skF_1', B_55, '#skF_3')!='#skF_3' | ~m1_subset_1(B_55, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_56, c_84])).
% 4.78/1.91  tff(c_106, plain, (r1_lattices('#skF_1', '#skF_2', '#skF_3') | k1_lattices('#skF_1', '#skF_2', '#skF_3')!='#skF_3'), inference(resolution, [status(thm)], [c_48, c_90])).
% 4.78/1.91  tff(c_108, plain, (k1_lattices('#skF_1', '#skF_2', '#skF_3')!='#skF_3'), inference(splitLeft, [status(thm)], [c_106])).
% 4.78/1.91  tff(c_352, plain, (k1_lattices('#skF_1', '#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_350, c_108])).
% 4.78/1.91  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.78/1.91  tff(c_57, plain, (![A_42]: (l1_lattices(A_42) | ~l3_lattices(A_42))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.78/1.91  tff(c_61, plain, (l1_lattices('#skF_1')), inference(resolution, [status(thm)], [c_50, c_57])).
% 4.78/1.91  tff(c_255, plain, (![A_71, B_72, C_73]: (k4_lattices(A_71, B_72, C_73)=k2_lattices(A_71, B_72, C_73) | ~m1_subset_1(C_73, u1_struct_0(A_71)) | ~m1_subset_1(B_72, u1_struct_0(A_71)) | ~l1_lattices(A_71) | ~v6_lattices(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.78/1.91  tff(c_261, plain, (![B_72]: (k4_lattices('#skF_1', B_72, '#skF_2')=k2_lattices('#skF_1', B_72, '#skF_2') | ~m1_subset_1(B_72, u1_struct_0('#skF_1')) | ~l1_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_255])).
% 4.78/1.91  tff(c_269, plain, (![B_72]: (k4_lattices('#skF_1', B_72, '#skF_2')=k2_lattices('#skF_1', B_72, '#skF_2') | ~m1_subset_1(B_72, u1_struct_0('#skF_1')) | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_261])).
% 4.78/1.91  tff(c_270, plain, (![B_72]: (k4_lattices('#skF_1', B_72, '#skF_2')=k2_lattices('#skF_1', B_72, '#skF_2') | ~m1_subset_1(B_72, u1_struct_0('#skF_1')) | ~v6_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_56, c_269])).
% 4.78/1.91  tff(c_279, plain, (~v6_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_270])).
% 4.78/1.91  tff(c_283, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_8, c_279])).
% 4.78/1.91  tff(c_286, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_283])).
% 4.78/1.91  tff(c_288, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_286])).
% 4.78/1.91  tff(c_290, plain, (v6_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_270])).
% 4.78/1.91  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.78/1.91  tff(c_408, plain, (![A_81, B_82, C_83]: (r1_lattices(A_81, B_82, C_83) | k2_lattices(A_81, B_82, C_83)!=B_82 | ~m1_subset_1(C_83, u1_struct_0(A_81)) | ~m1_subset_1(B_82, u1_struct_0(A_81)) | ~l3_lattices(A_81) | ~v9_lattices(A_81) | ~v8_lattices(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.78/1.91  tff(c_412, plain, (![B_82]: (r1_lattices('#skF_1', B_82, '#skF_3') | k2_lattices('#skF_1', B_82, '#skF_3')!=B_82 | ~m1_subset_1(B_82, u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_408])).
% 4.78/1.91  tff(c_418, plain, (![B_82]: (r1_lattices('#skF_1', B_82, '#skF_3') | k2_lattices('#skF_1', B_82, '#skF_3')!=B_82 | ~m1_subset_1(B_82, u1_struct_0('#skF_1')) | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_412])).
% 4.78/1.91  tff(c_419, plain, (![B_82]: (r1_lattices('#skF_1', B_82, '#skF_3') | k2_lattices('#skF_1', B_82, '#skF_3')!=B_82 | ~m1_subset_1(B_82, u1_struct_0('#skF_1')) | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_56, c_418])).
% 4.78/1.91  tff(c_574, plain, (~v8_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_419])).
% 4.78/1.91  tff(c_584, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_4, c_574])).
% 4.78/1.91  tff(c_587, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_584])).
% 4.78/1.91  tff(c_589, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_587])).
% 4.78/1.91  tff(c_591, plain, (v8_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_419])).
% 4.78/1.91  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.78/1.91  tff(c_590, plain, (![B_82]: (~v9_lattices('#skF_1') | r1_lattices('#skF_1', B_82, '#skF_3') | k2_lattices('#skF_1', B_82, '#skF_3')!=B_82 | ~m1_subset_1(B_82, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_419])).
% 4.78/1.91  tff(c_592, plain, (~v9_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_590])).
% 4.78/1.91  tff(c_598, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_2, c_592])).
% 4.78/1.91  tff(c_601, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_598])).
% 4.78/1.91  tff(c_603, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_601])).
% 4.78/1.91  tff(c_605, plain, (v9_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_590])).
% 4.78/1.91  tff(c_44, plain, (r3_lattices('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.78/1.91  tff(c_624, plain, (![A_96, B_97, C_98]: (r1_lattices(A_96, B_97, C_98) | ~r3_lattices(A_96, B_97, C_98) | ~m1_subset_1(C_98, u1_struct_0(A_96)) | ~m1_subset_1(B_97, u1_struct_0(A_96)) | ~l3_lattices(A_96) | ~v9_lattices(A_96) | ~v8_lattices(A_96) | ~v6_lattices(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.78/1.91  tff(c_626, plain, (r1_lattices('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_624])).
% 4.78/1.91  tff(c_629, plain, (r1_lattices('#skF_1', '#skF_2', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_290, c_591, c_605, c_50, c_48, c_46, c_626])).
% 4.78/1.91  tff(c_630, plain, (r1_lattices('#skF_1', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_629])).
% 4.78/1.91  tff(c_20, plain, (![A_5, B_9, C_11]: (k1_lattices(A_5, B_9, C_11)=C_11 | ~r1_lattices(A_5, B_9, C_11) | ~m1_subset_1(C_11, u1_struct_0(A_5)) | ~m1_subset_1(B_9, u1_struct_0(A_5)) | ~l2_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.78/1.91  tff(c_634, plain, (k1_lattices('#skF_1', '#skF_2', '#skF_3')='#skF_3' | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_630, c_20])).
% 4.78/1.91  tff(c_641, plain, (k1_lattices('#skF_1', '#skF_3', '#skF_2')='#skF_3' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_48, c_46, c_350, c_634])).
% 4.78/1.91  tff(c_643, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_352, c_641])).
% 4.78/1.91  tff(c_645, plain, (k1_lattices('#skF_1', '#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_106])).
% 4.78/1.91  tff(c_690, plain, (![A_105, C_106, B_107]: (k3_lattices(A_105, C_106, B_107)=k3_lattices(A_105, B_107, C_106) | ~m1_subset_1(C_106, u1_struct_0(A_105)) | ~m1_subset_1(B_107, u1_struct_0(A_105)) | ~l2_lattices(A_105) | ~v4_lattices(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.78/1.91  tff(c_694, plain, (![B_107]: (k3_lattices('#skF_1', B_107, '#skF_3')=k3_lattices('#skF_1', '#skF_3', B_107) | ~m1_subset_1(B_107, u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_690])).
% 4.78/1.91  tff(c_700, plain, (![B_107]: (k3_lattices('#skF_1', B_107, '#skF_3')=k3_lattices('#skF_1', '#skF_3', B_107) | ~m1_subset_1(B_107, u1_struct_0('#skF_1')) | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_694])).
% 4.78/1.91  tff(c_701, plain, (![B_107]: (k3_lattices('#skF_1', B_107, '#skF_3')=k3_lattices('#skF_1', '#skF_3', B_107) | ~m1_subset_1(B_107, u1_struct_0('#skF_1')) | ~v4_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_56, c_700])).
% 4.78/1.91  tff(c_706, plain, (~v4_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_701])).
% 4.78/1.91  tff(c_710, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_12, c_706])).
% 4.78/1.91  tff(c_713, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_710])).
% 4.78/1.91  tff(c_715, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_713])).
% 4.78/1.91  tff(c_717, plain, (v4_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_701])).
% 4.78/1.91  tff(c_840, plain, (![A_115, B_116, C_117]: (k3_lattices(A_115, B_116, C_117)=k1_lattices(A_115, B_116, C_117) | ~m1_subset_1(C_117, u1_struct_0(A_115)) | ~m1_subset_1(B_116, u1_struct_0(A_115)) | ~l2_lattices(A_115) | ~v4_lattices(A_115) | v2_struct_0(A_115))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.78/1.91  tff(c_844, plain, (![B_116]: (k3_lattices('#skF_1', B_116, '#skF_3')=k1_lattices('#skF_1', B_116, '#skF_3') | ~m1_subset_1(B_116, u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_840])).
% 4.78/1.91  tff(c_850, plain, (![B_116]: (k3_lattices('#skF_1', B_116, '#skF_3')=k1_lattices('#skF_1', B_116, '#skF_3') | ~m1_subset_1(B_116, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_717, c_66, c_844])).
% 4.78/1.91  tff(c_856, plain, (![B_118]: (k3_lattices('#skF_1', B_118, '#skF_3')=k1_lattices('#skF_1', B_118, '#skF_3') | ~m1_subset_1(B_118, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_56, c_850])).
% 4.78/1.91  tff(c_866, plain, (k3_lattices('#skF_1', '#skF_2', '#skF_3')=k1_lattices('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_856])).
% 4.78/1.91  tff(c_873, plain, (k3_lattices('#skF_1', '#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_645, c_866])).
% 4.78/1.91  tff(c_718, plain, (![B_108]: (k3_lattices('#skF_1', B_108, '#skF_3')=k3_lattices('#skF_1', '#skF_3', B_108) | ~m1_subset_1(B_108, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_701])).
% 4.78/1.91  tff(c_735, plain, (k3_lattices('#skF_1', '#skF_2', '#skF_3')=k3_lattices('#skF_1', '#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_48, c_718])).
% 4.78/1.91  tff(c_874, plain, (k3_lattices('#skF_1', '#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_873, c_735])).
% 4.78/1.91  tff(c_52, plain, (v17_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.78/1.91  tff(c_761, plain, (![A_110, B_111, C_112]: (k4_lattices(A_110, B_111, C_112)=k2_lattices(A_110, B_111, C_112) | ~m1_subset_1(C_112, u1_struct_0(A_110)) | ~m1_subset_1(B_111, u1_struct_0(A_110)) | ~l1_lattices(A_110) | ~v6_lattices(A_110) | v2_struct_0(A_110))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.78/1.91  tff(c_765, plain, (![B_111]: (k4_lattices('#skF_1', B_111, '#skF_3')=k2_lattices('#skF_1', B_111, '#skF_3') | ~m1_subset_1(B_111, u1_struct_0('#skF_1')) | ~l1_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_761])).
% 4.78/1.91  tff(c_771, plain, (![B_111]: (k4_lattices('#skF_1', B_111, '#skF_3')=k2_lattices('#skF_1', B_111, '#skF_3') | ~m1_subset_1(B_111, u1_struct_0('#skF_1')) | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_765])).
% 4.78/1.91  tff(c_772, plain, (![B_111]: (k4_lattices('#skF_1', B_111, '#skF_3')=k2_lattices('#skF_1', B_111, '#skF_3') | ~m1_subset_1(B_111, u1_struct_0('#skF_1')) | ~v6_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_56, c_771])).
% 4.78/1.91  tff(c_777, plain, (~v6_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_772])).
% 4.78/1.91  tff(c_780, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_8, c_777])).
% 4.78/1.91  tff(c_783, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_780])).
% 4.78/1.91  tff(c_785, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_783])).
% 4.78/1.91  tff(c_787, plain, (v6_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_772])).
% 4.78/1.91  tff(c_22, plain, (![A_12, B_13]: (m1_subset_1(k7_lattices(A_12, B_13), u1_struct_0(A_12)) | ~m1_subset_1(B_13, u1_struct_0(A_12)) | ~l3_lattices(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.78/1.91  tff(c_644, plain, (r1_lattices('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_106])).
% 4.78/1.91  tff(c_1024, plain, (![A_127, B_128, C_129]: (k2_lattices(A_127, B_128, C_129)=B_128 | ~r1_lattices(A_127, B_128, C_129) | ~m1_subset_1(C_129, u1_struct_0(A_127)) | ~m1_subset_1(B_128, u1_struct_0(A_127)) | ~l3_lattices(A_127) | ~v9_lattices(A_127) | ~v8_lattices(A_127) | v2_struct_0(A_127))), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.78/1.91  tff(c_1030, plain, (k2_lattices('#skF_1', '#skF_2', '#skF_3')='#skF_2' | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_644, c_1024])).
% 4.78/1.91  tff(c_1041, plain, (k2_lattices('#skF_1', '#skF_2', '#skF_3')='#skF_2' | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_1030])).
% 4.78/1.91  tff(c_1042, plain, (k2_lattices('#skF_1', '#skF_2', '#skF_3')='#skF_2' | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_56, c_1041])).
% 4.78/1.91  tff(c_1043, plain, (~v8_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_1042])).
% 4.78/1.91  tff(c_1046, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_4, c_1043])).
% 4.78/1.91  tff(c_1049, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_1046])).
% 4.78/1.91  tff(c_1051, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1049])).
% 4.78/1.91  tff(c_1053, plain, (v8_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_1042])).
% 4.78/1.91  tff(c_1052, plain, (~v9_lattices('#skF_1') | k2_lattices('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_1042])).
% 4.78/1.91  tff(c_1071, plain, (~v9_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_1052])).
% 4.78/1.91  tff(c_1074, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_2, c_1071])).
% 4.78/1.91  tff(c_1077, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_1074])).
% 4.78/1.91  tff(c_1079, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1077])).
% 4.78/1.91  tff(c_1081, plain, (v9_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_1052])).
% 4.78/1.91  tff(c_1091, plain, (![A_131, B_132, C_133]: (r3_lattices(A_131, B_132, C_133) | ~r1_lattices(A_131, B_132, C_133) | ~m1_subset_1(C_133, u1_struct_0(A_131)) | ~m1_subset_1(B_132, u1_struct_0(A_131)) | ~l3_lattices(A_131) | ~v9_lattices(A_131) | ~v8_lattices(A_131) | ~v6_lattices(A_131) | v2_struct_0(A_131))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.78/1.91  tff(c_1685, plain, (![A_186, B_187, B_188]: (r3_lattices(A_186, B_187, k7_lattices(A_186, B_188)) | ~r1_lattices(A_186, B_187, k7_lattices(A_186, B_188)) | ~m1_subset_1(B_187, u1_struct_0(A_186)) | ~v9_lattices(A_186) | ~v8_lattices(A_186) | ~v6_lattices(A_186) | ~m1_subset_1(B_188, u1_struct_0(A_186)) | ~l3_lattices(A_186) | v2_struct_0(A_186))), inference(resolution, [status(thm)], [c_22, c_1091])).
% 4.78/1.91  tff(c_42, plain, (~r3_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.78/1.91  tff(c_1690, plain, (~r1_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', '#skF_2')) | ~m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1')) | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | ~v6_lattices('#skF_1') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1685, c_42])).
% 4.78/1.91  tff(c_1694, plain, (~r1_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', '#skF_2')) | ~m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_787, c_1053, c_1081, c_1690])).
% 4.78/1.91  tff(c_1695, plain, (~r1_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', '#skF_2')) | ~m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_56, c_1694])).
% 4.78/1.91  tff(c_1696, plain, (~m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_1695])).
% 4.78/1.91  tff(c_1699, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_1696])).
% 4.78/1.91  tff(c_1702, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_1699])).
% 4.78/1.91  tff(c_1704, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1702])).
% 4.78/1.91  tff(c_1706, plain, (m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_1695])).
% 4.78/1.91  tff(c_768, plain, (![A_12, B_111, B_13]: (k4_lattices(A_12, B_111, k7_lattices(A_12, B_13))=k2_lattices(A_12, B_111, k7_lattices(A_12, B_13)) | ~m1_subset_1(B_111, u1_struct_0(A_12)) | ~l1_lattices(A_12) | ~v6_lattices(A_12) | ~m1_subset_1(B_13, u1_struct_0(A_12)) | ~l3_lattices(A_12) | v2_struct_0(A_12))), inference(resolution, [status(thm)], [c_22, c_761])).
% 4.78/1.91  tff(c_1725, plain, (![B_13]: (k4_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', B_13))=k2_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', B_13)) | ~l1_lattices('#skF_1') | ~v6_lattices('#skF_1') | ~m1_subset_1(B_13, u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_1706, c_768])).
% 4.78/1.91  tff(c_1808, plain, (![B_13]: (k4_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', B_13))=k2_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', B_13)) | ~m1_subset_1(B_13, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_787, c_61, c_1725])).
% 4.78/1.91  tff(c_2381, plain, (![B_207]: (k4_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', B_207))=k2_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', B_207)) | ~m1_subset_1(B_207, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_56, c_1808])).
% 4.78/1.91  tff(c_40, plain, (![A_31, B_35, C_37]: (k4_lattices(A_31, k7_lattices(A_31, B_35), k7_lattices(A_31, C_37))=k7_lattices(A_31, k3_lattices(A_31, B_35, C_37)) | ~m1_subset_1(C_37, u1_struct_0(A_31)) | ~m1_subset_1(B_35, u1_struct_0(A_31)) | ~l3_lattices(A_31) | ~v17_lattices(A_31) | ~v10_lattices(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_171])).
% 4.78/1.91  tff(c_2393, plain, (![B_207]: (k2_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', B_207))=k7_lattices('#skF_1', k3_lattices('#skF_1', '#skF_3', B_207)) | ~m1_subset_1(B_207, u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v17_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~m1_subset_1(B_207, u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2381, c_40])).
% 4.78/1.91  tff(c_2416, plain, (![B_207]: (k2_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', B_207))=k7_lattices('#skF_1', k3_lattices('#skF_1', '#skF_3', B_207)) | v2_struct_0('#skF_1') | ~m1_subset_1(B_207, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_46, c_2393])).
% 4.78/1.91  tff(c_2438, plain, (![B_211]: (k2_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', B_211))=k7_lattices('#skF_1', k3_lattices('#skF_1', '#skF_3', B_211)) | ~m1_subset_1(B_211, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_56, c_2416])).
% 4.78/1.91  tff(c_931, plain, (![A_121, B_122, C_123]: (r1_lattices(A_121, B_122, C_123) | k2_lattices(A_121, B_122, C_123)!=B_122 | ~m1_subset_1(C_123, u1_struct_0(A_121)) | ~m1_subset_1(B_122, u1_struct_0(A_121)) | ~l3_lattices(A_121) | ~v9_lattices(A_121) | ~v8_lattices(A_121) | v2_struct_0(A_121))), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.78/1.91  tff(c_938, plain, (![A_12, B_122, B_13]: (r1_lattices(A_12, B_122, k7_lattices(A_12, B_13)) | k2_lattices(A_12, B_122, k7_lattices(A_12, B_13))!=B_122 | ~m1_subset_1(B_122, u1_struct_0(A_12)) | ~v9_lattices(A_12) | ~v8_lattices(A_12) | ~m1_subset_1(B_13, u1_struct_0(A_12)) | ~l3_lattices(A_12) | v2_struct_0(A_12))), inference(resolution, [status(thm)], [c_22, c_931])).
% 4.78/1.91  tff(c_1705, plain, (~r1_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_1695])).
% 4.78/1.91  tff(c_1891, plain, (k2_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', '#skF_2'))!=k7_lattices('#skF_1', '#skF_3') | ~m1_subset_1(k7_lattices('#skF_1', '#skF_3'), u1_struct_0('#skF_1')) | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_938, c_1705])).
% 4.78/1.91  tff(c_1897, plain, (k2_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', '#skF_2'))!=k7_lattices('#skF_1', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_1053, c_1081, c_1706, c_1891])).
% 4.78/1.91  tff(c_1898, plain, (k2_lattices('#skF_1', k7_lattices('#skF_1', '#skF_3'), k7_lattices('#skF_1', '#skF_2'))!=k7_lattices('#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_1897])).
% 4.78/1.91  tff(c_2447, plain, (k7_lattices('#skF_1', k3_lattices('#skF_1', '#skF_3', '#skF_2'))!=k7_lattices('#skF_1', '#skF_3') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2438, c_1898])).
% 4.78/1.91  tff(c_2459, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_874, c_2447])).
% 4.78/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.78/1.91  
% 4.78/1.91  Inference rules
% 4.78/1.91  ----------------------
% 4.78/1.91  #Ref     : 0
% 4.78/1.91  #Sup     : 519
% 4.78/1.91  #Fact    : 0
% 4.78/1.91  #Define  : 0
% 4.78/1.91  #Split   : 28
% 4.78/1.91  #Chain   : 0
% 4.78/1.91  #Close   : 0
% 4.78/1.91  
% 4.78/1.91  Ordering : KBO
% 4.78/1.91  
% 4.78/1.91  Simplification rules
% 4.78/1.91  ----------------------
% 4.78/1.91  #Subsume      : 12
% 4.78/1.91  #Demod        : 454
% 4.78/1.91  #Tautology    : 281
% 4.78/1.91  #SimpNegUnit  : 139
% 4.78/1.91  #BackRed      : 17
% 4.78/1.91  
% 4.78/1.91  #Partial instantiations: 0
% 4.78/1.91  #Strategies tried      : 1
% 4.78/1.91  
% 4.78/1.91  Timing (in seconds)
% 4.78/1.91  ----------------------
% 4.78/1.92  Preprocessing        : 0.34
% 4.78/1.92  Parsing              : 0.18
% 4.78/1.92  CNF conversion       : 0.02
% 4.78/1.92  Main loop            : 0.79
% 4.78/1.92  Inferencing          : 0.28
% 5.23/1.92  Reduction            : 0.26
% 5.23/1.92  Demodulation         : 0.18
% 5.23/1.92  BG Simplification    : 0.04
% 5.23/1.92  Subsumption          : 0.16
% 5.23/1.92  Abstraction          : 0.04
% 5.23/1.92  MUC search           : 0.00
% 5.23/1.92  Cooper               : 0.00
% 5.23/1.92  Total                : 1.18
% 5.23/1.92  Index Insertion      : 0.00
% 5.23/1.92  Index Deletion       : 0.00
% 5.23/1.92  Index Matching       : 0.00
% 5.23/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
