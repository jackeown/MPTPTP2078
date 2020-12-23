%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:17 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 342 expanded)
%              Number of leaves         :   36 ( 135 expanded)
%              Depth                    :   14
%              Number of atoms          :  261 (1068 expanded)
%              Number of equality atoms :   53 ( 162 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v14_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > k6_lattices > #skF_2 > #skF_1 > #skF_3 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_lattices,type,(
    k4_lattices: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_lattices,type,(
    k1_lattices: ( $i * $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v14_lattices,type,(
    v14_lattices: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_156,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v14_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => k3_lattices(A,k6_lattices(A),B) = k6_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_lattices)).

tff(f_101,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

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

tff(f_114,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k1_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

tff(f_95,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => m1_subset_1(k6_lattices(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_lattices)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k3_lattices(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).

tff(f_88,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( v8_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k1_lattices(A,k2_lattices(A,B,C),C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattices)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k4_lattices(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).

tff(f_141,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v14_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k4_lattices(A,k6_lattices(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattices)).

tff(f_127,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k2_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_44,plain,(
    l3_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_56,plain,(
    ! [A_32] :
      ( l2_lattices(A_32)
      | ~ l3_lattices(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_60,plain,(
    l2_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_56])).

tff(c_48,plain,(
    v10_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_180,plain,(
    ! [A_53,B_54,C_55] :
      ( k3_lattices(A_53,B_54,C_55) = k1_lattices(A_53,B_54,C_55)
      | ~ m1_subset_1(C_55,u1_struct_0(A_53))
      | ~ m1_subset_1(B_54,u1_struct_0(A_53))
      | ~ l2_lattices(A_53)
      | ~ v4_lattices(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_188,plain,(
    ! [B_54] :
      ( k3_lattices('#skF_3',B_54,'#skF_4') = k1_lattices('#skF_3',B_54,'#skF_4')
      | ~ m1_subset_1(B_54,u1_struct_0('#skF_3'))
      | ~ l2_lattices('#skF_3')
      | ~ v4_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_180])).

tff(c_194,plain,(
    ! [B_54] :
      ( k3_lattices('#skF_3',B_54,'#skF_4') = k1_lattices('#skF_3',B_54,'#skF_4')
      | ~ m1_subset_1(B_54,u1_struct_0('#skF_3'))
      | ~ v4_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_188])).

tff(c_195,plain,(
    ! [B_54] :
      ( k3_lattices('#skF_3',B_54,'#skF_4') = k1_lattices('#skF_3',B_54,'#skF_4')
      | ~ m1_subset_1(B_54,u1_struct_0('#skF_3'))
      | ~ v4_lattices('#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_194])).

tff(c_196,plain,(
    ~ v4_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_195])).

tff(c_199,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_196])).

tff(c_202,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48,c_199])).

tff(c_204,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_202])).

tff(c_206,plain,(
    v4_lattices('#skF_3') ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_28,plain,(
    ! [A_19] :
      ( m1_subset_1(k6_lattices(A_19),u1_struct_0(A_19))
      | ~ l2_lattices(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_223,plain,(
    ! [B_59] :
      ( k3_lattices('#skF_3',B_59,'#skF_4') = k1_lattices('#skF_3',B_59,'#skF_4')
      | ~ m1_subset_1(B_59,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_235,plain,
    ( k3_lattices('#skF_3',k6_lattices('#skF_3'),'#skF_4') = k1_lattices('#skF_3',k6_lattices('#skF_3'),'#skF_4')
    | ~ l2_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_223])).

tff(c_249,plain,
    ( k3_lattices('#skF_3',k6_lattices('#skF_3'),'#skF_4') = k1_lattices('#skF_3',k6_lattices('#skF_3'),'#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_235])).

tff(c_250,plain,(
    k3_lattices('#skF_3',k6_lattices('#skF_3'),'#skF_4') = k1_lattices('#skF_3',k6_lattices('#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_249])).

tff(c_306,plain,(
    ! [A_61,C_62,B_63] :
      ( k3_lattices(A_61,C_62,B_63) = k3_lattices(A_61,B_63,C_62)
      | ~ m1_subset_1(C_62,u1_struct_0(A_61))
      | ~ m1_subset_1(B_63,u1_struct_0(A_61))
      | ~ l2_lattices(A_61)
      | ~ v4_lattices(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_314,plain,(
    ! [B_63] :
      ( k3_lattices('#skF_3',B_63,'#skF_4') = k3_lattices('#skF_3','#skF_4',B_63)
      | ~ m1_subset_1(B_63,u1_struct_0('#skF_3'))
      | ~ l2_lattices('#skF_3')
      | ~ v4_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_306])).

tff(c_320,plain,(
    ! [B_63] :
      ( k3_lattices('#skF_3',B_63,'#skF_4') = k3_lattices('#skF_3','#skF_4',B_63)
      | ~ m1_subset_1(B_63,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_60,c_314])).

tff(c_322,plain,(
    ! [B_64] :
      ( k3_lattices('#skF_3',B_64,'#skF_4') = k3_lattices('#skF_3','#skF_4',B_64)
      | ~ m1_subset_1(B_64,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_320])).

tff(c_334,plain,
    ( k3_lattices('#skF_3',k6_lattices('#skF_3'),'#skF_4') = k3_lattices('#skF_3','#skF_4',k6_lattices('#skF_3'))
    | ~ l2_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_322])).

tff(c_348,plain,
    ( k3_lattices('#skF_3','#skF_4',k6_lattices('#skF_3')) = k1_lattices('#skF_3',k6_lattices('#skF_3'),'#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_250,c_334])).

tff(c_349,plain,(
    k3_lattices('#skF_3','#skF_4',k6_lattices('#skF_3')) = k1_lattices('#skF_3',k6_lattices('#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_348])).

tff(c_436,plain,(
    ! [A_71,B_72] :
      ( k3_lattices(A_71,B_72,k6_lattices(A_71)) = k1_lattices(A_71,B_72,k6_lattices(A_71))
      | ~ m1_subset_1(B_72,u1_struct_0(A_71))
      | ~ v4_lattices(A_71)
      | ~ l2_lattices(A_71)
      | v2_struct_0(A_71) ) ),
    inference(resolution,[status(thm)],[c_28,c_180])).

tff(c_444,plain,
    ( k3_lattices('#skF_3','#skF_4',k6_lattices('#skF_3')) = k1_lattices('#skF_3','#skF_4',k6_lattices('#skF_3'))
    | ~ v4_lattices('#skF_3')
    | ~ l2_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_436])).

tff(c_450,plain,
    ( k1_lattices('#skF_3',k6_lattices('#skF_3'),'#skF_4') = k1_lattices('#skF_3','#skF_4',k6_lattices('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_206,c_349,c_444])).

tff(c_451,plain,(
    k1_lattices('#skF_3',k6_lattices('#skF_3'),'#skF_4') = k1_lattices('#skF_3','#skF_4',k6_lattices('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_450])).

tff(c_40,plain,(
    k3_lattices('#skF_3',k6_lattices('#skF_3'),'#skF_4') != k6_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_256,plain,(
    k1_lattices('#skF_3',k6_lattices('#skF_3'),'#skF_4') != k6_lattices('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_40])).

tff(c_453,plain,(
    k1_lattices('#skF_3','#skF_4',k6_lattices('#skF_3')) != k6_lattices('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_451,c_256])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_100,plain,(
    ! [A_46,B_47,C_48] :
      ( k1_lattices(A_46,k2_lattices(A_46,B_47,C_48),C_48) = C_48
      | ~ m1_subset_1(C_48,u1_struct_0(A_46))
      | ~ m1_subset_1(B_47,u1_struct_0(A_46))
      | ~ v8_lattices(A_46)
      | ~ l3_lattices(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_108,plain,(
    ! [B_47] :
      ( k1_lattices('#skF_3',k2_lattices('#skF_3',B_47,'#skF_4'),'#skF_4') = '#skF_4'
      | ~ m1_subset_1(B_47,u1_struct_0('#skF_3'))
      | ~ v8_lattices('#skF_3')
      | ~ l3_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_100])).

tff(c_114,plain,(
    ! [B_47] :
      ( k1_lattices('#skF_3',k2_lattices('#skF_3',B_47,'#skF_4'),'#skF_4') = '#skF_4'
      | ~ m1_subset_1(B_47,u1_struct_0('#skF_3'))
      | ~ v8_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_108])).

tff(c_115,plain,(
    ! [B_47] :
      ( k1_lattices('#skF_3',k2_lattices('#skF_3',B_47,'#skF_4'),'#skF_4') = '#skF_4'
      | ~ m1_subset_1(B_47,u1_struct_0('#skF_3'))
      | ~ v8_lattices('#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_114])).

tff(c_116,plain,(
    ~ v8_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_135,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_116])).

tff(c_138,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48,c_135])).

tff(c_140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_138])).

tff(c_142,plain,(
    v8_lattices('#skF_3') ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_51,plain,(
    ! [A_31] :
      ( l1_lattices(A_31)
      | ~ l3_lattices(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_55,plain,(
    l1_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_51])).

tff(c_207,plain,(
    ! [A_56,C_57,B_58] :
      ( k4_lattices(A_56,C_57,B_58) = k4_lattices(A_56,B_58,C_57)
      | ~ m1_subset_1(C_57,u1_struct_0(A_56))
      | ~ m1_subset_1(B_58,u1_struct_0(A_56))
      | ~ l1_lattices(A_56)
      | ~ v6_lattices(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_215,plain,(
    ! [B_58] :
      ( k4_lattices('#skF_3',B_58,'#skF_4') = k4_lattices('#skF_3','#skF_4',B_58)
      | ~ m1_subset_1(B_58,u1_struct_0('#skF_3'))
      | ~ l1_lattices('#skF_3')
      | ~ v6_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_207])).

tff(c_221,plain,(
    ! [B_58] :
      ( k4_lattices('#skF_3',B_58,'#skF_4') = k4_lattices('#skF_3','#skF_4',B_58)
      | ~ m1_subset_1(B_58,u1_struct_0('#skF_3'))
      | ~ v6_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_215])).

tff(c_222,plain,(
    ! [B_58] :
      ( k4_lattices('#skF_3',B_58,'#skF_4') = k4_lattices('#skF_3','#skF_4',B_58)
      | ~ m1_subset_1(B_58,u1_struct_0('#skF_3'))
      | ~ v6_lattices('#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_221])).

tff(c_261,plain,(
    ~ v6_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_222])).

tff(c_264,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_261])).

tff(c_267,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48,c_264])).

tff(c_269,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_267])).

tff(c_271,plain,(
    v6_lattices('#skF_3') ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_46,plain,(
    v14_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_71,plain,(
    ! [A_43,B_44] :
      ( k4_lattices(A_43,k6_lattices(A_43),B_44) = B_44
      | ~ m1_subset_1(B_44,u1_struct_0(A_43))
      | ~ l3_lattices(A_43)
      | ~ v14_lattices(A_43)
      | ~ v10_lattices(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_79,plain,
    ( k4_lattices('#skF_3',k6_lattices('#skF_3'),'#skF_4') = '#skF_4'
    | ~ l3_lattices('#skF_3')
    | ~ v14_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_71])).

tff(c_85,plain,
    ( k4_lattices('#skF_3',k6_lattices('#skF_3'),'#skF_4') = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_79])).

tff(c_86,plain,(
    k4_lattices('#skF_3',k6_lattices('#skF_3'),'#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_85])).

tff(c_272,plain,(
    ! [B_60] :
      ( k4_lattices('#skF_3',B_60,'#skF_4') = k4_lattices('#skF_3','#skF_4',B_60)
      | ~ m1_subset_1(B_60,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_284,plain,
    ( k4_lattices('#skF_3',k6_lattices('#skF_3'),'#skF_4') = k4_lattices('#skF_3','#skF_4',k6_lattices('#skF_3'))
    | ~ l2_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_272])).

tff(c_298,plain,
    ( k4_lattices('#skF_3','#skF_4',k6_lattices('#skF_3')) = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_86,c_284])).

tff(c_299,plain,(
    k4_lattices('#skF_3','#skF_4',k6_lattices('#skF_3')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_298])).

tff(c_373,plain,(
    ! [A_67,B_68,C_69] :
      ( k4_lattices(A_67,B_68,C_69) = k2_lattices(A_67,B_68,C_69)
      | ~ m1_subset_1(C_69,u1_struct_0(A_67))
      | ~ m1_subset_1(B_68,u1_struct_0(A_67))
      | ~ l1_lattices(A_67)
      | ~ v6_lattices(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_493,plain,(
    ! [A_76,B_77] :
      ( k4_lattices(A_76,B_77,k6_lattices(A_76)) = k2_lattices(A_76,B_77,k6_lattices(A_76))
      | ~ m1_subset_1(B_77,u1_struct_0(A_76))
      | ~ l1_lattices(A_76)
      | ~ v6_lattices(A_76)
      | ~ l2_lattices(A_76)
      | v2_struct_0(A_76) ) ),
    inference(resolution,[status(thm)],[c_28,c_373])).

tff(c_501,plain,
    ( k4_lattices('#skF_3','#skF_4',k6_lattices('#skF_3')) = k2_lattices('#skF_3','#skF_4',k6_lattices('#skF_3'))
    | ~ l1_lattices('#skF_3')
    | ~ v6_lattices('#skF_3')
    | ~ l2_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_493])).

tff(c_507,plain,
    ( k2_lattices('#skF_3','#skF_4',k6_lattices('#skF_3')) = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_271,c_55,c_299,c_501])).

tff(c_508,plain,(
    k2_lattices('#skF_3','#skF_4',k6_lattices('#skF_3')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_507])).

tff(c_528,plain,(
    ! [A_79,B_80] :
      ( k1_lattices(A_79,k2_lattices(A_79,B_80,k6_lattices(A_79)),k6_lattices(A_79)) = k6_lattices(A_79)
      | ~ m1_subset_1(B_80,u1_struct_0(A_79))
      | ~ v8_lattices(A_79)
      | ~ l3_lattices(A_79)
      | ~ l2_lattices(A_79)
      | v2_struct_0(A_79) ) ),
    inference(resolution,[status(thm)],[c_28,c_100])).

tff(c_537,plain,
    ( k1_lattices('#skF_3','#skF_4',k6_lattices('#skF_3')) = k6_lattices('#skF_3')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ v8_lattices('#skF_3')
    | ~ l3_lattices('#skF_3')
    | ~ l2_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_508,c_528])).

tff(c_541,plain,
    ( k1_lattices('#skF_3','#skF_4',k6_lattices('#skF_3')) = k6_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_44,c_142,c_42,c_537])).

tff(c_543,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_453,c_541])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:42:44 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.38  
% 2.66/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.38  %$ m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v14_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > k6_lattices > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 2.66/1.38  
% 2.66/1.38  %Foreground sorts:
% 2.66/1.38  
% 2.66/1.38  
% 2.66/1.38  %Background operators:
% 2.66/1.38  
% 2.66/1.38  
% 2.66/1.38  %Foreground operators:
% 2.66/1.38  tff(l3_lattices, type, l3_lattices: $i > $o).
% 2.66/1.38  tff(k6_lattices, type, k6_lattices: $i > $i).
% 2.66/1.38  tff(k3_lattices, type, k3_lattices: ($i * $i * $i) > $i).
% 2.66/1.38  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.66/1.38  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 2.66/1.38  tff(l2_lattices, type, l2_lattices: $i > $o).
% 2.66/1.38  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.66/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.38  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 2.66/1.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.66/1.38  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 2.66/1.38  tff(l1_lattices, type, l1_lattices: $i > $o).
% 2.66/1.38  tff(v4_lattices, type, v4_lattices: $i > $o).
% 2.66/1.38  tff(v6_lattices, type, v6_lattices: $i > $o).
% 2.66/1.38  tff(v9_lattices, type, v9_lattices: $i > $o).
% 2.66/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.66/1.38  tff(v5_lattices, type, v5_lattices: $i > $o).
% 2.66/1.38  tff(v10_lattices, type, v10_lattices: $i > $o).
% 2.66/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.38  tff(v14_lattices, type, v14_lattices: $i > $o).
% 2.66/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.66/1.38  tff(v8_lattices, type, v8_lattices: $i > $o).
% 2.66/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.66/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.66/1.38  tff(v7_lattices, type, v7_lattices: $i > $o).
% 2.66/1.38  
% 2.90/1.40  tff(f_156, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v14_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k3_lattices(A, k6_lattices(A), B) = k6_lattices(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_lattices)).
% 2.90/1.40  tff(f_101, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 2.90/1.40  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 2.90/1.40  tff(f_114, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 2.90/1.40  tff(f_95, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => m1_subset_1(k6_lattices(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_lattices)).
% 2.90/1.40  tff(f_60, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k3_lattices(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_lattices)).
% 2.90/1.40  tff(f_88, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v8_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k1_lattices(A, k2_lattices(A, B, C), C) = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattices)).
% 2.90/1.40  tff(f_73, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k4_lattices(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k4_lattices)).
% 2.90/1.40  tff(f_141, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v14_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k4_lattices(A, k6_lattices(A), B) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_lattices)).
% 2.90/1.40  tff(f_127, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k2_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 2.90/1.40  tff(c_50, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.90/1.40  tff(c_44, plain, (l3_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.90/1.40  tff(c_56, plain, (![A_32]: (l2_lattices(A_32) | ~l3_lattices(A_32))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.90/1.40  tff(c_60, plain, (l2_lattices('#skF_3')), inference(resolution, [status(thm)], [c_44, c_56])).
% 2.90/1.40  tff(c_48, plain, (v10_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.90/1.40  tff(c_12, plain, (![A_1]: (v4_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.90/1.40  tff(c_42, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.90/1.40  tff(c_180, plain, (![A_53, B_54, C_55]: (k3_lattices(A_53, B_54, C_55)=k1_lattices(A_53, B_54, C_55) | ~m1_subset_1(C_55, u1_struct_0(A_53)) | ~m1_subset_1(B_54, u1_struct_0(A_53)) | ~l2_lattices(A_53) | ~v4_lattices(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.90/1.40  tff(c_188, plain, (![B_54]: (k3_lattices('#skF_3', B_54, '#skF_4')=k1_lattices('#skF_3', B_54, '#skF_4') | ~m1_subset_1(B_54, u1_struct_0('#skF_3')) | ~l2_lattices('#skF_3') | ~v4_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_180])).
% 2.90/1.40  tff(c_194, plain, (![B_54]: (k3_lattices('#skF_3', B_54, '#skF_4')=k1_lattices('#skF_3', B_54, '#skF_4') | ~m1_subset_1(B_54, u1_struct_0('#skF_3')) | ~v4_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_188])).
% 2.90/1.40  tff(c_195, plain, (![B_54]: (k3_lattices('#skF_3', B_54, '#skF_4')=k1_lattices('#skF_3', B_54, '#skF_4') | ~m1_subset_1(B_54, u1_struct_0('#skF_3')) | ~v4_lattices('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_194])).
% 2.90/1.40  tff(c_196, plain, (~v4_lattices('#skF_3')), inference(splitLeft, [status(thm)], [c_195])).
% 2.90/1.40  tff(c_199, plain, (~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~l3_lattices('#skF_3')), inference(resolution, [status(thm)], [c_12, c_196])).
% 2.90/1.40  tff(c_202, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_48, c_199])).
% 2.90/1.40  tff(c_204, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_202])).
% 2.90/1.40  tff(c_206, plain, (v4_lattices('#skF_3')), inference(splitRight, [status(thm)], [c_195])).
% 2.90/1.40  tff(c_28, plain, (![A_19]: (m1_subset_1(k6_lattices(A_19), u1_struct_0(A_19)) | ~l2_lattices(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.90/1.40  tff(c_223, plain, (![B_59]: (k3_lattices('#skF_3', B_59, '#skF_4')=k1_lattices('#skF_3', B_59, '#skF_4') | ~m1_subset_1(B_59, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_195])).
% 2.90/1.40  tff(c_235, plain, (k3_lattices('#skF_3', k6_lattices('#skF_3'), '#skF_4')=k1_lattices('#skF_3', k6_lattices('#skF_3'), '#skF_4') | ~l2_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_28, c_223])).
% 2.90/1.40  tff(c_249, plain, (k3_lattices('#skF_3', k6_lattices('#skF_3'), '#skF_4')=k1_lattices('#skF_3', k6_lattices('#skF_3'), '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_235])).
% 2.90/1.40  tff(c_250, plain, (k3_lattices('#skF_3', k6_lattices('#skF_3'), '#skF_4')=k1_lattices('#skF_3', k6_lattices('#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_50, c_249])).
% 2.90/1.40  tff(c_306, plain, (![A_61, C_62, B_63]: (k3_lattices(A_61, C_62, B_63)=k3_lattices(A_61, B_63, C_62) | ~m1_subset_1(C_62, u1_struct_0(A_61)) | ~m1_subset_1(B_63, u1_struct_0(A_61)) | ~l2_lattices(A_61) | ~v4_lattices(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.90/1.40  tff(c_314, plain, (![B_63]: (k3_lattices('#skF_3', B_63, '#skF_4')=k3_lattices('#skF_3', '#skF_4', B_63) | ~m1_subset_1(B_63, u1_struct_0('#skF_3')) | ~l2_lattices('#skF_3') | ~v4_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_306])).
% 2.90/1.40  tff(c_320, plain, (![B_63]: (k3_lattices('#skF_3', B_63, '#skF_4')=k3_lattices('#skF_3', '#skF_4', B_63) | ~m1_subset_1(B_63, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_206, c_60, c_314])).
% 2.90/1.40  tff(c_322, plain, (![B_64]: (k3_lattices('#skF_3', B_64, '#skF_4')=k3_lattices('#skF_3', '#skF_4', B_64) | ~m1_subset_1(B_64, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_50, c_320])).
% 2.90/1.40  tff(c_334, plain, (k3_lattices('#skF_3', k6_lattices('#skF_3'), '#skF_4')=k3_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3')) | ~l2_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_28, c_322])).
% 2.90/1.40  tff(c_348, plain, (k3_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3'))=k1_lattices('#skF_3', k6_lattices('#skF_3'), '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_250, c_334])).
% 2.90/1.40  tff(c_349, plain, (k3_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3'))=k1_lattices('#skF_3', k6_lattices('#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_50, c_348])).
% 2.90/1.40  tff(c_436, plain, (![A_71, B_72]: (k3_lattices(A_71, B_72, k6_lattices(A_71))=k1_lattices(A_71, B_72, k6_lattices(A_71)) | ~m1_subset_1(B_72, u1_struct_0(A_71)) | ~v4_lattices(A_71) | ~l2_lattices(A_71) | v2_struct_0(A_71))), inference(resolution, [status(thm)], [c_28, c_180])).
% 2.90/1.40  tff(c_444, plain, (k3_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3'))=k1_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3')) | ~v4_lattices('#skF_3') | ~l2_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_436])).
% 2.90/1.40  tff(c_450, plain, (k1_lattices('#skF_3', k6_lattices('#skF_3'), '#skF_4')=k1_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_206, c_349, c_444])).
% 2.90/1.40  tff(c_451, plain, (k1_lattices('#skF_3', k6_lattices('#skF_3'), '#skF_4')=k1_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_450])).
% 2.90/1.40  tff(c_40, plain, (k3_lattices('#skF_3', k6_lattices('#skF_3'), '#skF_4')!=k6_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.90/1.40  tff(c_256, plain, (k1_lattices('#skF_3', k6_lattices('#skF_3'), '#skF_4')!=k6_lattices('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_250, c_40])).
% 2.90/1.40  tff(c_453, plain, (k1_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3'))!=k6_lattices('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_451, c_256])).
% 2.90/1.40  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.90/1.40  tff(c_100, plain, (![A_46, B_47, C_48]: (k1_lattices(A_46, k2_lattices(A_46, B_47, C_48), C_48)=C_48 | ~m1_subset_1(C_48, u1_struct_0(A_46)) | ~m1_subset_1(B_47, u1_struct_0(A_46)) | ~v8_lattices(A_46) | ~l3_lattices(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.90/1.40  tff(c_108, plain, (![B_47]: (k1_lattices('#skF_3', k2_lattices('#skF_3', B_47, '#skF_4'), '#skF_4')='#skF_4' | ~m1_subset_1(B_47, u1_struct_0('#skF_3')) | ~v8_lattices('#skF_3') | ~l3_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_100])).
% 2.90/1.40  tff(c_114, plain, (![B_47]: (k1_lattices('#skF_3', k2_lattices('#skF_3', B_47, '#skF_4'), '#skF_4')='#skF_4' | ~m1_subset_1(B_47, u1_struct_0('#skF_3')) | ~v8_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_108])).
% 2.90/1.40  tff(c_115, plain, (![B_47]: (k1_lattices('#skF_3', k2_lattices('#skF_3', B_47, '#skF_4'), '#skF_4')='#skF_4' | ~m1_subset_1(B_47, u1_struct_0('#skF_3')) | ~v8_lattices('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_114])).
% 2.90/1.40  tff(c_116, plain, (~v8_lattices('#skF_3')), inference(splitLeft, [status(thm)], [c_115])).
% 2.90/1.40  tff(c_135, plain, (~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~l3_lattices('#skF_3')), inference(resolution, [status(thm)], [c_4, c_116])).
% 2.90/1.40  tff(c_138, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_48, c_135])).
% 2.90/1.40  tff(c_140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_138])).
% 2.90/1.40  tff(c_142, plain, (v8_lattices('#skF_3')), inference(splitRight, [status(thm)], [c_115])).
% 2.90/1.40  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.90/1.40  tff(c_51, plain, (![A_31]: (l1_lattices(A_31) | ~l3_lattices(A_31))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.90/1.40  tff(c_55, plain, (l1_lattices('#skF_3')), inference(resolution, [status(thm)], [c_44, c_51])).
% 2.90/1.40  tff(c_207, plain, (![A_56, C_57, B_58]: (k4_lattices(A_56, C_57, B_58)=k4_lattices(A_56, B_58, C_57) | ~m1_subset_1(C_57, u1_struct_0(A_56)) | ~m1_subset_1(B_58, u1_struct_0(A_56)) | ~l1_lattices(A_56) | ~v6_lattices(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.90/1.40  tff(c_215, plain, (![B_58]: (k4_lattices('#skF_3', B_58, '#skF_4')=k4_lattices('#skF_3', '#skF_4', B_58) | ~m1_subset_1(B_58, u1_struct_0('#skF_3')) | ~l1_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_207])).
% 2.90/1.40  tff(c_221, plain, (![B_58]: (k4_lattices('#skF_3', B_58, '#skF_4')=k4_lattices('#skF_3', '#skF_4', B_58) | ~m1_subset_1(B_58, u1_struct_0('#skF_3')) | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_215])).
% 2.90/1.40  tff(c_222, plain, (![B_58]: (k4_lattices('#skF_3', B_58, '#skF_4')=k4_lattices('#skF_3', '#skF_4', B_58) | ~m1_subset_1(B_58, u1_struct_0('#skF_3')) | ~v6_lattices('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_221])).
% 2.90/1.40  tff(c_261, plain, (~v6_lattices('#skF_3')), inference(splitLeft, [status(thm)], [c_222])).
% 2.90/1.40  tff(c_264, plain, (~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~l3_lattices('#skF_3')), inference(resolution, [status(thm)], [c_8, c_261])).
% 2.90/1.40  tff(c_267, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_48, c_264])).
% 2.90/1.40  tff(c_269, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_267])).
% 2.90/1.40  tff(c_271, plain, (v6_lattices('#skF_3')), inference(splitRight, [status(thm)], [c_222])).
% 2.90/1.40  tff(c_46, plain, (v14_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.90/1.40  tff(c_71, plain, (![A_43, B_44]: (k4_lattices(A_43, k6_lattices(A_43), B_44)=B_44 | ~m1_subset_1(B_44, u1_struct_0(A_43)) | ~l3_lattices(A_43) | ~v14_lattices(A_43) | ~v10_lattices(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.90/1.40  tff(c_79, plain, (k4_lattices('#skF_3', k6_lattices('#skF_3'), '#skF_4')='#skF_4' | ~l3_lattices('#skF_3') | ~v14_lattices('#skF_3') | ~v10_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_71])).
% 2.90/1.40  tff(c_85, plain, (k4_lattices('#skF_3', k6_lattices('#skF_3'), '#skF_4')='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_79])).
% 2.90/1.40  tff(c_86, plain, (k4_lattices('#skF_3', k6_lattices('#skF_3'), '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_50, c_85])).
% 2.90/1.40  tff(c_272, plain, (![B_60]: (k4_lattices('#skF_3', B_60, '#skF_4')=k4_lattices('#skF_3', '#skF_4', B_60) | ~m1_subset_1(B_60, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_222])).
% 2.90/1.40  tff(c_284, plain, (k4_lattices('#skF_3', k6_lattices('#skF_3'), '#skF_4')=k4_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3')) | ~l2_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_28, c_272])).
% 2.90/1.40  tff(c_298, plain, (k4_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3'))='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_86, c_284])).
% 2.90/1.40  tff(c_299, plain, (k4_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_50, c_298])).
% 2.90/1.40  tff(c_373, plain, (![A_67, B_68, C_69]: (k4_lattices(A_67, B_68, C_69)=k2_lattices(A_67, B_68, C_69) | ~m1_subset_1(C_69, u1_struct_0(A_67)) | ~m1_subset_1(B_68, u1_struct_0(A_67)) | ~l1_lattices(A_67) | ~v6_lattices(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.90/1.40  tff(c_493, plain, (![A_76, B_77]: (k4_lattices(A_76, B_77, k6_lattices(A_76))=k2_lattices(A_76, B_77, k6_lattices(A_76)) | ~m1_subset_1(B_77, u1_struct_0(A_76)) | ~l1_lattices(A_76) | ~v6_lattices(A_76) | ~l2_lattices(A_76) | v2_struct_0(A_76))), inference(resolution, [status(thm)], [c_28, c_373])).
% 2.90/1.40  tff(c_501, plain, (k4_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3'))=k2_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3')) | ~l1_lattices('#skF_3') | ~v6_lattices('#skF_3') | ~l2_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_493])).
% 2.90/1.40  tff(c_507, plain, (k2_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3'))='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_271, c_55, c_299, c_501])).
% 2.90/1.40  tff(c_508, plain, (k2_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_50, c_507])).
% 2.90/1.40  tff(c_528, plain, (![A_79, B_80]: (k1_lattices(A_79, k2_lattices(A_79, B_80, k6_lattices(A_79)), k6_lattices(A_79))=k6_lattices(A_79) | ~m1_subset_1(B_80, u1_struct_0(A_79)) | ~v8_lattices(A_79) | ~l3_lattices(A_79) | ~l2_lattices(A_79) | v2_struct_0(A_79))), inference(resolution, [status(thm)], [c_28, c_100])).
% 2.90/1.40  tff(c_537, plain, (k1_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3'))=k6_lattices('#skF_3') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~v8_lattices('#skF_3') | ~l3_lattices('#skF_3') | ~l2_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_508, c_528])).
% 2.90/1.40  tff(c_541, plain, (k1_lattices('#skF_3', '#skF_4', k6_lattices('#skF_3'))=k6_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_44, c_142, c_42, c_537])).
% 2.90/1.40  tff(c_543, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_453, c_541])).
% 2.90/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.40  
% 2.90/1.40  Inference rules
% 2.90/1.40  ----------------------
% 2.90/1.40  #Ref     : 0
% 2.90/1.40  #Sup     : 110
% 2.90/1.40  #Fact    : 0
% 2.90/1.40  #Define  : 0
% 2.90/1.40  #Split   : 3
% 2.90/1.40  #Chain   : 0
% 2.90/1.40  #Close   : 0
% 2.90/1.40  
% 2.90/1.40  Ordering : KBO
% 2.90/1.40  
% 2.90/1.40  Simplification rules
% 2.90/1.40  ----------------------
% 2.90/1.40  #Subsume      : 2
% 2.90/1.40  #Demod        : 73
% 2.90/1.40  #Tautology    : 57
% 2.90/1.40  #SimpNegUnit  : 30
% 2.90/1.40  #BackRed      : 6
% 2.90/1.40  
% 2.90/1.40  #Partial instantiations: 0
% 2.90/1.40  #Strategies tried      : 1
% 2.90/1.40  
% 2.90/1.40  Timing (in seconds)
% 2.90/1.40  ----------------------
% 2.90/1.41  Preprocessing        : 0.33
% 2.90/1.41  Parsing              : 0.17
% 2.90/1.41  CNF conversion       : 0.02
% 2.90/1.41  Main loop            : 0.31
% 2.90/1.41  Inferencing          : 0.12
% 2.90/1.41  Reduction            : 0.09
% 2.90/1.41  Demodulation         : 0.06
% 2.90/1.41  BG Simplification    : 0.02
% 2.90/1.41  Subsumption          : 0.06
% 2.90/1.41  Abstraction          : 0.02
% 2.90/1.41  MUC search           : 0.00
% 2.90/1.41  Cooper               : 0.00
% 2.90/1.41  Total                : 0.68
% 2.90/1.41  Index Insertion      : 0.00
% 2.90/1.41  Index Deletion       : 0.00
% 2.90/1.41  Index Matching       : 0.00
% 2.90/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
