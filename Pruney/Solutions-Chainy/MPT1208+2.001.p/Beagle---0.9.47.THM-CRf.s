%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:17 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 508 expanded)
%              Number of leaves         :   34 ( 187 expanded)
%              Depth                    :   15
%              Number of atoms          :  272 (1703 expanded)
%              Number of equality atoms :   57 ( 282 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v14_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > k6_lattices > #skF_2 > #skF_3 > #skF_1

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

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

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

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v14_lattices,type,(
    v14_lattices: $i > $o )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_154,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v14_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => k4_lattices(A,k6_lattices(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_lattices)).

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

tff(f_107,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k4_lattices(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).

tff(f_101,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => m1_subset_1(k6_lattices(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_lattices)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => ( v14_lattices(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( B = k6_lattices(A)
            <=> ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ( k1_lattices(A,B,C) = B
                    & k1_lattices(A,C,B) = B ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattices)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k2_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

tff(f_139,axiom,(
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

tff(f_94,axiom,(
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

tff(c_44,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_46,plain,(
    l3_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_50,plain,(
    v10_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_53,plain,(
    ! [A_35] :
      ( l1_lattices(A_35)
      | ~ l3_lattices(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_57,plain,(
    l1_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_53])).

tff(c_200,plain,(
    ! [A_60,C_61,B_62] :
      ( k4_lattices(A_60,C_61,B_62) = k4_lattices(A_60,B_62,C_61)
      | ~ m1_subset_1(C_61,u1_struct_0(A_60))
      | ~ m1_subset_1(B_62,u1_struct_0(A_60))
      | ~ l1_lattices(A_60)
      | ~ v6_lattices(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_208,plain,(
    ! [B_62] :
      ( k4_lattices('#skF_2',B_62,'#skF_3') = k4_lattices('#skF_2','#skF_3',B_62)
      | ~ m1_subset_1(B_62,u1_struct_0('#skF_2'))
      | ~ l1_lattices('#skF_2')
      | ~ v6_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_200])).

tff(c_217,plain,(
    ! [B_62] :
      ( k4_lattices('#skF_2',B_62,'#skF_3') = k4_lattices('#skF_2','#skF_3',B_62)
      | ~ m1_subset_1(B_62,u1_struct_0('#skF_2'))
      | ~ v6_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_208])).

tff(c_218,plain,(
    ! [B_62] :
      ( k4_lattices('#skF_2',B_62,'#skF_3') = k4_lattices('#skF_2','#skF_3',B_62)
      | ~ m1_subset_1(B_62,u1_struct_0('#skF_2'))
      | ~ v6_lattices('#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_217])).

tff(c_219,plain,(
    ~ v6_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_222,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_219])).

tff(c_225,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_50,c_222])).

tff(c_227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_225])).

tff(c_229,plain,(
    v6_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_58,plain,(
    ! [A_36] :
      ( l2_lattices(A_36)
      | ~ l3_lattices(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_62,plain,(
    l2_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_58])).

tff(c_30,plain,(
    ! [A_22] :
      ( m1_subset_1(k6_lattices(A_22),u1_struct_0(A_22))
      | ~ l2_lattices(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_48,plain,(
    v14_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_108,plain,(
    ! [A_53,C_54] :
      ( k1_lattices(A_53,C_54,k6_lattices(A_53)) = k6_lattices(A_53)
      | ~ m1_subset_1(C_54,u1_struct_0(A_53))
      | ~ m1_subset_1(k6_lattices(A_53),u1_struct_0(A_53))
      | ~ v14_lattices(A_53)
      | ~ l2_lattices(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_114,plain,
    ( k1_lattices('#skF_2','#skF_3',k6_lattices('#skF_2')) = k6_lattices('#skF_2')
    | ~ m1_subset_1(k6_lattices('#skF_2'),u1_struct_0('#skF_2'))
    | ~ v14_lattices('#skF_2')
    | ~ l2_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_108])).

tff(c_119,plain,
    ( k1_lattices('#skF_2','#skF_3',k6_lattices('#skF_2')) = k6_lattices('#skF_2')
    | ~ m1_subset_1(k6_lattices('#skF_2'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_48,c_114])).

tff(c_120,plain,
    ( k1_lattices('#skF_2','#skF_3',k6_lattices('#skF_2')) = k6_lattices('#skF_2')
    | ~ m1_subset_1(k6_lattices('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_119])).

tff(c_121,plain,(
    ~ m1_subset_1(k6_lattices('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_124,plain,
    ( ~ l2_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_121])).

tff(c_127,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_124])).

tff(c_129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_127])).

tff(c_131,plain,(
    m1_subset_1(k6_lattices('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_379,plain,(
    ! [A_70,B_71,C_72] :
      ( k4_lattices(A_70,B_71,C_72) = k2_lattices(A_70,B_71,C_72)
      | ~ m1_subset_1(C_72,u1_struct_0(A_70))
      | ~ m1_subset_1(B_71,u1_struct_0(A_70))
      | ~ l1_lattices(A_70)
      | ~ v6_lattices(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_381,plain,(
    ! [B_71] :
      ( k4_lattices('#skF_2',B_71,k6_lattices('#skF_2')) = k2_lattices('#skF_2',B_71,k6_lattices('#skF_2'))
      | ~ m1_subset_1(B_71,u1_struct_0('#skF_2'))
      | ~ l1_lattices('#skF_2')
      | ~ v6_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_131,c_379])).

tff(c_390,plain,(
    ! [B_71] :
      ( k4_lattices('#skF_2',B_71,k6_lattices('#skF_2')) = k2_lattices('#skF_2',B_71,k6_lattices('#skF_2'))
      | ~ m1_subset_1(B_71,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_57,c_381])).

tff(c_461,plain,(
    ! [B_76] :
      ( k4_lattices('#skF_2',B_76,k6_lattices('#skF_2')) = k2_lattices('#skF_2',B_76,k6_lattices('#skF_2'))
      | ~ m1_subset_1(B_76,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_390])).

tff(c_485,plain,(
    k4_lattices('#skF_2','#skF_3',k6_lattices('#skF_2')) = k2_lattices('#skF_2','#skF_3',k6_lattices('#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_461])).

tff(c_202,plain,(
    ! [B_62] :
      ( k4_lattices('#skF_2',k6_lattices('#skF_2'),B_62) = k4_lattices('#skF_2',B_62,k6_lattices('#skF_2'))
      | ~ m1_subset_1(B_62,u1_struct_0('#skF_2'))
      | ~ l1_lattices('#skF_2')
      | ~ v6_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_131,c_200])).

tff(c_211,plain,(
    ! [B_62] :
      ( k4_lattices('#skF_2',k6_lattices('#skF_2'),B_62) = k4_lattices('#skF_2',B_62,k6_lattices('#skF_2'))
      | ~ m1_subset_1(B_62,u1_struct_0('#skF_2'))
      | ~ v6_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_202])).

tff(c_212,plain,(
    ! [B_62] :
      ( k4_lattices('#skF_2',k6_lattices('#skF_2'),B_62) = k4_lattices('#skF_2',B_62,k6_lattices('#skF_2'))
      | ~ m1_subset_1(B_62,u1_struct_0('#skF_2'))
      | ~ v6_lattices('#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_211])).

tff(c_232,plain,(
    ! [B_63] :
      ( k4_lattices('#skF_2',k6_lattices('#skF_2'),B_63) = k4_lattices('#skF_2',B_63,k6_lattices('#skF_2'))
      | ~ m1_subset_1(B_63,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_212])).

tff(c_258,plain,(
    k4_lattices('#skF_2',k6_lattices('#skF_2'),'#skF_3') = k4_lattices('#skF_2','#skF_3',k6_lattices('#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_232])).

tff(c_387,plain,(
    ! [B_71] :
      ( k4_lattices('#skF_2',B_71,'#skF_3') = k2_lattices('#skF_2',B_71,'#skF_3')
      | ~ m1_subset_1(B_71,u1_struct_0('#skF_2'))
      | ~ l1_lattices('#skF_2')
      | ~ v6_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_379])).

tff(c_396,plain,(
    ! [B_71] :
      ( k4_lattices('#skF_2',B_71,'#skF_3') = k2_lattices('#skF_2',B_71,'#skF_3')
      | ~ m1_subset_1(B_71,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_57,c_387])).

tff(c_398,plain,(
    ! [B_73] :
      ( k4_lattices('#skF_2',B_73,'#skF_3') = k2_lattices('#skF_2',B_73,'#skF_3')
      | ~ m1_subset_1(B_73,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_396])).

tff(c_409,plain,
    ( k4_lattices('#skF_2',k6_lattices('#skF_2'),'#skF_3') = k2_lattices('#skF_2',k6_lattices('#skF_2'),'#skF_3')
    | ~ l2_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_398])).

tff(c_420,plain,
    ( k4_lattices('#skF_2','#skF_3',k6_lattices('#skF_2')) = k2_lattices('#skF_2',k6_lattices('#skF_2'),'#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_258,c_409])).

tff(c_421,plain,(
    k4_lattices('#skF_2','#skF_3',k6_lattices('#skF_2')) = k2_lattices('#skF_2',k6_lattices('#skF_2'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_420])).

tff(c_487,plain,(
    k2_lattices('#skF_2',k6_lattices('#skF_2'),'#skF_3') = k2_lattices('#skF_2','#skF_3',k6_lattices('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_421])).

tff(c_42,plain,(
    k4_lattices('#skF_2',k6_lattices('#skF_2'),'#skF_3') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_259,plain,(
    k4_lattices('#skF_2','#skF_3',k6_lattices('#skF_2')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_42])).

tff(c_456,plain,(
    k2_lattices('#skF_2',k6_lattices('#skF_2'),'#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_259])).

tff(c_492,plain,(
    k2_lattices('#skF_2','#skF_3',k6_lattices('#skF_2')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_456])).

tff(c_130,plain,(
    k1_lattices('#skF_2','#skF_3',k6_lattices('#skF_2')) = k6_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_502,plain,(
    ! [A_77,B_78,C_79] :
      ( r1_lattices(A_77,B_78,C_79)
      | k2_lattices(A_77,B_78,C_79) != B_78
      | ~ m1_subset_1(C_79,u1_struct_0(A_77))
      | ~ m1_subset_1(B_78,u1_struct_0(A_77))
      | ~ l3_lattices(A_77)
      | ~ v9_lattices(A_77)
      | ~ v8_lattices(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_510,plain,(
    ! [B_78] :
      ( r1_lattices('#skF_2',B_78,'#skF_3')
      | k2_lattices('#skF_2',B_78,'#skF_3') != B_78
      | ~ m1_subset_1(B_78,u1_struct_0('#skF_2'))
      | ~ l3_lattices('#skF_2')
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_502])).

tff(c_519,plain,(
    ! [B_78] :
      ( r1_lattices('#skF_2',B_78,'#skF_3')
      | k2_lattices('#skF_2',B_78,'#skF_3') != B_78
      | ~ m1_subset_1(B_78,u1_struct_0('#skF_2'))
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_510])).

tff(c_520,plain,(
    ! [B_78] :
      ( r1_lattices('#skF_2',B_78,'#skF_3')
      | k2_lattices('#skF_2',B_78,'#skF_3') != B_78
      | ~ m1_subset_1(B_78,u1_struct_0('#skF_2'))
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_519])).

tff(c_526,plain,(
    ~ v8_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_520])).

tff(c_558,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_526])).

tff(c_561,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_50,c_558])).

tff(c_563,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_561])).

tff(c_565,plain,(
    v8_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_520])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_564,plain,(
    ! [B_78] :
      ( ~ v9_lattices('#skF_2')
      | r1_lattices('#skF_2',B_78,'#skF_3')
      | k2_lattices('#skF_2',B_78,'#skF_3') != B_78
      | ~ m1_subset_1(B_78,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_520])).

tff(c_566,plain,(
    ~ v9_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_564])).

tff(c_569,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_566])).

tff(c_572,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_50,c_569])).

tff(c_574,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_572])).

tff(c_576,plain,(
    v9_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_564])).

tff(c_26,plain,(
    ! [A_15,B_19,C_21] :
      ( r1_lattices(A_15,B_19,C_21)
      | k1_lattices(A_15,B_19,C_21) != C_21
      | ~ m1_subset_1(C_21,u1_struct_0(A_15))
      | ~ m1_subset_1(B_19,u1_struct_0(A_15))
      | ~ l2_lattices(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_138,plain,(
    ! [B_19] :
      ( r1_lattices('#skF_2',B_19,k6_lattices('#skF_2'))
      | k1_lattices('#skF_2',B_19,k6_lattices('#skF_2')) != k6_lattices('#skF_2')
      | ~ m1_subset_1(B_19,u1_struct_0('#skF_2'))
      | ~ l2_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_131,c_26])).

tff(c_146,plain,(
    ! [B_19] :
      ( r1_lattices('#skF_2',B_19,k6_lattices('#skF_2'))
      | k1_lattices('#skF_2',B_19,k6_lattices('#skF_2')) != k6_lattices('#skF_2')
      | ~ m1_subset_1(B_19,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_138])).

tff(c_147,plain,(
    ! [B_19] :
      ( r1_lattices('#skF_2',B_19,k6_lattices('#skF_2'))
      | k1_lattices('#skF_2',B_19,k6_lattices('#skF_2')) != k6_lattices('#skF_2')
      | ~ m1_subset_1(B_19,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_146])).

tff(c_577,plain,(
    ! [A_81,B_82,C_83] :
      ( k2_lattices(A_81,B_82,C_83) = B_82
      | ~ r1_lattices(A_81,B_82,C_83)
      | ~ m1_subset_1(C_83,u1_struct_0(A_81))
      | ~ m1_subset_1(B_82,u1_struct_0(A_81))
      | ~ l3_lattices(A_81)
      | ~ v9_lattices(A_81)
      | ~ v8_lattices(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_583,plain,(
    ! [B_19] :
      ( k2_lattices('#skF_2',B_19,k6_lattices('#skF_2')) = B_19
      | ~ m1_subset_1(k6_lattices('#skF_2'),u1_struct_0('#skF_2'))
      | ~ l3_lattices('#skF_2')
      | ~ v9_lattices('#skF_2')
      | ~ v8_lattices('#skF_2')
      | v2_struct_0('#skF_2')
      | k1_lattices('#skF_2',B_19,k6_lattices('#skF_2')) != k6_lattices('#skF_2')
      | ~ m1_subset_1(B_19,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_147,c_577])).

tff(c_591,plain,(
    ! [B_19] :
      ( k2_lattices('#skF_2',B_19,k6_lattices('#skF_2')) = B_19
      | v2_struct_0('#skF_2')
      | k1_lattices('#skF_2',B_19,k6_lattices('#skF_2')) != k6_lattices('#skF_2')
      | ~ m1_subset_1(B_19,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_565,c_576,c_46,c_131,c_583])).

tff(c_621,plain,(
    ! [B_85] :
      ( k2_lattices('#skF_2',B_85,k6_lattices('#skF_2')) = B_85
      | k1_lattices('#skF_2',B_85,k6_lattices('#skF_2')) != k6_lattices('#skF_2')
      | ~ m1_subset_1(B_85,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_591])).

tff(c_635,plain,
    ( k2_lattices('#skF_2','#skF_3',k6_lattices('#skF_2')) = '#skF_3'
    | k1_lattices('#skF_2','#skF_3',k6_lattices('#skF_2')) != k6_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_621])).

tff(c_649,plain,(
    k2_lattices('#skF_2','#skF_3',k6_lattices('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_635])).

tff(c_651,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_492,c_649])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n023.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:55:20 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.49  
% 2.88/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.50  %$ r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v14_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > k6_lattices > #skF_2 > #skF_3 > #skF_1
% 2.88/1.50  
% 2.88/1.50  %Foreground sorts:
% 2.88/1.50  
% 2.88/1.50  
% 2.88/1.50  %Background operators:
% 2.88/1.50  
% 2.88/1.50  
% 2.88/1.50  %Foreground operators:
% 2.88/1.50  tff(l3_lattices, type, l3_lattices: $i > $o).
% 2.88/1.50  tff(k6_lattices, type, k6_lattices: $i > $i).
% 2.88/1.50  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.88/1.50  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 2.88/1.50  tff(l2_lattices, type, l2_lattices: $i > $o).
% 2.88/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.50  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 2.88/1.50  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 2.88/1.50  tff(l1_lattices, type, l1_lattices: $i > $o).
% 2.88/1.50  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 2.88/1.50  tff(v4_lattices, type, v4_lattices: $i > $o).
% 2.88/1.50  tff(v6_lattices, type, v6_lattices: $i > $o).
% 2.88/1.50  tff('#skF_2', type, '#skF_2': $i).
% 2.88/1.50  tff(v9_lattices, type, v9_lattices: $i > $o).
% 2.88/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.88/1.50  tff(v5_lattices, type, v5_lattices: $i > $o).
% 2.88/1.50  tff(v10_lattices, type, v10_lattices: $i > $o).
% 2.88/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.50  tff(v14_lattices, type, v14_lattices: $i > $o).
% 2.88/1.50  tff(v8_lattices, type, v8_lattices: $i > $o).
% 2.88/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.88/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.88/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.88/1.50  tff(v7_lattices, type, v7_lattices: $i > $o).
% 2.88/1.50  
% 2.88/1.52  tff(f_154, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v14_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k4_lattices(A, k6_lattices(A), B) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_lattices)).
% 2.88/1.52  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 2.88/1.52  tff(f_107, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 2.88/1.52  tff(f_60, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k4_lattices(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k4_lattices)).
% 2.88/1.52  tff(f_101, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => m1_subset_1(k6_lattices(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_lattices)).
% 2.88/1.52  tff(f_79, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (v14_lattices(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((B = k6_lattices(A)) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k1_lattices(A, B, C) = B) & (k1_lattices(A, C, B) = B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattices)).
% 2.88/1.52  tff(f_120, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k2_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 2.88/1.52  tff(f_139, axiom, (![A]: ((((~v2_struct_0(A) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k2_lattices(A, B, C) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 2.88/1.52  tff(f_94, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k1_lattices(A, B, C) = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_lattices)).
% 2.88/1.52  tff(c_44, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.88/1.52  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.88/1.52  tff(c_46, plain, (l3_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.88/1.52  tff(c_50, plain, (v10_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.88/1.52  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.88/1.52  tff(c_53, plain, (![A_35]: (l1_lattices(A_35) | ~l3_lattices(A_35))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.88/1.52  tff(c_57, plain, (l1_lattices('#skF_2')), inference(resolution, [status(thm)], [c_46, c_53])).
% 2.88/1.52  tff(c_200, plain, (![A_60, C_61, B_62]: (k4_lattices(A_60, C_61, B_62)=k4_lattices(A_60, B_62, C_61) | ~m1_subset_1(C_61, u1_struct_0(A_60)) | ~m1_subset_1(B_62, u1_struct_0(A_60)) | ~l1_lattices(A_60) | ~v6_lattices(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.88/1.52  tff(c_208, plain, (![B_62]: (k4_lattices('#skF_2', B_62, '#skF_3')=k4_lattices('#skF_2', '#skF_3', B_62) | ~m1_subset_1(B_62, u1_struct_0('#skF_2')) | ~l1_lattices('#skF_2') | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_200])).
% 2.88/1.52  tff(c_217, plain, (![B_62]: (k4_lattices('#skF_2', B_62, '#skF_3')=k4_lattices('#skF_2', '#skF_3', B_62) | ~m1_subset_1(B_62, u1_struct_0('#skF_2')) | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_208])).
% 2.88/1.52  tff(c_218, plain, (![B_62]: (k4_lattices('#skF_2', B_62, '#skF_3')=k4_lattices('#skF_2', '#skF_3', B_62) | ~m1_subset_1(B_62, u1_struct_0('#skF_2')) | ~v6_lattices('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_217])).
% 2.88/1.52  tff(c_219, plain, (~v6_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_218])).
% 2.88/1.52  tff(c_222, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_8, c_219])).
% 2.88/1.52  tff(c_225, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_50, c_222])).
% 2.88/1.52  tff(c_227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_225])).
% 2.88/1.52  tff(c_229, plain, (v6_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_218])).
% 2.88/1.52  tff(c_58, plain, (![A_36]: (l2_lattices(A_36) | ~l3_lattices(A_36))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.88/1.52  tff(c_62, plain, (l2_lattices('#skF_2')), inference(resolution, [status(thm)], [c_46, c_58])).
% 2.88/1.52  tff(c_30, plain, (![A_22]: (m1_subset_1(k6_lattices(A_22), u1_struct_0(A_22)) | ~l2_lattices(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.88/1.52  tff(c_48, plain, (v14_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.88/1.52  tff(c_108, plain, (![A_53, C_54]: (k1_lattices(A_53, C_54, k6_lattices(A_53))=k6_lattices(A_53) | ~m1_subset_1(C_54, u1_struct_0(A_53)) | ~m1_subset_1(k6_lattices(A_53), u1_struct_0(A_53)) | ~v14_lattices(A_53) | ~l2_lattices(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.88/1.52  tff(c_114, plain, (k1_lattices('#skF_2', '#skF_3', k6_lattices('#skF_2'))=k6_lattices('#skF_2') | ~m1_subset_1(k6_lattices('#skF_2'), u1_struct_0('#skF_2')) | ~v14_lattices('#skF_2') | ~l2_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_108])).
% 2.88/1.52  tff(c_119, plain, (k1_lattices('#skF_2', '#skF_3', k6_lattices('#skF_2'))=k6_lattices('#skF_2') | ~m1_subset_1(k6_lattices('#skF_2'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_48, c_114])).
% 2.88/1.52  tff(c_120, plain, (k1_lattices('#skF_2', '#skF_3', k6_lattices('#skF_2'))=k6_lattices('#skF_2') | ~m1_subset_1(k6_lattices('#skF_2'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_119])).
% 2.88/1.52  tff(c_121, plain, (~m1_subset_1(k6_lattices('#skF_2'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_120])).
% 2.88/1.52  tff(c_124, plain, (~l2_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_121])).
% 2.88/1.52  tff(c_127, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_124])).
% 2.88/1.52  tff(c_129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_127])).
% 2.88/1.52  tff(c_131, plain, (m1_subset_1(k6_lattices('#skF_2'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_120])).
% 2.88/1.52  tff(c_379, plain, (![A_70, B_71, C_72]: (k4_lattices(A_70, B_71, C_72)=k2_lattices(A_70, B_71, C_72) | ~m1_subset_1(C_72, u1_struct_0(A_70)) | ~m1_subset_1(B_71, u1_struct_0(A_70)) | ~l1_lattices(A_70) | ~v6_lattices(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.88/1.52  tff(c_381, plain, (![B_71]: (k4_lattices('#skF_2', B_71, k6_lattices('#skF_2'))=k2_lattices('#skF_2', B_71, k6_lattices('#skF_2')) | ~m1_subset_1(B_71, u1_struct_0('#skF_2')) | ~l1_lattices('#skF_2') | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_131, c_379])).
% 2.88/1.52  tff(c_390, plain, (![B_71]: (k4_lattices('#skF_2', B_71, k6_lattices('#skF_2'))=k2_lattices('#skF_2', B_71, k6_lattices('#skF_2')) | ~m1_subset_1(B_71, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_57, c_381])).
% 2.88/1.52  tff(c_461, plain, (![B_76]: (k4_lattices('#skF_2', B_76, k6_lattices('#skF_2'))=k2_lattices('#skF_2', B_76, k6_lattices('#skF_2')) | ~m1_subset_1(B_76, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_52, c_390])).
% 2.88/1.52  tff(c_485, plain, (k4_lattices('#skF_2', '#skF_3', k6_lattices('#skF_2'))=k2_lattices('#skF_2', '#skF_3', k6_lattices('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_461])).
% 2.88/1.52  tff(c_202, plain, (![B_62]: (k4_lattices('#skF_2', k6_lattices('#skF_2'), B_62)=k4_lattices('#skF_2', B_62, k6_lattices('#skF_2')) | ~m1_subset_1(B_62, u1_struct_0('#skF_2')) | ~l1_lattices('#skF_2') | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_131, c_200])).
% 2.88/1.52  tff(c_211, plain, (![B_62]: (k4_lattices('#skF_2', k6_lattices('#skF_2'), B_62)=k4_lattices('#skF_2', B_62, k6_lattices('#skF_2')) | ~m1_subset_1(B_62, u1_struct_0('#skF_2')) | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_202])).
% 2.88/1.52  tff(c_212, plain, (![B_62]: (k4_lattices('#skF_2', k6_lattices('#skF_2'), B_62)=k4_lattices('#skF_2', B_62, k6_lattices('#skF_2')) | ~m1_subset_1(B_62, u1_struct_0('#skF_2')) | ~v6_lattices('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_211])).
% 2.88/1.52  tff(c_232, plain, (![B_63]: (k4_lattices('#skF_2', k6_lattices('#skF_2'), B_63)=k4_lattices('#skF_2', B_63, k6_lattices('#skF_2')) | ~m1_subset_1(B_63, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_212])).
% 2.88/1.52  tff(c_258, plain, (k4_lattices('#skF_2', k6_lattices('#skF_2'), '#skF_3')=k4_lattices('#skF_2', '#skF_3', k6_lattices('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_232])).
% 2.88/1.52  tff(c_387, plain, (![B_71]: (k4_lattices('#skF_2', B_71, '#skF_3')=k2_lattices('#skF_2', B_71, '#skF_3') | ~m1_subset_1(B_71, u1_struct_0('#skF_2')) | ~l1_lattices('#skF_2') | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_379])).
% 2.88/1.52  tff(c_396, plain, (![B_71]: (k4_lattices('#skF_2', B_71, '#skF_3')=k2_lattices('#skF_2', B_71, '#skF_3') | ~m1_subset_1(B_71, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_57, c_387])).
% 2.88/1.52  tff(c_398, plain, (![B_73]: (k4_lattices('#skF_2', B_73, '#skF_3')=k2_lattices('#skF_2', B_73, '#skF_3') | ~m1_subset_1(B_73, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_52, c_396])).
% 2.88/1.52  tff(c_409, plain, (k4_lattices('#skF_2', k6_lattices('#skF_2'), '#skF_3')=k2_lattices('#skF_2', k6_lattices('#skF_2'), '#skF_3') | ~l2_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_398])).
% 2.88/1.52  tff(c_420, plain, (k4_lattices('#skF_2', '#skF_3', k6_lattices('#skF_2'))=k2_lattices('#skF_2', k6_lattices('#skF_2'), '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_258, c_409])).
% 2.88/1.52  tff(c_421, plain, (k4_lattices('#skF_2', '#skF_3', k6_lattices('#skF_2'))=k2_lattices('#skF_2', k6_lattices('#skF_2'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_52, c_420])).
% 2.88/1.52  tff(c_487, plain, (k2_lattices('#skF_2', k6_lattices('#skF_2'), '#skF_3')=k2_lattices('#skF_2', '#skF_3', k6_lattices('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_485, c_421])).
% 2.88/1.52  tff(c_42, plain, (k4_lattices('#skF_2', k6_lattices('#skF_2'), '#skF_3')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.88/1.52  tff(c_259, plain, (k4_lattices('#skF_2', '#skF_3', k6_lattices('#skF_2'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_258, c_42])).
% 2.88/1.52  tff(c_456, plain, (k2_lattices('#skF_2', k6_lattices('#skF_2'), '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_421, c_259])).
% 2.88/1.52  tff(c_492, plain, (k2_lattices('#skF_2', '#skF_3', k6_lattices('#skF_2'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_487, c_456])).
% 2.88/1.52  tff(c_130, plain, (k1_lattices('#skF_2', '#skF_3', k6_lattices('#skF_2'))=k6_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_120])).
% 2.88/1.52  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.88/1.52  tff(c_502, plain, (![A_77, B_78, C_79]: (r1_lattices(A_77, B_78, C_79) | k2_lattices(A_77, B_78, C_79)!=B_78 | ~m1_subset_1(C_79, u1_struct_0(A_77)) | ~m1_subset_1(B_78, u1_struct_0(A_77)) | ~l3_lattices(A_77) | ~v9_lattices(A_77) | ~v8_lattices(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.88/1.52  tff(c_510, plain, (![B_78]: (r1_lattices('#skF_2', B_78, '#skF_3') | k2_lattices('#skF_2', B_78, '#skF_3')!=B_78 | ~m1_subset_1(B_78, u1_struct_0('#skF_2')) | ~l3_lattices('#skF_2') | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_502])).
% 2.88/1.52  tff(c_519, plain, (![B_78]: (r1_lattices('#skF_2', B_78, '#skF_3') | k2_lattices('#skF_2', B_78, '#skF_3')!=B_78 | ~m1_subset_1(B_78, u1_struct_0('#skF_2')) | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_510])).
% 2.88/1.52  tff(c_520, plain, (![B_78]: (r1_lattices('#skF_2', B_78, '#skF_3') | k2_lattices('#skF_2', B_78, '#skF_3')!=B_78 | ~m1_subset_1(B_78, u1_struct_0('#skF_2')) | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_519])).
% 2.88/1.52  tff(c_526, plain, (~v8_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_520])).
% 2.88/1.52  tff(c_558, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_4, c_526])).
% 2.88/1.52  tff(c_561, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_50, c_558])).
% 2.88/1.52  tff(c_563, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_561])).
% 2.88/1.52  tff(c_565, plain, (v8_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_520])).
% 2.88/1.52  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.88/1.52  tff(c_564, plain, (![B_78]: (~v9_lattices('#skF_2') | r1_lattices('#skF_2', B_78, '#skF_3') | k2_lattices('#skF_2', B_78, '#skF_3')!=B_78 | ~m1_subset_1(B_78, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_520])).
% 2.88/1.52  tff(c_566, plain, (~v9_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_564])).
% 2.88/1.52  tff(c_569, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_2, c_566])).
% 2.88/1.52  tff(c_572, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_50, c_569])).
% 2.88/1.52  tff(c_574, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_572])).
% 2.88/1.52  tff(c_576, plain, (v9_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_564])).
% 2.88/1.52  tff(c_26, plain, (![A_15, B_19, C_21]: (r1_lattices(A_15, B_19, C_21) | k1_lattices(A_15, B_19, C_21)!=C_21 | ~m1_subset_1(C_21, u1_struct_0(A_15)) | ~m1_subset_1(B_19, u1_struct_0(A_15)) | ~l2_lattices(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.88/1.52  tff(c_138, plain, (![B_19]: (r1_lattices('#skF_2', B_19, k6_lattices('#skF_2')) | k1_lattices('#skF_2', B_19, k6_lattices('#skF_2'))!=k6_lattices('#skF_2') | ~m1_subset_1(B_19, u1_struct_0('#skF_2')) | ~l2_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_131, c_26])).
% 2.88/1.52  tff(c_146, plain, (![B_19]: (r1_lattices('#skF_2', B_19, k6_lattices('#skF_2')) | k1_lattices('#skF_2', B_19, k6_lattices('#skF_2'))!=k6_lattices('#skF_2') | ~m1_subset_1(B_19, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_138])).
% 2.88/1.52  tff(c_147, plain, (![B_19]: (r1_lattices('#skF_2', B_19, k6_lattices('#skF_2')) | k1_lattices('#skF_2', B_19, k6_lattices('#skF_2'))!=k6_lattices('#skF_2') | ~m1_subset_1(B_19, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_52, c_146])).
% 2.88/1.52  tff(c_577, plain, (![A_81, B_82, C_83]: (k2_lattices(A_81, B_82, C_83)=B_82 | ~r1_lattices(A_81, B_82, C_83) | ~m1_subset_1(C_83, u1_struct_0(A_81)) | ~m1_subset_1(B_82, u1_struct_0(A_81)) | ~l3_lattices(A_81) | ~v9_lattices(A_81) | ~v8_lattices(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.88/1.52  tff(c_583, plain, (![B_19]: (k2_lattices('#skF_2', B_19, k6_lattices('#skF_2'))=B_19 | ~m1_subset_1(k6_lattices('#skF_2'), u1_struct_0('#skF_2')) | ~l3_lattices('#skF_2') | ~v9_lattices('#skF_2') | ~v8_lattices('#skF_2') | v2_struct_0('#skF_2') | k1_lattices('#skF_2', B_19, k6_lattices('#skF_2'))!=k6_lattices('#skF_2') | ~m1_subset_1(B_19, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_147, c_577])).
% 2.88/1.52  tff(c_591, plain, (![B_19]: (k2_lattices('#skF_2', B_19, k6_lattices('#skF_2'))=B_19 | v2_struct_0('#skF_2') | k1_lattices('#skF_2', B_19, k6_lattices('#skF_2'))!=k6_lattices('#skF_2') | ~m1_subset_1(B_19, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_565, c_576, c_46, c_131, c_583])).
% 2.88/1.52  tff(c_621, plain, (![B_85]: (k2_lattices('#skF_2', B_85, k6_lattices('#skF_2'))=B_85 | k1_lattices('#skF_2', B_85, k6_lattices('#skF_2'))!=k6_lattices('#skF_2') | ~m1_subset_1(B_85, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_52, c_591])).
% 2.88/1.52  tff(c_635, plain, (k2_lattices('#skF_2', '#skF_3', k6_lattices('#skF_2'))='#skF_3' | k1_lattices('#skF_2', '#skF_3', k6_lattices('#skF_2'))!=k6_lattices('#skF_2')), inference(resolution, [status(thm)], [c_44, c_621])).
% 2.88/1.52  tff(c_649, plain, (k2_lattices('#skF_2', '#skF_3', k6_lattices('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_130, c_635])).
% 2.88/1.52  tff(c_651, plain, $false, inference(negUnitSimplification, [status(thm)], [c_492, c_649])).
% 2.88/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.52  
% 2.88/1.52  Inference rules
% 2.88/1.52  ----------------------
% 2.88/1.52  #Ref     : 0
% 2.88/1.52  #Sup     : 110
% 2.88/1.52  #Fact    : 0
% 2.88/1.52  #Define  : 0
% 2.88/1.52  #Split   : 9
% 2.88/1.52  #Chain   : 0
% 2.88/1.52  #Close   : 0
% 2.88/1.52  
% 2.88/1.52  Ordering : KBO
% 2.88/1.52  
% 2.88/1.52  Simplification rules
% 2.88/1.52  ----------------------
% 2.88/1.52  #Subsume      : 8
% 2.88/1.52  #Demod        : 117
% 2.88/1.52  #Tautology    : 51
% 2.88/1.52  #SimpNegUnit  : 46
% 2.88/1.52  #BackRed      : 15
% 2.88/1.52  
% 2.88/1.52  #Partial instantiations: 0
% 2.88/1.52  #Strategies tried      : 1
% 2.88/1.52  
% 2.88/1.52  Timing (in seconds)
% 2.88/1.52  ----------------------
% 2.88/1.52  Preprocessing        : 0.32
% 2.88/1.52  Parsing              : 0.16
% 2.88/1.52  CNF conversion       : 0.02
% 2.88/1.52  Main loop            : 0.32
% 2.88/1.52  Inferencing          : 0.11
% 2.88/1.52  Reduction            : 0.10
% 2.88/1.52  Demodulation         : 0.07
% 2.88/1.52  BG Simplification    : 0.02
% 2.88/1.52  Subsumption          : 0.06
% 2.88/1.52  Abstraction          : 0.02
% 2.88/1.52  MUC search           : 0.00
% 2.88/1.52  Cooper               : 0.00
% 2.88/1.52  Total                : 0.69
% 2.88/1.52  Index Insertion      : 0.00
% 2.88/1.52  Index Deletion       : 0.00
% 2.88/1.52  Index Matching       : 0.00
% 2.88/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
