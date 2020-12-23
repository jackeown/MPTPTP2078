%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:15 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 148 expanded)
%              Number of leaves         :   29 (  66 expanded)
%              Depth                    :    9
%              Number of atoms          :  117 ( 418 expanded)
%              Number of equality atoms :   21 (  70 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k2_lattices > #nlpp > u1_struct_0 > k5_lattices > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

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

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

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

tff(v13_lattices,type,(
    v13_lattices: $i > $o )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_lattices,type,(
    k5_lattices: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v13_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => k4_lattices(A,k5_lattices(A),B) = k5_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_lattices)).

tff(f_79,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => m1_subset_1(k5_lattices(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

tff(f_66,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => ( v13_lattices(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( B = k5_lattices(A)
            <=> ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ( k2_lattices(A,B,C) = B
                    & k2_lattices(A,C,B) = B ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).

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

tff(f_92,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k2_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

tff(c_32,plain,(
    k4_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') != k5_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_36,plain,(
    l3_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_43,plain,(
    ! [A_18] :
      ( l1_lattices(A_18)
      | ~ l3_lattices(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_47,plain,(
    l1_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_43])).

tff(c_38,plain,(
    v13_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_24,plain,(
    ! [A_12] :
      ( m1_subset_1(k5_lattices(A_12),u1_struct_0(A_12))
      | ~ l1_lattices(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_61,plain,(
    ! [A_29,C_30] :
      ( k2_lattices(A_29,C_30,k5_lattices(A_29)) = k5_lattices(A_29)
      | ~ m1_subset_1(C_30,u1_struct_0(A_29))
      | ~ m1_subset_1(k5_lattices(A_29),u1_struct_0(A_29))
      | ~ v13_lattices(A_29)
      | ~ l1_lattices(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_67,plain,
    ( k2_lattices('#skF_2','#skF_3',k5_lattices('#skF_2')) = k5_lattices('#skF_2')
    | ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2'))
    | ~ v13_lattices('#skF_2')
    | ~ l1_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_61])).

tff(c_72,plain,
    ( k2_lattices('#skF_2','#skF_3',k5_lattices('#skF_2')) = k5_lattices('#skF_2')
    | ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_38,c_67])).

tff(c_73,plain,
    ( k2_lattices('#skF_2','#skF_3',k5_lattices('#skF_2')) = k5_lattices('#skF_2')
    | ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_72])).

tff(c_74,plain,(
    ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_73])).

tff(c_77,plain,
    ( ~ l1_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_74])).

tff(c_80,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_77])).

tff(c_82,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_80])).

tff(c_84,plain,(
    m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_109,plain,(
    ! [A_32,C_33] :
      ( k2_lattices(A_32,k5_lattices(A_32),C_33) = k5_lattices(A_32)
      | ~ m1_subset_1(C_33,u1_struct_0(A_32))
      | ~ m1_subset_1(k5_lattices(A_32),u1_struct_0(A_32))
      | ~ v13_lattices(A_32)
      | ~ l1_lattices(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_117,plain,
    ( k2_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = k5_lattices('#skF_2')
    | ~ m1_subset_1(k5_lattices('#skF_2'),u1_struct_0('#skF_2'))
    | ~ v13_lattices('#skF_2')
    | ~ l1_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_109])).

tff(c_126,plain,
    ( k2_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = k5_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_38,c_84,c_117])).

tff(c_127,plain,(
    k2_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = k5_lattices('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_126])).

tff(c_40,plain,(
    v10_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_155,plain,(
    ! [A_35,B_36,C_37] :
      ( k4_lattices(A_35,B_36,C_37) = k2_lattices(A_35,B_36,C_37)
      | ~ m1_subset_1(C_37,u1_struct_0(A_35))
      | ~ m1_subset_1(B_36,u1_struct_0(A_35))
      | ~ l1_lattices(A_35)
      | ~ v6_lattices(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_163,plain,(
    ! [B_36] :
      ( k4_lattices('#skF_2',B_36,'#skF_3') = k2_lattices('#skF_2',B_36,'#skF_3')
      | ~ m1_subset_1(B_36,u1_struct_0('#skF_2'))
      | ~ l1_lattices('#skF_2')
      | ~ v6_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_34,c_155])).

tff(c_172,plain,(
    ! [B_36] :
      ( k4_lattices('#skF_2',B_36,'#skF_3') = k2_lattices('#skF_2',B_36,'#skF_3')
      | ~ m1_subset_1(B_36,u1_struct_0('#skF_2'))
      | ~ v6_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_163])).

tff(c_173,plain,(
    ! [B_36] :
      ( k4_lattices('#skF_2',B_36,'#skF_3') = k2_lattices('#skF_2',B_36,'#skF_3')
      | ~ m1_subset_1(B_36,u1_struct_0('#skF_2'))
      | ~ v6_lattices('#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_172])).

tff(c_174,plain,(
    ~ v6_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_173])).

tff(c_177,plain,
    ( ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_174])).

tff(c_180,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_40,c_177])).

tff(c_182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_180])).

tff(c_185,plain,(
    ! [B_38] :
      ( k4_lattices('#skF_2',B_38,'#skF_3') = k2_lattices('#skF_2',B_38,'#skF_3')
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_188,plain,(
    k4_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = k2_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_185])).

tff(c_201,plain,(
    k4_lattices('#skF_2',k5_lattices('#skF_2'),'#skF_3') = k5_lattices('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_188])).

tff(c_203,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_201])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:43:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.24  
% 2.12/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.25  %$ m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k2_lattices > #nlpp > u1_struct_0 > k5_lattices > #skF_2 > #skF_3 > #skF_1
% 2.12/1.25  
% 2.12/1.25  %Foreground sorts:
% 2.12/1.25  
% 2.12/1.25  
% 2.12/1.25  %Background operators:
% 2.12/1.25  
% 2.12/1.25  
% 2.12/1.25  %Foreground operators:
% 2.12/1.25  tff(l3_lattices, type, l3_lattices: $i > $o).
% 2.12/1.25  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.12/1.25  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 2.12/1.25  tff(l2_lattices, type, l2_lattices: $i > $o).
% 2.12/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.25  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 2.12/1.25  tff(l1_lattices, type, l1_lattices: $i > $o).
% 2.12/1.25  tff(v4_lattices, type, v4_lattices: $i > $o).
% 2.12/1.25  tff(v6_lattices, type, v6_lattices: $i > $o).
% 2.12/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.12/1.25  tff(v9_lattices, type, v9_lattices: $i > $o).
% 2.12/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.12/1.25  tff(v5_lattices, type, v5_lattices: $i > $o).
% 2.12/1.25  tff(v10_lattices, type, v10_lattices: $i > $o).
% 2.12/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.25  tff(v13_lattices, type, v13_lattices: $i > $o).
% 2.12/1.25  tff(v8_lattices, type, v8_lattices: $i > $o).
% 2.12/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.25  tff(k5_lattices, type, k5_lattices: $i > $i).
% 2.12/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.12/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.12/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.12/1.25  tff(v7_lattices, type, v7_lattices: $i > $o).
% 2.12/1.25  
% 2.12/1.26  tff(f_107, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v13_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k4_lattices(A, k5_lattices(A), B) = k5_lattices(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_lattices)).
% 2.12/1.26  tff(f_79, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 2.12/1.26  tff(f_73, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => m1_subset_1(k5_lattices(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_lattices)).
% 2.12/1.26  tff(f_66, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((B = k5_lattices(A)) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattices)).
% 2.12/1.26  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 2.12/1.26  tff(f_92, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k2_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 2.12/1.26  tff(c_32, plain, (k4_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')!=k5_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.12/1.26  tff(c_42, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.12/1.26  tff(c_36, plain, (l3_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.12/1.26  tff(c_43, plain, (![A_18]: (l1_lattices(A_18) | ~l3_lattices(A_18))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.12/1.26  tff(c_47, plain, (l1_lattices('#skF_2')), inference(resolution, [status(thm)], [c_36, c_43])).
% 2.12/1.26  tff(c_38, plain, (v13_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.12/1.26  tff(c_24, plain, (![A_12]: (m1_subset_1(k5_lattices(A_12), u1_struct_0(A_12)) | ~l1_lattices(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.12/1.26  tff(c_34, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.12/1.26  tff(c_61, plain, (![A_29, C_30]: (k2_lattices(A_29, C_30, k5_lattices(A_29))=k5_lattices(A_29) | ~m1_subset_1(C_30, u1_struct_0(A_29)) | ~m1_subset_1(k5_lattices(A_29), u1_struct_0(A_29)) | ~v13_lattices(A_29) | ~l1_lattices(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.12/1.26  tff(c_67, plain, (k2_lattices('#skF_2', '#skF_3', k5_lattices('#skF_2'))=k5_lattices('#skF_2') | ~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2')) | ~v13_lattices('#skF_2') | ~l1_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_61])).
% 2.12/1.26  tff(c_72, plain, (k2_lattices('#skF_2', '#skF_3', k5_lattices('#skF_2'))=k5_lattices('#skF_2') | ~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_38, c_67])).
% 2.12/1.26  tff(c_73, plain, (k2_lattices('#skF_2', '#skF_3', k5_lattices('#skF_2'))=k5_lattices('#skF_2') | ~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_42, c_72])).
% 2.12/1.26  tff(c_74, plain, (~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_73])).
% 2.12/1.26  tff(c_77, plain, (~l1_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_24, c_74])).
% 2.12/1.26  tff(c_80, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_77])).
% 2.12/1.26  tff(c_82, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_80])).
% 2.12/1.26  tff(c_84, plain, (m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_73])).
% 2.12/1.26  tff(c_109, plain, (![A_32, C_33]: (k2_lattices(A_32, k5_lattices(A_32), C_33)=k5_lattices(A_32) | ~m1_subset_1(C_33, u1_struct_0(A_32)) | ~m1_subset_1(k5_lattices(A_32), u1_struct_0(A_32)) | ~v13_lattices(A_32) | ~l1_lattices(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.12/1.26  tff(c_117, plain, (k2_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')=k5_lattices('#skF_2') | ~m1_subset_1(k5_lattices('#skF_2'), u1_struct_0('#skF_2')) | ~v13_lattices('#skF_2') | ~l1_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_109])).
% 2.12/1.26  tff(c_126, plain, (k2_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')=k5_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_38, c_84, c_117])).
% 2.12/1.26  tff(c_127, plain, (k2_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')=k5_lattices('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_42, c_126])).
% 2.12/1.26  tff(c_40, plain, (v10_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.12/1.26  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.12/1.26  tff(c_155, plain, (![A_35, B_36, C_37]: (k4_lattices(A_35, B_36, C_37)=k2_lattices(A_35, B_36, C_37) | ~m1_subset_1(C_37, u1_struct_0(A_35)) | ~m1_subset_1(B_36, u1_struct_0(A_35)) | ~l1_lattices(A_35) | ~v6_lattices(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.12/1.26  tff(c_163, plain, (![B_36]: (k4_lattices('#skF_2', B_36, '#skF_3')=k2_lattices('#skF_2', B_36, '#skF_3') | ~m1_subset_1(B_36, u1_struct_0('#skF_2')) | ~l1_lattices('#skF_2') | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_155])).
% 2.12/1.26  tff(c_172, plain, (![B_36]: (k4_lattices('#skF_2', B_36, '#skF_3')=k2_lattices('#skF_2', B_36, '#skF_3') | ~m1_subset_1(B_36, u1_struct_0('#skF_2')) | ~v6_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_163])).
% 2.12/1.26  tff(c_173, plain, (![B_36]: (k4_lattices('#skF_2', B_36, '#skF_3')=k2_lattices('#skF_2', B_36, '#skF_3') | ~m1_subset_1(B_36, u1_struct_0('#skF_2')) | ~v6_lattices('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_42, c_172])).
% 2.12/1.26  tff(c_174, plain, (~v6_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_173])).
% 2.12/1.26  tff(c_177, plain, (~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_8, c_174])).
% 2.12/1.26  tff(c_180, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_40, c_177])).
% 2.12/1.26  tff(c_182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_180])).
% 2.12/1.26  tff(c_185, plain, (![B_38]: (k4_lattices('#skF_2', B_38, '#skF_3')=k2_lattices('#skF_2', B_38, '#skF_3') | ~m1_subset_1(B_38, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_173])).
% 2.12/1.26  tff(c_188, plain, (k4_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')=k2_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_84, c_185])).
% 2.12/1.26  tff(c_201, plain, (k4_lattices('#skF_2', k5_lattices('#skF_2'), '#skF_3')=k5_lattices('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_188])).
% 2.12/1.26  tff(c_203, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_201])).
% 2.12/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.26  
% 2.12/1.26  Inference rules
% 2.12/1.26  ----------------------
% 2.12/1.26  #Ref     : 0
% 2.12/1.26  #Sup     : 32
% 2.12/1.26  #Fact    : 0
% 2.12/1.26  #Define  : 0
% 2.12/1.26  #Split   : 2
% 2.12/1.26  #Chain   : 0
% 2.12/1.26  #Close   : 0
% 2.12/1.26  
% 2.12/1.26  Ordering : KBO
% 2.12/1.26  
% 2.12/1.26  Simplification rules
% 2.12/1.26  ----------------------
% 2.12/1.26  #Subsume      : 2
% 2.12/1.26  #Demod        : 25
% 2.12/1.26  #Tautology    : 13
% 2.12/1.26  #SimpNegUnit  : 12
% 2.12/1.26  #BackRed      : 0
% 2.12/1.26  
% 2.12/1.26  #Partial instantiations: 0
% 2.12/1.26  #Strategies tried      : 1
% 2.12/1.26  
% 2.12/1.26  Timing (in seconds)
% 2.12/1.26  ----------------------
% 2.12/1.26  Preprocessing        : 0.30
% 2.12/1.26  Parsing              : 0.15
% 2.12/1.26  CNF conversion       : 0.02
% 2.12/1.26  Main loop            : 0.17
% 2.12/1.26  Inferencing          : 0.07
% 2.12/1.26  Reduction            : 0.05
% 2.12/1.26  Demodulation         : 0.04
% 2.12/1.26  BG Simplification    : 0.01
% 2.12/1.26  Subsumption          : 0.03
% 2.12/1.26  Abstraction          : 0.01
% 2.12/1.26  MUC search           : 0.00
% 2.12/1.26  Cooper               : 0.00
% 2.12/1.26  Total                : 0.50
% 2.12/1.26  Index Insertion      : 0.00
% 2.12/1.26  Index Deletion       : 0.00
% 2.12/1.26  Index Matching       : 0.00
% 2.12/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
