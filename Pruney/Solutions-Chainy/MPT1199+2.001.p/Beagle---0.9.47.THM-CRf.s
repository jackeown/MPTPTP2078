%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:13 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   51 (  98 expanded)
%              Number of leaves         :   18 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :  105 ( 347 expanded)
%              Number of equality atoms :   29 (  58 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_lattices > m1_subset_1 > v4_lattices > v2_struct_0 > l2_lattices > k3_lattices > k1_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k3_lattices,type,(
    k3_lattices: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_lattices,type,(
    k1_lattices: ( $i * $i * $i ) > $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v4_lattices(A)
          & l2_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( ( r1_lattices(A,B,C)
                    & r1_lattices(A,C,B) )
                 => B = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_lattices)).

tff(f_53,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_lattices(A,B,C)
              <=> k1_lattices(A,B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k1_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k3_lattices(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).

tff(c_10,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_24,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_20,plain,(
    l2_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_16,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_12,plain,(
    r1_lattices('#skF_1','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_60,plain,(
    ! [A_23,B_24,C_25] :
      ( k1_lattices(A_23,B_24,C_25) = C_25
      | ~ r1_lattices(A_23,B_24,C_25)
      | ~ m1_subset_1(C_25,u1_struct_0(A_23))
      | ~ m1_subset_1(B_24,u1_struct_0(A_23))
      | ~ l2_lattices(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_62,plain,
    ( k1_lattices('#skF_1','#skF_3','#skF_2') = '#skF_2'
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ l2_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_60])).

tff(c_67,plain,
    ( k1_lattices('#skF_1','#skF_3','#skF_2') = '#skF_2'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_18,c_62])).

tff(c_68,plain,(
    k1_lattices('#skF_1','#skF_3','#skF_2') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_67])).

tff(c_22,plain,(
    v4_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_81,plain,(
    ! [A_26,B_27,C_28] :
      ( k3_lattices(A_26,B_27,C_28) = k1_lattices(A_26,B_27,C_28)
      | ~ m1_subset_1(C_28,u1_struct_0(A_26))
      | ~ m1_subset_1(B_27,u1_struct_0(A_26))
      | ~ l2_lattices(A_26)
      | ~ v4_lattices(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_85,plain,(
    ! [B_27] :
      ( k3_lattices('#skF_1',B_27,'#skF_2') = k1_lattices('#skF_1',B_27,'#skF_2')
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_1'))
      | ~ l2_lattices('#skF_1')
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_18,c_81])).

tff(c_92,plain,(
    ! [B_27] :
      ( k3_lattices('#skF_1',B_27,'#skF_2') = k1_lattices('#skF_1',B_27,'#skF_2')
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_85])).

tff(c_112,plain,(
    ! [B_30] :
      ( k3_lattices('#skF_1',B_30,'#skF_2') = k1_lattices('#skF_1',B_30,'#skF_2')
      | ~ m1_subset_1(B_30,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_92])).

tff(c_115,plain,(
    k3_lattices('#skF_1','#skF_3','#skF_2') = k1_lattices('#skF_1','#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_112])).

tff(c_120,plain,(
    k3_lattices('#skF_1','#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_115])).

tff(c_14,plain,(
    r1_lattices('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_64,plain,
    ( k1_lattices('#skF_1','#skF_2','#skF_3') = '#skF_3'
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l2_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_60])).

tff(c_71,plain,
    ( k1_lattices('#skF_1','#skF_2','#skF_3') = '#skF_3'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_64])).

tff(c_72,plain,(
    k1_lattices('#skF_1','#skF_2','#skF_3') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_71])).

tff(c_83,plain,(
    ! [B_27] :
      ( k3_lattices('#skF_1',B_27,'#skF_3') = k1_lattices('#skF_1',B_27,'#skF_3')
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_1'))
      | ~ l2_lattices('#skF_1')
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_16,c_81])).

tff(c_88,plain,(
    ! [B_27] :
      ( k3_lattices('#skF_1',B_27,'#skF_3') = k1_lattices('#skF_1',B_27,'#skF_3')
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_83])).

tff(c_94,plain,(
    ! [B_29] :
      ( k3_lattices('#skF_1',B_29,'#skF_3') = k1_lattices('#skF_1',B_29,'#skF_3')
      | ~ m1_subset_1(B_29,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_88])).

tff(c_100,plain,(
    k3_lattices('#skF_1','#skF_2','#skF_3') = k1_lattices('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_94])).

tff(c_103,plain,(
    k3_lattices('#skF_1','#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_100])).

tff(c_130,plain,(
    ! [A_31,C_32,B_33] :
      ( k3_lattices(A_31,C_32,B_33) = k3_lattices(A_31,B_33,C_32)
      | ~ m1_subset_1(C_32,u1_struct_0(A_31))
      | ~ m1_subset_1(B_33,u1_struct_0(A_31))
      | ~ l2_lattices(A_31)
      | ~ v4_lattices(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_132,plain,(
    ! [B_33] :
      ( k3_lattices('#skF_1',B_33,'#skF_3') = k3_lattices('#skF_1','#skF_3',B_33)
      | ~ m1_subset_1(B_33,u1_struct_0('#skF_1'))
      | ~ l2_lattices('#skF_1')
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_16,c_130])).

tff(c_137,plain,(
    ! [B_33] :
      ( k3_lattices('#skF_1',B_33,'#skF_3') = k3_lattices('#skF_1','#skF_3',B_33)
      | ~ m1_subset_1(B_33,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_132])).

tff(c_143,plain,(
    ! [B_34] :
      ( k3_lattices('#skF_1',B_34,'#skF_3') = k3_lattices('#skF_1','#skF_3',B_34)
      | ~ m1_subset_1(B_34,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_137])).

tff(c_149,plain,(
    k3_lattices('#skF_1','#skF_2','#skF_3') = k3_lattices('#skF_1','#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_143])).

tff(c_153,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_103,c_149])).

tff(c_155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_153])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:10:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.20  
% 1.85/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.20  %$ r1_lattices > m1_subset_1 > v4_lattices > v2_struct_0 > l2_lattices > k3_lattices > k1_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1
% 1.85/1.20  
% 1.85/1.20  %Foreground sorts:
% 1.85/1.20  
% 1.85/1.20  
% 1.85/1.20  %Background operators:
% 1.85/1.20  
% 1.85/1.20  
% 1.85/1.20  %Foreground operators:
% 1.85/1.20  tff(k3_lattices, type, k3_lattices: ($i * $i * $i) > $i).
% 1.85/1.20  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.85/1.20  tff(l2_lattices, type, l2_lattices: $i > $o).
% 1.85/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.20  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 1.85/1.20  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 1.85/1.20  tff(v4_lattices, type, v4_lattices: $i > $o).
% 1.85/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.85/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.85/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.85/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.20  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.85/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.85/1.20  
% 1.96/1.21  tff(f_86, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((r1_lattices(A, B, C) & r1_lattices(A, C, B)) => (B = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_lattices)).
% 1.96/1.21  tff(f_53, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k1_lattices(A, B, C) = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_lattices)).
% 1.96/1.21  tff(f_66, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 1.96/1.21  tff(f_38, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k3_lattices(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_lattices)).
% 1.96/1.21  tff(c_10, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.96/1.21  tff(c_24, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.96/1.21  tff(c_20, plain, (l2_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.96/1.21  tff(c_16, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.96/1.21  tff(c_18, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.96/1.21  tff(c_12, plain, (r1_lattices('#skF_1', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.96/1.21  tff(c_60, plain, (![A_23, B_24, C_25]: (k1_lattices(A_23, B_24, C_25)=C_25 | ~r1_lattices(A_23, B_24, C_25) | ~m1_subset_1(C_25, u1_struct_0(A_23)) | ~m1_subset_1(B_24, u1_struct_0(A_23)) | ~l2_lattices(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.96/1.21  tff(c_62, plain, (k1_lattices('#skF_1', '#skF_3', '#skF_2')='#skF_2' | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_12, c_60])).
% 1.96/1.21  tff(c_67, plain, (k1_lattices('#skF_1', '#skF_3', '#skF_2')='#skF_2' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_18, c_62])).
% 1.96/1.21  tff(c_68, plain, (k1_lattices('#skF_1', '#skF_3', '#skF_2')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_24, c_67])).
% 1.96/1.21  tff(c_22, plain, (v4_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.96/1.21  tff(c_81, plain, (![A_26, B_27, C_28]: (k3_lattices(A_26, B_27, C_28)=k1_lattices(A_26, B_27, C_28) | ~m1_subset_1(C_28, u1_struct_0(A_26)) | ~m1_subset_1(B_27, u1_struct_0(A_26)) | ~l2_lattices(A_26) | ~v4_lattices(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.96/1.21  tff(c_85, plain, (![B_27]: (k3_lattices('#skF_1', B_27, '#skF_2')=k1_lattices('#skF_1', B_27, '#skF_2') | ~m1_subset_1(B_27, u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_81])).
% 1.96/1.21  tff(c_92, plain, (![B_27]: (k3_lattices('#skF_1', B_27, '#skF_2')=k1_lattices('#skF_1', B_27, '#skF_2') | ~m1_subset_1(B_27, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_85])).
% 1.96/1.21  tff(c_112, plain, (![B_30]: (k3_lattices('#skF_1', B_30, '#skF_2')=k1_lattices('#skF_1', B_30, '#skF_2') | ~m1_subset_1(B_30, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_24, c_92])).
% 1.96/1.21  tff(c_115, plain, (k3_lattices('#skF_1', '#skF_3', '#skF_2')=k1_lattices('#skF_1', '#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_16, c_112])).
% 1.96/1.21  tff(c_120, plain, (k3_lattices('#skF_1', '#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_115])).
% 1.96/1.21  tff(c_14, plain, (r1_lattices('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.96/1.21  tff(c_64, plain, (k1_lattices('#skF_1', '#skF_2', '#skF_3')='#skF_3' | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_14, c_60])).
% 1.96/1.21  tff(c_71, plain, (k1_lattices('#skF_1', '#skF_2', '#skF_3')='#skF_3' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_16, c_64])).
% 1.96/1.21  tff(c_72, plain, (k1_lattices('#skF_1', '#skF_2', '#skF_3')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_24, c_71])).
% 1.96/1.21  tff(c_83, plain, (![B_27]: (k3_lattices('#skF_1', B_27, '#skF_3')=k1_lattices('#skF_1', B_27, '#skF_3') | ~m1_subset_1(B_27, u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_16, c_81])).
% 1.96/1.21  tff(c_88, plain, (![B_27]: (k3_lattices('#skF_1', B_27, '#skF_3')=k1_lattices('#skF_1', B_27, '#skF_3') | ~m1_subset_1(B_27, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_83])).
% 1.96/1.21  tff(c_94, plain, (![B_29]: (k3_lattices('#skF_1', B_29, '#skF_3')=k1_lattices('#skF_1', B_29, '#skF_3') | ~m1_subset_1(B_29, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_24, c_88])).
% 1.96/1.21  tff(c_100, plain, (k3_lattices('#skF_1', '#skF_2', '#skF_3')=k1_lattices('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_18, c_94])).
% 1.96/1.21  tff(c_103, plain, (k3_lattices('#skF_1', '#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_100])).
% 1.96/1.21  tff(c_130, plain, (![A_31, C_32, B_33]: (k3_lattices(A_31, C_32, B_33)=k3_lattices(A_31, B_33, C_32) | ~m1_subset_1(C_32, u1_struct_0(A_31)) | ~m1_subset_1(B_33, u1_struct_0(A_31)) | ~l2_lattices(A_31) | ~v4_lattices(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.96/1.21  tff(c_132, plain, (![B_33]: (k3_lattices('#skF_1', B_33, '#skF_3')=k3_lattices('#skF_1', '#skF_3', B_33) | ~m1_subset_1(B_33, u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_16, c_130])).
% 1.96/1.21  tff(c_137, plain, (![B_33]: (k3_lattices('#skF_1', B_33, '#skF_3')=k3_lattices('#skF_1', '#skF_3', B_33) | ~m1_subset_1(B_33, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_132])).
% 1.96/1.21  tff(c_143, plain, (![B_34]: (k3_lattices('#skF_1', B_34, '#skF_3')=k3_lattices('#skF_1', '#skF_3', B_34) | ~m1_subset_1(B_34, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_24, c_137])).
% 1.96/1.21  tff(c_149, plain, (k3_lattices('#skF_1', '#skF_2', '#skF_3')=k3_lattices('#skF_1', '#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_18, c_143])).
% 1.96/1.21  tff(c_153, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_120, c_103, c_149])).
% 1.96/1.21  tff(c_155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_153])).
% 1.96/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.21  
% 1.96/1.21  Inference rules
% 1.96/1.21  ----------------------
% 1.96/1.21  #Ref     : 0
% 1.96/1.21  #Sup     : 30
% 1.96/1.21  #Fact    : 0
% 1.96/1.21  #Define  : 0
% 1.96/1.21  #Split   : 2
% 1.96/1.21  #Chain   : 0
% 1.96/1.21  #Close   : 0
% 1.96/1.21  
% 1.96/1.21  Ordering : KBO
% 1.96/1.21  
% 1.96/1.21  Simplification rules
% 1.96/1.21  ----------------------
% 1.96/1.21  #Subsume      : 0
% 1.96/1.21  #Demod        : 24
% 1.96/1.21  #Tautology    : 15
% 1.96/1.21  #SimpNegUnit  : 9
% 1.96/1.21  #BackRed      : 0
% 1.96/1.21  
% 1.96/1.21  #Partial instantiations: 0
% 1.96/1.21  #Strategies tried      : 1
% 1.96/1.21  
% 1.96/1.21  Timing (in seconds)
% 1.96/1.21  ----------------------
% 1.96/1.22  Preprocessing        : 0.30
% 1.96/1.22  Parsing              : 0.16
% 1.96/1.22  CNF conversion       : 0.02
% 1.96/1.22  Main loop            : 0.14
% 1.96/1.22  Inferencing          : 0.05
% 1.96/1.22  Reduction            : 0.05
% 1.96/1.22  Demodulation         : 0.04
% 1.96/1.22  BG Simplification    : 0.01
% 1.96/1.22  Subsumption          : 0.02
% 1.96/1.22  Abstraction          : 0.01
% 1.96/1.22  MUC search           : 0.00
% 1.96/1.22  Cooper               : 0.00
% 1.96/1.22  Total                : 0.47
% 1.96/1.22  Index Insertion      : 0.00
% 1.96/1.22  Index Deletion       : 0.00
% 1.96/1.22  Index Matching       : 0.00
% 1.96/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
