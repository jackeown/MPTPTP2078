%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:08 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 111 expanded)
%              Number of leaves         :   22 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :   79 ( 220 expanded)
%              Number of equality atoms :   20 (  67 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_waybel_0 > l1_waybel_0 > v1_orders_2 > l1_orders_2 > k3_relset_1 > u1_waybel_0 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k7_lattice3 > k3_waybel_9 > k3_struct_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v6_waybel_0,type,(
    v6_waybel_0: ( $i * $i ) > $o )).

tff(k3_waybel_9,type,(
    k3_waybel_9: $i > $i )).

tff(k3_relset_1,type,(
    k3_relset_1: ( $i * $i * $i ) > $i )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff(k7_lattice3,type,(
    k7_lattice3: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(u1_waybel_0,type,(
    u1_waybel_0: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k3_struct_0,type,(
    k3_struct_0: $i > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => g1_orders_2(u1_struct_0(k7_lattice3(A)),u1_orders_2(k7_lattice3(A))) = g1_orders_2(u1_struct_0(k3_waybel_9(A)),u1_orders_2(k3_waybel_9(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_waybel_9)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(k7_lattice3(A))
        & l1_orders_2(k7_lattice3(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattice3)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v6_waybel_0(k3_waybel_9(A),A)
        & l1_waybel_0(k3_waybel_9(A),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_waybel_9)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( ( v6_waybel_0(B,A)
            & l1_waybel_0(B,A) )
         => ( B = k3_waybel_9(A)
          <=> ( u1_struct_0(B) = u1_struct_0(A)
              & u1_orders_2(B) = k3_relset_1(u1_struct_0(A),u1_struct_0(A),u1_orders_2(A))
              & u1_waybel_0(A,B) = k3_struct_0(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_waybel_9)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k7_lattice3(A) = g1_orders_2(u1_struct_0(A),k3_relset_1(u1_struct_0(A),u1_struct_0(A),u1_orders_2(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_lattice3)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(A)
       => A = g1_orders_2(u1_struct_0(A),u1_orders_2(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

tff(c_24,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8,plain,(
    ! [A_3] :
      ( v1_orders_2(k7_lattice3(A_3))
      | ~ l1_orders_2(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_7] :
      ( l1_waybel_0(k3_waybel_9(A_7),A_7)
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_20,plain,(
    ! [A_7] :
      ( v6_waybel_0(k3_waybel_9(A_7),A_7)
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_137,plain,(
    ! [A_21] :
      ( k3_relset_1(u1_struct_0(A_21),u1_struct_0(A_21),u1_orders_2(A_21)) = u1_orders_2(k3_waybel_9(A_21))
      | ~ l1_waybel_0(k3_waybel_9(A_21),A_21)
      | ~ v6_waybel_0(k3_waybel_9(A_21),A_21)
      | ~ l1_orders_2(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [A_2] :
      ( g1_orders_2(u1_struct_0(A_2),k3_relset_1(u1_struct_0(A_2),u1_struct_0(A_2),u1_orders_2(A_2))) = k7_lattice3(A_2)
      | ~ l1_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_155,plain,(
    ! [A_22] :
      ( g1_orders_2(u1_struct_0(A_22),u1_orders_2(k3_waybel_9(A_22))) = k7_lattice3(A_22)
      | ~ l1_orders_2(A_22)
      | ~ l1_waybel_0(k3_waybel_9(A_22),A_22)
      | ~ v6_waybel_0(k3_waybel_9(A_22),A_22)
      | ~ l1_orders_2(A_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_4])).

tff(c_50,plain,(
    ! [A_14] :
      ( u1_struct_0(k3_waybel_9(A_14)) = u1_struct_0(A_14)
      | ~ l1_waybel_0(k3_waybel_9(A_14),A_14)
      | ~ v6_waybel_0(k3_waybel_9(A_14),A_14)
      | ~ l1_orders_2(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_65,plain,(
    ! [A_15] :
      ( u1_struct_0(k3_waybel_9(A_15)) = u1_struct_0(A_15)
      | ~ l1_waybel_0(k3_waybel_9(A_15),A_15)
      | ~ l1_orders_2(A_15) ) ),
    inference(resolution,[status(thm)],[c_20,c_50])).

tff(c_69,plain,(
    ! [A_7] :
      ( u1_struct_0(k3_waybel_9(A_7)) = u1_struct_0(A_7)
      | ~ l1_orders_2(A_7) ) ),
    inference(resolution,[status(thm)],[c_18,c_65])).

tff(c_6,plain,(
    ! [A_3] :
      ( l1_orders_2(k7_lattice3(A_3))
      | ~ l1_orders_2(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_orders_2(u1_struct_0(A_1),u1_orders_2(A_1)) = A_1
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    g1_orders_2(u1_struct_0(k7_lattice3('#skF_1')),u1_orders_2(k7_lattice3('#skF_1'))) != g1_orders_2(u1_struct_0(k3_waybel_9('#skF_1')),u1_orders_2(k3_waybel_9('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_49,plain,
    ( g1_orders_2(u1_struct_0(k3_waybel_9('#skF_1')),u1_orders_2(k3_waybel_9('#skF_1'))) != k7_lattice3('#skF_1')
    | ~ v1_orders_2(k7_lattice3('#skF_1'))
    | ~ l1_orders_2(k7_lattice3('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_22])).

tff(c_55,plain,(
    ~ l1_orders_2(k7_lattice3('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_49])).

tff(c_58,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_55])).

tff(c_62,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_58])).

tff(c_63,plain,
    ( ~ v1_orders_2(k7_lattice3('#skF_1'))
    | g1_orders_2(u1_struct_0(k3_waybel_9('#skF_1')),u1_orders_2(k3_waybel_9('#skF_1'))) != k7_lattice3('#skF_1') ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_91,plain,(
    g1_orders_2(u1_struct_0(k3_waybel_9('#skF_1')),u1_orders_2(k3_waybel_9('#skF_1'))) != k7_lattice3('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_99,plain,
    ( g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2(k3_waybel_9('#skF_1'))) != k7_lattice3('#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_91])).

tff(c_104,plain,(
    g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2(k3_waybel_9('#skF_1'))) != k7_lattice3('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_99])).

tff(c_164,plain,
    ( ~ l1_waybel_0(k3_waybel_9('#skF_1'),'#skF_1')
    | ~ v6_waybel_0(k3_waybel_9('#skF_1'),'#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_104])).

tff(c_177,plain,
    ( ~ l1_waybel_0(k3_waybel_9('#skF_1'),'#skF_1')
    | ~ v6_waybel_0(k3_waybel_9('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_164])).

tff(c_186,plain,(
    ~ v6_waybel_0(k3_waybel_9('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_189,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_186])).

tff(c_193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_189])).

tff(c_194,plain,(
    ~ l1_waybel_0(k3_waybel_9('#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_198,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_194])).

tff(c_202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_198])).

tff(c_203,plain,(
    ~ v1_orders_2(k7_lattice3('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_207,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_203])).

tff(c_211,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_207])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:19:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.30  
% 1.99/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.31  %$ v6_waybel_0 > l1_waybel_0 > v1_orders_2 > l1_orders_2 > k3_relset_1 > u1_waybel_0 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k7_lattice3 > k3_waybel_9 > k3_struct_0 > #skF_1
% 1.99/1.31  
% 1.99/1.31  %Foreground sorts:
% 1.99/1.31  
% 1.99/1.31  
% 1.99/1.31  %Background operators:
% 1.99/1.31  
% 1.99/1.31  
% 1.99/1.31  %Foreground operators:
% 1.99/1.31  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 1.99/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.31  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 1.99/1.31  tff(k3_waybel_9, type, k3_waybel_9: $i > $i).
% 1.99/1.31  tff(k3_relset_1, type, k3_relset_1: ($i * $i * $i) > $i).
% 1.99/1.31  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 1.99/1.31  tff(k7_lattice3, type, k7_lattice3: $i > $i).
% 1.99/1.31  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.31  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.99/1.31  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 1.99/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.31  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 1.99/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.31  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 1.99/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.99/1.31  tff(k3_struct_0, type, k3_struct_0: $i > $i).
% 1.99/1.31  
% 1.99/1.32  tff(f_67, negated_conjecture, ~(![A]: (l1_orders_2(A) => (g1_orders_2(u1_struct_0(k7_lattice3(A)), u1_orders_2(k7_lattice3(A))) = g1_orders_2(u1_struct_0(k3_waybel_9(A)), u1_orders_2(k3_waybel_9(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_waybel_9)).
% 1.99/1.32  tff(f_41, axiom, (![A]: (l1_orders_2(A) => (v1_orders_2(k7_lattice3(A)) & l1_orders_2(k7_lattice3(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_lattice3)).
% 1.99/1.32  tff(f_62, axiom, (![A]: (l1_orders_2(A) => (v6_waybel_0(k3_waybel_9(A), A) & l1_waybel_0(k3_waybel_9(A), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_waybel_9)).
% 1.99/1.32  tff(f_56, axiom, (![A]: (l1_orders_2(A) => (![B]: ((v6_waybel_0(B, A) & l1_waybel_0(B, A)) => ((B = k3_waybel_9(A)) <=> (((u1_struct_0(B) = u1_struct_0(A)) & (u1_orders_2(B) = k3_relset_1(u1_struct_0(A), u1_struct_0(A), u1_orders_2(A)))) & (u1_waybel_0(A, B) = k3_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_waybel_9)).
% 1.99/1.32  tff(f_35, axiom, (![A]: (l1_orders_2(A) => (k7_lattice3(A) = g1_orders_2(u1_struct_0(A), k3_relset_1(u1_struct_0(A), u1_struct_0(A), u1_orders_2(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_lattice3)).
% 1.99/1.32  tff(f_31, axiom, (![A]: (l1_orders_2(A) => (v1_orders_2(A) => (A = g1_orders_2(u1_struct_0(A), u1_orders_2(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_orders_2)).
% 1.99/1.32  tff(c_24, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.99/1.32  tff(c_8, plain, (![A_3]: (v1_orders_2(k7_lattice3(A_3)) | ~l1_orders_2(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.99/1.32  tff(c_18, plain, (![A_7]: (l1_waybel_0(k3_waybel_9(A_7), A_7) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.99/1.32  tff(c_20, plain, (![A_7]: (v6_waybel_0(k3_waybel_9(A_7), A_7) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.99/1.32  tff(c_137, plain, (![A_21]: (k3_relset_1(u1_struct_0(A_21), u1_struct_0(A_21), u1_orders_2(A_21))=u1_orders_2(k3_waybel_9(A_21)) | ~l1_waybel_0(k3_waybel_9(A_21), A_21) | ~v6_waybel_0(k3_waybel_9(A_21), A_21) | ~l1_orders_2(A_21))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.99/1.32  tff(c_4, plain, (![A_2]: (g1_orders_2(u1_struct_0(A_2), k3_relset_1(u1_struct_0(A_2), u1_struct_0(A_2), u1_orders_2(A_2)))=k7_lattice3(A_2) | ~l1_orders_2(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.99/1.32  tff(c_155, plain, (![A_22]: (g1_orders_2(u1_struct_0(A_22), u1_orders_2(k3_waybel_9(A_22)))=k7_lattice3(A_22) | ~l1_orders_2(A_22) | ~l1_waybel_0(k3_waybel_9(A_22), A_22) | ~v6_waybel_0(k3_waybel_9(A_22), A_22) | ~l1_orders_2(A_22))), inference(superposition, [status(thm), theory('equality')], [c_137, c_4])).
% 1.99/1.32  tff(c_50, plain, (![A_14]: (u1_struct_0(k3_waybel_9(A_14))=u1_struct_0(A_14) | ~l1_waybel_0(k3_waybel_9(A_14), A_14) | ~v6_waybel_0(k3_waybel_9(A_14), A_14) | ~l1_orders_2(A_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.99/1.32  tff(c_65, plain, (![A_15]: (u1_struct_0(k3_waybel_9(A_15))=u1_struct_0(A_15) | ~l1_waybel_0(k3_waybel_9(A_15), A_15) | ~l1_orders_2(A_15))), inference(resolution, [status(thm)], [c_20, c_50])).
% 1.99/1.32  tff(c_69, plain, (![A_7]: (u1_struct_0(k3_waybel_9(A_7))=u1_struct_0(A_7) | ~l1_orders_2(A_7))), inference(resolution, [status(thm)], [c_18, c_65])).
% 1.99/1.32  tff(c_6, plain, (![A_3]: (l1_orders_2(k7_lattice3(A_3)) | ~l1_orders_2(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.99/1.32  tff(c_2, plain, (![A_1]: (g1_orders_2(u1_struct_0(A_1), u1_orders_2(A_1))=A_1 | ~v1_orders_2(A_1) | ~l1_orders_2(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.99/1.32  tff(c_22, plain, (g1_orders_2(u1_struct_0(k7_lattice3('#skF_1')), u1_orders_2(k7_lattice3('#skF_1')))!=g1_orders_2(u1_struct_0(k3_waybel_9('#skF_1')), u1_orders_2(k3_waybel_9('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.99/1.32  tff(c_49, plain, (g1_orders_2(u1_struct_0(k3_waybel_9('#skF_1')), u1_orders_2(k3_waybel_9('#skF_1')))!=k7_lattice3('#skF_1') | ~v1_orders_2(k7_lattice3('#skF_1')) | ~l1_orders_2(k7_lattice3('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_22])).
% 1.99/1.32  tff(c_55, plain, (~l1_orders_2(k7_lattice3('#skF_1'))), inference(splitLeft, [status(thm)], [c_49])).
% 1.99/1.32  tff(c_58, plain, (~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_6, c_55])).
% 1.99/1.32  tff(c_62, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_58])).
% 1.99/1.32  tff(c_63, plain, (~v1_orders_2(k7_lattice3('#skF_1')) | g1_orders_2(u1_struct_0(k3_waybel_9('#skF_1')), u1_orders_2(k3_waybel_9('#skF_1')))!=k7_lattice3('#skF_1')), inference(splitRight, [status(thm)], [c_49])).
% 1.99/1.32  tff(c_91, plain, (g1_orders_2(u1_struct_0(k3_waybel_9('#skF_1')), u1_orders_2(k3_waybel_9('#skF_1')))!=k7_lattice3('#skF_1')), inference(splitLeft, [status(thm)], [c_63])).
% 1.99/1.32  tff(c_99, plain, (g1_orders_2(u1_struct_0('#skF_1'), u1_orders_2(k3_waybel_9('#skF_1')))!=k7_lattice3('#skF_1') | ~l1_orders_2('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_69, c_91])).
% 1.99/1.32  tff(c_104, plain, (g1_orders_2(u1_struct_0('#skF_1'), u1_orders_2(k3_waybel_9('#skF_1')))!=k7_lattice3('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_99])).
% 1.99/1.32  tff(c_164, plain, (~l1_waybel_0(k3_waybel_9('#skF_1'), '#skF_1') | ~v6_waybel_0(k3_waybel_9('#skF_1'), '#skF_1') | ~l1_orders_2('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_155, c_104])).
% 1.99/1.32  tff(c_177, plain, (~l1_waybel_0(k3_waybel_9('#skF_1'), '#skF_1') | ~v6_waybel_0(k3_waybel_9('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_164])).
% 1.99/1.32  tff(c_186, plain, (~v6_waybel_0(k3_waybel_9('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_177])).
% 1.99/1.32  tff(c_189, plain, (~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_20, c_186])).
% 1.99/1.32  tff(c_193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_189])).
% 1.99/1.32  tff(c_194, plain, (~l1_waybel_0(k3_waybel_9('#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_177])).
% 1.99/1.32  tff(c_198, plain, (~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_18, c_194])).
% 1.99/1.32  tff(c_202, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_198])).
% 1.99/1.32  tff(c_203, plain, (~v1_orders_2(k7_lattice3('#skF_1'))), inference(splitRight, [status(thm)], [c_63])).
% 1.99/1.32  tff(c_207, plain, (~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_8, c_203])).
% 1.99/1.32  tff(c_211, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_207])).
% 1.99/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.32  
% 1.99/1.32  Inference rules
% 1.99/1.32  ----------------------
% 1.99/1.32  #Ref     : 0
% 1.99/1.32  #Sup     : 41
% 1.99/1.32  #Fact    : 0
% 1.99/1.32  #Define  : 0
% 1.99/1.32  #Split   : 4
% 1.99/1.32  #Chain   : 0
% 1.99/1.32  #Close   : 0
% 1.99/1.32  
% 1.99/1.32  Ordering : KBO
% 1.99/1.32  
% 1.99/1.32  Simplification rules
% 1.99/1.32  ----------------------
% 1.99/1.32  #Subsume      : 5
% 1.99/1.32  #Demod        : 7
% 1.99/1.32  #Tautology    : 14
% 1.99/1.32  #SimpNegUnit  : 0
% 1.99/1.32  #BackRed      : 0
% 1.99/1.32  
% 1.99/1.32  #Partial instantiations: 0
% 1.99/1.32  #Strategies tried      : 1
% 1.99/1.32  
% 1.99/1.32  Timing (in seconds)
% 1.99/1.32  ----------------------
% 1.99/1.32  Preprocessing        : 0.33
% 1.99/1.32  Parsing              : 0.17
% 1.99/1.32  CNF conversion       : 0.02
% 1.99/1.32  Main loop            : 0.17
% 1.99/1.32  Inferencing          : 0.07
% 1.99/1.32  Reduction            : 0.04
% 1.99/1.32  Demodulation         : 0.03
% 1.99/1.32  BG Simplification    : 0.02
% 1.99/1.32  Subsumption          : 0.03
% 1.99/1.32  Abstraction          : 0.01
% 1.99/1.32  MUC search           : 0.00
% 1.99/1.32  Cooper               : 0.00
% 1.99/1.32  Total                : 0.53
% 1.99/1.32  Index Insertion      : 0.00
% 1.99/1.32  Index Deletion       : 0.00
% 1.99/1.32  Index Matching       : 0.00
% 1.99/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
