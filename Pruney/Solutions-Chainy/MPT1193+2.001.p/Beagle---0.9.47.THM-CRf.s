%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:11 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   50 (  76 expanded)
%              Number of leaves         :   24 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :   92 ( 214 expanded)
%              Number of equality atoms :   21 (  37 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > v9_lattices > v8_lattices > v6_lattices > v2_struct_0 > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4

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

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v6_lattices(A)
          & v8_lattices(A)
          & v9_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => k4_lattices(A,B,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_lattices)).

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k1_lattices(A,B,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_lattices)).

tff(f_40,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( v9_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k2_lattices(A,B,k1_lattices(A,B,C)) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).

tff(f_46,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k2_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

tff(c_18,plain,(
    k4_lattices('#skF_3','#skF_4','#skF_4') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_28,plain,(
    v6_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_26,plain,(
    v8_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_24,plain,(
    v9_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_22,plain,(
    l3_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_20,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_44,plain,(
    ! [A_25,B_26] :
      ( k1_lattices(A_25,B_26,B_26) = B_26
      | ~ m1_subset_1(B_26,u1_struct_0(A_25))
      | ~ l3_lattices(A_25)
      | ~ v9_lattices(A_25)
      | ~ v8_lattices(A_25)
      | ~ v6_lattices(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_50,plain,
    ( k1_lattices('#skF_3','#skF_4','#skF_4') = '#skF_4'
    | ~ l3_lattices('#skF_3')
    | ~ v9_lattices('#skF_3')
    | ~ v8_lattices('#skF_3')
    | ~ v6_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_44])).

tff(c_55,plain,
    ( k1_lattices('#skF_3','#skF_4','#skF_4') = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_22,c_50])).

tff(c_56,plain,(
    k1_lattices('#skF_3','#skF_4','#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_55])).

tff(c_57,plain,(
    ! [A_27,B_28,C_29] :
      ( k2_lattices(A_27,B_28,k1_lattices(A_27,B_28,C_29)) = B_28
      | ~ m1_subset_1(C_29,u1_struct_0(A_27))
      | ~ m1_subset_1(B_28,u1_struct_0(A_27))
      | ~ v9_lattices(A_27)
      | ~ l3_lattices(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_63,plain,(
    ! [B_28] :
      ( k2_lattices('#skF_3',B_28,k1_lattices('#skF_3',B_28,'#skF_4')) = B_28
      | ~ m1_subset_1(B_28,u1_struct_0('#skF_3'))
      | ~ v9_lattices('#skF_3')
      | ~ l3_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_57])).

tff(c_68,plain,(
    ! [B_28] :
      ( k2_lattices('#skF_3',B_28,k1_lattices('#skF_3',B_28,'#skF_4')) = B_28
      | ~ m1_subset_1(B_28,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_63])).

tff(c_74,plain,(
    ! [B_30] :
      ( k2_lattices('#skF_3',B_30,k1_lattices('#skF_3',B_30,'#skF_4')) = B_30
      | ~ m1_subset_1(B_30,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_68])).

tff(c_82,plain,(
    k2_lattices('#skF_3','#skF_4',k1_lattices('#skF_3','#skF_4','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_20,c_74])).

tff(c_92,plain,(
    k2_lattices('#skF_3','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_82])).

tff(c_31,plain,(
    ! [A_20] :
      ( l1_lattices(A_20)
      | ~ l3_lattices(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_35,plain,(
    l1_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_31])).

tff(c_97,plain,(
    ! [A_31,B_32,C_33] :
      ( k4_lattices(A_31,B_32,C_33) = k2_lattices(A_31,B_32,C_33)
      | ~ m1_subset_1(C_33,u1_struct_0(A_31))
      | ~ m1_subset_1(B_32,u1_struct_0(A_31))
      | ~ l1_lattices(A_31)
      | ~ v6_lattices(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_103,plain,(
    ! [B_32] :
      ( k4_lattices('#skF_3',B_32,'#skF_4') = k2_lattices('#skF_3',B_32,'#skF_4')
      | ~ m1_subset_1(B_32,u1_struct_0('#skF_3'))
      | ~ l1_lattices('#skF_3')
      | ~ v6_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_97])).

tff(c_108,plain,(
    ! [B_32] :
      ( k4_lattices('#skF_3',B_32,'#skF_4') = k2_lattices('#skF_3',B_32,'#skF_4')
      | ~ m1_subset_1(B_32,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_35,c_103])).

tff(c_110,plain,(
    ! [B_34] :
      ( k4_lattices('#skF_3',B_34,'#skF_4') = k2_lattices('#skF_3',B_34,'#skF_4')
      | ~ m1_subset_1(B_34,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_108])).

tff(c_121,plain,(
    k4_lattices('#skF_3','#skF_4','#skF_4') = k2_lattices('#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_110])).

tff(c_131,plain,(
    k4_lattices('#skF_3','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_121])).

tff(c_133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_131])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:38:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.29  
% 1.98/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.29  %$ m1_subset_1 > v9_lattices > v8_lattices > v6_lattices > v2_struct_0 > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 1.98/1.29  
% 1.98/1.29  %Foreground sorts:
% 1.98/1.29  
% 1.98/1.29  
% 1.98/1.29  %Background operators:
% 1.98/1.29  
% 1.98/1.29  
% 1.98/1.29  %Foreground operators:
% 1.98/1.29  tff(l3_lattices, type, l3_lattices: $i > $o).
% 1.98/1.29  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.98/1.29  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 1.98/1.29  tff(l2_lattices, type, l2_lattices: $i > $o).
% 1.98/1.29  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.98/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.29  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 1.98/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.98/1.29  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 1.98/1.29  tff(l1_lattices, type, l1_lattices: $i > $o).
% 1.98/1.29  tff(v6_lattices, type, v6_lattices: $i > $o).
% 1.98/1.29  tff(v9_lattices, type, v9_lattices: $i > $o).
% 1.98/1.29  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.29  tff('#skF_4', type, '#skF_4': $i).
% 1.98/1.29  tff(v8_lattices, type, v8_lattices: $i > $o).
% 1.98/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.98/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.29  
% 1.98/1.30  tff(f_92, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k4_lattices(A, B, B) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_lattices)).
% 1.98/1.30  tff(f_75, axiom, (![A]: (((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k1_lattices(A, B, B) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_lattices)).
% 1.98/1.30  tff(f_40, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v9_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k2_lattices(A, B, k1_lattices(A, B, C)) = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattices)).
% 1.98/1.30  tff(f_46, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 1.98/1.30  tff(f_59, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k2_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 1.98/1.30  tff(c_18, plain, (k4_lattices('#skF_3', '#skF_4', '#skF_4')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_92])).
% 1.98/1.30  tff(c_30, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 1.98/1.30  tff(c_28, plain, (v6_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 1.98/1.30  tff(c_26, plain, (v8_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 1.98/1.30  tff(c_24, plain, (v9_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 1.98/1.30  tff(c_22, plain, (l3_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 1.98/1.30  tff(c_20, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 1.98/1.30  tff(c_44, plain, (![A_25, B_26]: (k1_lattices(A_25, B_26, B_26)=B_26 | ~m1_subset_1(B_26, u1_struct_0(A_25)) | ~l3_lattices(A_25) | ~v9_lattices(A_25) | ~v8_lattices(A_25) | ~v6_lattices(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.98/1.30  tff(c_50, plain, (k1_lattices('#skF_3', '#skF_4', '#skF_4')='#skF_4' | ~l3_lattices('#skF_3') | ~v9_lattices('#skF_3') | ~v8_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_20, c_44])).
% 1.98/1.30  tff(c_55, plain, (k1_lattices('#skF_3', '#skF_4', '#skF_4')='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_22, c_50])).
% 1.98/1.30  tff(c_56, plain, (k1_lattices('#skF_3', '#skF_4', '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_30, c_55])).
% 1.98/1.30  tff(c_57, plain, (![A_27, B_28, C_29]: (k2_lattices(A_27, B_28, k1_lattices(A_27, B_28, C_29))=B_28 | ~m1_subset_1(C_29, u1_struct_0(A_27)) | ~m1_subset_1(B_28, u1_struct_0(A_27)) | ~v9_lattices(A_27) | ~l3_lattices(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.98/1.30  tff(c_63, plain, (![B_28]: (k2_lattices('#skF_3', B_28, k1_lattices('#skF_3', B_28, '#skF_4'))=B_28 | ~m1_subset_1(B_28, u1_struct_0('#skF_3')) | ~v9_lattices('#skF_3') | ~l3_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_57])).
% 1.98/1.30  tff(c_68, plain, (![B_28]: (k2_lattices('#skF_3', B_28, k1_lattices('#skF_3', B_28, '#skF_4'))=B_28 | ~m1_subset_1(B_28, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_63])).
% 1.98/1.30  tff(c_74, plain, (![B_30]: (k2_lattices('#skF_3', B_30, k1_lattices('#skF_3', B_30, '#skF_4'))=B_30 | ~m1_subset_1(B_30, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_30, c_68])).
% 1.98/1.30  tff(c_82, plain, (k2_lattices('#skF_3', '#skF_4', k1_lattices('#skF_3', '#skF_4', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_20, c_74])).
% 1.98/1.30  tff(c_92, plain, (k2_lattices('#skF_3', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_82])).
% 1.98/1.30  tff(c_31, plain, (![A_20]: (l1_lattices(A_20) | ~l3_lattices(A_20))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.98/1.30  tff(c_35, plain, (l1_lattices('#skF_3')), inference(resolution, [status(thm)], [c_22, c_31])).
% 1.98/1.30  tff(c_97, plain, (![A_31, B_32, C_33]: (k4_lattices(A_31, B_32, C_33)=k2_lattices(A_31, B_32, C_33) | ~m1_subset_1(C_33, u1_struct_0(A_31)) | ~m1_subset_1(B_32, u1_struct_0(A_31)) | ~l1_lattices(A_31) | ~v6_lattices(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.98/1.30  tff(c_103, plain, (![B_32]: (k4_lattices('#skF_3', B_32, '#skF_4')=k2_lattices('#skF_3', B_32, '#skF_4') | ~m1_subset_1(B_32, u1_struct_0('#skF_3')) | ~l1_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_97])).
% 1.98/1.30  tff(c_108, plain, (![B_32]: (k4_lattices('#skF_3', B_32, '#skF_4')=k2_lattices('#skF_3', B_32, '#skF_4') | ~m1_subset_1(B_32, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_35, c_103])).
% 1.98/1.30  tff(c_110, plain, (![B_34]: (k4_lattices('#skF_3', B_34, '#skF_4')=k2_lattices('#skF_3', B_34, '#skF_4') | ~m1_subset_1(B_34, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_30, c_108])).
% 1.98/1.30  tff(c_121, plain, (k4_lattices('#skF_3', '#skF_4', '#skF_4')=k2_lattices('#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_20, c_110])).
% 1.98/1.30  tff(c_131, plain, (k4_lattices('#skF_3', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_121])).
% 1.98/1.30  tff(c_133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_131])).
% 1.98/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.30  
% 1.98/1.30  Inference rules
% 1.98/1.30  ----------------------
% 1.98/1.30  #Ref     : 0
% 1.98/1.30  #Sup     : 21
% 1.98/1.30  #Fact    : 0
% 1.98/1.30  #Define  : 0
% 1.98/1.30  #Split   : 0
% 1.98/1.30  #Chain   : 0
% 1.98/1.30  #Close   : 0
% 1.98/1.30  
% 1.98/1.30  Ordering : KBO
% 1.98/1.30  
% 1.98/1.30  Simplification rules
% 1.98/1.30  ----------------------
% 1.98/1.30  #Subsume      : 0
% 1.98/1.30  #Demod        : 18
% 1.98/1.30  #Tautology    : 12
% 1.98/1.30  #SimpNegUnit  : 8
% 1.98/1.30  #BackRed      : 0
% 1.98/1.30  
% 1.98/1.30  #Partial instantiations: 0
% 1.98/1.30  #Strategies tried      : 1
% 1.98/1.30  
% 1.98/1.30  Timing (in seconds)
% 1.98/1.30  ----------------------
% 1.98/1.31  Preprocessing        : 0.29
% 1.98/1.31  Parsing              : 0.16
% 1.98/1.31  CNF conversion       : 0.02
% 1.98/1.31  Main loop            : 0.18
% 1.98/1.31  Inferencing          : 0.07
% 1.98/1.31  Reduction            : 0.06
% 1.98/1.31  Demodulation         : 0.04
% 1.98/1.31  BG Simplification    : 0.01
% 1.98/1.31  Subsumption          : 0.02
% 1.98/1.31  Abstraction          : 0.01
% 1.98/1.31  MUC search           : 0.00
% 1.98/1.31  Cooper               : 0.00
% 1.98/1.31  Total                : 0.51
% 1.98/1.31  Index Insertion      : 0.00
% 1.98/1.31  Index Deletion       : 0.00
% 1.98/1.31  Index Matching       : 0.00
% 1.98/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
