%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:12 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   46 (  64 expanded)
%              Number of leaves         :   26 (  38 expanded)
%              Depth                    :    7
%              Number of atoms          :   91 ( 205 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v6_lattices > v5_lattices > v2_struct_0 > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_lattices,type,(
    k1_lattices: ( $i * $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

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

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v5_lattices(A)
          & v6_lattices(A)
          & v8_lattices(A)
          & v9_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => r1_lattices(A,B,k1_lattices(A,B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_lattices)).

tff(f_57,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

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

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k1_lattices(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_lattices)).

tff(f_76,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_26,plain,(
    l3_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_37,plain,(
    ! [A_27] :
      ( l2_lattices(A_27)
      | ~ l3_lattices(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_41,plain,(
    l2_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_37])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_22,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_30,plain,(
    v8_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_28,plain,(
    v9_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_51,plain,(
    ! [A_35,B_36,C_37] :
      ( k2_lattices(A_35,B_36,k1_lattices(A_35,B_36,C_37)) = B_36
      | ~ m1_subset_1(C_37,u1_struct_0(A_35))
      | ~ m1_subset_1(B_36,u1_struct_0(A_35))
      | ~ v9_lattices(A_35)
      | ~ l3_lattices(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_59,plain,(
    ! [B_36] :
      ( k2_lattices('#skF_3',B_36,k1_lattices('#skF_3',B_36,'#skF_5')) = B_36
      | ~ m1_subset_1(B_36,u1_struct_0('#skF_3'))
      | ~ v9_lattices('#skF_3')
      | ~ l3_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_51])).

tff(c_67,plain,(
    ! [B_36] :
      ( k2_lattices('#skF_3',B_36,k1_lattices('#skF_3',B_36,'#skF_5')) = B_36
      | ~ m1_subset_1(B_36,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_59])).

tff(c_73,plain,(
    ! [B_38] :
      ( k2_lattices('#skF_3',B_38,k1_lattices('#skF_3',B_38,'#skF_5')) = B_38
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_67])).

tff(c_100,plain,(
    k2_lattices('#skF_3','#skF_4',k1_lattices('#skF_3','#skF_4','#skF_5')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_24,c_73])).

tff(c_10,plain,(
    ! [A_12,B_13,C_14] :
      ( m1_subset_1(k1_lattices(A_12,B_13,C_14),u1_struct_0(A_12))
      | ~ m1_subset_1(C_14,u1_struct_0(A_12))
      | ~ m1_subset_1(B_13,u1_struct_0(A_12))
      | ~ l2_lattices(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_145,plain,(
    ! [A_40,B_41,C_42] :
      ( r1_lattices(A_40,B_41,C_42)
      | k2_lattices(A_40,B_41,C_42) != B_41
      | ~ m1_subset_1(C_42,u1_struct_0(A_40))
      | ~ m1_subset_1(B_41,u1_struct_0(A_40))
      | ~ l3_lattices(A_40)
      | ~ v9_lattices(A_40)
      | ~ v8_lattices(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_279,plain,(
    ! [A_60,B_61,B_62,C_63] :
      ( r1_lattices(A_60,B_61,k1_lattices(A_60,B_62,C_63))
      | k2_lattices(A_60,B_61,k1_lattices(A_60,B_62,C_63)) != B_61
      | ~ m1_subset_1(B_61,u1_struct_0(A_60))
      | ~ l3_lattices(A_60)
      | ~ v9_lattices(A_60)
      | ~ v8_lattices(A_60)
      | ~ m1_subset_1(C_63,u1_struct_0(A_60))
      | ~ m1_subset_1(B_62,u1_struct_0(A_60))
      | ~ l2_lattices(A_60)
      | v2_struct_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_10,c_145])).

tff(c_20,plain,(
    ~ r1_lattices('#skF_3','#skF_4',k1_lattices('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_284,plain,
    ( k2_lattices('#skF_3','#skF_4',k1_lattices('#skF_3','#skF_4','#skF_5')) != '#skF_4'
    | ~ l3_lattices('#skF_3')
    | ~ v9_lattices('#skF_3')
    | ~ v8_lattices('#skF_3')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l2_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_279,c_20])).

tff(c_288,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_24,c_22,c_30,c_28,c_26,c_100,c_284])).

tff(c_290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_288])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:14:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.27  
% 2.33/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.27  %$ r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v6_lattices > v5_lattices > v2_struct_0 > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 2.33/1.27  
% 2.33/1.27  %Foreground sorts:
% 2.33/1.27  
% 2.33/1.27  
% 2.33/1.27  %Background operators:
% 2.33/1.27  
% 2.33/1.27  
% 2.33/1.27  %Foreground operators:
% 2.33/1.27  tff(l3_lattices, type, l3_lattices: $i > $o).
% 2.33/1.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.33/1.27  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 2.33/1.27  tff(l2_lattices, type, l2_lattices: $i > $o).
% 2.33/1.27  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.33/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.33/1.27  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 2.33/1.27  tff(l1_lattices, type, l1_lattices: $i > $o).
% 2.33/1.27  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 2.33/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.33/1.27  tff(v6_lattices, type, v6_lattices: $i > $o).
% 2.33/1.27  tff(v9_lattices, type, v9_lattices: $i > $o).
% 2.33/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.33/1.27  tff(v5_lattices, type, v5_lattices: $i > $o).
% 2.33/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.33/1.27  tff(v8_lattices, type, v8_lattices: $i > $o).
% 2.33/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.33/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.33/1.27  
% 2.33/1.29  tff(f_98, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v5_lattices(A)) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => r1_lattices(A, B, k1_lattices(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_lattices)).
% 2.33/1.29  tff(f_57, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 2.33/1.29  tff(f_40, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v9_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k2_lattices(A, B, k1_lattices(A, B, C)) = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattices)).
% 2.33/1.29  tff(f_51, axiom, (![A, B, C]: ((((~v2_struct_0(A) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k1_lattices(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_lattices)).
% 2.33/1.29  tff(f_76, axiom, (![A]: ((((~v2_struct_0(A) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k2_lattices(A, B, C) = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_lattices)).
% 2.33/1.29  tff(c_36, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.33/1.29  tff(c_26, plain, (l3_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.33/1.29  tff(c_37, plain, (![A_27]: (l2_lattices(A_27) | ~l3_lattices(A_27))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.33/1.29  tff(c_41, plain, (l2_lattices('#skF_3')), inference(resolution, [status(thm)], [c_26, c_37])).
% 2.33/1.29  tff(c_24, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.33/1.29  tff(c_22, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.33/1.29  tff(c_30, plain, (v8_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.33/1.29  tff(c_28, plain, (v9_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.33/1.29  tff(c_51, plain, (![A_35, B_36, C_37]: (k2_lattices(A_35, B_36, k1_lattices(A_35, B_36, C_37))=B_36 | ~m1_subset_1(C_37, u1_struct_0(A_35)) | ~m1_subset_1(B_36, u1_struct_0(A_35)) | ~v9_lattices(A_35) | ~l3_lattices(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.33/1.29  tff(c_59, plain, (![B_36]: (k2_lattices('#skF_3', B_36, k1_lattices('#skF_3', B_36, '#skF_5'))=B_36 | ~m1_subset_1(B_36, u1_struct_0('#skF_3')) | ~v9_lattices('#skF_3') | ~l3_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_51])).
% 2.33/1.29  tff(c_67, plain, (![B_36]: (k2_lattices('#skF_3', B_36, k1_lattices('#skF_3', B_36, '#skF_5'))=B_36 | ~m1_subset_1(B_36, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_59])).
% 2.33/1.29  tff(c_73, plain, (![B_38]: (k2_lattices('#skF_3', B_38, k1_lattices('#skF_3', B_38, '#skF_5'))=B_38 | ~m1_subset_1(B_38, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_36, c_67])).
% 2.33/1.29  tff(c_100, plain, (k2_lattices('#skF_3', '#skF_4', k1_lattices('#skF_3', '#skF_4', '#skF_5'))='#skF_4'), inference(resolution, [status(thm)], [c_24, c_73])).
% 2.33/1.29  tff(c_10, plain, (![A_12, B_13, C_14]: (m1_subset_1(k1_lattices(A_12, B_13, C_14), u1_struct_0(A_12)) | ~m1_subset_1(C_14, u1_struct_0(A_12)) | ~m1_subset_1(B_13, u1_struct_0(A_12)) | ~l2_lattices(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.33/1.29  tff(c_145, plain, (![A_40, B_41, C_42]: (r1_lattices(A_40, B_41, C_42) | k2_lattices(A_40, B_41, C_42)!=B_41 | ~m1_subset_1(C_42, u1_struct_0(A_40)) | ~m1_subset_1(B_41, u1_struct_0(A_40)) | ~l3_lattices(A_40) | ~v9_lattices(A_40) | ~v8_lattices(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.33/1.29  tff(c_279, plain, (![A_60, B_61, B_62, C_63]: (r1_lattices(A_60, B_61, k1_lattices(A_60, B_62, C_63)) | k2_lattices(A_60, B_61, k1_lattices(A_60, B_62, C_63))!=B_61 | ~m1_subset_1(B_61, u1_struct_0(A_60)) | ~l3_lattices(A_60) | ~v9_lattices(A_60) | ~v8_lattices(A_60) | ~m1_subset_1(C_63, u1_struct_0(A_60)) | ~m1_subset_1(B_62, u1_struct_0(A_60)) | ~l2_lattices(A_60) | v2_struct_0(A_60))), inference(resolution, [status(thm)], [c_10, c_145])).
% 2.33/1.29  tff(c_20, plain, (~r1_lattices('#skF_3', '#skF_4', k1_lattices('#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.33/1.29  tff(c_284, plain, (k2_lattices('#skF_3', '#skF_4', k1_lattices('#skF_3', '#skF_4', '#skF_5'))!='#skF_4' | ~l3_lattices('#skF_3') | ~v9_lattices('#skF_3') | ~v8_lattices('#skF_3') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l2_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_279, c_20])).
% 2.33/1.29  tff(c_288, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_41, c_24, c_22, c_30, c_28, c_26, c_100, c_284])).
% 2.33/1.29  tff(c_290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_288])).
% 2.33/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.29  
% 2.33/1.29  Inference rules
% 2.33/1.29  ----------------------
% 2.33/1.29  #Ref     : 0
% 2.33/1.29  #Sup     : 50
% 2.33/1.29  #Fact    : 0
% 2.33/1.29  #Define  : 0
% 2.33/1.29  #Split   : 4
% 2.33/1.29  #Chain   : 0
% 2.33/1.29  #Close   : 0
% 2.33/1.29  
% 2.33/1.29  Ordering : KBO
% 2.33/1.29  
% 2.33/1.29  Simplification rules
% 2.33/1.29  ----------------------
% 2.33/1.29  #Subsume      : 0
% 2.33/1.29  #Demod        : 45
% 2.33/1.29  #Tautology    : 29
% 2.33/1.29  #SimpNegUnit  : 19
% 2.33/1.29  #BackRed      : 0
% 2.33/1.29  
% 2.33/1.29  #Partial instantiations: 0
% 2.33/1.29  #Strategies tried      : 1
% 2.33/1.29  
% 2.33/1.29  Timing (in seconds)
% 2.33/1.29  ----------------------
% 2.33/1.29  Preprocessing        : 0.28
% 2.33/1.29  Parsing              : 0.15
% 2.33/1.29  CNF conversion       : 0.02
% 2.33/1.29  Main loop            : 0.24
% 2.33/1.29  Inferencing          : 0.10
% 2.33/1.29  Reduction            : 0.07
% 2.33/1.29  Demodulation         : 0.05
% 2.33/1.29  BG Simplification    : 0.02
% 2.33/1.29  Subsumption          : 0.04
% 2.33/1.29  Abstraction          : 0.01
% 2.33/1.29  MUC search           : 0.00
% 2.33/1.29  Cooper               : 0.00
% 2.33/1.29  Total                : 0.55
% 2.33/1.29  Index Insertion      : 0.00
% 2.33/1.29  Index Deletion       : 0.00
% 2.33/1.29  Index Matching       : 0.00
% 2.33/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
