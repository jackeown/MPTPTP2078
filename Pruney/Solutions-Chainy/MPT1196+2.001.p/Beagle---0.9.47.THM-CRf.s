%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:12 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   55 (  82 expanded)
%              Number of leaves         :   27 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :  114 ( 272 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v6_lattices > v5_lattices > v2_struct_0 > l3_lattices > l2_lattices > l1_lattices > k1_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
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

tff(f_75,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_91,axiom,(
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

tff(f_58,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => ( v5_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => k1_lattices(A,B,k1_lattices(A,C,D)) = k1_lattices(A,k1_lattices(A,B,C),D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_lattices)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k1_lattices(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_lattices)).

tff(f_40,axiom,(
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

tff(c_40,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_30,plain,(
    l3_lattices('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_41,plain,(
    ! [A_45] :
      ( l2_lattices(A_45)
      | ~ l3_lattices(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_45,plain,(
    l2_lattices('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_41])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_26,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_36,plain,(
    v6_lattices('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_34,plain,(
    v8_lattices('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_32,plain,(
    v9_lattices('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_54,plain,(
    ! [A_50,B_51] :
      ( k1_lattices(A_50,B_51,B_51) = B_51
      | ~ m1_subset_1(B_51,u1_struct_0(A_50))
      | ~ l3_lattices(A_50)
      | ~ v9_lattices(A_50)
      | ~ v8_lattices(A_50)
      | ~ v6_lattices(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_64,plain,
    ( k1_lattices('#skF_4','#skF_5','#skF_5') = '#skF_5'
    | ~ l3_lattices('#skF_4')
    | ~ v9_lattices('#skF_4')
    | ~ v8_lattices('#skF_4')
    | ~ v6_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_54])).

tff(c_74,plain,
    ( k1_lattices('#skF_4','#skF_5','#skF_5') = '#skF_5'
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_64])).

tff(c_75,plain,(
    k1_lattices('#skF_4','#skF_5','#skF_5') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_74])).

tff(c_38,plain,(
    v5_lattices('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_351,plain,(
    ! [A_77,B_78,C_79,D_80] :
      ( k1_lattices(A_77,k1_lattices(A_77,B_78,C_79),D_80) = k1_lattices(A_77,B_78,k1_lattices(A_77,C_79,D_80))
      | ~ m1_subset_1(D_80,u1_struct_0(A_77))
      | ~ m1_subset_1(C_79,u1_struct_0(A_77))
      | ~ m1_subset_1(B_78,u1_struct_0(A_77))
      | ~ v5_lattices(A_77)
      | ~ l2_lattices(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_361,plain,(
    ! [B_78,C_79] :
      ( k1_lattices('#skF_4',k1_lattices('#skF_4',B_78,C_79),'#skF_6') = k1_lattices('#skF_4',B_78,k1_lattices('#skF_4',C_79,'#skF_6'))
      | ~ m1_subset_1(C_79,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_78,u1_struct_0('#skF_4'))
      | ~ v5_lattices('#skF_4')
      | ~ l2_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_351])).

tff(c_370,plain,(
    ! [B_78,C_79] :
      ( k1_lattices('#skF_4',k1_lattices('#skF_4',B_78,C_79),'#skF_6') = k1_lattices('#skF_4',B_78,k1_lattices('#skF_4',C_79,'#skF_6'))
      | ~ m1_subset_1(C_79,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_78,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_38,c_361])).

tff(c_376,plain,(
    ! [B_81,C_82] :
      ( k1_lattices('#skF_4',k1_lattices('#skF_4',B_81,C_82),'#skF_6') = k1_lattices('#skF_4',B_81,k1_lattices('#skF_4',C_82,'#skF_6'))
      | ~ m1_subset_1(C_82,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_81,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_370])).

tff(c_474,plain,(
    ! [B_84] :
      ( k1_lattices('#skF_4',k1_lattices('#skF_4',B_84,'#skF_5'),'#skF_6') = k1_lattices('#skF_4',B_84,k1_lattices('#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1(B_84,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_28,c_376])).

tff(c_496,plain,(
    k1_lattices('#skF_4',k1_lattices('#skF_4','#skF_5','#skF_5'),'#skF_6') = k1_lattices('#skF_4','#skF_5',k1_lattices('#skF_4','#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_28,c_474])).

tff(c_515,plain,(
    k1_lattices('#skF_4','#skF_5',k1_lattices('#skF_4','#skF_5','#skF_6')) = k1_lattices('#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_496])).

tff(c_16,plain,(
    ! [A_34,B_35,C_36] :
      ( m1_subset_1(k1_lattices(A_34,B_35,C_36),u1_struct_0(A_34))
      | ~ m1_subset_1(C_36,u1_struct_0(A_34))
      | ~ m1_subset_1(B_35,u1_struct_0(A_34))
      | ~ l2_lattices(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_100,plain,(
    ! [A_55,B_56,C_57] :
      ( r1_lattices(A_55,B_56,C_57)
      | k1_lattices(A_55,B_56,C_57) != C_57
      | ~ m1_subset_1(C_57,u1_struct_0(A_55))
      | ~ m1_subset_1(B_56,u1_struct_0(A_55))
      | ~ l2_lattices(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_781,plain,(
    ! [A_88,B_89,B_90,C_91] :
      ( r1_lattices(A_88,B_89,k1_lattices(A_88,B_90,C_91))
      | k1_lattices(A_88,B_89,k1_lattices(A_88,B_90,C_91)) != k1_lattices(A_88,B_90,C_91)
      | ~ m1_subset_1(B_89,u1_struct_0(A_88))
      | ~ m1_subset_1(C_91,u1_struct_0(A_88))
      | ~ m1_subset_1(B_90,u1_struct_0(A_88))
      | ~ l2_lattices(A_88)
      | v2_struct_0(A_88) ) ),
    inference(resolution,[status(thm)],[c_16,c_100])).

tff(c_24,plain,(
    ~ r1_lattices('#skF_4','#skF_5',k1_lattices('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_786,plain,
    ( k1_lattices('#skF_4','#skF_5',k1_lattices('#skF_4','#skF_5','#skF_6')) != k1_lattices('#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l2_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_781,c_24])).

tff(c_820,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_28,c_26,c_515,c_786])).

tff(c_822,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_820])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:10:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.45  
% 2.78/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.45  %$ r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v6_lattices > v5_lattices > v2_struct_0 > l3_lattices > l2_lattices > l1_lattices > k1_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3
% 2.78/1.45  
% 2.78/1.45  %Foreground sorts:
% 2.78/1.45  
% 2.78/1.45  
% 2.78/1.45  %Background operators:
% 2.78/1.45  
% 2.78/1.45  
% 2.78/1.45  %Foreground operators:
% 2.78/1.45  tff(l3_lattices, type, l3_lattices: $i > $o).
% 2.78/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.78/1.45  tff(l2_lattices, type, l2_lattices: $i > $o).
% 2.78/1.45  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.78/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.78/1.45  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 2.78/1.45  tff(l1_lattices, type, l1_lattices: $i > $o).
% 2.78/1.45  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 2.78/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.78/1.45  tff('#skF_6', type, '#skF_6': $i).
% 2.78/1.45  tff(v6_lattices, type, v6_lattices: $i > $o).
% 2.78/1.45  tff(v9_lattices, type, v9_lattices: $i > $o).
% 2.78/1.45  tff(v5_lattices, type, v5_lattices: $i > $o).
% 2.78/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.78/1.45  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.78/1.45  tff(v8_lattices, type, v8_lattices: $i > $o).
% 2.78/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.78/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.78/1.45  
% 2.78/1.46  tff(f_113, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v5_lattices(A)) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => r1_lattices(A, B, k1_lattices(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_lattices)).
% 2.78/1.46  tff(f_75, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 2.78/1.46  tff(f_91, axiom, (![A]: (((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k1_lattices(A, B, B) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_lattices)).
% 2.78/1.46  tff(f_58, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (v5_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (k1_lattices(A, B, k1_lattices(A, C, D)) = k1_lattices(A, k1_lattices(A, B, C), D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_lattices)).
% 2.78/1.46  tff(f_69, axiom, (![A, B, C]: ((((~v2_struct_0(A) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k1_lattices(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_lattices)).
% 2.78/1.46  tff(f_40, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k1_lattices(A, B, C) = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_lattices)).
% 2.78/1.46  tff(c_40, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.46  tff(c_30, plain, (l3_lattices('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.46  tff(c_41, plain, (![A_45]: (l2_lattices(A_45) | ~l3_lattices(A_45))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.78/1.46  tff(c_45, plain, (l2_lattices('#skF_4')), inference(resolution, [status(thm)], [c_30, c_41])).
% 2.78/1.46  tff(c_28, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.46  tff(c_26, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.46  tff(c_36, plain, (v6_lattices('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.46  tff(c_34, plain, (v8_lattices('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.46  tff(c_32, plain, (v9_lattices('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.46  tff(c_54, plain, (![A_50, B_51]: (k1_lattices(A_50, B_51, B_51)=B_51 | ~m1_subset_1(B_51, u1_struct_0(A_50)) | ~l3_lattices(A_50) | ~v9_lattices(A_50) | ~v8_lattices(A_50) | ~v6_lattices(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.78/1.46  tff(c_64, plain, (k1_lattices('#skF_4', '#skF_5', '#skF_5')='#skF_5' | ~l3_lattices('#skF_4') | ~v9_lattices('#skF_4') | ~v8_lattices('#skF_4') | ~v6_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_28, c_54])).
% 2.78/1.46  tff(c_74, plain, (k1_lattices('#skF_4', '#skF_5', '#skF_5')='#skF_5' | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_64])).
% 2.78/1.46  tff(c_75, plain, (k1_lattices('#skF_4', '#skF_5', '#skF_5')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_40, c_74])).
% 2.78/1.46  tff(c_38, plain, (v5_lattices('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.46  tff(c_351, plain, (![A_77, B_78, C_79, D_80]: (k1_lattices(A_77, k1_lattices(A_77, B_78, C_79), D_80)=k1_lattices(A_77, B_78, k1_lattices(A_77, C_79, D_80)) | ~m1_subset_1(D_80, u1_struct_0(A_77)) | ~m1_subset_1(C_79, u1_struct_0(A_77)) | ~m1_subset_1(B_78, u1_struct_0(A_77)) | ~v5_lattices(A_77) | ~l2_lattices(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.78/1.46  tff(c_361, plain, (![B_78, C_79]: (k1_lattices('#skF_4', k1_lattices('#skF_4', B_78, C_79), '#skF_6')=k1_lattices('#skF_4', B_78, k1_lattices('#skF_4', C_79, '#skF_6')) | ~m1_subset_1(C_79, u1_struct_0('#skF_4')) | ~m1_subset_1(B_78, u1_struct_0('#skF_4')) | ~v5_lattices('#skF_4') | ~l2_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_351])).
% 2.78/1.46  tff(c_370, plain, (![B_78, C_79]: (k1_lattices('#skF_4', k1_lattices('#skF_4', B_78, C_79), '#skF_6')=k1_lattices('#skF_4', B_78, k1_lattices('#skF_4', C_79, '#skF_6')) | ~m1_subset_1(C_79, u1_struct_0('#skF_4')) | ~m1_subset_1(B_78, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_38, c_361])).
% 2.78/1.46  tff(c_376, plain, (![B_81, C_82]: (k1_lattices('#skF_4', k1_lattices('#skF_4', B_81, C_82), '#skF_6')=k1_lattices('#skF_4', B_81, k1_lattices('#skF_4', C_82, '#skF_6')) | ~m1_subset_1(C_82, u1_struct_0('#skF_4')) | ~m1_subset_1(B_81, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_40, c_370])).
% 2.78/1.46  tff(c_474, plain, (![B_84]: (k1_lattices('#skF_4', k1_lattices('#skF_4', B_84, '#skF_5'), '#skF_6')=k1_lattices('#skF_4', B_84, k1_lattices('#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1(B_84, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_28, c_376])).
% 2.78/1.46  tff(c_496, plain, (k1_lattices('#skF_4', k1_lattices('#skF_4', '#skF_5', '#skF_5'), '#skF_6')=k1_lattices('#skF_4', '#skF_5', k1_lattices('#skF_4', '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_28, c_474])).
% 2.78/1.46  tff(c_515, plain, (k1_lattices('#skF_4', '#skF_5', k1_lattices('#skF_4', '#skF_5', '#skF_6'))=k1_lattices('#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_496])).
% 2.78/1.46  tff(c_16, plain, (![A_34, B_35, C_36]: (m1_subset_1(k1_lattices(A_34, B_35, C_36), u1_struct_0(A_34)) | ~m1_subset_1(C_36, u1_struct_0(A_34)) | ~m1_subset_1(B_35, u1_struct_0(A_34)) | ~l2_lattices(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.78/1.46  tff(c_100, plain, (![A_55, B_56, C_57]: (r1_lattices(A_55, B_56, C_57) | k1_lattices(A_55, B_56, C_57)!=C_57 | ~m1_subset_1(C_57, u1_struct_0(A_55)) | ~m1_subset_1(B_56, u1_struct_0(A_55)) | ~l2_lattices(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.78/1.46  tff(c_781, plain, (![A_88, B_89, B_90, C_91]: (r1_lattices(A_88, B_89, k1_lattices(A_88, B_90, C_91)) | k1_lattices(A_88, B_89, k1_lattices(A_88, B_90, C_91))!=k1_lattices(A_88, B_90, C_91) | ~m1_subset_1(B_89, u1_struct_0(A_88)) | ~m1_subset_1(C_91, u1_struct_0(A_88)) | ~m1_subset_1(B_90, u1_struct_0(A_88)) | ~l2_lattices(A_88) | v2_struct_0(A_88))), inference(resolution, [status(thm)], [c_16, c_100])).
% 2.78/1.46  tff(c_24, plain, (~r1_lattices('#skF_4', '#skF_5', k1_lattices('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.46  tff(c_786, plain, (k1_lattices('#skF_4', '#skF_5', k1_lattices('#skF_4', '#skF_5', '#skF_6'))!=k1_lattices('#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l2_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_781, c_24])).
% 2.78/1.46  tff(c_820, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_45, c_28, c_26, c_515, c_786])).
% 2.78/1.46  tff(c_822, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_820])).
% 2.78/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.46  
% 2.78/1.46  Inference rules
% 2.78/1.46  ----------------------
% 2.78/1.46  #Ref     : 0
% 2.78/1.46  #Sup     : 152
% 2.78/1.46  #Fact    : 0
% 2.78/1.46  #Define  : 0
% 2.78/1.46  #Split   : 4
% 2.78/1.46  #Chain   : 0
% 2.78/1.46  #Close   : 0
% 2.78/1.46  
% 2.78/1.46  Ordering : KBO
% 2.78/1.46  
% 2.78/1.46  Simplification rules
% 2.78/1.46  ----------------------
% 2.78/1.46  #Subsume      : 12
% 2.78/1.46  #Demod        : 210
% 2.78/1.46  #Tautology    : 69
% 2.78/1.46  #SimpNegUnit  : 59
% 2.78/1.46  #BackRed      : 0
% 2.78/1.46  
% 2.78/1.46  #Partial instantiations: 0
% 2.78/1.46  #Strategies tried      : 1
% 2.78/1.46  
% 2.78/1.46  Timing (in seconds)
% 2.78/1.46  ----------------------
% 3.18/1.47  Preprocessing        : 0.33
% 3.18/1.47  Parsing              : 0.18
% 3.18/1.47  CNF conversion       : 0.03
% 3.18/1.47  Main loop            : 0.38
% 3.18/1.47  Inferencing          : 0.14
% 3.18/1.47  Reduction            : 0.12
% 3.18/1.47  Demodulation         : 0.09
% 3.18/1.47  BG Simplification    : 0.02
% 3.18/1.47  Subsumption          : 0.08
% 3.18/1.47  Abstraction          : 0.02
% 3.18/1.47  MUC search           : 0.00
% 3.18/1.47  Cooper               : 0.00
% 3.18/1.47  Total                : 0.74
% 3.18/1.47  Index Insertion      : 0.00
% 3.18/1.47  Index Deletion       : 0.00
% 3.18/1.47  Index Matching       : 0.00
% 3.18/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
