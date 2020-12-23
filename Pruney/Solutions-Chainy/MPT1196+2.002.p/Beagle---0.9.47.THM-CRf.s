%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:12 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   54 (  85 expanded)
%              Number of leaves         :   29 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :  113 ( 283 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v6_lattices > v5_lattices > v2_struct_0 > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_4 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3

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

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_lattices,type,(
    k1_lattices: ( $i * $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(f_109,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_lattices)).

tff(f_87,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k1_lattices(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).

tff(f_70,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( v9_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k2_lattices(A,B,k1_lattices(A,B,C)) = B ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).

tff(f_55,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( v8_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k1_lattices(A,k2_lattices(A,B,C),C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_34,plain,(
    l3_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_45,plain,(
    ! [A_38] :
      ( l2_lattices(A_38)
      | ~ l3_lattices(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_49,plain,(
    l2_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_45])).

tff(c_32,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_30,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_22,plain,(
    ! [A_30,B_31,C_32] :
      ( m1_subset_1(k1_lattices(A_30,B_31,C_32),u1_struct_0(A_30))
      | ~ m1_subset_1(C_32,u1_struct_0(A_30))
      | ~ m1_subset_1(B_31,u1_struct_0(A_30))
      | ~ l2_lattices(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_63,plain,(
    ! [A_52,B_53,C_54] :
      ( r1_lattices(A_52,B_53,C_54)
      | k1_lattices(A_52,B_53,C_54) != C_54
      | ~ m1_subset_1(C_54,u1_struct_0(A_52))
      | ~ m1_subset_1(B_53,u1_struct_0(A_52))
      | ~ l2_lattices(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1020,plain,(
    ! [A_99,B_100,B_101,C_102] :
      ( r1_lattices(A_99,B_100,k1_lattices(A_99,B_101,C_102))
      | k1_lattices(A_99,B_100,k1_lattices(A_99,B_101,C_102)) != k1_lattices(A_99,B_101,C_102)
      | ~ m1_subset_1(B_100,u1_struct_0(A_99))
      | ~ m1_subset_1(C_102,u1_struct_0(A_99))
      | ~ m1_subset_1(B_101,u1_struct_0(A_99))
      | ~ l2_lattices(A_99)
      | v2_struct_0(A_99) ) ),
    inference(resolution,[status(thm)],[c_22,c_63])).

tff(c_28,plain,(
    ~ r1_lattices('#skF_5','#skF_6',k1_lattices('#skF_5','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1025,plain,
    ( k1_lattices('#skF_5','#skF_6',k1_lattices('#skF_5','#skF_6','#skF_7')) != k1_lattices('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l2_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1020,c_28])).

tff(c_1053,plain,
    ( k1_lattices('#skF_5','#skF_6',k1_lattices('#skF_5','#skF_6','#skF_7')) != k1_lattices('#skF_5','#skF_6','#skF_7')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_32,c_30,c_1025])).

tff(c_1054,plain,(
    k1_lattices('#skF_5','#skF_6',k1_lattices('#skF_5','#skF_6','#skF_7')) != k1_lattices('#skF_5','#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1053])).

tff(c_38,plain,(
    v8_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_36,plain,(
    v9_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_141,plain,(
    ! [A_56,B_57,C_58] :
      ( k2_lattices(A_56,B_57,k1_lattices(A_56,B_57,C_58)) = B_57
      | ~ m1_subset_1(C_58,u1_struct_0(A_56))
      | ~ m1_subset_1(B_57,u1_struct_0(A_56))
      | ~ v9_lattices(A_56)
      | ~ l3_lattices(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_153,plain,(
    ! [B_57] :
      ( k2_lattices('#skF_5',B_57,k1_lattices('#skF_5',B_57,'#skF_7')) = B_57
      | ~ m1_subset_1(B_57,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_141])).

tff(c_163,plain,(
    ! [B_57] :
      ( k2_lattices('#skF_5',B_57,k1_lattices('#skF_5',B_57,'#skF_7')) = B_57
      | ~ m1_subset_1(B_57,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36,c_153])).

tff(c_170,plain,(
    ! [B_59] :
      ( k2_lattices('#skF_5',B_59,k1_lattices('#skF_5',B_59,'#skF_7')) = B_59
      | ~ m1_subset_1(B_59,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_163])).

tff(c_211,plain,(
    k2_lattices('#skF_5','#skF_6',k1_lattices('#skF_5','#skF_6','#skF_7')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_32,c_170])).

tff(c_319,plain,(
    ! [A_62,B_63,C_64] :
      ( k1_lattices(A_62,k2_lattices(A_62,B_63,C_64),C_64) = C_64
      | ~ m1_subset_1(C_64,u1_struct_0(A_62))
      | ~ m1_subset_1(B_63,u1_struct_0(A_62))
      | ~ v8_lattices(A_62)
      | ~ l3_lattices(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1119,plain,(
    ! [A_105,B_106,B_107,C_108] :
      ( k1_lattices(A_105,k2_lattices(A_105,B_106,k1_lattices(A_105,B_107,C_108)),k1_lattices(A_105,B_107,C_108)) = k1_lattices(A_105,B_107,C_108)
      | ~ m1_subset_1(B_106,u1_struct_0(A_105))
      | ~ v8_lattices(A_105)
      | ~ l3_lattices(A_105)
      | ~ m1_subset_1(C_108,u1_struct_0(A_105))
      | ~ m1_subset_1(B_107,u1_struct_0(A_105))
      | ~ l2_lattices(A_105)
      | v2_struct_0(A_105) ) ),
    inference(resolution,[status(thm)],[c_22,c_319])).

tff(c_1257,plain,
    ( k1_lattices('#skF_5','#skF_6',k1_lattices('#skF_5','#skF_6','#skF_7')) = k1_lattices('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ v8_lattices('#skF_5')
    | ~ l3_lattices('#skF_5')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l2_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_1119])).

tff(c_1339,plain,
    ( k1_lattices('#skF_5','#skF_6',k1_lattices('#skF_5','#skF_6','#skF_7')) = k1_lattices('#skF_5','#skF_6','#skF_7')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_32,c_30,c_34,c_38,c_32,c_1257])).

tff(c_1341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1054,c_1339])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:48:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.36/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.52  
% 3.36/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.52  %$ r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v6_lattices > v5_lattices > v2_struct_0 > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_4 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3
% 3.36/1.52  
% 3.36/1.52  %Foreground sorts:
% 3.36/1.52  
% 3.36/1.52  
% 3.36/1.52  %Background operators:
% 3.36/1.52  
% 3.36/1.52  
% 3.36/1.52  %Foreground operators:
% 3.36/1.52  tff(l3_lattices, type, l3_lattices: $i > $o).
% 3.36/1.52  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.36/1.52  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 3.36/1.52  tff(l2_lattices, type, l2_lattices: $i > $o).
% 3.36/1.52  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.36/1.52  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.36/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.52  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.36/1.52  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 3.36/1.52  tff(l1_lattices, type, l1_lattices: $i > $o).
% 3.36/1.52  tff('#skF_7', type, '#skF_7': $i).
% 3.36/1.52  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 3.36/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.36/1.52  tff('#skF_6', type, '#skF_6': $i).
% 3.36/1.52  tff(v6_lattices, type, v6_lattices: $i > $o).
% 3.36/1.52  tff(v9_lattices, type, v9_lattices: $i > $o).
% 3.36/1.52  tff(v5_lattices, type, v5_lattices: $i > $o).
% 3.36/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.52  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.36/1.52  tff(v8_lattices, type, v8_lattices: $i > $o).
% 3.36/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.36/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.36/1.52  
% 3.36/1.53  tff(f_109, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v5_lattices(A)) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => r1_lattices(A, B, k1_lattices(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_lattices)).
% 3.36/1.53  tff(f_87, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 3.36/1.53  tff(f_81, axiom, (![A, B, C]: ((((~v2_struct_0(A) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k1_lattices(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_lattices)).
% 3.36/1.53  tff(f_40, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k1_lattices(A, B, C) = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_lattices)).
% 3.36/1.53  tff(f_70, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v9_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k2_lattices(A, B, k1_lattices(A, B, C)) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattices)).
% 3.36/1.53  tff(f_55, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v8_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k1_lattices(A, k2_lattices(A, B, C), C) = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattices)).
% 3.36/1.53  tff(c_44, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.36/1.53  tff(c_34, plain, (l3_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.36/1.53  tff(c_45, plain, (![A_38]: (l2_lattices(A_38) | ~l3_lattices(A_38))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.36/1.53  tff(c_49, plain, (l2_lattices('#skF_5')), inference(resolution, [status(thm)], [c_34, c_45])).
% 3.36/1.53  tff(c_32, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.36/1.53  tff(c_30, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.36/1.53  tff(c_22, plain, (![A_30, B_31, C_32]: (m1_subset_1(k1_lattices(A_30, B_31, C_32), u1_struct_0(A_30)) | ~m1_subset_1(C_32, u1_struct_0(A_30)) | ~m1_subset_1(B_31, u1_struct_0(A_30)) | ~l2_lattices(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.36/1.53  tff(c_63, plain, (![A_52, B_53, C_54]: (r1_lattices(A_52, B_53, C_54) | k1_lattices(A_52, B_53, C_54)!=C_54 | ~m1_subset_1(C_54, u1_struct_0(A_52)) | ~m1_subset_1(B_53, u1_struct_0(A_52)) | ~l2_lattices(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.36/1.53  tff(c_1020, plain, (![A_99, B_100, B_101, C_102]: (r1_lattices(A_99, B_100, k1_lattices(A_99, B_101, C_102)) | k1_lattices(A_99, B_100, k1_lattices(A_99, B_101, C_102))!=k1_lattices(A_99, B_101, C_102) | ~m1_subset_1(B_100, u1_struct_0(A_99)) | ~m1_subset_1(C_102, u1_struct_0(A_99)) | ~m1_subset_1(B_101, u1_struct_0(A_99)) | ~l2_lattices(A_99) | v2_struct_0(A_99))), inference(resolution, [status(thm)], [c_22, c_63])).
% 3.36/1.53  tff(c_28, plain, (~r1_lattices('#skF_5', '#skF_6', k1_lattices('#skF_5', '#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.36/1.53  tff(c_1025, plain, (k1_lattices('#skF_5', '#skF_6', k1_lattices('#skF_5', '#skF_6', '#skF_7'))!=k1_lattices('#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l2_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1020, c_28])).
% 3.36/1.53  tff(c_1053, plain, (k1_lattices('#skF_5', '#skF_6', k1_lattices('#skF_5', '#skF_6', '#skF_7'))!=k1_lattices('#skF_5', '#skF_6', '#skF_7') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_49, c_32, c_30, c_1025])).
% 3.36/1.53  tff(c_1054, plain, (k1_lattices('#skF_5', '#skF_6', k1_lattices('#skF_5', '#skF_6', '#skF_7'))!=k1_lattices('#skF_5', '#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_44, c_1053])).
% 3.36/1.53  tff(c_38, plain, (v8_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.36/1.53  tff(c_36, plain, (v9_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.36/1.53  tff(c_141, plain, (![A_56, B_57, C_58]: (k2_lattices(A_56, B_57, k1_lattices(A_56, B_57, C_58))=B_57 | ~m1_subset_1(C_58, u1_struct_0(A_56)) | ~m1_subset_1(B_57, u1_struct_0(A_56)) | ~v9_lattices(A_56) | ~l3_lattices(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.36/1.53  tff(c_153, plain, (![B_57]: (k2_lattices('#skF_5', B_57, k1_lattices('#skF_5', B_57, '#skF_7'))=B_57 | ~m1_subset_1(B_57, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_30, c_141])).
% 3.36/1.53  tff(c_163, plain, (![B_57]: (k2_lattices('#skF_5', B_57, k1_lattices('#skF_5', B_57, '#skF_7'))=B_57 | ~m1_subset_1(B_57, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36, c_153])).
% 3.36/1.53  tff(c_170, plain, (![B_59]: (k2_lattices('#skF_5', B_59, k1_lattices('#skF_5', B_59, '#skF_7'))=B_59 | ~m1_subset_1(B_59, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_44, c_163])).
% 3.36/1.53  tff(c_211, plain, (k2_lattices('#skF_5', '#skF_6', k1_lattices('#skF_5', '#skF_6', '#skF_7'))='#skF_6'), inference(resolution, [status(thm)], [c_32, c_170])).
% 3.36/1.53  tff(c_319, plain, (![A_62, B_63, C_64]: (k1_lattices(A_62, k2_lattices(A_62, B_63, C_64), C_64)=C_64 | ~m1_subset_1(C_64, u1_struct_0(A_62)) | ~m1_subset_1(B_63, u1_struct_0(A_62)) | ~v8_lattices(A_62) | ~l3_lattices(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.36/1.53  tff(c_1119, plain, (![A_105, B_106, B_107, C_108]: (k1_lattices(A_105, k2_lattices(A_105, B_106, k1_lattices(A_105, B_107, C_108)), k1_lattices(A_105, B_107, C_108))=k1_lattices(A_105, B_107, C_108) | ~m1_subset_1(B_106, u1_struct_0(A_105)) | ~v8_lattices(A_105) | ~l3_lattices(A_105) | ~m1_subset_1(C_108, u1_struct_0(A_105)) | ~m1_subset_1(B_107, u1_struct_0(A_105)) | ~l2_lattices(A_105) | v2_struct_0(A_105))), inference(resolution, [status(thm)], [c_22, c_319])).
% 3.36/1.53  tff(c_1257, plain, (k1_lattices('#skF_5', '#skF_6', k1_lattices('#skF_5', '#skF_6', '#skF_7'))=k1_lattices('#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~v8_lattices('#skF_5') | ~l3_lattices('#skF_5') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l2_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_211, c_1119])).
% 3.36/1.53  tff(c_1339, plain, (k1_lattices('#skF_5', '#skF_6', k1_lattices('#skF_5', '#skF_6', '#skF_7'))=k1_lattices('#skF_5', '#skF_6', '#skF_7') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_49, c_32, c_30, c_34, c_38, c_32, c_1257])).
% 3.36/1.53  tff(c_1341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_1054, c_1339])).
% 3.36/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.53  
% 3.36/1.53  Inference rules
% 3.36/1.53  ----------------------
% 3.36/1.53  #Ref     : 0
% 3.36/1.53  #Sup     : 249
% 3.36/1.53  #Fact    : 0
% 3.36/1.53  #Define  : 0
% 3.36/1.53  #Split   : 5
% 3.36/1.53  #Chain   : 0
% 3.36/1.53  #Close   : 0
% 3.36/1.53  
% 3.36/1.53  Ordering : KBO
% 3.36/1.53  
% 3.36/1.53  Simplification rules
% 3.36/1.53  ----------------------
% 3.36/1.53  #Subsume      : 42
% 3.36/1.53  #Demod        : 438
% 3.36/1.53  #Tautology    : 123
% 3.36/1.53  #SimpNegUnit  : 101
% 3.36/1.53  #BackRed      : 0
% 3.36/1.53  
% 3.36/1.53  #Partial instantiations: 0
% 3.36/1.53  #Strategies tried      : 1
% 3.36/1.53  
% 3.36/1.53  Timing (in seconds)
% 3.36/1.53  ----------------------
% 3.36/1.54  Preprocessing        : 0.30
% 3.36/1.54  Parsing              : 0.16
% 3.36/1.54  CNF conversion       : 0.02
% 3.36/1.54  Main loop            : 0.48
% 3.36/1.54  Inferencing          : 0.18
% 3.36/1.54  Reduction            : 0.16
% 3.36/1.54  Demodulation         : 0.12
% 3.36/1.54  BG Simplification    : 0.03
% 3.36/1.54  Subsumption          : 0.08
% 3.36/1.54  Abstraction          : 0.03
% 3.36/1.54  MUC search           : 0.00
% 3.36/1.54  Cooper               : 0.00
% 3.36/1.54  Total                : 0.80
% 3.36/1.54  Index Insertion      : 0.00
% 3.36/1.54  Index Deletion       : 0.00
% 3.36/1.54  Index Matching       : 0.00
% 3.36/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
