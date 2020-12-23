%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:21 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 103 expanded)
%              Number of leaves         :   18 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :  111 ( 406 expanded)
%              Number of equality atoms :    7 (  15 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > m1_subset_1 > v5_orders_2 > v4_orders_2 > l1_orders_2 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ( v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r2_orders_2(A,B,C)
                        & r2_orders_2(A,C,D) )
                     => r2_orders_2(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_orders_2)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_orders_2(A,B,C)
              <=> ( r1_orders_2(A,B,C)
                  & B != C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( ( r1_orders_2(A,B,C)
                      & r1_orders_2(A,C,D) )
                   => r1_orders_2(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_orders_2)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ~ ( r2_orders_2(A,B,C)
                  & r2_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_orders_2)).

tff(c_14,plain,(
    r2_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_12,plain,(
    ~ r2_orders_2('#skF_1','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_24,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_18,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_41,plain,(
    ! [A_46,B_47,C_48] :
      ( r2_orders_2(A_46,B_47,C_48)
      | C_48 = B_47
      | ~ r1_orders_2(A_46,B_47,C_48)
      | ~ m1_subset_1(C_48,u1_struct_0(A_46))
      | ~ m1_subset_1(B_47,u1_struct_0(A_46))
      | ~ l1_orders_2(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_43,plain,(
    ! [B_47] :
      ( r2_orders_2('#skF_1',B_47,'#skF_4')
      | B_47 = '#skF_4'
      | ~ r1_orders_2('#skF_1',B_47,'#skF_4')
      | ~ m1_subset_1(B_47,u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_18,c_41])).

tff(c_57,plain,(
    ! [B_49] :
      ( r2_orders_2('#skF_1',B_49,'#skF_4')
      | B_49 = '#skF_4'
      | ~ r1_orders_2('#skF_1',B_49,'#skF_4')
      | ~ m1_subset_1(B_49,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_43])).

tff(c_66,plain,
    ( r2_orders_2('#skF_1','#skF_2','#skF_4')
    | '#skF_2' = '#skF_4'
    | ~ r1_orders_2('#skF_1','#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_57])).

tff(c_74,plain,
    ( '#skF_2' = '#skF_4'
    | ~ r1_orders_2('#skF_1','#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_66])).

tff(c_86,plain,(
    ~ r1_orders_2('#skF_1','#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_16,plain,(
    r2_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_30,plain,(
    ! [A_43,B_44,C_45] :
      ( r1_orders_2(A_43,B_44,C_45)
      | ~ r2_orders_2(A_43,B_44,C_45)
      | ~ m1_subset_1(C_45,u1_struct_0(A_43))
      | ~ m1_subset_1(B_44,u1_struct_0(A_43))
      | ~ l1_orders_2(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_32,plain,
    ( r1_orders_2('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_30])).

tff(c_37,plain,(
    r1_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_32])).

tff(c_28,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_34,plain,
    ( r1_orders_2('#skF_1','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_30])).

tff(c_40,plain,(
    r1_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_18,c_34])).

tff(c_105,plain,(
    ! [A_54,B_55,D_56,C_57] :
      ( r1_orders_2(A_54,B_55,D_56)
      | ~ r1_orders_2(A_54,C_57,D_56)
      | ~ r1_orders_2(A_54,B_55,C_57)
      | ~ m1_subset_1(D_56,u1_struct_0(A_54))
      | ~ m1_subset_1(C_57,u1_struct_0(A_54))
      | ~ m1_subset_1(B_55,u1_struct_0(A_54))
      | ~ l1_orders_2(A_54)
      | ~ v4_orders_2(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_107,plain,(
    ! [B_55] :
      ( r1_orders_2('#skF_1',B_55,'#skF_4')
      | ~ r1_orders_2('#skF_1',B_55,'#skF_3')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
      | ~ m1_subset_1(B_55,u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_105])).

tff(c_116,plain,(
    ! [B_58] :
      ( r1_orders_2('#skF_1',B_58,'#skF_4')
      | ~ r1_orders_2('#skF_1',B_58,'#skF_3')
      | ~ m1_subset_1(B_58,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_20,c_18,c_107])).

tff(c_125,plain,
    ( r1_orders_2('#skF_1','#skF_2','#skF_4')
    | ~ r1_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_116])).

tff(c_131,plain,(
    r1_orders_2('#skF_1','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_125])).

tff(c_133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_131])).

tff(c_134,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_26,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_75,plain,(
    ! [A_50,C_51,B_52] :
      ( ~ r2_orders_2(A_50,C_51,B_52)
      | ~ r2_orders_2(A_50,B_52,C_51)
      | ~ m1_subset_1(C_51,u1_struct_0(A_50))
      | ~ m1_subset_1(B_52,u1_struct_0(A_50))
      | ~ l1_orders_2(A_50)
      | ~ v5_orders_2(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_77,plain,
    ( ~ r2_orders_2('#skF_1','#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_75])).

tff(c_82,plain,(
    ~ r2_orders_2('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_20,c_22,c_77])).

tff(c_136,plain,(
    ~ r2_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_82])).

tff(c_143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:58:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.29  
% 2.04/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.29  %$ r2_orders_2 > r1_orders_2 > m1_subset_1 > v5_orders_2 > v4_orders_2 > l1_orders_2 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.04/1.29  
% 2.04/1.29  %Foreground sorts:
% 2.04/1.29  
% 2.04/1.29  
% 2.04/1.29  %Background operators:
% 2.04/1.29  
% 2.04/1.29  
% 2.04/1.29  %Foreground operators:
% 2.04/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.29  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.04/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.04/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.04/1.29  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.04/1.29  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.04/1.29  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.04/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.04/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.29  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.04/1.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.04/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.04/1.29  
% 2.04/1.30  tff(f_96, negated_conjecture, ~(![A]: (((v4_orders_2(A) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_orders_2(A, B, C) & r2_orders_2(A, C, D)) => r2_orders_2(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_orders_2)).
% 2.04/1.30  tff(f_40, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 2.04/1.30  tff(f_59, axiom, (![A]: ((v4_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r1_orders_2(A, B, C) & r1_orders_2(A, C, D)) => r1_orders_2(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_orders_2)).
% 2.04/1.30  tff(f_74, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_orders_2(A, B, C) & r2_orders_2(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_orders_2)).
% 2.04/1.30  tff(c_14, plain, (r2_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.04/1.30  tff(c_12, plain, (~r2_orders_2('#skF_1', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.04/1.30  tff(c_22, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.04/1.30  tff(c_24, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.04/1.30  tff(c_18, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.04/1.30  tff(c_41, plain, (![A_46, B_47, C_48]: (r2_orders_2(A_46, B_47, C_48) | C_48=B_47 | ~r1_orders_2(A_46, B_47, C_48) | ~m1_subset_1(C_48, u1_struct_0(A_46)) | ~m1_subset_1(B_47, u1_struct_0(A_46)) | ~l1_orders_2(A_46))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.04/1.30  tff(c_43, plain, (![B_47]: (r2_orders_2('#skF_1', B_47, '#skF_4') | B_47='#skF_4' | ~r1_orders_2('#skF_1', B_47, '#skF_4') | ~m1_subset_1(B_47, u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_41])).
% 2.04/1.30  tff(c_57, plain, (![B_49]: (r2_orders_2('#skF_1', B_49, '#skF_4') | B_49='#skF_4' | ~r1_orders_2('#skF_1', B_49, '#skF_4') | ~m1_subset_1(B_49, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_43])).
% 2.04/1.30  tff(c_66, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_4') | '#skF_2'='#skF_4' | ~r1_orders_2('#skF_1', '#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_22, c_57])).
% 2.04/1.30  tff(c_74, plain, ('#skF_2'='#skF_4' | ~r1_orders_2('#skF_1', '#skF_2', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_12, c_66])).
% 2.04/1.30  tff(c_86, plain, (~r1_orders_2('#skF_1', '#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_74])).
% 2.04/1.30  tff(c_20, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.04/1.30  tff(c_16, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.04/1.30  tff(c_30, plain, (![A_43, B_44, C_45]: (r1_orders_2(A_43, B_44, C_45) | ~r2_orders_2(A_43, B_44, C_45) | ~m1_subset_1(C_45, u1_struct_0(A_43)) | ~m1_subset_1(B_44, u1_struct_0(A_43)) | ~l1_orders_2(A_43))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.04/1.30  tff(c_32, plain, (r1_orders_2('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_16, c_30])).
% 2.04/1.30  tff(c_37, plain, (r1_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_32])).
% 2.04/1.30  tff(c_28, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.04/1.30  tff(c_34, plain, (r1_orders_2('#skF_1', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_14, c_30])).
% 2.04/1.30  tff(c_40, plain, (r1_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_18, c_34])).
% 2.04/1.30  tff(c_105, plain, (![A_54, B_55, D_56, C_57]: (r1_orders_2(A_54, B_55, D_56) | ~r1_orders_2(A_54, C_57, D_56) | ~r1_orders_2(A_54, B_55, C_57) | ~m1_subset_1(D_56, u1_struct_0(A_54)) | ~m1_subset_1(C_57, u1_struct_0(A_54)) | ~m1_subset_1(B_55, u1_struct_0(A_54)) | ~l1_orders_2(A_54) | ~v4_orders_2(A_54))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.04/1.30  tff(c_107, plain, (![B_55]: (r1_orders_2('#skF_1', B_55, '#skF_4') | ~r1_orders_2('#skF_1', B_55, '#skF_3') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~m1_subset_1(B_55, u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1') | ~v4_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_105])).
% 2.04/1.30  tff(c_116, plain, (![B_58]: (r1_orders_2('#skF_1', B_58, '#skF_4') | ~r1_orders_2('#skF_1', B_58, '#skF_3') | ~m1_subset_1(B_58, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_20, c_18, c_107])).
% 2.04/1.30  tff(c_125, plain, (r1_orders_2('#skF_1', '#skF_2', '#skF_4') | ~r1_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_116])).
% 2.04/1.30  tff(c_131, plain, (r1_orders_2('#skF_1', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_37, c_125])).
% 2.04/1.30  tff(c_133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_131])).
% 2.04/1.30  tff(c_134, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_74])).
% 2.04/1.30  tff(c_26, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.04/1.30  tff(c_75, plain, (![A_50, C_51, B_52]: (~r2_orders_2(A_50, C_51, B_52) | ~r2_orders_2(A_50, B_52, C_51) | ~m1_subset_1(C_51, u1_struct_0(A_50)) | ~m1_subset_1(B_52, u1_struct_0(A_50)) | ~l1_orders_2(A_50) | ~v5_orders_2(A_50))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.04/1.30  tff(c_77, plain, (~r2_orders_2('#skF_1', '#skF_3', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_16, c_75])).
% 2.04/1.30  tff(c_82, plain, (~r2_orders_2('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_20, c_22, c_77])).
% 2.04/1.30  tff(c_136, plain, (~r2_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_82])).
% 2.04/1.30  tff(c_143, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_136])).
% 2.04/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.30  
% 2.04/1.30  Inference rules
% 2.04/1.30  ----------------------
% 2.04/1.30  #Ref     : 0
% 2.04/1.30  #Sup     : 18
% 2.04/1.30  #Fact    : 0
% 2.04/1.30  #Define  : 0
% 2.04/1.30  #Split   : 3
% 2.04/1.30  #Chain   : 0
% 2.04/1.30  #Close   : 0
% 2.04/1.30  
% 2.04/1.30  Ordering : KBO
% 2.04/1.30  
% 2.04/1.30  Simplification rules
% 2.04/1.30  ----------------------
% 2.04/1.30  #Subsume      : 0
% 2.04/1.30  #Demod        : 35
% 2.04/1.30  #Tautology    : 4
% 2.04/1.30  #SimpNegUnit  : 3
% 2.04/1.30  #BackRed      : 5
% 2.04/1.30  
% 2.04/1.30  #Partial instantiations: 0
% 2.04/1.30  #Strategies tried      : 1
% 2.04/1.30  
% 2.04/1.30  Timing (in seconds)
% 2.04/1.30  ----------------------
% 2.04/1.31  Preprocessing        : 0.32
% 2.04/1.31  Parsing              : 0.18
% 2.04/1.31  CNF conversion       : 0.03
% 2.04/1.31  Main loop            : 0.16
% 2.04/1.31  Inferencing          : 0.06
% 2.04/1.31  Reduction            : 0.05
% 2.04/1.31  Demodulation         : 0.04
% 2.04/1.31  BG Simplification    : 0.01
% 2.04/1.31  Subsumption          : 0.02
% 2.04/1.31  Abstraction          : 0.01
% 2.04/1.31  MUC search           : 0.00
% 2.04/1.31  Cooper               : 0.00
% 2.04/1.31  Total                : 0.51
% 2.04/1.31  Index Insertion      : 0.00
% 2.04/1.31  Index Deletion       : 0.00
% 2.04/1.31  Index Matching       : 0.00
% 2.04/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
