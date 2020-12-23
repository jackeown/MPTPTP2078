%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:21 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 109 expanded)
%              Number of leaves         :   17 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :  128 ( 463 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :   14 (   4 average)
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

tff(f_87,negated_conjecture,(
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
                   => ( ( ( r2_orders_2(A,B,C)
                          & r1_orders_2(A,C,D) )
                        | ( r1_orders_2(A,B,C)
                          & r2_orders_2(A,C,D) ) )
                     => r2_orders_2(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_orders_2)).

tff(f_61,axiom,(
    ! [A] :
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

tff(c_10,plain,(
    ~ r2_orders_2('#skF_1','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_26,plain,
    ( r2_orders_2('#skF_1','#skF_2','#skF_3')
    | r2_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_31,plain,(
    r2_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_16,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_22,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_20,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_18,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_14,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_12,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_159,plain,(
    ! [A_50,B_51,D_52,C_53] :
      ( r2_orders_2(A_50,B_51,D_52)
      | ~ r2_orders_2(A_50,C_53,D_52)
      | ~ r2_orders_2(A_50,B_51,C_53)
      | ~ m1_subset_1(D_52,u1_struct_0(A_50))
      | ~ m1_subset_1(C_53,u1_struct_0(A_50))
      | ~ m1_subset_1(B_51,u1_struct_0(A_50))
      | ~ l1_orders_2(A_50)
      | ~ v5_orders_2(A_50)
      | ~ v4_orders_2(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_161,plain,(
    ! [B_51] :
      ( r2_orders_2('#skF_1',B_51,'#skF_4')
      | ~ r2_orders_2('#skF_1',B_51,'#skF_3')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
      | ~ m1_subset_1(B_51,u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_31,c_159])).

tff(c_176,plain,(
    ! [B_54] :
      ( r2_orders_2('#skF_1',B_54,'#skF_4')
      | ~ r2_orders_2('#skF_1',B_54,'#skF_3')
      | ~ m1_subset_1(B_54,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_14,c_12,c_161])).

tff(c_185,plain,
    ( r2_orders_2('#skF_1','#skF_2','#skF_4')
    | ~ r2_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_176])).

tff(c_191,plain,(
    ~ r2_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_185])).

tff(c_28,plain,
    ( r1_orders_2('#skF_1','#skF_3','#skF_4')
    | r1_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_33,plain,(
    r1_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_42,plain,(
    ! [A_39,B_40,C_41] :
      ( r2_orders_2(A_39,B_40,C_41)
      | C_41 = B_40
      | ~ r1_orders_2(A_39,B_40,C_41)
      | ~ m1_subset_1(C_41,u1_struct_0(A_39))
      | ~ m1_subset_1(B_40,u1_struct_0(A_39))
      | ~ l1_orders_2(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_46,plain,(
    ! [B_40] :
      ( r2_orders_2('#skF_1',B_40,'#skF_3')
      | B_40 = '#skF_3'
      | ~ r1_orders_2('#skF_1',B_40,'#skF_3')
      | ~ m1_subset_1(B_40,u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_42])).

tff(c_207,plain,(
    ! [B_56] :
      ( r2_orders_2('#skF_1',B_56,'#skF_3')
      | B_56 = '#skF_3'
      | ~ r1_orders_2('#skF_1',B_56,'#skF_3')
      | ~ m1_subset_1(B_56,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_46])).

tff(c_216,plain,
    ( r2_orders_2('#skF_1','#skF_2','#skF_3')
    | '#skF_2' = '#skF_3'
    | ~ r1_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_207])).

tff(c_224,plain,
    ( r2_orders_2('#skF_1','#skF_2','#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_216])).

tff(c_225,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_224])).

tff(c_233,plain,(
    ~ r2_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_10])).

tff(c_237,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_233])).

tff(c_239,plain,(
    ~ r1_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_30,plain,
    ( r2_orders_2('#skF_1','#skF_2','#skF_3')
    | r1_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_240,plain,(
    r2_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_239,c_30])).

tff(c_242,plain,(
    ! [A_59,B_60,C_61] :
      ( r1_orders_2(A_59,B_60,C_61)
      | ~ r2_orders_2(A_59,B_60,C_61)
      | ~ m1_subset_1(C_61,u1_struct_0(A_59))
      | ~ m1_subset_1(B_60,u1_struct_0(A_59))
      | ~ l1_orders_2(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_244,plain,
    ( r1_orders_2('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_240,c_242])).

tff(c_249,plain,(
    r1_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_14,c_244])).

tff(c_251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_239,c_249])).

tff(c_253,plain,(
    ~ r2_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_24,plain,
    ( r1_orders_2('#skF_1','#skF_3','#skF_4')
    | r2_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_254,plain,(
    r1_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_253,c_24])).

tff(c_264,plain,(
    ! [A_67,B_68,C_69] :
      ( r2_orders_2(A_67,B_68,C_69)
      | C_69 = B_68
      | ~ r1_orders_2(A_67,B_68,C_69)
      | ~ m1_subset_1(C_69,u1_struct_0(A_67))
      | ~ m1_subset_1(B_68,u1_struct_0(A_67))
      | ~ l1_orders_2(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_266,plain,(
    ! [B_68] :
      ( r2_orders_2('#skF_1',B_68,'#skF_4')
      | B_68 = '#skF_4'
      | ~ r1_orders_2('#skF_1',B_68,'#skF_4')
      | ~ m1_subset_1(B_68,u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_12,c_264])).

tff(c_280,plain,(
    ! [B_70] :
      ( r2_orders_2('#skF_1',B_70,'#skF_4')
      | B_70 = '#skF_4'
      | ~ r1_orders_2('#skF_1',B_70,'#skF_4')
      | ~ m1_subset_1(B_70,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_266])).

tff(c_286,plain,
    ( r2_orders_2('#skF_1','#skF_3','#skF_4')
    | '#skF_3' = '#skF_4'
    | ~ r1_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_280])).

tff(c_294,plain,
    ( r2_orders_2('#skF_1','#skF_3','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_286])).

tff(c_295,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_253,c_294])).

tff(c_252,plain,(
    r2_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_302,plain,(
    r2_orders_2('#skF_1','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_252])).

tff(c_305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_302])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:30:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.25  
% 2.36/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.26  %$ r2_orders_2 > r1_orders_2 > m1_subset_1 > v5_orders_2 > v4_orders_2 > l1_orders_2 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.36/1.26  
% 2.36/1.26  %Foreground sorts:
% 2.36/1.26  
% 2.36/1.26  
% 2.36/1.26  %Background operators:
% 2.36/1.26  
% 2.36/1.26  
% 2.36/1.26  %Foreground operators:
% 2.36/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.26  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.36/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.36/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.36/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.36/1.26  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.36/1.26  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.36/1.26  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.36/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.36/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.26  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.36/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.36/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.36/1.26  
% 2.44/1.27  tff(f_87, negated_conjecture, ~(![A]: (((v4_orders_2(A) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (((r2_orders_2(A, B, C) & r1_orders_2(A, C, D)) | (r1_orders_2(A, B, C) & r2_orders_2(A, C, D))) => r2_orders_2(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_orders_2)).
% 2.44/1.27  tff(f_61, axiom, (![A]: (((v4_orders_2(A) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_orders_2(A, B, C) & r2_orders_2(A, C, D)) => r2_orders_2(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_orders_2)).
% 2.44/1.27  tff(f_40, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 2.44/1.27  tff(c_10, plain, (~r2_orders_2('#skF_1', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.44/1.27  tff(c_26, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_3') | r2_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.44/1.27  tff(c_31, plain, (r2_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_26])).
% 2.44/1.27  tff(c_16, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.44/1.27  tff(c_22, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.44/1.27  tff(c_20, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.44/1.27  tff(c_18, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.44/1.27  tff(c_14, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.44/1.27  tff(c_12, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.44/1.27  tff(c_159, plain, (![A_50, B_51, D_52, C_53]: (r2_orders_2(A_50, B_51, D_52) | ~r2_orders_2(A_50, C_53, D_52) | ~r2_orders_2(A_50, B_51, C_53) | ~m1_subset_1(D_52, u1_struct_0(A_50)) | ~m1_subset_1(C_53, u1_struct_0(A_50)) | ~m1_subset_1(B_51, u1_struct_0(A_50)) | ~l1_orders_2(A_50) | ~v5_orders_2(A_50) | ~v4_orders_2(A_50))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.44/1.27  tff(c_161, plain, (![B_51]: (r2_orders_2('#skF_1', B_51, '#skF_4') | ~r2_orders_2('#skF_1', B_51, '#skF_3') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~m1_subset_1(B_51, u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_31, c_159])).
% 2.44/1.27  tff(c_176, plain, (![B_54]: (r2_orders_2('#skF_1', B_54, '#skF_4') | ~r2_orders_2('#skF_1', B_54, '#skF_3') | ~m1_subset_1(B_54, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_18, c_14, c_12, c_161])).
% 2.44/1.27  tff(c_185, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_4') | ~r2_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_16, c_176])).
% 2.44/1.27  tff(c_191, plain, (~r2_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_10, c_185])).
% 2.44/1.27  tff(c_28, plain, (r1_orders_2('#skF_1', '#skF_3', '#skF_4') | r1_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.44/1.27  tff(c_33, plain, (r1_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_28])).
% 2.44/1.27  tff(c_42, plain, (![A_39, B_40, C_41]: (r2_orders_2(A_39, B_40, C_41) | C_41=B_40 | ~r1_orders_2(A_39, B_40, C_41) | ~m1_subset_1(C_41, u1_struct_0(A_39)) | ~m1_subset_1(B_40, u1_struct_0(A_39)) | ~l1_orders_2(A_39))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.44/1.27  tff(c_46, plain, (![B_40]: (r2_orders_2('#skF_1', B_40, '#skF_3') | B_40='#skF_3' | ~r1_orders_2('#skF_1', B_40, '#skF_3') | ~m1_subset_1(B_40, u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_42])).
% 2.44/1.27  tff(c_207, plain, (![B_56]: (r2_orders_2('#skF_1', B_56, '#skF_3') | B_56='#skF_3' | ~r1_orders_2('#skF_1', B_56, '#skF_3') | ~m1_subset_1(B_56, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_46])).
% 2.44/1.27  tff(c_216, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_3') | '#skF_2'='#skF_3' | ~r1_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_16, c_207])).
% 2.44/1.27  tff(c_224, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_3') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_33, c_216])).
% 2.44/1.27  tff(c_225, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_191, c_224])).
% 2.44/1.27  tff(c_233, plain, (~r2_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_225, c_10])).
% 2.44/1.27  tff(c_237, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_31, c_233])).
% 2.44/1.27  tff(c_239, plain, (~r1_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_28])).
% 2.44/1.27  tff(c_30, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_3') | r1_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.44/1.27  tff(c_240, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_239, c_30])).
% 2.44/1.27  tff(c_242, plain, (![A_59, B_60, C_61]: (r1_orders_2(A_59, B_60, C_61) | ~r2_orders_2(A_59, B_60, C_61) | ~m1_subset_1(C_61, u1_struct_0(A_59)) | ~m1_subset_1(B_60, u1_struct_0(A_59)) | ~l1_orders_2(A_59))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.44/1.27  tff(c_244, plain, (r1_orders_2('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_240, c_242])).
% 2.44/1.27  tff(c_249, plain, (r1_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_14, c_244])).
% 2.44/1.27  tff(c_251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_239, c_249])).
% 2.44/1.27  tff(c_253, plain, (~r2_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_26])).
% 2.44/1.27  tff(c_24, plain, (r1_orders_2('#skF_1', '#skF_3', '#skF_4') | r2_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.44/1.27  tff(c_254, plain, (r1_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_253, c_24])).
% 2.44/1.27  tff(c_264, plain, (![A_67, B_68, C_69]: (r2_orders_2(A_67, B_68, C_69) | C_69=B_68 | ~r1_orders_2(A_67, B_68, C_69) | ~m1_subset_1(C_69, u1_struct_0(A_67)) | ~m1_subset_1(B_68, u1_struct_0(A_67)) | ~l1_orders_2(A_67))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.44/1.27  tff(c_266, plain, (![B_68]: (r2_orders_2('#skF_1', B_68, '#skF_4') | B_68='#skF_4' | ~r1_orders_2('#skF_1', B_68, '#skF_4') | ~m1_subset_1(B_68, u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_264])).
% 2.44/1.27  tff(c_280, plain, (![B_70]: (r2_orders_2('#skF_1', B_70, '#skF_4') | B_70='#skF_4' | ~r1_orders_2('#skF_1', B_70, '#skF_4') | ~m1_subset_1(B_70, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_266])).
% 2.44/1.27  tff(c_286, plain, (r2_orders_2('#skF_1', '#skF_3', '#skF_4') | '#skF_3'='#skF_4' | ~r1_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_14, c_280])).
% 2.44/1.27  tff(c_294, plain, (r2_orders_2('#skF_1', '#skF_3', '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_254, c_286])).
% 2.44/1.27  tff(c_295, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_253, c_294])).
% 2.44/1.27  tff(c_252, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_26])).
% 2.44/1.27  tff(c_302, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_295, c_252])).
% 2.44/1.27  tff(c_305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_302])).
% 2.44/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.27  
% 2.44/1.27  Inference rules
% 2.44/1.27  ----------------------
% 2.44/1.27  #Ref     : 0
% 2.44/1.27  #Sup     : 38
% 2.44/1.27  #Fact    : 0
% 2.44/1.27  #Define  : 0
% 2.44/1.27  #Split   : 8
% 2.44/1.27  #Chain   : 0
% 2.44/1.27  #Close   : 0
% 2.44/1.27  
% 2.44/1.27  Ordering : KBO
% 2.44/1.27  
% 2.44/1.27  Simplification rules
% 2.44/1.27  ----------------------
% 2.44/1.27  #Subsume      : 3
% 2.44/1.27  #Demod        : 83
% 2.44/1.27  #Tautology    : 15
% 2.44/1.27  #SimpNegUnit  : 13
% 2.44/1.27  #BackRed      : 27
% 2.44/1.27  
% 2.44/1.27  #Partial instantiations: 0
% 2.44/1.27  #Strategies tried      : 1
% 2.44/1.27  
% 2.44/1.27  Timing (in seconds)
% 2.44/1.27  ----------------------
% 2.44/1.27  Preprocessing        : 0.27
% 2.44/1.27  Parsing              : 0.15
% 2.44/1.27  CNF conversion       : 0.02
% 2.44/1.27  Main loop            : 0.22
% 2.44/1.27  Inferencing          : 0.08
% 2.44/1.27  Reduction            : 0.07
% 2.44/1.27  Demodulation         : 0.05
% 2.44/1.28  BG Simplification    : 0.02
% 2.44/1.28  Subsumption          : 0.04
% 2.44/1.28  Abstraction          : 0.01
% 2.44/1.28  MUC search           : 0.00
% 2.44/1.28  Cooper               : 0.00
% 2.44/1.28  Total                : 0.52
% 2.44/1.28  Index Insertion      : 0.00
% 2.44/1.28  Index Deletion       : 0.00
% 2.44/1.28  Index Matching       : 0.00
% 2.44/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
