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
% DateTime   : Thu Dec  3 10:19:21 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 243 expanded)
%              Number of leaves         :   18 (  90 expanded)
%              Depth                    :   11
%              Number of atoms          :  177 (1109 expanded)
%              Number of equality atoms :   23 (  62 expanded)
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

tff(f_101,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_orders_2)).

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

tff(f_75,axiom,(
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

tff(f_56,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( r1_orders_2(A,B,C)
                  & r1_orders_2(A,C,B) )
               => B = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_orders_2)).

tff(c_12,plain,(
    ~ r2_orders_2('#skF_1','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_20,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_14,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_44,plain,(
    ! [A_46,B_47,C_48] :
      ( r2_orders_2(A_46,B_47,C_48)
      | C_48 = B_47
      | ~ r1_orders_2(A_46,B_47,C_48)
      | ~ m1_subset_1(C_48,u1_struct_0(A_46))
      | ~ m1_subset_1(B_47,u1_struct_0(A_46))
      | ~ l1_orders_2(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_46,plain,(
    ! [B_47] :
      ( r2_orders_2('#skF_1',B_47,'#skF_4')
      | B_47 = '#skF_4'
      | ~ r1_orders_2('#skF_1',B_47,'#skF_4')
      | ~ m1_subset_1(B_47,u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_44])).

tff(c_60,plain,(
    ! [B_49] :
      ( r2_orders_2('#skF_1',B_49,'#skF_4')
      | B_49 = '#skF_4'
      | ~ r1_orders_2('#skF_1',B_49,'#skF_4')
      | ~ m1_subset_1(B_49,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_46])).

tff(c_69,plain,
    ( r2_orders_2('#skF_1','#skF_2','#skF_4')
    | '#skF_2' = '#skF_4'
    | ~ r1_orders_2('#skF_1','#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_60])).

tff(c_77,plain,
    ( '#skF_2' = '#skF_4'
    | ~ r1_orders_2('#skF_1','#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_69])).

tff(c_78,plain,(
    ~ r1_orders_2('#skF_1','#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_30,plain,
    ( r1_orders_2('#skF_1','#skF_3','#skF_4')
    | r1_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_35,plain,(
    r1_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_24,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_16,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_28,plain,
    ( r2_orders_2('#skF_1','#skF_2','#skF_3')
    | r2_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_33,plain,(
    r2_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_38,plain,(
    ! [A_43,B_44,C_45] :
      ( r1_orders_2(A_43,B_44,C_45)
      | ~ r2_orders_2(A_43,B_44,C_45)
      | ~ m1_subset_1(C_45,u1_struct_0(A_43))
      | ~ m1_subset_1(B_44,u1_struct_0(A_43))
      | ~ l1_orders_2(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_40,plain,
    ( r1_orders_2('#skF_1','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_33,c_38])).

tff(c_43,plain,(
    r1_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_14,c_40])).

tff(c_141,plain,(
    ! [A_55,B_56,D_57,C_58] :
      ( r1_orders_2(A_55,B_56,D_57)
      | ~ r1_orders_2(A_55,C_58,D_57)
      | ~ r1_orders_2(A_55,B_56,C_58)
      | ~ m1_subset_1(D_57,u1_struct_0(A_55))
      | ~ m1_subset_1(C_58,u1_struct_0(A_55))
      | ~ m1_subset_1(B_56,u1_struct_0(A_55))
      | ~ l1_orders_2(A_55)
      | ~ v4_orders_2(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_143,plain,(
    ! [B_56] :
      ( r1_orders_2('#skF_1',B_56,'#skF_4')
      | ~ r1_orders_2('#skF_1',B_56,'#skF_3')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
      | ~ m1_subset_1(B_56,u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_43,c_141])).

tff(c_167,plain,(
    ! [B_60] :
      ( r1_orders_2('#skF_1',B_60,'#skF_4')
      | ~ r1_orders_2('#skF_1',B_60,'#skF_3')
      | ~ m1_subset_1(B_60,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_16,c_14,c_143])).

tff(c_176,plain,
    ( r1_orders_2('#skF_1','#skF_2','#skF_4')
    | ~ r1_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_167])).

tff(c_182,plain,(
    r1_orders_2('#skF_1','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_176])).

tff(c_184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_182])).

tff(c_185,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_188,plain,(
    ~ r2_orders_2('#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_12])).

tff(c_187,plain,(
    r1_orders_2('#skF_1','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_35])).

tff(c_48,plain,(
    ! [B_47] :
      ( r2_orders_2('#skF_1',B_47,'#skF_3')
      | B_47 = '#skF_3'
      | ~ r1_orders_2('#skF_1',B_47,'#skF_3')
      | ~ m1_subset_1(B_47,u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_16,c_44])).

tff(c_197,plain,(
    ! [B_61] :
      ( r2_orders_2('#skF_1',B_61,'#skF_3')
      | B_61 = '#skF_3'
      | ~ r1_orders_2('#skF_1',B_61,'#skF_3')
      | ~ m1_subset_1(B_61,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_48])).

tff(c_200,plain,
    ( r2_orders_2('#skF_1','#skF_4','#skF_3')
    | '#skF_3' = '#skF_4'
    | ~ r1_orders_2('#skF_1','#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_197])).

tff(c_206,plain,
    ( r2_orders_2('#skF_1','#skF_4','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_200])).

tff(c_209,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_206])).

tff(c_213,plain,(
    r2_orders_2('#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_33])).

tff(c_218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_213])).

tff(c_220,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_22,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_221,plain,(
    ! [C_62,B_63,A_64] :
      ( C_62 = B_63
      | ~ r1_orders_2(A_64,C_62,B_63)
      | ~ r1_orders_2(A_64,B_63,C_62)
      | ~ m1_subset_1(C_62,u1_struct_0(A_64))
      | ~ m1_subset_1(B_63,u1_struct_0(A_64))
      | ~ l1_orders_2(A_64)
      | ~ v5_orders_2(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_223,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_orders_2('#skF_1','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_187,c_221])).

tff(c_230,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_16,c_14,c_43,c_223])).

tff(c_232,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_220,c_230])).

tff(c_234,plain,(
    ~ r1_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_32,plain,
    ( r2_orders_2('#skF_1','#skF_2','#skF_3')
    | r1_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_235,plain,(
    r2_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_234,c_32])).

tff(c_237,plain,(
    ! [A_67,B_68,C_69] :
      ( r1_orders_2(A_67,B_68,C_69)
      | ~ r2_orders_2(A_67,B_68,C_69)
      | ~ m1_subset_1(C_69,u1_struct_0(A_67))
      | ~ m1_subset_1(B_68,u1_struct_0(A_67))
      | ~ l1_orders_2(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_239,plain,
    ( r1_orders_2('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_235,c_237])).

tff(c_244,plain,(
    r1_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_239])).

tff(c_246,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_234,c_244])).

tff(c_248,plain,(
    ~ r2_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_26,plain,
    ( r1_orders_2('#skF_1','#skF_3','#skF_4')
    | r2_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_250,plain,(
    r1_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_248,c_26])).

tff(c_259,plain,(
    ! [A_75,B_76,C_77] :
      ( r2_orders_2(A_75,B_76,C_77)
      | C_77 = B_76
      | ~ r1_orders_2(A_75,B_76,C_77)
      | ~ m1_subset_1(C_77,u1_struct_0(A_75))
      | ~ m1_subset_1(B_76,u1_struct_0(A_75))
      | ~ l1_orders_2(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_261,plain,(
    ! [B_76] :
      ( r2_orders_2('#skF_1',B_76,'#skF_4')
      | B_76 = '#skF_4'
      | ~ r1_orders_2('#skF_1',B_76,'#skF_4')
      | ~ m1_subset_1(B_76,u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_259])).

tff(c_275,plain,(
    ! [B_78] :
      ( r2_orders_2('#skF_1',B_78,'#skF_4')
      | B_78 = '#skF_4'
      | ~ r1_orders_2('#skF_1',B_78,'#skF_4')
      | ~ m1_subset_1(B_78,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_261])).

tff(c_281,plain,
    ( r2_orders_2('#skF_1','#skF_3','#skF_4')
    | '#skF_3' = '#skF_4'
    | ~ r1_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_275])).

tff(c_289,plain,
    ( r2_orders_2('#skF_1','#skF_3','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_281])).

tff(c_290,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_248,c_289])).

tff(c_247,plain,(
    r2_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_297,plain,(
    r2_orders_2('#skF_1','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_247])).

tff(c_300,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_297])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:24:08 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.27  
% 2.19/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.27  %$ r2_orders_2 > r1_orders_2 > m1_subset_1 > v5_orders_2 > v4_orders_2 > l1_orders_2 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.19/1.27  
% 2.19/1.27  %Foreground sorts:
% 2.19/1.27  
% 2.19/1.27  
% 2.19/1.27  %Background operators:
% 2.19/1.27  
% 2.19/1.27  
% 2.19/1.27  %Foreground operators:
% 2.19/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.27  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.19/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.19/1.27  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.19/1.27  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.19/1.27  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.19/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.19/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.27  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.19/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.19/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.27  
% 2.19/1.29  tff(f_101, negated_conjecture, ~(![A]: (((v4_orders_2(A) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (((r2_orders_2(A, B, C) & r1_orders_2(A, C, D)) | (r1_orders_2(A, B, C) & r2_orders_2(A, C, D))) => r2_orders_2(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_orders_2)).
% 2.19/1.29  tff(f_40, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 2.19/1.29  tff(f_75, axiom, (![A]: ((v4_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r1_orders_2(A, B, C) & r1_orders_2(A, C, D)) => r1_orders_2(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_orders_2)).
% 2.19/1.29  tff(f_56, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((r1_orders_2(A, B, C) & r1_orders_2(A, C, B)) => (B = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_orders_2)).
% 2.19/1.29  tff(c_12, plain, (~r2_orders_2('#skF_1', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.19/1.29  tff(c_18, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.19/1.29  tff(c_20, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.19/1.29  tff(c_14, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.19/1.29  tff(c_44, plain, (![A_46, B_47, C_48]: (r2_orders_2(A_46, B_47, C_48) | C_48=B_47 | ~r1_orders_2(A_46, B_47, C_48) | ~m1_subset_1(C_48, u1_struct_0(A_46)) | ~m1_subset_1(B_47, u1_struct_0(A_46)) | ~l1_orders_2(A_46))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.19/1.29  tff(c_46, plain, (![B_47]: (r2_orders_2('#skF_1', B_47, '#skF_4') | B_47='#skF_4' | ~r1_orders_2('#skF_1', B_47, '#skF_4') | ~m1_subset_1(B_47, u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_44])).
% 2.19/1.29  tff(c_60, plain, (![B_49]: (r2_orders_2('#skF_1', B_49, '#skF_4') | B_49='#skF_4' | ~r1_orders_2('#skF_1', B_49, '#skF_4') | ~m1_subset_1(B_49, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_46])).
% 2.19/1.29  tff(c_69, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_4') | '#skF_2'='#skF_4' | ~r1_orders_2('#skF_1', '#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_18, c_60])).
% 2.19/1.29  tff(c_77, plain, ('#skF_2'='#skF_4' | ~r1_orders_2('#skF_1', '#skF_2', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_12, c_69])).
% 2.19/1.29  tff(c_78, plain, (~r1_orders_2('#skF_1', '#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_77])).
% 2.19/1.29  tff(c_30, plain, (r1_orders_2('#skF_1', '#skF_3', '#skF_4') | r1_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.19/1.29  tff(c_35, plain, (r1_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_30])).
% 2.19/1.29  tff(c_24, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.19/1.29  tff(c_16, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.19/1.29  tff(c_28, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_3') | r2_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.19/1.29  tff(c_33, plain, (r2_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_28])).
% 2.19/1.29  tff(c_38, plain, (![A_43, B_44, C_45]: (r1_orders_2(A_43, B_44, C_45) | ~r2_orders_2(A_43, B_44, C_45) | ~m1_subset_1(C_45, u1_struct_0(A_43)) | ~m1_subset_1(B_44, u1_struct_0(A_43)) | ~l1_orders_2(A_43))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.19/1.29  tff(c_40, plain, (r1_orders_2('#skF_1', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_33, c_38])).
% 2.19/1.29  tff(c_43, plain, (r1_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_14, c_40])).
% 2.19/1.29  tff(c_141, plain, (![A_55, B_56, D_57, C_58]: (r1_orders_2(A_55, B_56, D_57) | ~r1_orders_2(A_55, C_58, D_57) | ~r1_orders_2(A_55, B_56, C_58) | ~m1_subset_1(D_57, u1_struct_0(A_55)) | ~m1_subset_1(C_58, u1_struct_0(A_55)) | ~m1_subset_1(B_56, u1_struct_0(A_55)) | ~l1_orders_2(A_55) | ~v4_orders_2(A_55))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.19/1.29  tff(c_143, plain, (![B_56]: (r1_orders_2('#skF_1', B_56, '#skF_4') | ~r1_orders_2('#skF_1', B_56, '#skF_3') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~m1_subset_1(B_56, u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1') | ~v4_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_43, c_141])).
% 2.19/1.29  tff(c_167, plain, (![B_60]: (r1_orders_2('#skF_1', B_60, '#skF_4') | ~r1_orders_2('#skF_1', B_60, '#skF_3') | ~m1_subset_1(B_60, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_16, c_14, c_143])).
% 2.19/1.29  tff(c_176, plain, (r1_orders_2('#skF_1', '#skF_2', '#skF_4') | ~r1_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_18, c_167])).
% 2.19/1.29  tff(c_182, plain, (r1_orders_2('#skF_1', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_35, c_176])).
% 2.19/1.29  tff(c_184, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_182])).
% 2.19/1.29  tff(c_185, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_77])).
% 2.19/1.29  tff(c_188, plain, (~r2_orders_2('#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_185, c_12])).
% 2.19/1.29  tff(c_187, plain, (r1_orders_2('#skF_1', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_185, c_35])).
% 2.19/1.29  tff(c_48, plain, (![B_47]: (r2_orders_2('#skF_1', B_47, '#skF_3') | B_47='#skF_3' | ~r1_orders_2('#skF_1', B_47, '#skF_3') | ~m1_subset_1(B_47, u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_16, c_44])).
% 2.19/1.29  tff(c_197, plain, (![B_61]: (r2_orders_2('#skF_1', B_61, '#skF_3') | B_61='#skF_3' | ~r1_orders_2('#skF_1', B_61, '#skF_3') | ~m1_subset_1(B_61, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_48])).
% 2.19/1.29  tff(c_200, plain, (r2_orders_2('#skF_1', '#skF_4', '#skF_3') | '#skF_3'='#skF_4' | ~r1_orders_2('#skF_1', '#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_14, c_197])).
% 2.19/1.29  tff(c_206, plain, (r2_orders_2('#skF_1', '#skF_4', '#skF_3') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_187, c_200])).
% 2.19/1.29  tff(c_209, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_206])).
% 2.19/1.29  tff(c_213, plain, (r2_orders_2('#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_209, c_33])).
% 2.19/1.29  tff(c_218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_188, c_213])).
% 2.19/1.29  tff(c_220, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_206])).
% 2.19/1.29  tff(c_22, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.19/1.29  tff(c_221, plain, (![C_62, B_63, A_64]: (C_62=B_63 | ~r1_orders_2(A_64, C_62, B_63) | ~r1_orders_2(A_64, B_63, C_62) | ~m1_subset_1(C_62, u1_struct_0(A_64)) | ~m1_subset_1(B_63, u1_struct_0(A_64)) | ~l1_orders_2(A_64) | ~v5_orders_2(A_64))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.19/1.29  tff(c_223, plain, ('#skF_3'='#skF_4' | ~r1_orders_2('#skF_1', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_187, c_221])).
% 2.19/1.29  tff(c_230, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_16, c_14, c_43, c_223])).
% 2.19/1.29  tff(c_232, plain, $false, inference(negUnitSimplification, [status(thm)], [c_220, c_230])).
% 2.19/1.29  tff(c_234, plain, (~r1_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 2.19/1.29  tff(c_32, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_3') | r1_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.19/1.29  tff(c_235, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_234, c_32])).
% 2.19/1.29  tff(c_237, plain, (![A_67, B_68, C_69]: (r1_orders_2(A_67, B_68, C_69) | ~r2_orders_2(A_67, B_68, C_69) | ~m1_subset_1(C_69, u1_struct_0(A_67)) | ~m1_subset_1(B_68, u1_struct_0(A_67)) | ~l1_orders_2(A_67))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.19/1.29  tff(c_239, plain, (r1_orders_2('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_235, c_237])).
% 2.19/1.29  tff(c_244, plain, (r1_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_16, c_239])).
% 2.19/1.29  tff(c_246, plain, $false, inference(negUnitSimplification, [status(thm)], [c_234, c_244])).
% 2.19/1.29  tff(c_248, plain, (~r2_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_28])).
% 2.19/1.29  tff(c_26, plain, (r1_orders_2('#skF_1', '#skF_3', '#skF_4') | r2_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.19/1.29  tff(c_250, plain, (r1_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_248, c_26])).
% 2.19/1.29  tff(c_259, plain, (![A_75, B_76, C_77]: (r2_orders_2(A_75, B_76, C_77) | C_77=B_76 | ~r1_orders_2(A_75, B_76, C_77) | ~m1_subset_1(C_77, u1_struct_0(A_75)) | ~m1_subset_1(B_76, u1_struct_0(A_75)) | ~l1_orders_2(A_75))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.19/1.29  tff(c_261, plain, (![B_76]: (r2_orders_2('#skF_1', B_76, '#skF_4') | B_76='#skF_4' | ~r1_orders_2('#skF_1', B_76, '#skF_4') | ~m1_subset_1(B_76, u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_259])).
% 2.19/1.29  tff(c_275, plain, (![B_78]: (r2_orders_2('#skF_1', B_78, '#skF_4') | B_78='#skF_4' | ~r1_orders_2('#skF_1', B_78, '#skF_4') | ~m1_subset_1(B_78, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_261])).
% 2.19/1.29  tff(c_281, plain, (r2_orders_2('#skF_1', '#skF_3', '#skF_4') | '#skF_3'='#skF_4' | ~r1_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_16, c_275])).
% 2.19/1.29  tff(c_289, plain, (r2_orders_2('#skF_1', '#skF_3', '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_250, c_281])).
% 2.19/1.29  tff(c_290, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_248, c_289])).
% 2.19/1.29  tff(c_247, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_28])).
% 2.19/1.29  tff(c_297, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_290, c_247])).
% 2.19/1.29  tff(c_300, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_297])).
% 2.19/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.29  
% 2.19/1.29  Inference rules
% 2.19/1.29  ----------------------
% 2.19/1.29  #Ref     : 0
% 2.19/1.29  #Sup     : 40
% 2.19/1.29  #Fact    : 0
% 2.19/1.29  #Define  : 0
% 2.19/1.29  #Split   : 8
% 2.19/1.29  #Chain   : 0
% 2.19/1.29  #Close   : 0
% 2.19/1.29  
% 2.19/1.29  Ordering : KBO
% 2.19/1.29  
% 2.19/1.29  Simplification rules
% 2.19/1.29  ----------------------
% 2.19/1.29  #Subsume      : 9
% 2.19/1.29  #Demod        : 84
% 2.19/1.29  #Tautology    : 18
% 2.19/1.29  #SimpNegUnit  : 11
% 2.19/1.29  #BackRed      : 20
% 2.19/1.29  
% 2.19/1.29  #Partial instantiations: 0
% 2.19/1.29  #Strategies tried      : 1
% 2.19/1.29  
% 2.19/1.29  Timing (in seconds)
% 2.19/1.29  ----------------------
% 2.19/1.30  Preprocessing        : 0.29
% 2.19/1.30  Parsing              : 0.16
% 2.19/1.30  CNF conversion       : 0.02
% 2.19/1.30  Main loop            : 0.23
% 2.19/1.30  Inferencing          : 0.09
% 2.19/1.30  Reduction            : 0.07
% 2.19/1.30  Demodulation         : 0.05
% 2.19/1.30  BG Simplification    : 0.02
% 2.19/1.30  Subsumption          : 0.04
% 2.19/1.30  Abstraction          : 0.01
% 2.19/1.30  MUC search           : 0.00
% 2.19/1.30  Cooper               : 0.00
% 2.19/1.30  Total                : 0.57
% 2.19/1.30  Index Insertion      : 0.00
% 2.19/1.30  Index Deletion       : 0.00
% 2.19/1.30  Index Matching       : 0.00
% 2.19/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
